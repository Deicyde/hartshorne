"""Stream the stock skeleton bytes and hashes through its original transaction guards."""

import contextlib
import hashlib
import json
import os
from pathlib import Path
import secrets
import stat

from autoform_cli import skeleton as sk


def text_bytes(parts):
    for part in parts:
        for offset in range(0, len(part), 1024 * 1024):
            yield part[offset:offset + 1024 * 1024].encode("utf-8")


def text_hash(parts):
    digest = hashlib.sha256()
    for block in text_bytes(parts):
        digest.update(block)
    return "sha256:" + digest.hexdigest()


def json_parts(value, *, compact):
    options = {"sort_keys": True, "ensure_ascii": False}
    if compact:
        options["separators"] = (",", ":")
    return json.JSONEncoder(**options).iterencode(value)


def declaration_hash(declaration):
    material = {
        "axioms": list(declaration.axioms),
        "axiom_semantics": [list(item) for item in declaration.axiom_semantics],
        "assumed": list(declaration.assumed),
        "assumed_semantics": [list(item) for item in declaration.assumed_semantics],
        "boundary_modules": [list(item) for item in declaration.boundary_modules],
        "depends": list(declaration.depends), "kind": declaration.kind,
        "lean_version": declaration.lean_version, "name": declaration.name,
        "semantic": declaration.semantic, "semantic_schema": sk.SEMANTIC_SCHEMA,
        "trusted": [[item.name, item.kind, item.semantic, list(item.depends)] for item in declaration.trusted],
    }
    return text_hash(json_parts(material, compact=False))


def declaration_parts(declaration):
    yield f"-- {declaration.kind} {declaration.name}\n"
    yield f"-- assumed from libraries: {', '.join(declaration.assumed) if declaration.assumed else 'none'}\n"
    yield f"-- axioms: {', '.join(declaration.axioms) if declaration.axioms else 'none'}\n\n"
    yield declaration.signature
    yield "\n-- raw signature:\n"
    yield declaration.raw_signature
    yield "\n-- canonical kernel material: "
    yield declaration.semantic
    yield "\n"
    own = sk._without_comments(declaration.source or "", declaration.source_comments).strip("\n")
    if own:
        yield own + "\n"
    elif declaration.statement:
        written = sk._without_comments(declaration.statement, declaration.statement_comments).strip("\n")
        if written:
            yield "-- as written:\n" + written + "\n"
    if declaration.source_withheld or not (own or declaration.statement):
        yield sk._NOT_SHOWN + "\n"
    for item in declaration.trusted:
        yield f"\n-- {item.kind} {item.name}\n-- signature: {item.signature}\n-- raw signature: {item.raw_signature}\n"
        yield "-- canonical kernel material: "
        yield item.semantic
        yield "\n"
        body = sk._without_comments(item.source or "", item.source_comments).strip("\n")
        if body:
            yield body + "\n"
        elif item.source_withheld:
            yield sk._NOT_SHOWN + "\n"


def article_parts(node):
    yield f"-- article with {len(node.declarations)} declaration(s)"
    for declaration in node.declarations:
        yield "\n"
        yield from declaration_parts(declaration)


def write_parts(path, parts):
    with path.open("xb") as stream:
        for block in text_bytes(parts):
            stream.write(block)
        stream.flush()
        os.fsync(stream.fileno())


def stage_report(report, destination):
    identity = sk._output_identity(destination)
    if identity is not None and not destination.is_file():
        raise sk.SkeletonError([f"report output exists and is not a regular file: {destination}"])
    destination.parent.mkdir(parents=True, exist_ok=True)
    stage = destination.with_name(f".{destination.name}.autoform-stage-{secrets.token_hex(8)}")
    # Exclusive creation precedes the cleanup that owns this private stage.
    stream = stage.open("xb")
    try:
        with stream:
            for block in text_bytes(json_parts(report.as_dict(), compact=True)):
                stream.write(block)
            stream.write(b"\n")
            stream.flush()
            os.fsync(stream.fileno())
        if not destination.is_symlink() and destination.is_file():
            stage.chmod(stat.S_IMODE(destination.stat().st_mode))
    except BaseException:
        with contextlib.suppress(OSError):
            sk._remove_output(stage)
        raise
    return stage, identity


def write_packets(report, directory, *, passages=None, report_path=None):
    if not report.clean:
        raise sk.SkeletonError(["refusing to publish review packets from an incomplete skeleton report"])
    root = sk._output_path(directory, "packet")
    passages_root = None if passages is None else sk._output_path(passages, "packet")
    if passages_root is not None and sk._paths_overlap(root, passages_root):
        raise sk.SkeletonError(["packet and passage output directories must be disjoint"])
    report_destination = None if report_path is None else sk._output_path(report_path, "report")
    if report_destination is not None and (
        sk._paths_overlap(root, report_destination)
        or passages_root is not None and sk._paths_overlap(passages_root, report_destination)
    ):
        raise sk.SkeletonError(["report output must be disjoint from packet and passage directories"])
    root_identity = sk._validate_managed_output(root, kind="packets")
    passages_identity = sk._validate_managed_output(passages_root, kind="passages") if passages_root is not None else None
    packet_stage = passages_stage = report_stage = None
    report_identity = None
    written = []
    manifest = []
    passage_manifest = []
    files = []
    try:
        packet_stage = sk._stage_output(root)
        passages_stage = sk._stage_output(passages_root) if passages_root is not None else None
        if report_destination is not None:
            report_stage, report_identity = stage_report(report, report_destination)
        for node in report.nodes:
            node_path = sk._safe_node_path(node.node_id)
            passage_path = None
            if passages_stage is not None and node.passage is not None:
                passage_path = (node_path / "passage.txt").as_posix()
                passage_bytes = (node.passage + "\n").encode("utf-8")
                files.append((passages_stage / passage_path, lambda data=passage_bytes: (data.decode("utf-8"),)))
                passage_manifest.append({"hash": sk._sha256_id(passage_bytes), "node_id": node.node_id,
                                         "passage": passage_path, "review_hash": node.review_hash})
            article_relative = node_path / sk.ARTICLE_PACKET
            if node.declarations:
                files.append((packet_stage / article_relative, lambda item=node: article_parts(item)))
                written.append(root / article_relative)
            for declaration in node.declarations:
                relative = node_path / sk._packet_filename(declaration.name)
                files.append((packet_stage / relative, lambda item=declaration: declaration_parts(item)))
                written.append(root / relative)
                entry = {"article_packet": article_relative.as_posix(), "article_packet_hash": node.evidence_hash,
                         "declaration": declaration.name, "hash": declaration.hash, "node_id": node.node_id,
                         "packet": relative.as_posix(), "packet_hash": declaration.evidence_hash,
                         "review_hash": node.review_hash}
                if passage_path is not None:
                    entry["passage"] = passage_path
                    entry["passage_locator"] = node.passage_locator or ""
                manifest.append(entry)
        for stage, kind, entries, schema in (
            (packet_stage, "packets", manifest, sk.PACKET_SCHEMA),
            (passages_stage, "passages", passage_manifest, sk.PASSAGE_SCHEMA),
        ):
            if stage is not None:
                payload = json.dumps({"kind": kind, kind: entries, "schema": schema}, indent=2, sort_keys=True)
                os.replace(sk._stage_output(stage / sk.PACKET_MANIFEST, payload + "\n"), stage / sk.PACKET_MANIFEST)
        for path, parts in files:
            path.parent.mkdir(parents=True, exist_ok=True)
            write_parts(path, parts())
        outputs = [(root, packet_stage, root_identity)]
        if passages_root is not None:
            outputs.append((passages_root, passages_stage, passages_identity))
        if report_destination is not None:
            outputs.append((report_destination, report_stage, report_identity))
        sk._replace_outputs(outputs)
    except OSError as exc:
        raise sk.SkeletonError([f"could not prepare skeleton output: {exc}"]) from exc
    finally:
        for stage in (packet_stage, passages_stage, report_stage):
            if stage is not None:
                with contextlib.suppress(OSError):
                    sk._remove_output(stage)
    return written


def install():
    sk.DeclarationSkeleton.hash = property(declaration_hash)
    sk.DeclarationSkeleton.evidence_hash = property(lambda declaration: text_hash(declaration_parts(declaration)))
    sk.NodeSkeleton.evidence_hash = property(lambda node: text_hash(article_parts(node)))
