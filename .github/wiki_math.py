"""Extract the built wiki's formulas and reject code in statement prose."""
from __future__ import annotations

from html.parser import HTMLParser
import json
from pathlib import Path
import sys


class Formulas(HTMLParser):
    def __init__(self, path: str) -> None:
        super().__init__(convert_charrefs=True)
        self.path = path
        self.stack: list[tuple[str, set[str]]] = []
        self.formula: list[str] | None = None
        self.formula_depth = 0
        self.results: list[dict[str, object]] = []
        self.code: list[str] | None = None
        self.code_depth = 0
        self.problems: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag in {'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link', 'meta', 'param', 'source', 'track', 'wbr'}:
            return
        values = dict(attrs)
        classes = set((values.get('class') or '').split())
        self.stack.append((tag, classes))
        if 'arithmatex' in classes and self.formula is None:
            self.formula = []
            self.formula_depth = len(self.stack)
        if tag == 'code' and self.code is None and any('bp-thmcontent' in names for _, names in self.stack):
            self.code = []
            self.code_depth = len(self.stack)

    def handle_endtag(self, tag: str) -> None:
        index = next((i for i in range(len(self.stack) - 1, -1, -1) if self.stack[i][0] == tag), None)
        if index is None:
            return
        if self.formula is not None and index < self.formula_depth:
            source = ''.join(self.formula).strip()
            if source.startswith('\\(') and source.endswith('\\)'):
                self.results.append({'path': self.path, 'tex': source[2:-2], 'display': False})
            elif source.startswith('\\[') and source.endswith('\\]'):
                self.results.append({'path': self.path, 'tex': source[2:-2], 'display': True})
            self.formula = None
        if self.code is not None and index < self.code_depth:
            self.problems.append(f'{self.path}: code in mathematical statement prose: {"".join(self.code)[:160]}')
            self.code = None
        del self.stack[index:]

    def handle_data(self, data: str) -> None:
        if self.formula is not None:
            self.formula.append(data)
        if self.code is not None:
            self.code.append(data)


def main() -> int:
    root = Path(sys.argv[1])
    results = []
    problems = []
    pages = sorted((root / 'roadmap').rglob('*.html'))
    for path in pages:
        parser = Formulas(path.relative_to(root).as_posix())
        parser.feed(path.read_text(encoding='utf-8'))
        results.extend(parser.results)
        problems.extend(parser.problems)
    if not pages or not results:
        problems.append('No book pages or formulas found in the built site.')
    for problem in problems:
        print(problem, file=sys.stderr)
    if problems:
        return 1
    json.dump(results, sys.stdout, ensure_ascii=False)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
