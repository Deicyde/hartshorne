---
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.GermRep Hartshorne.GermRep.Rel Hartshorne.GermRep.rel_trans Hartshorne.isRegularVia_restrict Hartshorne.preirreducible_univ_of_isOpen Hartshorne.Variety.GermRep Hartshorne.Variety.GermRep.Rel Hartshorne.Variety.GermRep.rel_trans Hartshorne.Variety.LocalRingAt Hartshorne.affinePoint Hartshorne.germRepToVariety Hartshorne.germRepOfVariety Hartshorne.localRingEquivAffine
---

# The local ring at a point

For `P` a point of a variety `Y`, the *local ring* `𝒪_{P,Y}` is the ring of germs
of regular functions near `P`: pairs `(U, f)` with `U` an open neighbourhood of
`P` and `f` regular on `U`, identified when they agree on a common refinement.

That it deserves the name — that `𝒪_{P,Y}` is a local ring with maximal ideal
the germs vanishing at `P`, and residue field `k` — is a theorem and lives in
[its own article](local-ring-is-local.md). This node is the construction and its
ring structure.

Well-definedness of the identification is where Remark 3.1.1 is used —
transitivity of the relation needs that two regular functions agreeing on a
nonempty open set agree on the overlap of their domains — which is why the
continuity node is a proof prerequisite rather than an aside.

## The same construction for an arbitrary variety

The version above is built from `IsRegularVia`, in affine coordinates.
Theorem 3.4 is about `𝒪_P` for a *projective* variety, so it needs the
construction over the abstract `Variety` instead
(`Hartshorne.Variety.LocalRingAt`).

Over the abstract structure it is shorter, not longer: restriction is a field,
and the transitivity argument is the same one with
[the general identity principle](variety.md) in place of the affine Lemma 3.1.
Nothing about polynomials survives into it.

Both constructions are kept. The affine one is what §3's earlier results are
stated over and what carries the local-ring and localisation theorems; the
general one is what §3's projective results are stated over.

For a quasi-affine `Y` they are the same ring
(`Hartshorne.localRingEquivAffine`), which is what Theorem 3.4(b) needs in order
to reach Theorem 3.2(c) from the projective side. There is no mathematics in it:
a representative is an open neighbourhood carrying a regular function, and
`regular` on `Variety.ofQuasiAffine hY` is by definition `IsRegularVia` in the
affine coordinates. The only difference is that one side packages the
neighbourhood as a set plus a proof and the other as an `Opens`, so both
directions and all four ring-map obligations are `rfl` on representatives.

Writing it down still needed one trick. Instance search will not unfold
`Variety.ofQuasiAffine` to see that its carrier is `↥Y`, so with the point typed
on one side the ring structure on the other is not found, and the two sides
cannot both be satisfied by one variable. Spelling the point as `⟨P.1, P.2⟩` on
the affine side, which is `P` by eta, gives instance search a term of the type
it expects.

## Functoriality

Hartshorne never says `𝒪_P` is a functor, because he never needs to move a local
ring from one variety to another. Theorem 3.4(b) does, and that is
[its own node](local-ring-functorial.md).

## Depends on

- [The ring of regular functions](ring-of-regular-functions.md)
- [Varieties](variety.md)

## Proof depends on

- [Regular functions are continuous](regular-function-continuous.md)

## Sources

- [Hartshorne I.3, definition of the local ring `𝒪_{P,Y}` (p. 16)](../../sources/hartshorne.md#i3)
