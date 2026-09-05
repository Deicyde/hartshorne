---
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.GermRep Hartshorne.GermRep.Rel Hartshorne.GermRep.rel_trans Hartshorne.isRegularVia_restrict Hartshorne.preirreducible_univ_of_isOpen Hartshorne.Variety.GermRep Hartshorne.Variety.GermRep.Rel Hartshorne.Variety.GermRep.rel_trans Hartshorne.Variety.LocalRingAt Hartshorne.VarietyHom.germPullback Hartshorne.VarietyHom.localRingHom Hartshorne.VarietyHom.localRingHom_id Hartshorne.VarietyHom.localRingHom_comp Hartshorne.VarietyHom.bijective_localRingHom_of_isIso
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
general one is what §3's projective results will be stated over. Identifying
them for an affine `Y` is not needed by anything yet and has not been done.

## Functoriality

Hartshorne never says `𝒪_P` is a functor, because he never needs to move a
local ring from one variety to another. Theorem 3.4(b) does need it: the local
ring in question sits on a projective `Y`, and every affine result is stated on
the chart `Yᵢ`. So a morphism `φ : X → Y` has to induce
`𝒪_{φ(P),Y} → 𝒪_{P,X}` (`Hartshorne.VarietyHom.localRingHom`), contravariantly
(`localRingHom_comp`), and an isomorphism of varieties has to induce a
bijection (`bijective_localRingHom_of_isIso`).

The construction is free: pulling back a germ is pulling back a representative,
and that a morphism pulls regular functions back to regular functions is what a
morphism is. What cost something is the last statement, and only for a reason
with no mathematical content. The inverse morphism `ψ` gives a map indexed by
`ψ(φ(P))`, not by `P`, so composing the two ring maps means transporting along
`ψ(φ(P)) = P` — a rewrite inside the *type* of a ring hom, which Lean will not
do. Proving bijectivity directly on representatives sidesteps it: injectivity
then needs only that `φ` is surjective on points, and surjectivity pushes a germ
forward along `ψ` by hand.

The pattern is worth naming, since it has now come up wherever a point index
appears in a type: state the conclusion as a property of one map rather than as
an equation between two composites, and the dependent rewrite disappears.

## Depends on

- [The ring of regular functions](ring-of-regular-functions.md)
- [Varieties](variety.md)

## Proof depends on

- [Regular functions are continuous](regular-function-continuous.md)

## Sources

- [Hartshorne I.3, definition of the local ring `𝒪_{P,Y}` (p. 16)](../../sources/hartshorne.md#i3)
