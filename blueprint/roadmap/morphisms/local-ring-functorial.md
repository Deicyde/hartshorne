---
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.VarietyHom.germPullback Hartshorne.VarietyHom.localRingHom Hartshorne.VarietyHom.localRingHom_id Hartshorne.VarietyHom.localRingHom_comp Hartshorne.VarietyHom.bijective_localRingHom_of_isIso Hartshorne.inclHom Hartshorne.pushGerm Hartshorne.pullPoint Hartshorne.regular_pullPoint Hartshorne.isOpen_pushOpens Hartshorne.bijective_localRingHom_inclHom
---

# The local ring is functorial

A morphism `φ : X → Y` induces a ring map `𝒪_{φ(P),Y} → 𝒪_{P,X}`,
contravariantly. Two consequences are what Theorem 3.4 actually consumes: an
isomorphism of varieties induces an isomorphism of local rings, and the
inclusion of an open subvariety does too.

Neither statement is in Hartshorne. He does not need the first because he never
moves a local ring between varieties, and he uses the second silently. Theorem
3.4(b) needs both: it is about `𝒪_P` for a projective `Y`, every affine result
is stated on the chart, and the chart is `Yᵢ = Y ∩ Uᵢ`, not `Y`. So the local
ring has to travel twice, once along the open inclusion `Yᵢ ⊆ Y` and once along
the chart isomorphism `Yᵢ ≅ φᵢ(Yᵢ)`.

## The construction is free; the isomorphism statement is not

Pulling back a germ is pulling back a representative, and that a morphism pulls
regular functions back to regular functions is what a morphism is. Functoriality
is then three lines of `Quotient.sound`.

What cost something is the isomorphism, for a reason with no mathematical
content. The inverse morphism `ψ` gives a map indexed by `ψ(φ(P))`, not by `P`,
so composing the two ring maps means transporting along `ψ(φ(P)) = P` — a
rewrite inside the *type* of a ring hom, which Lean will not do. Stating the
conclusion as bijectivity of one map instead of an equation between two
composites removes the transport: injectivity then needs only that `φ` is
surjective on points, and surjectivity pushes a germ forward along `ψ` by hand.

That is the general lesson wherever a point index appears in a type. State a
property of one map, not an equation between composites.

## The open inclusion

For `Z ⊆ Y` quasi-projective with `Z` open in `Y`, the inclusion is a morphism —
regularity is a condition on the map to projective space, and that map is the
same on both sides — and it induces an isomorphism on local rings at every
point of `Z`.

Both halves reuse machinery already built. Injectivity is
[the identity principle](variety.md): two germs whose restrictions to `Z` agree
agree on the whole overlap of their domains, because `Z` meets that overlap in a
nonempty open set and a variety is irreducible. Surjectivity pushes a germ
forward, which needs only that an open subset of `Z` is an open subset of `Y`.

One Lean obstacle is worth recording, because it is not mathematics and cost
more than the proof did. Naming the pushed-forward open set as a definition
makes `Continuous` unstatable on it: instance search runs at reducible
transparency and will not unfold a definition far enough to see that `↥V` is a
subtype, so the topology on the domain is never found. Marking the definition
`@[reducible]` does not help. Carrying the open set as a variable together with
a hypothesis describing it sidesteps the problem entirely. The same failure will
recur for any construction that produces an `Opens` and then quantifies over its
points.

## Depends on

- [The local ring at a point](local-ring.md)
- [Morphisms](morphism.md)

## Proof depends on

- [Varieties](variety.md)
- [Regular functions on a quasi-projective variety](regular-function-quasi-projective.md)

## Sources

- [Hartshorne I.3, Theorem 3.4(b) (pp. 18-19)](../../sources/hartshorne.md#i3)
