---
declaration: instance
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.instNoetherianSpace Hartshorne.strictMono_vanishingIdeal_compl
---

# Affine space is a Noetherian space

A topological space is *Noetherian* when its closed subsets satisfy the
descending chain condition. Affine `n`-space with the Zariski topology is
Noetherian.

The proof is one application of the Galois connection: a descending chain of
closed sets `Y₁ ⊇ Y₂ ⊇ …` gives an ascending chain `I(Y₁) ⊆ I(Y₂) ⊆ …` of ideals
in the Noetherian ring `A`, which stabilises, and `Yᵢ = Z(I(Yᵢ))` transports the
stabilisation back.

Mathlib has `TopologicalSpace.NoetherianSpace` and the standard consequences
(quasi-compactness, subspaces are Noetherian). What is missing is this instance
for the Zariski topology on `𝔸ⁿ`, because that topology does not yet exist in
Mathlib in Hartshorne's classical form.

## Depends on

- [The Zariski topology on affine space](zariski-topology.md)
- [The vanishing ideal](vanishing-ideal.md)

## Sources

- [Hartshorne I.1, definition of Noetherian space and Example 1.4.7 (p. 5)](../../sources/hartshorne.md#i1)
