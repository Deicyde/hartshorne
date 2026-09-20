---
article_id: af_bee9a975db6a53592b5a0819
declaration: theorem
origin: cited
source_units: [chapter-i-section-4]
statement: formalized
proof: formalized
lean: Hartshorne.birational_criterion
---

# The birational criterion

For varieties `X` and `Y` in Hartshorne's four concrete classes, carrying the
affine-open-basis and separatedness witnesses used by the §4 category, the
following are equivalent (Corollary 4.5):

1. `X` and `Y` are birationally equivalent;
2. there are open subsets `U ⊆ X` and `V ⊆ Y` with `U` isomorphic to `V`;
3. `K(X) ≅ K(Y)` as `k`-algebras.

Clause 2 is the one that makes birational equivalence concrete: birational
varieties are not merely related by a formal correspondence, they are literally
the same variety away from a proper closed subset of each.

## The proof

`(1) ⇒ (2)` is the only step with content. Let `φ : X ⇢ Y` and `ψ : Y ⇢ X` be
mutually inverse, represented by `⟨U, φ⟩` and `⟨V, ψ⟩`. Then `ψ ∘ φ` is
represented by `⟨φ⁻¹(V), ψ ∘ φ⟩` and equals `id_X` as a rational map, so it is
the identity on `φ⁻¹(V)`; symmetrically `φ ∘ ψ` is the identity on `ψ⁻¹(U)`.
Taking `φ⁻¹(ψ⁻¹(U)) ⊆ X` and `ψ⁻¹(φ⁻¹(V)) ⊆ Y` gives two open sets carried to
each other by `φ` and `ψ`, mutually inverse there, hence isomorphic.

`(2) ⇒ (3)` is the definition of the function field: an open subset of a variety
has the same rational functions as the variety, since a rational function is
already only defined on an open set.

`(3) ⇒ (1)` is [Theorem 4.4](rational-map-function-field.md), the isomorphism
and its inverse giving mutually inverse dominant rational maps.

## Depends on

- [Birational varieties have isomorphic open subsets](birational-open-subsets.md)
- [Birational varieties have isomorphic function fields](birational-function-fields.md)

## Sources

- [Hartshorne I.4, Corollary 4.5 (p. 26)](../../sources/hartshorne.md#i4)
