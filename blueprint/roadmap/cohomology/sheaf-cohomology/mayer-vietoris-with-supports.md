---
article_id: af_dc6feac9cb3e2d0a0bbd53e9
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-1-4]
---

# Mayer–Vietoris with supports

For closed subsets `Y₁,Y₂ ⊆ X` and an abelian sheaf `F`, there is a natural
long exact sequence

`⋯ ⟶ Hⁿ_{Y₁∩Y₂}(X,F) ⟶ Hⁿ_{Y₁}(X,F) ⊕ Hⁿ_{Y₂}(X,F)
 ⟶ Hⁿ_{Y₁∪Y₂}(X,F) ⟶ Hⁿ⁺¹_{Y₁∩Y₂}(X,F) ⟶ ⋯`.

This closed-support statement is not the open-cover Mayer–Vietoris sequence
already available in pinned Mathlib. Its supporting input is the natural exact
sequence of support functors

`0 ⟶ Γ_{Y₁∩Y₂} ⟶ Γ_{Y₁} ⊕ Γ_{Y₂} ⟶ Γ_{Y₁∪Y₂}`,

with the sign convention chosen so consecutive maps compose to zero.

## Depends on

- [The localization sequence for cohomology with supports](cohomology-with-supports.md)

## Proof depends on

- [The long exact sequence of right derived functors](../derived-functors/right-derived-long-exact-sequence.md)
- Exactness of the displayed natural sequence of support functors.

## Sources

- [Hartshorne III.2, Exercise 2.4, printed p. 212](../../../sources/hartshorne-iii-1-2.md#adopted-exercises-printed-pp-212213)
