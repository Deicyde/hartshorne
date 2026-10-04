---
article_id: af_715fb5ec66f4afe0a1b18ada
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-1-4]
mathlib: true
mathlib_declaration: TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
mathlib_file: Mathlib/Topology/Sheaves/Flasque.lean
---

# Flasque closure in short exact sequences

In a short exact sequence of abelian sheaves
`0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0`, if `F'` and `F` are flasque, then `F''` is
flasque.

The unique main result is quotient closure. Supporting clauses from II.1.16
say that a constant sheaf on an irreducible space is flasque, pushforward
preserves flasqueness, products of flasques are flasque, and global sections
surject onto `F''` when `F'` is flasque. The quotient and section-surjectivity
clauses are exact pinned results in `Mathlib/Topology/Sheaves/Flasque.lean`.

## Depends on

- [Sheaves of abelian groups](../../schemes/sheaves/sheaves-of-abelian-groups.md)

## Proof depends on

- [Global sections are left exact](../../schemes/sheaf-functors/global-sections-left-exact.md)

## Sources

- [Hartshorne II.1.16(a–d), adopted for III.2](../../../sources/hartshorne-iii-1-2.md#filtered-colimits-and-closed-support-printed-pp-208210)
