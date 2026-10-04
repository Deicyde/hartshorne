---
article_id: af_052d2f1600357bdd3ecb1208
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-6-7]
---

# Extensions are classified by Ext one

For two `O_X`-modules `F'` and `F''`, sending a short exact extension

`0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0`

to the connecting image of `𝟙 F''` induces a bijection between isomorphism
classes of extensions and `Ext^1_X(F'',F')`.

Here an extension is a short exact short complex with ends identified with
`F'` and `F''`; two extensions are equivalent when an isomorphism of the
middle objects makes the endpoint-identity diagram commute. The main result
is the resulting set-level bijection. No Baer-sum compatibility is asserted.

## Depends on

- [Global Ext groups](global-ext-groups.md)
- [The covariant long exact sequence of global Ext](global-ext-covariant-long-exact.md)

## Proof depends on

- Pinned Mathlib's `CategoryTheory.ShortComplex.ShortExact.extClass`.
- The extension setoid above and invariance of `extClass` under its relation.

## Sources

- [Hartshorne III, Exercise 6.1, printed p.237](../../../../sources/hartshorne-iii-6.md#adopted-exercises-printed-pp237238)
- Hilton–Stammbach [1], Chapter III, as cited by Hartshorne.
