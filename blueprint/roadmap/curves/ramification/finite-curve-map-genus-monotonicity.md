---
declaration: theorem
origin: cited
source_units: [chapter-iv-sections-1-2]
---

# Genus is monotone under finite curve maps

For every finite morphism of curves `f : X -> Y`,

`g(X) >= g(Y)`.

If `f` is separable and `g(Y) >= 1`, equality occurs only when `deg f=1`, or
when `g(Y)=1` and `f` is unramified; both alternatives do give equality. For
`g(Y)=0`, higher-degree maps `P^1 -> P^1` show that no degree-one conclusion
is possible. No such restriction is asserted for a purely inseparable map,
which can preserve genus in higher degree.

## Depends on

- [Riemann–Hurwitz](riemann-hurwitz.md)
- [Genus invariance under purely inseparable curve maps](purely-inseparable-genus-invariance.md)
- [Purely inseparable curve maps are iterated Frobenius](purely-inseparable-frobenius-factorization.md)

## Proof depends on

- Factor the finite function-field extension into a purely inseparable part
  followed by a separable extension, as in Stacks tag `0CD2`.
- For a separable map rewrite Riemann–Hurwitz as
  `g(X)=g(Y)+(n-1)(g(Y)-1)+deg(R_f)/2`, treating `g(Y)=0` separately.

## Sources

- [Hartshorne IV.2, Example 2.5.4, p.303](../../../sources/hartshorne-iv-2.md#consequences-pp302303)
- [Stacks Project, separable–inseparable factorization, tag 0CD2](../../../sources/hartshorne-iv-2.md#external-proof-sources)
