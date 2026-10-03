---
declaration: theorem
origin: cited
source_units: [appendix-c-section-4]
---

# Determinants under a scaled perfect pairing

Let `V` and `W` be `r`-dimensional vector spaces with a perfect pairing, a
nonzero scalar `A`, and endomorphisms `phi,psi` satisfying

`<phi(v),psi(w)>=A*<v,w>`.

The condition with `A!=0` forces both endomorphisms to be invertible.

Then `psi` is the scaled contragredient of `phi`; in particular its
characteristic determinant polynomial and determinant are

`det(1-t*psi)=(-1)^r*A^r*t^r/det(phi) * det(1-phi/(A*t))`,

`det(psi)=A^r/det(phi)`.

## Depends on

- This is a foundational finite-dimensional linear-algebra leaf with no
  roadmap prerequisite.

## Sources

- [Hartshorne Appendix C.4, Lemma 4.3, p.456](../../../sources/hartshorne-appendix-c-4.md#linear-algebra-lemmas-printed-pp455456)
