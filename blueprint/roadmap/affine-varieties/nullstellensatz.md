---
article_id: af_f8d7b54996f51594f707d44f
declaration: theorem
origin: background
mathlib: true
mathlib_declaration: MvPolynomial.vanishingIdeal_zeroLocus_eq_radical
mathlib_file: Mathlib/RingTheory/Nullstellensatz.lean
statement: formalized
proof: formalized
lean: Hartshorne.vanishingIdeal_zeroSet_eq_radical Hartshorne.exists_pow_mem_of_forall_eval_eq_zero
---

# Hilbert's Nullstellensatz

Let $k$ be algebraically closed and let $\mathfrak a$ be an ideal of
$A=k[x_1,\ldots,x_n]$. If $f\in A$ vanishes at every point of
$Z(\mathfrak a)$, then $f^r\in\mathfrak a$ for some integer $r>0$.
Equivalently,

$$I(Z(\mathfrak a))=\sqrt{\mathfrak a}.$$

Hartshorne quotes this as Theorem I.1.3A and immediately uses it for
[Proposition I.1.2](vanishing-ideal.md)(d). It makes the correspondence between algebraic sets
and radical ideals a bijection. Algebraic closedness is essential: over
$\mathbb R$, the polynomial $x^2+y^2+1$ has no zero, although the ideal
it generates is proper.

## Depends on

- [Algebraic sets](algebraic-set.md)
- [The vanishing ideal](vanishing-ideal.md)

## Sources

- [Hartshorne I.1, Theorem 1.3A and Proposition 1.2(d) (pp. 3-4)](../../sources/hartshorne.md#i1)
