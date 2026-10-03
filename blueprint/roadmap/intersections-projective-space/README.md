---
article_id: af_21c9cb401d2047b3887059a4
---

# Intersections in projective space

This 50-leaf milestone covers Hartshorne I.7's running mathematical text
through Remark 7.8.2 (printed pp. 47–54), together with Exercises 2.8,
2.10(a)–(c), and 3.15(a),(b),(d), which its proofs require. It develops the
dimension theorem for intersections, integer-graded Hilbert theory, projective
degree, and the hypersurface and plane-curve forms of Bézout's theorem.
Forty-seven leaves are formalized; the pure-curve degree and the two
reducible-curve leaves remain.

The dependency split follows Hartshorne's proof. The geometric branch reaches
Theorem 7.2. The algebraic branch builds the missing `ℤ`-graded module and
prime-filtration infrastructure, then proves Hilbert–Serre. The final branch
extracts leading coefficients and intersection multiplicities.

## Chapters

- [Affine and projective dimension theorems](dimension/README.md) — products,
  cones, finite equation cuts, Proposition 7.1, and Theorem 7.2.
- [Numerical polynomials and graded Hilbert theory](hilbert/README.md) —
  Proposition 7.3 through Hilbert–Serre and the definition of projective degree.
- [Degree and Bézout](bezout/README.md) — Proposition 7.6, hypersurface
  intersection multiplicity, Theorem 7.7, Corollary 7.8, and Remark 7.8.2.

## Representation and source boundary

Polynomial rings are regraded over `ℤ`, with negative pieces zero, so the
source's twist `M(l)ₐ = Mₐ₊ₗ` is represented literally. Dimension inequalities
use additive, subtraction-free statements in `WithBot ℕ∞`; localized lengths
remain `ℕ∞` until their finiteness is proved.

Pinned Mathlib contains Krull's height theorem, ungraded prime filtrations,
associated-prime localization, module length, homogeneous submodules, and
rational generating-function Hilbert polynomials. It explicitly lacks Hilbert
polynomials of finite graded modules and has no exact result corresponding to
Proposition 7.1, Theorem 7.2, Theorem 7.7, or Corollary 7.8.

Remark 7.8.1, comparing homogeneous and local intersection multiplicities, is
deferred because its local definition comes from unadopted Exercise 5.4.
Exercises 7.3–7.4 and the other §7 exercises remain out under the project's
exercise policy; see the [coverage contract](../../coverage/README.md).
