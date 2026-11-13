---
article_id: af_3122495be6d2ec287ac6e2a2
declaration: def
origin: bridged
lean: Hartshorne.pluricanonicalMap Hartshorne.pluricanonicalSystem Hartshorne.mem_pluricanonicalDomain_iff Hartshorne.pluricanonicalImage Hartshorne.pluricanonicalImageDim Hartshorne.pluricanonicalSystem_divisors_eq_empty_iff Hartshorne.pluricanonicalSystem_dim_eq_neg_one_iff Hartshorne.pluricanonicalImageDim_eq_zero Hartshorne.linearSystemMorphism_map
statement: formalized
proof: formalized
---

# Pluricanonical rational maps and their image dimensions

Let $X$ be a nonsingular projective variety over an algebraically closed field
$k$, with canonical sheaf $\omega_X$ and canonical divisor $K$. For $n > 0$ with
$H^0(X,\omega_X^{\otimes n}) \neq 0$, let $N = \dim_k H^0(X,\omega_X^{\otimes n}) - 1$.
The pluricanonical rational map

$\phi_n : X \dashrightarrow \mathbb{P}^N$

is defined by a basis of $H^0(X,\omega_X^{\otimes n})$ off the base locus of $|nK|$.
As in Remark II.7.8.1 (p.158), a different basis changes the morphism only by an
automorphism of $\mathbb{P}^N$. The image of $\phi_n$ is the closure in
$\mathbb{P}^N$ of the image of the complement of the base locus. Its dimension is
the dimension of this closed subset. If $H^0(X,\omega_X^{\otimes n}) = 0$, then
$|nK|$ is empty and $\phi_n$ is not defined. If $H^0(X,\omega_X^{\otimes n})$ is
one-dimensional, the image has dimension zero.

The construction uses only that $X$ is integral and projective over a field and
that $\omega_X$ is invertible; it does not use that $k$ is algebraically closed.

## Depends on

- [The canonical section ring](canonical-section-ring.md)
- [Linear systems](../../../schemes/projective-geometry/linear-systems-ampleness/linear-system-api.md)
- [Rational maps](../../../rational-maps/rational-map.md)
- [Finite-dimensional linear systems on an arbitrary variety](../../../cohomology/smooth-morphisms/finite-dimensional-linear-system-on-variety.md)

## Sources

- [Hartshorne V.6, pluricanonical-map formulation, pp.421–422](../../../../sources/hartshorne-v-6.md)
