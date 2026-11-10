---
article_id: af_a52cb991e62958c97fc00e45
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.hilbertSerre
---

# Hilbert–Serre

Let $M$ be a finite integer-graded module over
$S = k[x_{0},\ldots ,x_{n}]$. There is a unique polynomial $P_M \in \mathbb{Q} [z]$ such that

$\varphi _M(d) = P_M(d)$

for every sufficiently large integer $d$. It is numerical, and its degree,
with the zero polynomial assigned degree $-1$, is

$\dim Z(\operatorname{Ann}M)$, with the zero-support case interpreted by the same convention.

The proof establishes the result simultaneously for all finite graded modules by strong
induction on the dimension of their projective support, strengthening the
induction claim with positivity of the leading coefficient whenever the
support is nonempty. Apply Hilbert-function additivity along a graded prime
filtration. A factor whose support has smaller dimension is covered directly
by the induction hypothesis. For a
maximal-dimensional shifted prime factor $(S/p)(l)$, choose a variable
$x_i \notin p$. Multiplication by $x_i$, viewed as a degree-zero map from the
correspondingly shifted source, is injective and has cokernel
$(S/(p+(x_i)))(l)$. Its projective support has smaller dimension (or is empty
in the zero-dimensional case). Crucially, $p+(x_i)$ need not be prime or
radical; the induction hypothesis applies because the cokernel is an arbitrary
finite graded module. Degreewise exactness identifies its Hilbert function
with the finite difference of the prime factor's Hilbert function, and
discrete antidifferentiation produces the required numerical polynomial.

The empty-support case starts the induction. For a zero-dimensional nonempty
prime support, the cokernel has empty support, so antidifferentiation gives an
eventual constant. It is positive: $x_i \notin p$ and primeness imply
$x_i^d \notin p$ for every $d$, hence the large-degree pieces of $S/p$ do not
vanish. This also supplies the positivity base case for the strengthened
induction.

Summing the factor polynomials gives the polynomial for $M$. The
filtration-support theorem identifies $Z(\operatorname{Ann}M)$ with the union of the factor
supports. Maximal-dimensional prime factors have positive leading coefficient,
so their contributions cannot cancel; lower-dimensional factors do not change
the degree. Uniqueness follows because two rational polynomials agreeing at all
sufficiently large integers agree on an infinite set.


## Depends on

- [Numerical polynomials have integral binomial expansions](numerical-binomial-expansion.md)
- [Discrete antidifferentiation of a numerical polynomial](numerical-antidifference.md)
- [Homogeneous annihilators and cyclic modules](graded-annihilator.md)
- [Graded prime filtrations](graded-prime-filtration.md)
- [Minimal primes in a graded prime filtration](prime-filtration-support.md)
- [The Hilbert function](hilbert-function.md)

## Proof depends on

- [The projective dimension theorem](../dimension/projective-dimension-theorem.md)
- [Projective varieties of complementary dimension meet](../dimension/projective-intersection-nonempty.md)
- [Projective codimension one is a hypersurface](../dimension/projective-codimension-one-hypersurface.md)
- [Algebraic sets and homogeneous radical ideals](../../projective-varieties/homogeneous-ideal-correspondence.md)
- [Proper closed subsets of projective varieties have smaller dimension](../dimension/projective-proper-closed-dimension-drop.md)

## Sources

- [Hartshorne I.7, Theorem 7.5 and its proof (pp. 51–52)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
