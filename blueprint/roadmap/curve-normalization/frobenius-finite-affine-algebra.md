---
article_id: af_c443fb28d7ae4626b5a146aa
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.moduleFinite_frobeniusPowerSubalgebra Hartshorne.frobeniusPowerHom_finite Hartshorne.iterateFrobenius_finite
---

# Frobenius is finite on an affine algebra over a perfect field

Let $k$ be a perfect field of positive characteristic $p$, let $A$ be a
finitely generated $k$-algebra, and let $q = p^e$. Then $A$ is a finite module
over its subring of $q$th powers $A^q$.

Choose finite algebra generators $a_{1},\ldots ,a_{n}$. Perfection of $k$ puts every
coefficient in $k$ in the image of the $q$th-power map. Reducing each exponent
modulo $q$ shows that the finitely many monomials

$a_1^{r_1}\cdots a_n^{r_n}$, with every $r_{i} < q$,

span $A$ over $A^q$.

## Provenance

Stacks Project, Tag 0CCD proves that relative Frobenius is finite for a
locally finite-type morphism in positive characteristic. Over a perfect base
field, the image of the corresponding affine ring map is the subring of
$p$th powers; iteration gives the stated $q$th-power result. The iterated-power formulation is project-authored. This remains a
bridge article because it is an intermediate input to Hartshorne's theorem,
not a direct source target.

## Depends on

No project-local statement prerequisites.

## Sources

- [Project-authored proof specification for Hartshorne I.3.9A](../../sources/hartshorne.md#project-authored-proof-specification-for-theorem-i39a)
- [Stacks Project, relative Frobenius is finite (Tag 0CCD)](https://stacks.math.columbia.edu/tag/0CCD)
