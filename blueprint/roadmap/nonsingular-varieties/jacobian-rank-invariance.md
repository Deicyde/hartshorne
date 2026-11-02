---
article_id: af_dfbfb056049d16cdd33cb367
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.definingIdealGradientSpace_eq_jacobianRowSpace_of_span_eq Hartshorne.jacobianMatrix_rank_eq_jacobianRank Hartshorne.jacobianMatrix_rank_eq_of_span_eq Hartshorne.exists_fin_jacobianMatrix_rank_eq_jacobianRank
---

# Jacobian rank is independent of generators

For an affine variety $Y \subseteq \mathbb{A} ^{n}$ and $P \in Y$, define its intrinsic
*Jacobian row space at $P$* to be

$J_P(Y)=\operatorname{span}_k\{\nabla f(P):f\in I(Y)\}\subseteq k^n$,

and define $\operatorname{rank} J(P) = \dim _k J_P(Y)$. If
$f_{1},\ldots ,f_{t}$ is any finite generating family for $I(Y)$, then $J_P(Y)$ is
already spanned by the rows

$\left(\frac{\partial f_i}{\partial x_j}(P)\right)_j$.

Thus $\operatorname{rank} J(P)$ is the rank of Hartshorne's displayed Jacobian
matrix, and any two finite generating families give the same rank.

For the nontrivial containment, write an arbitrary $f \in I(Y)$ as
$\sum_i g_i f_i$. The product rule and $f_{i}(P)=0$ show
$\nabla f(P)=\sum_i g_i(P)\nabla f_i(P)$. The reverse containment is immediate. The
finite-generation input is available because the polynomial ring has finitely
many variables and is Noetherian.

## Depends on

- [The cotangent space of affine space](ambient-cotangent-space.md)
- [The defining ideal and the local cotangent space](defining-ideal-cotangent-sequence.md)
- [The vanishing ideal](../affine-varieties/vanishing-ideal.md)

## Sources

- [Hartshorne I.5, definition of the Jacobian and generator-independence remark (pp. 31-32)](../../sources/hartshorne.md#i5)
