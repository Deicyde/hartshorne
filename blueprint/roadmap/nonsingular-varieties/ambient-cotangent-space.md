---
article_id: af_3ba438db4aaadf9e7dbd4162
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.ambientCotangentEquiv_toCotangent Hartshorne.aeval_pderiv_eq_zero_of_mem_affinePointIdeal_sq Hartshorne.ambientCotangentEquiv_generator
---

# The cotangent space of affine space

For $P=(a_1,\ldots,a_n)\in\mathbb A^n$, let $\mathfrak n_P$ be
the kernel of evaluation at $P$ in $k[x_1,\ldots,x_n]$. The derivative map

$$\theta_P(f)=\left(\frac{\partial f}{\partial x_1}(P),\ldots,
\frac{\partial f}{\partial x_n}(P)\right)$$

vanishes on $\mathfrak n_P^2$ and induces an isomorphism of vector spaces

$$\mathfrak n_P/\mathfrak n_P^2\cong k^n.$$

It sends the class of $x_i-a_i$ to the $i$th standard basis vector and
the class of $f\in\mathfrak n_P$ to its gradient at $P$. This is
Hartshorne's map $\theta'$ in the proof of [Theorem I.5.1](jacobian-criterion.md) and works in every
characteristic.

## Depends on

No project-local prerequisites.

## Sources

- [Hartshorne I.5, proof of Theorem 5.1 (p. 32)](../../sources/hartshorne.md#i5)
