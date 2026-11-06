---
article_id: af_aa7d8d94ee5baa072d738b95
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.baseExtension_irreducibleComponent_topologicalKrullDim
---

# Dimension after extending the ground field

Let $X$ be integral and finite type over a field $k$. For every extension $k \subseteq k'$, each irreducible component of $X \times _k k'$ has dimension $\dim X$.

Here the dimension of an irreducible component is its dimension as a topological subspace of $X \times _k k'$.

Work affine-locally. Let $A$ be a finitely generated $k$-domain and choose a Noether normalization $R = k[y_1, \ldots, y_s] \subseteq A$, so that $\dim A = s$. Then $A \otimes _k k' \cong R' \otimes _R A$ with $R' = R \otimes _k k' \cong k'[y_1, \ldots, y_s]$, which is a domain, flat over $R$. Since $A$ is torsion-free over $R$, it embeds in $K \otimes _R A$ with $K$ the fraction field of $R$, so $R' \otimes _R A$ embeds in the flat $R'$-module $R' \otimes _R (K \otimes _R A)$ and is torsion-free over $R'$. Every element of a minimal prime $P$ of $A \otimes _k k'$ is a zero divisor, hence $P \cap R' = 0$, and $(A \otimes _k k')/P$ is an integral extension of $R'$, of dimension $s = \dim A$.

Every point of $X \times _k k'$ lies over an affine open $U = \operatorname{Spec} A$ of $X$, whose preimage is $\operatorname{Spec} (A \otimes _k k')$, and every nonempty affine open of $X$ has dimension $\dim X$. The trace of an irreducible component $Z$ on such a chart is an irreducible component of $\operatorname{Spec} (A \otimes _k k')$, the closed set of a minimal prime, so it has dimension $\dim X$. A space covered by open subspaces of dimension at most $n$ has dimension at most $n$, so $\dim Z \leq \dim X$, and any chart meeting $Z$ gives $\dim Z \geq \dim X$.

## Depends on

- [Dimension of a scheme](../subschemes-and-dimension/scheme-dimension.md)
- [Base extension](base-extension.md)
- [Integral schemes](../first-properties/integral-scheme.md)
- [Morphisms of finite type](../first-properties/finite-type.md)

## Proof depends on

- Dimension of finitely generated domains via transcendence degree and minimal primes after scalar extension.

## Sources

- [Hartshorne II.3 (later-used-exercises)](../../../sources/hartshorne-ii-3.md#later-used-exercises)
