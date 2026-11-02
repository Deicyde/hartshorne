---
article_id: af_363afc5bb951feaadf99ac85
declaration: short exact sequence
origin: cited
---

# The hyperplane exact-sequence bridge

Let $H=V_{+}(x_{r})\subseteq \mathbb{P}^{r}_A$, identified with $\mathbb{P}^{r-1}_A$, and let $i:H\to \mathbb{P}^{r}_A$
be the closed immersion. Multiplication by $x_{r}$, restriction, and the chosen
twist identifications form a natural graded short exact sequence

$0\longrightarrow\bigoplus_n\mathcal{O}_X(n-1)\longrightarrow\bigoplus_n\mathcal{O}_X(n)\longrightarrow i_*\left(\bigoplus_n\mathcal{O}_H(n)\right)\longrightarrow0$.

The first map is degree zero after shifting, and the resulting cohomology map
is multiplication by $x_{r}$ under the graded Čech identifications.

## Depends on

- [Twists and graded shifts](../../schemes/projective-sheaves/proj-twist-compatibility.md)
- [Closed extension by zero](../../schemes/sheaf-functors/closed-extension-by-zero.md)

## Proof depends on

- [The long exact sequence of sheaf cohomology](../sheaf-cohomology/sheaf-cohomology-long-exact-sequence.md)
- [Closed pushforward preserves cohomology](../sheaf-cohomology/closed-pushforward-cohomology.md)
- Exactness of sheafification of $0\to S(-1)\to S\to S/(x_{r})\to 0$.

## Sources

- [Hartshorne III.5, proof of Theorem 5.1(b), p.227](../../../sources/hartshorne-iii-5.md#cohomology-of-twists-pp225228)
