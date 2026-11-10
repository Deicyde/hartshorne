---
article_id: af_bea91b5c0ddec6bb61bd8618
declaration: theorem
origin: bridged
---

# Fibres of the differential sheaf on an affine chart

Let $f : X \to Y$ be a morphism of schemes, and let $U \subseteq X$ and
$V \subseteq Y$ be affine opens with $f(U) \subseteq V$. Put $A = \Gamma(V, \mathcal{O}_Y)$
and $B = \Gamma(U, \mathcal{O}_X)$. If $x \in U$ is the point corresponding to the prime
$\mathfrak q \subset B$, then

$$\dim_{k(x)} \bigl((\Omega_{X/Y})_x \otimes k(x)\bigr) = \dim_{\kappa(\mathfrak q)} \bigl(\kappa(\mathfrak q) \otimes_B \Omega_{B/A}\bigr).$$

Indeed $\Omega_{X/Y}|_U \cong \widetilde{\Omega_{B/A}}$, and for a module $M$ over a ring $R$ the
stalk of $\widetilde M$ at a prime $\mathfrak p$ is $M_{\mathfrak p}$, so its fibre there is
$\kappa(\mathfrak p) \otimes_R M$.

## Depends on

- [Differentials on affine schemes](affine-relative-differentials.md)
- [Quasi-coherence and coherence of differentials](relative-differentials-quasicoherent.md)

## Sources

- [Project bridge for Hartshorne II.8, Remark 8.9.1, printed p. 175](../../../../sources/hartshorne-ii-8.md#modules-and-sheaves-of-differentials)
