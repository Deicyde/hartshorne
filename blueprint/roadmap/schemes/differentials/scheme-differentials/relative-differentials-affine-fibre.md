---
article_id: af_bea91b5c0ddec6bb61bd8618
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.rank_fibre_relativeDifferentials_affine Hartshorne.rank_fibre_eq_of_iso_tilde Hartshorne.finrank_fibre_relativeDifferentials_affine Hartshorne.finrank_fibre_eq_of_iso_tilde
---

# Fibres of the differential sheaf on an affine chart

Let $f : X \to Y$ be a morphism of schemes, and let $U \subseteq X$ and
$V \subseteq Y$ be affine opens with $f(U) \subseteq V$. Put $A = \Gamma(V, \mathcal{O}_Y)$
and $B = \Gamma(U, \mathcal{O}_X)$. If $x \in U$ is the point corresponding to the prime
$\mathfrak q \subset B$, then

$$\dim_{k(x)} \bigl((\Omega_{X/Y})_x \otimes k(x)\bigr) = \dim_{\kappa(\mathfrak q)} \bigl(\kappa(\mathfrak q) \otimes_B \Omega_{B/A}\bigr).$$

## Proof

Restricting to the open subscheme $U$ does not change the fibre at $x$, and
$\Omega_{X/Y}|_U \cong \widetilde{\Omega_{B/A}}$. For a module $M$ over a ring $R$ the
stalk of $\widetilde M$ at a prime $\mathfrak p$ is $M_{\mathfrak p}$, so its fibre there is
$\kappa(\mathfrak p) \otimes_R M$.

## Depends on

- [The relative differential sheaf](relative-differentials.md)

## Proof depends on

- [Differentials on affine schemes](affine-relative-differentials.md)
- [Quasi-coherence and coherence of differentials](relative-differentials-quasicoherent.md)
- [Constant fibre dimension forces local freeness](../../coherent-sheaves/coherent-constant-fibre-rank-locally-free.md)

## Sources

- [Project bridge for Hartshorne II.8, Remark 8.9.1, printed p. 175](../../../../sources/hartshorne-ii-8.md#modules-and-sheaves-of-differentials)
