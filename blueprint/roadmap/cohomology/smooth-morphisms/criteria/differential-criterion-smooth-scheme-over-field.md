---
article_id: af_193fab189fbfe831c74ed1e1
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.smooth_of_forall_topologicalKrullDim_eq_of_finrank_fibre_le Hartshorne.finrank_fibre_relativeDifferentials_affine
---

# The differential criterion for a scheme over a field

Let $k$ be a field, let $Z$ be a scheme of finite type over $k$, and let $n$ be
a natural number. Suppose that every irreducible component of $Z$ has dimension
$n$ and that

$$\dim_{k(z)} \bigl((\Omega_{Z/k})_z \otimes k(z)\bigr) \leq n$$

for every $z \in Z$. Then the structure morphism $Z \to \operatorname{Spec} k$ is
smooth.

Smoothness is local on $Z$, so let $\operatorname{Spec} T \subseteq Z$ be an
affine open and $\mathfrak q$ the prime of a point $z$ in it. Because every
component of $Z$ has dimension $n$ and finite-type $k$-schemes are
catenary, $\dim \mathcal O_{Z,z} + \dim \overline{\{z\}} = n$; transporting along
the open immersion gives $\dim T_{\mathfrak q} + \dim T/\mathfrak q = n$. On the
affine open, $(\Omega_{Z/k})_z \otimes k(z) \cong \kappa(\mathfrak q) \otimes_T \Omega_{T/k}$.
The [differential criterion](differential-criterion-smooth-over-field.md) then
makes $T$ smooth over $k$ at every prime.

## Depends on

- [The relative differential sheaf](../../../schemes/differentials/scheme-differentials/relative-differentials.md)
- [Dimension of a scheme](../../../schemes/subschemes-and-dimension/scheme-dimension.md)

## Proof depends on

- [The differential criterion for smoothness over a field](differential-criterion-smooth-over-field.md)
- [The dimension formula for a finitely generated domain](../../../affine-varieties/dim-formula-catenary.md)
- [Equidimensionality in a flat family](../../flat-families/families-hilbert/flat-equidimensional-total-space-iff-fibers.md)
- [Differentials on affine schemes](../../../schemes/differentials/scheme-differentials/affine-relative-differentials.md)
- [Fibres of the differential sheaf on an affine chart](../../../schemes/differentials/scheme-differentials/relative-differentials-affine-fibre.md)

## Sources

- [Project bridge for Hartshorne III.10, definition of smoothness, p.268](../../../../sources/hartshorne-iii-10.md#smoothness-and-geometric-fibres-pp268270)
- [Stacks Project, Section 10.140, tag 00TQ](../../../../sources/hartshorne-iii-10.md#smoothness-and-geometric-fibres-pp268270)
