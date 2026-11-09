---
article_id: af_abf62cba2721e18c484f0f47
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.topologicalKrullDim_of_mem_irreducibleComponents_of_smoothOfRelativeDimension Hartshorne.SubmersivePresentation.isRegularLocalRing_localization Hartshorne.SubmersivePresentation.ringKrullDim_localization_add_ringKrullDim_quotient Hartshorne.SubmersivePresentation.linearIndependent_D_relation
---

# Dimension of a scheme smooth over a field

Let $k$ be a field and let $Z$ be a scheme of finite type over $k$ whose
structure morphism $Z \to \operatorname{Spec} k$ is smooth of relative
dimension $n$. Then every irreducible component of $Z$ has dimension $n$.

The local input is the corresponding statement for a standard smooth algebra
$S = k[x_1, \dots, x_N]/(f_1, \dots, f_c)$, presented so that the
$c \times c$ Jacobian minor of the relations is invertible in $S$, with
$n = N - c$: for every prime $\mathfrak q$ of $S$, the local ring
$S_{\mathfrak q}$ is regular and
$\dim S_{\mathfrak q} + \dim S/\mathfrak q = n$. Indeed, let $Q$ be the
preimage of $\mathfrak q$ in $P = k[x_1, \dots, x_N]$. The invertible minor
makes the differentials of $f_1, \dots, f_c$ linearly independent in
$\kappa(Q) \otimes_P \Omega_{P/k}$, and $P_Q$ is regular, so
[the regular quotient theorem](independent-differentials-regular-quotient.md)
shows that $S_{\mathfrak q} \cong P_Q/(f_1, \dots, f_c)$ is regular of dimension
$\operatorname{ht} Q - c$. The dimension formula for the polynomial ring gives
$\operatorname{ht} Q + \dim P/Q = N$, and $P/Q \cong S/\mathfrak q$.

For the scheme statement, let $\zeta$ be the generic point of a component $C$
and choose an affine open $\operatorname{Spec} S \ni \zeta$ with $S$ standard
smooth of relative dimension $n$. Since $\zeta$ is a maximal point,
$\dim S_{\mathfrak q} = \dim \mathcal O_{Z,\zeta} = 0$, and
$\dim C = \dim S/\mathfrak q$ by transporting heights along the open immersion,
so $\dim C = n$.

## Depends on

- [Dimension of a scheme](../../../schemes/subschemes-and-dimension/scheme-dimension.md)

## Proof depends on

- [Elements with independent differentials cut out a regular local ring](independent-differentials-regular-quotient.md)
- [The dimension formula for a finitely generated domain](../../../affine-varieties/dim-formula-catenary.md)
- [Equidimensionality in a flat family](../../flat-families/families-hilbert/flat-equidimensional-total-space-iff-fibers.md)
- Localizations of a polynomial ring over a field are regular local rings.
- A morphism smooth of relative dimension $n$ has standard smooth affine charts of relative dimension $n$.

## Sources

- [Stacks Project, Section 10.140, tag 00TQ](../../../../sources/hartshorne-iii-10.md#smoothness-and-geometric-fibres-pp268270)
