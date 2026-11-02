---
article_id: af_0034b5758463326d85c5e9ba
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.quasicoherent_affine_local_tfae
---

# The affine-local criterion for quasi-coherence

For an $\mathcal{O} _X$-module $F$, prove the equivalence of the following conditions:

1. $F$ locally has a presentation by free module sheaves;
2. $X$ has an affine open cover on which $F$ is isomorphic to $\widetilde{M}$; and
3. for every affine open $U = \operatorname{Spec} A$, the restriction $F|_U$ is isomorphic
   to $\widetilde{\Gamma(U,F)}$.

This relates Hartshorne's running definition and Proposition II.5.4
to the local-presentation formulation in Exercise II.5.4.

## Depends on

- [Modules and quasi-coherent sheaves on an affine scheme](affine-quasicoherent-equivalence.md)
- [Quasi-coherence by local presentations](quasicoherent-local-presentations.md)

## Proof depends on

- Quasi-coherence is preserved by restriction to an open subscheme and is
  local on an open cover.
- Affine opens form a basis for the topology of a scheme.

## Sources

- [Hartshorne II.5, definition and Proposition 5.4 on printed pp. 111–113](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
