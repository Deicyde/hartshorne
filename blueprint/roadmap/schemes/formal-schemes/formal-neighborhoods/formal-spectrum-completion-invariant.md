---
article_id: af_002135c46b13e5a861f9ddf7
declaration: theorem
origin: bridged
source_units: [chapter-ii-section-9]
---

# Formal spectrum is invariant under adic completion

For Noetherian `A` and ideal `I`, let `Ahat` be the `I`-adic completion and
let `Ihat = I Ahat`. Assume the usual topological formal spectrum of the
`Ihat`-adic ring `Ahat` is formed from the open-prime space and the limit of
the sheaves of its discrete quotients. After forgetting the topology on
sections, construct a canonical locally ringed-space isomorphism

`Spf_I(A) ≅ Spf_Ihat(Ahat)`.

This is an explicitly project-authored comparison justifying project `Spf`
notation. Its assumptions include the open-prime/`V(I)` homeomorphism and the
ordinary ring-valued forgetful comparison for the limit structure sheaf. It
does not identify Hartshorne's morphisms with continuous ring homomorphisms.

## Depends on

- [The project formal-spectrum bridge](formal-spectrum.md)
- [Adic completion of rings and modules](../adic-completion/adic-completion.md)

## Proof depends on

- The compatible isomorphisms
  `Ahat / Ihat^(n+1) ≅ A / I^(n+1)` induce an isomorphism of limit sheaves.
- [Quotients of an adic completion](../adic-completion/adic-completion-quotients.md)
- The EGA `Spf` construction and the forgetful functor from topological-ring
  sheaves are comparison inputs, not Hartshorne definitions.

## Sources

- [Hartshorne II.9, replacement by the complete affine ring in Proposition 9.6 (pp.197–198)](../../../../sources/hartshorne-ii-9.md#coherent-modules-on-formal-schemes)
- [Project-authored bridge assumptions](../../../../sources/hartshorne-ii-9.md#formal-completions-and-formal-schemes)
- Stacks Project, tag `0AHY`, as comparison context rather than Hartshorne provenance.
