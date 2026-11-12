---
article_id: af_56636760e63acc3203c2e28c
declaration: theorem
origin: cited
lean: Hartshorne.QuasicoherentIdealSubsheaf.formalCompletion_support_invariant Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionIsoOfSupportEq Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionIsoOfSupportEq_hom_c_app_π Hartshorne.QuasicoherentIdealSubsheaf.infinitesimalNeighborhoodι_formalCompletionIsoOfSupportEq_hom_base Hartshorne.QuasicoherentIdealSubsheaf.exists_pow_carrier_le_of_support_le
statement: formalized
proof: formalized
---

# Completion depends only on the closed support

If two coherent ideal sheaves $I$ and $J$ on a Noetherian scheme define
closed subschemes with the same underlying closed set, then there are positive
powers of each contained in the other, and the resulting formal completions
are canonically isomorphic as locally ringed spaces.

## Depends on

- [Formal completion as a locally ringed space](formal-completion.md)

## Proof depends on

- Noetherian radical containment gives $I^a \le J$ and $J^b \le I$ locally, and a
  finite affine cover makes the exponents uniform.
- Cofinal inverse systems have isomorphic limits.

## Sources

- [Hartshorne II.9, Remark 9.3.1 (p.194)](../../../../sources/hartshorne-ii-9.md#formal-completions-and-formal-schemes)
- Stacks Project, tag $0319$.
