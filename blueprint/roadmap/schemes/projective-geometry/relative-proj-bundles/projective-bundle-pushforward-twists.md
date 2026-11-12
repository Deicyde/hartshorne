---
article_id: af_68c90e98d598e1577f8f1ce4
declaration: theorem
origin: cited
lean: AlgebraicGeometry.Scheme.Modules.projectiveBundlePushforwardTwistHom AlgebraicGeometry.Scheme.Modules.isIso_projectiveBundlePushforwardTwistHom AlgebraicGeometry.Scheme.Modules.projectiveBundlePushforwardTwistIso AlgebraicGeometry.Scheme.Modules.isZero_pushforward_projectiveBundleTwistingSheaf AlgebraicGeometry.Scheme.Modules.projectiveBundlePushforwardTwistZeroIso AlgebraicGeometry.Scheme.Modules.projectiveBundlePushforwardTwistOneIso AlgebraicGeometry.Scheme.Modules.projectiveBundlePushforwardTwistHom_app_restrict AlgebraicGeometry.Scheme.Modules.projectiveBundlePushforwardTwistHom_mul
statement: formalized
proof: formalized
---

# Pushforwards of projective-bundle twists

If $E$ has rank at least two and $\pi : P(E) \to X$, there is a canonical graded
isomorphism $\operatorname{Sym}(E)\cong\bigoplus_{l\in\mathbb{Z}}\pi_*\mathcal{O}(l)$. In particular the
negative terms vanish, $\pi _* O = \mathcal{O}_X$, and $\pi _* \mathcal{O}(1) = E$.

## Depends on

- [Projective bundles](projective-bundle.md)
- [The section ring of projective space](../../projective-sheaves/projective-space-section-ring.md)

## Proof depends on

- Affine-local descent of the standard projective-space calculation.

## Sources

- [Hartshorne II.7, Proposition 7.11(a) (p.162)](../../../../sources/hartshorne-ii-7.md#relative-proj-and-projective-bundles)
- [Stacks Project, projective bundles, tag 01OA](../../../../sources/hartshorne-ii-7.md#adopted-auxiliary-proof-sources)
