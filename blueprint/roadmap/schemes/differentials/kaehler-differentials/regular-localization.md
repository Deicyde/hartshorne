---
article_id: af_ffc1f8639d78769d74b0efbe
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.RegularLocal.isRegularLocalRing_localization_atPrime Hartshorne.RegularLocal.hasProjectiveDimensionLE_residueField_localization Hartshorne.RegularLocal.localizedModuleQuotientIsoResidueField
---

# Localizations of regular local rings

If $A$ is a regular local ring and $\mathfrak{p}$ is a prime ideal of $A$, then the prime
localization $A_{\mathfrak{p}}$ is again a regular local ring.

This concerns localization at an arbitrary prime ideal, rather
than transport of regularity across a ring isomorphism.

The proof is Serre's homological argument. Since $A/\mathfrak p$ is a finitely
generated $A$-module, $\operatorname{pd}_A(A/\mathfrak p) \le \dim A$. Localizing
a finite projective resolution at $\mathfrak p$ gives
$\operatorname{pd}_{A_\mathfrak p}\big((A/\mathfrak p)_\mathfrak p\big) \le \dim A$,
and $(A/\mathfrak p)_\mathfrak p$ is the residue field of $A_\mathfrak p$. So the
residue field of the Noetherian local ring $A_\mathfrak p$ has finite projective
dimension, and $A_\mathfrak p$ is regular by Serre's criterion.

## Depends on

- [Regular local rings](../../../nonsingular-varieties/regular-local-rings.md)

## Proof depends on

- [Finitely generated modules over a regular local ring](../../../cohomology/ext-groups/homological-dimension/regular-local-finite-module-projective-dimension.md)
- [Serre's criterion for regularity](../../../cohomology/ext-groups/homological-dimension/serre-regularity-criterion.md)
- Localization of projective resolutions:
  $\operatorname{pd}_{S^{-1}A}(S^{-1}M) \le \operatorname{pd}_A(M)$.
- Stacks Project, Lemma 10.110.6, tag 0AFS.
- Hartshorne's cited source is Matsumura [2], p. 139.

## Sources

- [Hartshorne II.8, Theorem 8.14A, printed p. 177](../../../../sources/hartshorne-ii-8.md)
