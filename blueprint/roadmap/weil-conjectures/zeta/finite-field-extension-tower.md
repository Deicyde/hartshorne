---
article_id: af_23c0fb3577cdca1063ee339a
declaration: def
origin: cited
source_units: [appendix-c-section-1]
statement: formalized
proof: formalized
lean: Hartshorne.finiteFieldExtensionPolynomial Hartshorne.finiteFieldExtension Hartshorne.finiteFieldExtension_isSplittingField Hartshorne.finiteFieldExtension_finiteDimensional Hartshorne.finiteFieldExtension_finite Hartshorne.finiteFieldExtension_finrank Hartshorne.finiteFieldExtension_natCard Hartshorne.finiteFieldExtension_mono_of_dvd Hartshorne.finiteFieldExtensionHom Hartshorne.finiteFieldExtensionHom_apply Hartshorne.finiteFieldExtensionHom_refl Hartshorne.finiteFieldExtensionHom_trans Hartshorne.finiteFieldExtension_directed Hartshorne.iSup_finiteFieldExtension_eq_top
---

# The finite-field extension tower

Fix `k=F_q`. For every integer `r>=1`, choose the degree-`r` extension

`k_r=F_(q^r)`

inside a fixed algebraic closure, with its `q^r` elements and the canonical
inclusions whenever one extension divides another. Record the algebraic
closure as the filtered union of these finite extensions.

## Depends on

- This is a foundational finite-field leaf with no roadmap prerequisite.

## Sources

- [Hartshorne Appendix C.1, finite-field setup, p.449](../../../sources/hartshorne-appendix-c-1.md)
