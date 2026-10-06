---
article_id: af_40231fde0010c4c5ac29c28f
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-1-4]
statement: formalized
proof: formalized
lean: Hartshorne.injectiveLocalizationMap_surjective
---

# Localization of an injective module is reached globally

Let `A` be Noetherian, `I` an injective `A`-module, and `f ∈ A`. The
canonical map `I ⟶ I_f` is surjective.

## Depends on

No project-local prerequisites.

## Proof depends on

- Noetherian stabilization of the annihilators of the powers of `f`.
- Baer's extension property for injective modules.
- The localized-module API `IsLocalizedModule.surj`; this does not itself
  assert surjectivity of the canonical map from `I`.

## Sources

- [Hartshorne III, Lemma 3.3 (p.214)](../../../sources/hartshorne-iii-3-4.md#affine-cohomology)
