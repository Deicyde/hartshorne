---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-1-4]
---

# Ideal-power torsion in an injective module

Let `A` be Noetherian, `a` an ideal, and `I` an injective `A`-module. The
submodule

`Γ_a(I) = {x | a^n x = 0 for some n}`

is injective.

## Depends on

No project-local prerequisites.

## Proof depends on

- [Artin–Rees induced topology](artin-rees-induced-topology.md)
- `Submodule.primaryComponent` and `Submodule.primaryComponent_mem` from
  `Mathlib/Algebra/Module/Torsion/PrimaryComponent.lean` model `Γ_a`.
- `Module.Baer.iff_injective` from
  `Mathlib/Algebra/Module/Injective.lean` supplies Baer's criterion.

## Sources

- [Hartshorne III, Lemma 3.2 (pp.213–214)](../../../sources/hartshorne-iii-3-4.md#affine-cohomology)
