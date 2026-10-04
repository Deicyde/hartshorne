---
article_id: af_04f823fdc3f938711c5a757f
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
statement: formalized
proof: formalized
lean: Hartshorne.finiteType_of_comp
---

# Cancellation for finite type

If `f : X → Y` is quasi-compact and `g ∘ f : X → Z` is finite type, then `f` is finite type.

The given quasi-compactness supplies one conjunct. Cancel local finite type from the composite using `locallyOfFiniteType_of_comp`.

## Depends on

- [Morphisms of finite type](finite-type.md)
- [Quasi-compact morphisms](quasi-compact-morphism.md)

## Proof depends on

- Finite type of ring homomorphisms cancels from a composite in the required direction.

## Sources

- [Hartshorne II.3 (finite-type-and-finite-morphisms)](../../../sources/hartshorne-ii-3.md#finite-type-and-finite-morphisms)
