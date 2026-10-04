---
article_id: af_0054399084d8fcffca7fc1f8
declaration: def
origin: cited
source_units: [chapter-ii-section-9]
---

# Infinitesimal neighbourhoods

Let `X` be a Noetherian scheme and let `Y ↪ X` be a closed subscheme with
module ideal sheaf `I ↪ O_X`. For `n : Nat`, define the `n`th infinitesimal
neighbourhood `Y n` to be the closed subscheme cut out by `I^(n+1)`.
In particular `Y 0 = Y`; there is no artificial quotient by `I^0`.

The definition is made on the module ideal sheaf. It is transported to and
from Mathlib's affine-open `IdealSheafData` through the existing bridge; these
representations are not treated as definitionally equal.

## Depends on

- [Module ideal sheaves and ideal data](../../coherent-sheaves/module-ideal-sheaf-data.md)
- [Closed subschemes and ideal data](../../coherent-sheaves/closed-subschemes-ideal-data.md)

## Proof depends on

- Powers of quasi-coherent ideal subsheaves remain quasi-coherent.
- [Noetherian schemes and finite affine covers](../../first-properties/noetherian-scheme.md)

## Sources

- [Hartshorne II.9, introductory formal-neighbourhood discussion (p.190)](../../../../sources/hartshorne-ii-9.md#formal-completions-and-formal-schemes)
