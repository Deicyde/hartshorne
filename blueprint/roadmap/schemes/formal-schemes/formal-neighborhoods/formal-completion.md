---
article_id: af_2d321ba1dda8b1030bb0580d
declaration: def
origin: cited
source_units: [chapter-ii-section-9]
---

# Formal completion as a locally ringed space

For `X`, `Y`, and `I` as in the infinitesimal-neighbourhood construction,
define the formal completion `Xhat_Y` to have topological space `|Y|` and
structure sheaf

`O_(Xhat_Y) = lim_n (O_X / I^(n+1))|_|Y|`.

Equip every stalk with its induced local-ring structure, making `Xhat_Y` a
locally ringed space. This is Hartshorne's plain ring-valued construction: no
topology is added to section rings.

## Depends on

- [Infinitesimal neighbourhoods](infinitesimal-neighborhoods.md)
- [Locally ringed spaces](../../spectrum-and-schemes/locally-ringed-space.md)
- [Limits of sheaves are computed pointwise](../../sheaves/limits-of-sheaves.md)

## Proof depends on

- A compatible inverse limit of local quotient rings is local.
- The module-ideal-sheaf/`IdealSheafData` bridge before taking powers and
  quotients.

## Sources

- [Hartshorne II.9, formal-completion definition (p.194)](../../../../sources/hartshorne-ii-9.md#formal-completions-and-formal-schemes)
