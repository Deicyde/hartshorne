---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# Zariski's Main Theorem: connected fibres

Let `f : X -> Y` be a birational projective morphism of Noetherian integral
schemes, and assume that `Y` is normal. Then every fibre `X_y` is connected.

This is the theorem Hartshorne calls Zariski's Main Theorem in III.11.4. It is
not the modern theorem factoring a quasi-finite separated morphism as an open
immersion followed by an integral morphism, and it is not identified with
Mathlib's theorem of that form.

## Depends on

- [Normal birational targets recover the structure sheaf](birational-normal-pushforward-structure-sheaf.md)
- [Direct image of the structure sheaf forces connected fibres](direct-image-units-connected-fibers.md)

## Proof depends on

- Apply the connected-fibre criterion to the isomorphism
  `O_Y ~= f_*O_X` supplied by normality and birationality.

## Sources

- [Hartshorne III.11, Corollary 11.4, p.280](../../../../sources/hartshorne-iii-11-12.md#applications-of-formal-functions-pp279281)
- [Zariski's original connected-fibre theorem](../../../../sources/hartshorne-iii-11-12.md#applications-of-formal-functions-pp279281)
