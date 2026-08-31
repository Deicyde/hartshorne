---
declaration: theorem
origin: cited
---

# The three rings embed in the function field

Restriction of germs gives injective `k`-algebra maps

`𝒪(Y) ↪ 𝒪_{P,Y} ↪ K(Y)`

for every point `P` of a variety `Y`. Consequently all three rings may be
treated as subrings of `K(Y)`, and `𝒪(Y) = ⋂_{P ∈ Y} 𝒪_P` inside `K(Y)`.

Both maps are injective for the same reason: a regular function vanishing on a
nonempty open subset of an irreducible space vanishes everywhere, which is
Remark 3.1.1. Without that, the maps are merely restrictions and nothing may be
identified.

This is bookkeeping that Hartshorne does in a sentence and then relies on
silently for the rest of the section — Theorem 3.2(a) is stated as an
intersection of localizations *inside* `K(Y)`, and the whole of Theorem 3.4
compares subrings of `S(Y)`'s fraction field. In Lean the identification cannot
stay silent: it has to be a named map with a proved injectivity lemma, or every
later statement grows explicit coercions. That is why it is its own article
rather than a remark attached to the function field.

## Depends on

- [The ring of regular functions](ring-of-regular-functions.md)
- [The local ring at a point](local-ring.md)
- [The function field](function-field.md)

## Proof depends on

- [Regular functions are continuous](regular-function-continuous.md)
- [The local ring is local](local-ring-is-local.md)

## Sources

- [Hartshorne I.3, the injections `𝒪(Y) → 𝒪_P → K(Y)` (p. 16)](../../sources/hartshorne.md#i3)
