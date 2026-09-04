---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.LocalRingAt Hartshorne.FunctionField Hartshorne.globalToLocal Hartshorne.localToFunctionField Hartshorne.globalToLocal_injective Hartshorne.localToFunctionField_injective Hartshorne.GermRep.rel_iff_eventually
---

# The three rings embed in the function field

Restriction of germs gives injective `k`-algebra maps

`𝒪(Y) ↪ 𝒪_{P,Y} ↪ K(Y)`

for every point `P` of a variety `Y`. Consequently all three rings may be
treated as subrings of `K(Y)`, and `𝒪(Y) = ⋂_{P ∈ Y} 𝒪_P` inside `K(Y)`.

**What is formalized is injectivity of the maps, not yet that they are
`k`-algebra homomorphisms.** The ring structure on the two quotients is built
with Theorem 3.2, where it is first used; until then these are injections of
sets. `𝒪(Y) = ⋂_{P ∈ Y} 𝒪_P` is likewise deferred to that theorem, whose proof
is where the intersection is actually needed.

Injectivity turns out to be immediate, for a reason worth recording: Hartshorne
identifies `(U, f)` with `(V, g)` when they agree on the *whole* overlap, not
when they agree near `P`. With that relation two global functions have the same
germ exactly when they are equal, and the two germ relations are the same
condition.

What the identity principle buys is that this is not an accident of the choice
of relation: `GermRep.rel_iff_eventually` shows agreeing on some neighbourhood
of `P` already forces agreement on the whole overlap. Without it Hartshorne's
definition and the usual "agree near `P`" definition of a germ would be
different notions, and only one of them would give injectivity for free.

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
