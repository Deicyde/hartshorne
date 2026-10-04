---
article_id: af_8a57570ef4ec1d7a4d6b19c4
declaration: theorem
origin: cited
source_units: [chapter-ii-section-5]
---

# Finite pushforward preserves coherence

Let `f : X ⟶ Y` be a finite morphism of locally Noetherian schemes.  If `F`
is coherent on `X`, then `f_*F` is coherent on `Y`.  This is the positive
conclusion of Exercise 5.5(c), cited in Caution 5.8.1 and later in the proof of
Serre's theorem.  Exercise 5.5(a)'s counterexample remains explanatory rather
than a second completion target.

On an affine `V = Spec A` in `Y`, write `f⁻¹(V) = Spec B` with `B` finite over
`A`.  A finite `B`-module is finite over `A`; affine change of rings identifies
its tilde sheaf with the restriction of `f_*F` to `V`.

## Depends on

- [Finite morphisms](../first-properties/finite-morphism.md)
- [Pushforward, pullback, and their adjunction](module-push-pull-adjunction.md)
- [The affine-local criterion for coherence](coherent-affine-local-criterion.md)

## Proof depends on

- [Pushforward under Hartshorne's finiteness hypotheses](qcqs-pushforward-quasicoherent.md)
- A finite algebra is module-finite over its base, and a module finite over a
  finite algebra is finite over the base.
- Finite morphisms are affine, quasi-compact, and separated.

## Sources

- [Hartshorne II.5, Exercise 5.5(c), cited on printed pp. 115 and 121](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
