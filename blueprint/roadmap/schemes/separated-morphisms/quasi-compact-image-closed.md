---
article_id: af_2578974926636e66e8b2c175
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.isClosed_range_iff_stableUnderSpecialization
---

# Closed images and specialization

If $f : X \longrightarrow Y$ is quasi-compact, then the image $f(X)$ is closed if and only
if it is stable under specialization.

Only the reverse implication requires work. Reduce source and target, replace
the target by the reduced closure of the range, and localize around the chosen
specialization. Quasi-compactness gives finitely many affine source charts.
On one chart dominance gives an injective ring map; localizing above a minimal
prime produces a point over the required generalization, and stability under
specialization supplies the target point itself.

The assertion concerns the image of the whole source. It is the
form of the closed-image criterion used here.

## Depends on

- [Quasi-compact morphisms](../first-properties/quasi-compact-morphism.md)
- [Specialization and generization](../first-properties/specialization.md)

## Proof depends on

- [The reduced induced closed subscheme](../subschemes-and-dimension/reduced-induced-closed-subscheme.md)
- Existence of minimal primes and exactness of localization.
- For a quasi-compact scheme morphism, being a closed map is equivalent to preserving specialization.

## Sources

- [Hartshorne II.4, Lemma 4.5](../../../sources/hartshorne-ii-4.md#separatedness-and-the-valuative-criterion)
