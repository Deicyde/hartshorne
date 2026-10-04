---
article_id: af_d025599c8fd888815a2f19dd
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
---

# The scheme-theoretic image of a reduced source

If `f : Z → X` has reduced source, its scheme-theoretic image is the reduced
induced closed subscheme on `closure (f(Z))`.

Identify the kernel ideal sheaf defining `f.image` with the vanishing ideal of
the closure. Mathlib proves `Hom.support_ker` under a quasi-compact hypothesis;
Hartshorne's exercise is unrestricted, so the project must either remove that
hypothesis or give a direct local proof before invoking the smallest reduced
structure.

## Depends on

- [The scheme-theoretic image](scheme-theoretic-image.md)
- [The smallest structure on a closed subset](reduced-induced-smallest.md)
- [Reduced schemes](../first-properties/reduced-scheme.md)

## Proof depends on

- The support of the kernel ideal sheaf and the reduced-source vanishing
  argument.

## Sources

- [Hartshorne II.3, Exercise 3.11(d), reduced-source clause (p. 92)](../../../sources/hartshorne-ii-3.md#subschemes-and-dimension)

