---
article_id: af_22028ab9c58689fa84aba6a3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.imageSheafification_mono
---

# The image is a subsheaf

For a morphism of sheaves of abelian groups $\varphi : F \longrightarrow G$, sheafify the
pointwise image presheaf. The induced map $im \varphi \longrightarrow G$ is a monomorphism, so the
image identifies canonically with a subsheaf of $G$.

Sheafification sends a sectionwise injective morphism to a
monomorphism, as in Hartshorne's Exercise II.1.4(a). Apply this to
the inclusion of the pointwise image presheaf into the target.

## Depends on

- [The associated sheaf](associated-sheaf.md)

## Proof depends on

- Sheafification preserves finite limits.

## Sources

- [Hartshorne II.1, image sheaf (p. 64) and Exercise 1.4(a,b) (p. 66)](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)
