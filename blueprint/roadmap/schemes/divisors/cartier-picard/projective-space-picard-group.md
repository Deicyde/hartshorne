---
article_id: af_341d134f58a4a6e58ce14c1c
declaration: theorem
origin: cited
statement: retracted
lean: Hartshorne.exists_unique_iso_projTwistingSheaf Hartshorne.projectiveSpacePicardEquiv Hartshorne.projectiveSpacePicardEquiv_projTwistingSheaf
---

# The Picard group of projective space

Let $k$ be a field and $n \ge 0$. Every invertible sheaf on $\mathbb{P}^n_k$ is
isomorphic to $\mathcal{O}(l)$ for some integer $l$. If $n \ge 1$, this integer $l$ is
unique, and $\operatorname{Pic} (\mathbb{P}^n_k) \cong \mathbb{Z}$ with generator
$\mathcal{O}(1)$.

For $n \ge 1$, identify the hyperplane divisor with $\mathcal{O}(1)$ and transport the
degree isomorphism for the Weil class group through the locally factorial
class–Picard equivalence. For $n = 0$, $\mathbb{P}^0_k = \operatorname{Spec} k$, and every
invertible sheaf on the spectrum of a field is free of rank one, hence isomorphic to
$\mathcal{O} = \mathcal{O}(0)$.

## Depends on

- [The class group of projective space](../weil-divisors/projective-space-class-group.md)
- [Regular schemes are locally factorial](regular-locally-factorial.md)
- [Weil classes and the Picard group on a locally factorial scheme](locally-factorial-class-picard-equivalence.md)
- [Twisting sheaves on Proj](../../projective-sheaves/proj-twisting-sheaf.md)

## Proof depends on

- [The projective-space case of Bertini](../../differentials/canonical-bertini/bertini-projective-space-case.md), for regularity of projective space.
- The sheaf associated to a hyperplane is the standard twisting sheaf.

## Sources

- [Hartshorne II.6, Corollary 6.17 on printed p.145](../../../../sources/hartshorne-ii-6.md#cartier-divisors-and-invertible-sheaves)
