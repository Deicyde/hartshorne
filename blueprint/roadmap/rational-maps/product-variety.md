---
article_id: af_7b4c04ecca578f6cd6b4d287
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.product_variety
---

# Products of varieties

Use [the Segre embedding](segre-embedding.md) to identify $\mathbb{P} ^{r} \times \mathbb{P} ^{s}$ with its
image, giving it the structure of a projective variety. For quasi-projective
$X \subseteq \mathbb{P} ^{r}$ and $Y \subseteq \mathbb{P} ^{s}$, the subset $X \times Y \subseteq \mathbb{P} ^{r} \times \mathbb{P} ^{s}$ is then a quasi-projective
variety, projective when $X$ and $Y$ are (Exercise 3.16(a),(b)). The two
projections are morphisms, and a pair of morphisms $Z \to X$, $Z \to Y$ induces a
morphism $Z \to X \times Y$.

Adopted from §3 because the blowing-up construction is carried out inside
$\mathbb{A} ^{n} \times \mathbb{P} ^{n-1}$.

## What is claimed

Hartshorne's part (c), that $X \times Y$ is a product in the category of varieties,
is starred in the source. Only the part §4 consumes is claimed here: the
projections are morphisms and the universal arrow exists. Uniqueness of that
arrow is free once [Lemma 4.1](morphism-agreement.md) is available, but it is
not used.

The topology is the sticking point for a reader and deserves saying once: the
Zariski topology on $X \times Y$ is *not* the product of the Zariski topologies.
$\mathbb{P} ^{1} \times \mathbb{P} ^{1}$ is a quadric surface in $\mathbb{P} ^{3}$ containing curves that are not finite
unions of horizontal and vertical lines, so the product topology is strictly
coarser. Every statement here is about the topology induced from $\mathbb{P} ^{N}$ through the Segre embedding.

*Closed.* For $X$, $Y$ projective, $X \times Y$ is the intersection of the Segre
image with the zero sets of the bihomogeneous equations of $X$ and $Y$, read in
the $z_{ij}$. If $f(x)$ has degree $d$, the equations obtained by replacing each
$x_{i}$ by $z_{ij}$, for every column $j$, evaluate to $f(x)y_{j}^{d}$; the analogous row
equations for a degree-$e$ form $g(y)$ evaluate to $x_{i}^{e}g(y)$. Since each factor
has a nonzero coordinate, these homogeneous families recover exactly the two
factor conditions.

*Irreducible.* Fixing either factor makes the Segre map continuous: substituting
one homogeneous coordinate vector turns every homogeneous equation in the
Segre coordinates into a homogeneous equation on the other factor. For a
closed cover of the product, irreducibility of $Y$ forces each slice $\{x\} \times Y$
into one member; those two alternatives are closed conditions on $x$, so
irreducibility of $X$ forces every slice into the same member. This is the
closed-fibre argument of Exercise 3.15(a), applied directly to the
Segre-induced topology.

*Quasi-projective.* Write $X = V \cap U$ and $Y = W \cap T$, with $V,W$ projective
and $U,T$ ambient open. The same lifted factor equations show that $X \times Y$ is
the product $V \times W$ intersected with the complements of the loci corresponding
to $U^{c}$ and $T^{c}$, hence an ambient open intersection.

*Projections and the universal arrow.* Both are checked chartwise, where the
Segre coordinates $z_{ij}$ become ordinary affine coordinates and the criterion
for a morphism to an affine variety applies.

## Depends on

- [The Segre embedding](segre-embedding.md)
- [Morphisms](../morphisms/morphism.md)
- [Varieties](../morphisms/variety.md)

## Proof depends on

- [Varieties are covered by affine pieces](../projective-varieties/affine-cover.md)
- [Criterion for a morphism to an affine variety](../morphisms/morphism-to-affine-criterion.md)
- [The charts are isomorphisms of varieties](../morphisms/projective-rings/chart-isomorphism.md)

## Sources

- [Hartshorne I.3, Exercise 3.16 (p. 22)](../../sources/hartshorne.md#i4)
