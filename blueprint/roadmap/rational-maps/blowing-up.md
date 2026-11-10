---
article_id: af_4d390f0993f2c69e8e37f37c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.blowing_up
---

# Blowing up a point

The *blowing-up of $\mathbb{A} ^{n}$ at the origin* is the closed subset

$X=\{(x,y)\in\mathbb A^n\times\mathbb P^{n-1}:x_i y_j=x_j y_i\text{ for all }i,j\}$,

together with the morphism $\varphi : X \to \mathbb{A} ^{n}$ restricting the first projection. For a
closed subvariety $Y \subseteq \mathbb{A} ^{n}$ through the origin $O$, the *blowing-up of $Y$ at
$O$* is $\widetilde Y=\overline{\varphi^{-1}(Y\setminus\{O\})}$, with $\varphi : \widetilde{Y} \to Y$ the restriction. Blowing up
at any other point is a linear change of coordinates away.

This is the last construction of the section and the standard example of a
birational morphism that is not an isomorphism. It is also the tool resolution
of singularities is built from, which is why Hartshorne includes it here rather
than leaving it to the exercises.

## What is claimed

The formal statement treats the origin in a finite nonempty affine coordinate
space over an algebraically closed field. It constructs the incidence locus
and proves all four properties below. For every affine variety $Y$ through the
origin it records the exhaustive edge-case split: if $Y\setminus\{O\}$ is nonempty,
the strict transform is quasi-projective and birational to $Y$; otherwise
$Y = \{O\}$ and the displayed strict transform is empty. Thus Hartshorne's
birationality sentence is formalized in precisely its nondegenerate case,
while its omitted zero-dimensional exception is made explicit.

Moving the centre by a linear change of coordinates, the general criterion
that a blow-up of a singular variety is not an isomorphism, and the detailed
calculation for the nodal cubic are context rather than claims of this node.

## The four properties of $X$

1. For $P \ne O$, $\varphi^{-1}(\{P\})$ is a single point, and $\varphi$ restricts to an isomorphism
   $X\setminus\varphi^{-1}(\{O\})\cong\mathbb A^n\setminus\{O\}$. Given $P = (a_{1},\ldots ,a_n)$ with $a_i \ne 0$, the equations
   force $y_{j} = (a_{j}/a_{i}) y_{i}$, so $y = (a_{1},\ldots ,a_n)$ up to scalar. The inverse
   morphism is $P \mapsto P \times (a_{1},\ldots ,a_n)$.
2. $\varphi^{-1}(\{O\})\cong\mathbb P^{n-1}$: the equations are vacuous when $x = 0$, so the fibre is all
   of $\mathbb{P} ^{n-1}$.
3. Points of $\varphi^{-1}(\{O\})$ correspond to lines through $O$ in $\mathbb{A} ^{n}$. The line
   $x_{i} = a_{i}t$ lifts to $x_{i} = a_{i}t, y_{i} = a_{i}$, and those equations still make sense
   at $t = 0$, meeting $\varphi^{-1}(\{O\})$ in the point $(a_{1},\ldots ,a_n) \in \mathbb{P} ^{n-1}$.
4. $X$ is irreducible. It is the union of $X\setminus\varphi^{-1}(\{O\})$, isomorphic to $\mathbb A^n\setminus\{O\}$
   and so irreducible, and $\varphi^{-1}(\{O\})$; by (3) every point of $\varphi^{-1}(\{O\})$ lies in the
   closure of a line inside the first piece, so the first piece is dense.

Then $\varphi$ induces an isomorphism $\widetilde Y\setminus\varphi^{-1}(\{O\})\cong Y\setminus\{O\}$, so $\varphi : \widetilde{Y} \to Y$ is a
birational morphism. As motivation, Hartshorne explains that it is not an
isomorphism when $Y$ is singular at $O$: Example 4.9.1 blows up the plane cubic
$y^{2} = x^{2}(x + 1)$ at the origin and finds that the two branches, which met at
$O$, are pulled apart to the two points $u = \pm 1$ of the exceptional curve,
their slopes.

Hartshorne notes that the construction looks as though it depends on the
embedding $Y \subseteq \mathbb{A} ^{n}$ and remarks that it does not, referring forward to II.7.15.1.
That is out of scope and is not claimed.

## Depends on

- [Products of varieties](product-variety.md)
- [Birational maps](birational-map.md)
- [Morphisms](../morphisms/morphism.md)

## Proof depends on

- [Morphisms agreeing on an open set](morphism-agreement.md)
- [Criterion for a morphism to an affine variety](../morphisms/morphism-to-affine-criterion.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)
- [Every finitely generated domain is a coordinate ring](../affine-varieties/coordinate-ring-realization.md)
- [Birational varieties have isomorphic open subsets](birational-open-subsets.md)

## Sources

- [Hartshorne I.4, Blowing Up and Example 4.9.1 (pp. 28-29)](../../sources/hartshorne.md#i4)
