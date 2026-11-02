---
article_id: af_949c34bb369be4bc97dc3172
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.segre_embedding
---

# The Segre embedding

Let $N = rs + r + s$. The *Segre embedding* is

$\psi : \mathbb{P} ^{r} \times \mathbb{P} ^{s} \to \mathbb{P} ^{N}$, $(a_{0},\ldots ,a_r) \times (b_{0},\ldots ,b_s) \mapsto (\ldots , a_{i}b_{j}, \ldots )$

in lexicographic order. It is well defined and injective, and its image is a
projective variety: writing $z_{ij}$ for the homogeneous coordinates of $\mathbb{P} ^{N}$ and
$\mathfrak{a}$ for the kernel of the $k$-algebra map $k[z_{ij}]\longrightarrow k[x_0,\ldots,x_r,y_0,\ldots,y_s]$
sending $z_{ij}$ to $x_{i}y_{j}$, the image is $Z(\mathfrak{a} )$ (Exercise 2.14).

Adopted from §2 because [products of varieties](product-variety.md) are what
give $\mathbb{A} ^{n} \times \mathbb{P} ^{n-1}$ a meaning, and [blowing up](blowing-up.md) lives there.

## The three claims

*Well defined.* Rescaling $a$ by $\lambda$ and $b$ by $\mu$ rescales every $a_{i}b_{j}$ by
$\lambda \mu$, so the image point of $\mathbb{P} ^{N}$ is unchanged. The image vector is nonzero
because some $a_{i}$ and some $b_{j}$ are.

*Injective.* From the matrix $(a_{i}b_{j})$ up to scalar, pick a nonzero entry
$a_pb_q$; then the $q$-th column recovers $a$ up to scalar and the $p$-th row
recovers $b$ up to scalar.

*Image is $Z(\mathfrak{a} )$.* One inclusion is immediate: every element of $\mathfrak{a}$ vanishes on
the image by construction. The other is the calculation. A point of $Z(\mathfrak{a} )$ is a
matrix $(z_{ij})$, not identically zero, satisfying in particular the relations
$z_{ij}z_{lm}-z_{im}z_{lj}\in\mathfrak a$, so all $2 \times 2$ minors vanish; a nonzero matrix of
rank one is a product of a column and a row, which is exactly a point of the
image. Since $\mathfrak{a}$ is prime — it is the kernel of a map into a domain — $Z(\mathfrak{a} )$ is
irreducible, so the image is a projective variety and not merely a closed set.

The relations $z_{ij}z_{lm}=z_{im}z_{lj}$ generate $\mathfrak{a}$, but that is not needed: the
rank-one argument only uses that they *lie* in $\mathfrak{a}$.

## Depends on

- [Projective space](../projective-varieties/projective-space.md)
- [Projective algebraic sets](../projective-varieties/projective-algebraic-set.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)

## Proof depends on

- [Algebraic sets and homogeneous radical ideals](../projective-varieties/homogeneous-ideal-correspondence.md)
- [Homogeneous ideals](../projective-varieties/homogeneous-ideal.md)

## Sources

- [Hartshorne I.2, Exercise 2.14 (p. 13)](../../sources/hartshorne.md#i4)
