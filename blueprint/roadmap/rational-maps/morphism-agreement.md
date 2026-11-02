---
article_id: af_daad9faeda5a941ac86e9d79
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.eq_of_eqOn_isOpen_hom
---

# Morphisms agreeing on an open set

Let $X$ and $Y$ be varieties and $\varphi , \psi : X \to Y$ morphisms. If there is a
nonempty open $U \subseteq X$ with $\varphi |_U = \psi |_U$, then $\varphi = \psi$ (Lemma 4.1).

This is the whole reason rational maps are well behaved, and it is the algebraic
substitute for the Hausdorff separation that would make the statement trivial in
topology. The Zariski topology is not Hausdorff and the statement is not
topologically formal: it is the assertion that the diagonal of $Y \times Y$ is
closed.

## Hartshorne's proof, and the proof used here

Hartshorne reduces to $Y = \mathbb{P} ^{n}$, gives $\mathbb{P} ^{n} \times \mathbb{P} ^{n}$ its Segre structure, observes
that the diagonal $\Delta$ is cut out by the equations $x_{i}y_{j} = x_{j}y_{i}$ and so is
closed, and concludes because $(\varphi \times \psi )(U) \subseteq \Delta$ with $U$ dense.

That route makes products a prerequisite of everything downstream, and products
are themselves an adopted exercise. The same equations prove the lemma without
constructing the product, by reading them chartwise, and that is the route used
here:

- the agreement locus $Z = \{x \in X : \varphi (x) = \psi (x)\}$ is closed;
- it contains $U$, which is dense because $X$ is irreducible;
- so $Z = X$.

Only the first clause has content. Cover $X$ by the open sets
$W_{ij} = \varphi ^{-1}(U_{i}) \cap \psi ^{-1}(U_{j})$, which do cover since the charts cover $\mathbb{P} ^{n}$. On
$W_{ij}$ write $a_{0},\ldots ,a_{n}$ for the homogeneous coordinates of $\varphi$ normalised by
$a_{i} = 1$ and $b_{0},\ldots ,b_{n}$ for those of $\psi$ normalised by $b_{j} = 1$; each is a
regular function on $W_{ij}$, being a chart coordinate of a morphism. Two points
of $\mathbb{P} ^{n}$ given by nonzero coordinate vectors are equal exactly when all the
$2 \times 2$ minors vanish, so

$Z\cap W_{ij}=\{x\in W_{ij}:a_l(x)b_m(x)-a_m(x)b_l(x)=0\text{ for all }l,m\}$,

a common zero set of regular functions, hence closed in $W_{ij}$. Closedness is
local, so $Z$ is closed.

The mathematics is Hartshorne's — these are the Segre equations for the
diagonal — but arranged so that the Segre embedding is needed only where the
source needs it for its own sake, in the blow-up construction.

The target is assumed quasi-projective, as in Hartshorne's varieties.
The separatedness hypothesis cannot be dropped for arbitrary abstract
varieties: the line with doubled origin gives a counterexample.

## Depends on

- [Morphisms](../morphisms/morphism.md)
- [Varieties](../morphisms/variety.md)
- [Regular functions on a quasi-projective variety](../morphisms/regular-function-quasi-projective.md)

## Proof depends on

- [The standard affine charts](../projective-varieties/standard-affine-charts.md)
- [Regular functions are continuous](../morphisms/regular-function-continuous.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)

## Sources

- [Hartshorne I.4, Lemma 4.1 (p. 24)](../../sources/hartshorne.md#i4)
