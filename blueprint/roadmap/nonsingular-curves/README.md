---
article_id: af_ed89215a4d06659a130c6da1
---

# Local structure of nonsingular curves

Hartshorne's study of curves starts with a description of their local rings
in terms of valuations. A curve is a variety of dimension one. At a
nonsingular point, its local ring is a Noetherian regular local domain of
dimension one. By Theorem 6.2A, this ring is a discrete valuation ring. Its
image in the function field is therefore a valuation ring of $K(Y)/k$.

Lemma 6.4 then shows that local rings distinguish points. For a
quasi-projective variety $Y$, an inclusion
$\mathcal{O}_{Q,Y} \subseteq \mathcal{O}_{P,Y}$ inside $K(Y)$ forces $P=Q$.
Hartshorne puts the two points into a common affine chart. An equivalent
projective argument chooses a homogeneous linear fraction regular at $Q$
but with a pole at $P$, contradicting the inclusion when the points differ.

## Algebraic background

Theorem 6.1A characterizes valuation rings as maximal local subrings under
domination and shows that every local subring of a field is dominated by a
valuation ring. Theorem 6.2A connects this general theory to nonsingular
curves: for a Noetherian local domain of dimension one, being a discrete
valuation ring, being integrally closed, being regular, and having a
principal maximal ideal are equivalent.

## Valuation and DVR background

- [Valuation rings are maximal local subrings](valuation-ring-maximal-local-subring.md)
- [Every local subring is dominated by a valuation ring](valuation-ring-dominates-local-subring.md)
- [Characterizations of discrete valuation rings](dvr-characterizations.md)
- [Localizations of a Dedekind domain are DVRs](dedekind-localization-dvr.md)

## Curves and their local rings

- [Curves](curve.md)
- [The function field is the fraction field of every local ring](local-ring-fraction-field.md)
- [Dimension of the local ring of a variety](local-ring-dimension.md)
- [Local rings of nonsingular curves are DVRs](nonsingular-curve-local-ring-dvr.md)
- [Nonsingular curve points define discrete valuations](nonsingular-curve-valuation.md)

## The local ring determines the point

- [Linear fractions separate projective points](projective-linear-separation.md)
- [Membership of a homogeneous fraction in a local ring](homogeneous-fraction-local-membership.md)
- [The local ring determines the point](local-ring-inclusion-determines-point.md)

## Scope note

This milestone stops after Lemma 6.4 on printed p. 41. Theorem 6.3A is
handled in the following
[normalization and valuation-space milestone](../curve-normalization/README.md),
together with Theorem 3.9A and Lemma 6.5 through Proposition 6.7. Proposition
6.8 through Corollary 6.12 are decomposed in the following
[projective-model milestone](../projective-models/README.md); the §6 exercises
remain out of scope.
