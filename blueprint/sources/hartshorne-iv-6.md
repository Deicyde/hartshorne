# Hartshorne IV.6, classification of curves in projective three-space

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Chapter IV, §6, printed pp.349–355. The section begins after the final IV.5
exercise on p.349, and its nine exercises are on p.355.

## Parameter spaces and the existence problem, printed p.349

Hartshorne recalls the classical classification problem for smooth curves of
degree `d` and genus `g` in `P^3`. Chow varieties or Hilbert schemes show that
they are parametrized by a finite union of quasi-projective varieties, but
the component count and dimensions are generally difficult. Halphen stated
the possible `(d,g)` pairs; Hartshorne credits Gruson–Peskine with the first
correct proof. These assertions require external proof-level sources.

## Nonspecial embeddings, printed pp.349–350

Proposition 6.1 says a genus-`g>=2` curve has a nonspecial very ample divisor
of degree `d` exactly when `d>=g+3`. Necessity uses Riemann–Roch and excludes
the plane `d=g+2` case. Sufficiency bounds the locus of bad effective
degree-`d` divisors inside `X^d`: special residual divisors move in dimension
at most `g-1`, and adjoining two points gives a bad locus of dimension at
most `g+2`.

Corollary 6.2 gives the precise existence list for nonspecial hyperplane
sections of curves in `P^3`: `g=0,d>=1`; `g=1,d>=3`; or `g>=2,d>=g+3`.
Projection from higher projective space supplies the `P^3` model.

Proposition 6.3 treats special hyperplane sections. A nonplanar space curve
then has `d>=6` and `g>=d/2+1`; at degree six the only case is the canonical
genus-four curve.

## Castelnuovo's bound, printed pp.351–352

Theorem 6.4 bounds the genus of a nonplanar degree-`d` curve in `P^3` by

`d^2/4-d+1` for even `d`, and `(d^2-1)/4-d+1` for odd `d`.

Exercise IV.3.9 supplies a general hyperplane section of `d` distinct points
with no three collinear. Unions of planes give the successive lower bounds on
`dim|nD|-dim|(n-1)D|`; summation and eventual Riemann–Roch give the genus
bound. Equality forces a quadric containing the curve. Curves of balanced
types on a smooth quadric attain equality for every `d>=3`.

## Low-degree and degree-nine classifications, pp.352–355

Remark 6.4.1 inventories known families: plane curves, complete intersections,
curves on a smooth quadric, and curves on a quadric cone. The quadric-cone
degree/genus formulas are delegated forward to V Exercise 2.9 and are isolated
as a prerequisite article for later reconciliation.

Example 6.4.2 classifies degrees at most seven. The degree-one through
degree-four cases use earlier rational-normal and elliptic-quartic results.
Degrees five and six follow from the nonspecial and special bounds. At degree
seven, genus five occurs exactly from a genus-five curve with no `g^1_3`,
embedded by `K-P`; genus six is Castelnuovo-extremal on a quadric.

Example 6.4.3 classifies degree-nine genus-ten curves into two distinct
families: complete intersections of two cubics, and type `(3,6)` curves on a
smooth quadric. A pair of cohomology dimensions distinguishes them by
semicontinuity, so neither specializes to the other. Riemann–Roch and the
number of containing quadrics/cubics prove every curve with `(d,g)=(9,10)`
is one of the two types.

## Exercise disposition, printed p.355

- **Exercise 6.1 — OUT.** A rational quartic in `P^3` lies on a unique,
  necessarily smooth, quadric.
- **Exercise 6.2 — OUT.** Every rational quintic in `P^3` lies on a cubic,
  while examples exist on no quadric.
- **Exercise 6.3 — OUT.** A degree-five genus-two space curve lies on a
  unique quadric, and every abstract genus-two curve has such embeddings
  with the quadric smooth as well as embeddings with it singular.
- **Exercise 6.4 — OUT.** No degree-nine genus-eleven curve exists in
  `P^3`.
- **Exercise 6.5 — OUT.** A complete intersection of surfaces of degrees
  `a,b` in `P^3` lies on no surface of degree less than `min(a,b)`.
- **Exercise 6.6 — OUT.** A nonplanar projectively normal space curve has
  genus three or four in degree six, and genus five or six in degree seven.
- **Exercise 6.7 — OUT.** A line, conic, twisted cubic, and elliptic quartic
  have no multisecants, while every other space curve has infinitely many.
- **Exercise 6.8 — OUT.** A genus-`g` curve has a nonspecial degree-`d`
  divisor with basepoint-free complete system exactly when `d>=g+1`.
- **Exercise 6.9 — OUT.** If `X` is a smooth irreducible curve in `P^r`,
  then for every sufficiently large `m` a smooth degree-`m` surface in
  `P^r` contains `X`.

Later citations located in Chapter V occur in exercise-only or see-also
chains, not in included running-text proofs. In particular, V Exercise 2.4
cites IV Exercise 6.8, but this does not activate it under the standing rule.

## External sources and blockers

- A proof-level Chow/Hilbert parameter-space source is needed for the opening
  parameterization assertion.
- The Gruson–Peskine proof of Halphen's existence classification is a separate
  source root.
- Castelnuovo's theorem itself is proved in Hartshorne and is not blocked.
- The quadric-cone formulas are a forward source blocker until V Exercise 2.9
  and its singular-quadric divisor calculation are audited.

## Pinned Mathlib audit and false friends

The pinned checkout contains no exact Halphen, Castelnuovo, Hilbert/Chow
parameter-space, or smooth space-curve classification theorem. Existing
project nodes for projective cohomology, Riemann–Roch, quadrics, complete
intersections, semicontinuity, and IV Exercise 3.9 are the relevant inputs.

`Polynomial.hilbertPoly` is not a Hilbert scheme or the Hilbert polynomial of
a coherent sheaf. Generic projective spectra, algebraic cycles, and explicit
elliptic Weierstrass models do not supply the space-curve moduli statements.
No IV.6 article is an exact Mathlib leaf.

## Result-to-article map

| Source result | Roadmap article |
|---|---|
| Chow/Hilbert parameterization | `curves/space-curves/halphen/space-curve-parameter-space.md` |
| Halphen/Gruson–Peskine existence | `curves/space-curves/halphen/gruson-peskine-halphen-existence.md` |
| Proposition 6.1, necessity | `curves/space-curves/halphen/halphen-degree-necessity.md` |
| Bad-divisor dimension estimate | `curves/space-curves/halphen/special-divisor-locus-parameter-count.md` |
| Proposition 6.1 | `curves/space-curves/halphen/halphen-nonspecial-very-ample.md` |
| Corollary 6.2 | `curves/space-curves/halphen/nonspecial-p3-existence.md` |
| Proposition 6.3, degree bound | `curves/space-curves/halphen/special-hyperplane-degree-bound.md` |
| Proposition 6.3, genus bound | `curves/space-curves/halphen/special-hyperplane-genus-bound.md` |
| Proposition 6.3, degree six | `curves/space-curves/halphen/degree-six-special-canonical.md` |
| Castelnuovo hyperplane increments | `curves/space-curves/castelnuovo/castelnuovo-hyperplane-increment.md` |
| Castelnuovo summation bound | `curves/space-curves/castelnuovo/castelnuovo-genus-bound.md` |
| Equality implies a quadric | `curves/space-curves/castelnuovo/castelnuovo-equality-quadric.md` |
| Extremal examples | `curves/space-curves/castelnuovo/castelnuovo-extremal-examples.md` |
| Remark 6.4.1 | `curves/space-curves/castelnuovo/space-curve-existence-inventory.md` |
| Degrees one through four | `curves/space-curves/classification/space-curves-degree-at-most-four.md` |
| Degrees five and six | `curves/space-curves/classification/space-curves-degree-five-six.md` |
| Degree-seven genus-five criterion | `curves/space-curves/classification/degree-seven-genus-five-criterion.md` |
| Degree seven | `curves/space-curves/classification/space-curves-degree-seven.md` |
| Degree-nine types | `curves/space-curves/classification/degree-nine-genus-ten-two-families.md` |
| Semicontinuity separation | `curves/space-curves/classification/degree-nine-families-semicontinuity.md` |
| Degree-nine exhaustivity | `curves/space-curves/classification/degree-nine-genus-ten-exhaustivity.md` |
| Quadric-cone prerequisite | `curves/space-curves/prerequisites/quadric-cone-curve-degree-genus.md` |
