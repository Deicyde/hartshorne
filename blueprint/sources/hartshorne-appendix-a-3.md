# Hartshorne Appendix A, section 3: Chern classes

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Appendix A, §3, printed pp.429–431.  The projective-bundle formula A11 occurs
immediately before the section heading on p.429 and is supplied by the
Appendix A §§1–2 roadmap.  Exercise A.6.6, printed p.437, is the direct
exercise consequence retained with this section.

The base field is algebraically closed.  Unless stated otherwise, `X` is a
nonsingular quasi-projective variety, and all algebraic claims are valid in
arbitrary characteristic.  Hartshorne explicitly presents the appendix as an
outline: the projective-bundle formula, splitting principle, Whitney formula,
regular-section theorem, and self-intersection formula need exact external
proof sources.

## Projective-bundle definition, printed p.429

For a rank-`r` locally free sheaf `E`, use Hartshorne's quotient convention
for `pi:P(E)->X` and put `xi=c_1(O_(P(E))(1))`.  Property A11 says that

`A(P(E))`

is a free `A(X)`-module on `1,xi,...,xi^(r-1)`.  In particular `pi^*` is
injective.  Define `c_i(E) in A^i(X)`, for `0<=i<=r`, by `c_0(E)=1` and

`sum_(i=0)^r (-1)^i pi^*c_i(E) xi^(r-i)=0`.

The projective-bundle formula makes the coefficients exist uniquely.  Total
Chern classes and Chern polynomials are bookkeeping in the codimension-graded
Chow ring; the relation's signs depend on the quotient convention and must
not be transferred from a line-subbundle convention without checking them.

## Basic properties and splitting, printed p.430

- **C1.** For a divisor `D`,
  `c_t(O_X(D))=1+D*t`.
- **C2.** For a morphism `f:X'->X` between nonsingular quasi-projective
  varieties, `c_i(f^*E)=f^*c_i(E)`.
- **C3.** For an exact sequence
  `0->E'->E->E''->0`,
  `c_t(E)=c_t(E')c_t(E'')`.
- C1–C3 characterize the Chern-class theory uniquely.
- The splitting principle supplies `f:X'->X` with injective Chow pullback such
  that `f^*E` has a filtration by invertible-sheaf quotients.
- **C4.** For a filtration with quotients `L_1,...,L_r`,
  `c_t(E)=product_i c_t(L_i)`.

Hartshorne proves C1 directly and calls C2 immediate from functoriality.  He
does not construct the splitting space or prove C3 in the text.  A proof of
C3 must not circularly assume C4 merely because the bundle splits after an
injective pullback.

## Formal Chern roots, printed pp.430–431

After an injective splitting pullback, write

`c_t(E)=product_i (1+a_i*t)` and
`c_t(F)=product_j (1+b_j*t)`.

Then

`c_t(E tensor F)=product_(i,j)(1+(a_i+b_j)*t)`

and

`c_t(exteriorPower p E)=product_(i_1<...<i_p)
  (1+(a_(i_1)+...+a_(i_p))*t)`.

Duals are obtained by replacing each `a_i` by `-a_i`.  The roots are formal
symbols, not elements chosen in `A(X)`.  The coefficients are separately
symmetric and therefore descend to universal polynomials in the actual Chern
classes through the fundamental theorem of symmetric polynomials.

## Zero schemes, printed p.431

A section `s in Gamma(X,E)` gives `O_X->E`; its dual defines the zero
subscheme `Y` by

`E^dual -> O_X -> O_Y -> 0`.

The closed-scheme structure and its associated cycle, including generic
length multiplicities, are part of the statement.  Property C6 says that if
the zero scheme has the expected pure codimension `r=rank(E)`, then

`c_r(E)=[Y] in A^r(X)`.

This is the regular-section/top-Chern theorem.  Hartshorne gives no proof;
the adopted proof must supply the regular-sequence or localized-top-Chern
argument rather than replacing the zero scheme by its underlying set.

## Self-intersection, printed p.431

Let `i:Y->X` be a nonsingular closed subvariety of codimension `r`, and let
`N_(Y/X)` be its normal bundle.  Property C7 states

`i^* i_*(1_Y)=c_r(N_(Y/X)) in A^r(Y)`.

The projection formula then gives

`[Y].[Y]=i_*c_r(N_(Y/X)) in A^(2r)(X)`.

Hartshorne attributes the result to Mumford and cites Lascu–Mumford–Scott.
The formula uses the normal bundle, not the conormal bundle, and its pull-push
is a refined intersection statement rather than set-theoretic intersection.

## Exercise disposition, printed p.437

- **Exercise A.6.6 — ADOPTED.**  For a nonsingular projective `n`-fold, the
  diagonal has normal bundle canonically isomorphic to `T_X`.  Applying C7
  gives `c_n(T_X)=Delta_X^2` after identifying the diagonal with `X`.
- Exercise A.6.5 belongs to the earlier Chow/blowup calculation and remains
  optional there.
- Exercises A.6.7–A.6.10 use the later Riemann–Roch sections and are deferred
  to those source units.

## Proof sources and blockers

The exact source roots are:

1. the projective-bundle formula A11, supplied by Appendix A §§1–2;
2. the flag-bundle splitting principle with injective Chow pullback;
3. the Whitney sum formula and uniqueness package;
4. the expected-codimension zero-scheme/top-Chern theorem;
5. the regular-embedding self-intersection theorem.

Hartshorne points to Grothendieck [3] for the treatment, Hirzebruch I §4.4
for formal Chern-root calculations, and Lascu–Mumford–Scott for
self-intersection.  Chevalley [2], Fulton, or the Stacks Project may supply
modern proof passages, but exact statements and conventions must be adopted;
generic bibliography is not a proof specification.

## Pinned Mathlib audit

The pinned checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`).  It has no
algebraic-geometric Chow ring, Gysin pullback, Chern-class, regular-section,
or self-intersection theorem, so no §3 leaf is an exact Mathlib result.

`LinearAlgebra.Basis.Flag` and `RingTheory.Grassmannian` are not flag schemes
or the splitting principle.  Relative Proj infrastructure does not prove the
Chow projective-bundle formula.  The multivariable symmetric-polynomial API,
including `MvPolynomial.esymmAlgHom_surjective`, is useful for eliminating
formal roots but is only supporting algebra.

## Representation warnings

- Use Chow cohomological grading by codimension.  The smooth
  quasi-projective hypothesis is what gives the contravariant Chow ring used
  in C2 and C7.
- Preserve the quotient convention for `P(E)` and `O(1)`.
- Treat Chern roots as formal or as classes only after an injective splitting
  pullback.
- A filtration by line-bundle quotients is not a chosen direct-sum
  decomposition.
- In C6 retain the ideal image, scheme multiplicities, and expected pure
  codimension.
- In C7 distinguish the normal bundle from its dual and refined pull-push
  from ordinary inverse image of subsets.

## Result-to-article map

| Source result | Roadmap article |
|---|---|
| Chern-class projective-bundle definition | `intersection-theory/chern-classes/chern-classes-projective-bundle-definition.md` |
| C1 | `intersection-theory/chern-classes/line-bundle-first-chern-class.md` |
| C2 | `intersection-theory/chern-classes/chern-pullback-naturality.md` |
| Splitting principle | `intersection-theory/chern-classes/chow-splitting-principle.md` |
| C3 | `intersection-theory/chern-classes/chern-whitney-sum.md` |
| Uniqueness | `intersection-theory/chern-classes/chern-theory-uniqueness.md` |
| C4 | `intersection-theory/chern-classes/filtered-bundle-chern-product.md` |
| Symmetric elimination of formal roots | `intersection-theory/chern-classes/formal-chern-roots-symmetric-elimination.md` |
| Tensor-product formula | `intersection-theory/chern-classes/tensor-product-chern-polynomial.md` |
| Exterior-power formula | `intersection-theory/chern-classes/exterior-power-chern-polynomial.md` |
| Dual formula | `intersection-theory/chern-classes/dual-bundle-chern-polynomial.md` |
| Zero-scheme definition | `intersection-theory/chern-classes/section-zero-scheme.md` |
| C6 | `intersection-theory/chern-classes/regular-section-top-chern-cycle.md` |
| C7 pull-push | `intersection-theory/chern-classes/regular-embedding-self-intersection.md` |
| C7 projection consequence | `intersection-theory/chern-classes/self-intersection-projection-formula.md` |

## Reused prerequisite map

| Source result | Existing roadmap article |
|---|---|
| Chow projective-bundle formula A11 | `intersection-theory/chow/properties/chow-projective-bundle-formula.md` |
| Chow pullback functoriality | `intersection-theory/chow/product/pullback-ring-functoriality.md` |
| Chow proper pushforward | `intersection-theory/chow/product/proper-pushforward-functoriality.md` |
| Projection formula A4 | `intersection-theory/chow/product/projection-formula.md` |
| Graded Chow groups | `intersection-theory/chow/cycles/chow-groups-graded.md` |
| Intersection-product existence | `intersection-theory/chow/product/intersection-product-existence.md` |
