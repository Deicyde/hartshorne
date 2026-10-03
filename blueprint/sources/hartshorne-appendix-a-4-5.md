# Hartshorne Appendix A §§4–5, Riemann–Roch and generalizations

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Appendix A. The transition from Chern classes to §4 begins on printed p.431;
§4 occupies pp.431–434 and §5 pp.434–436. Exercises 6.1–6.10 occupy
pp.436–437. Appendix B begins on p.438, so there is no continuation.

Hartshorne explicitly presents an outline: the major Riemann–Roch,
positivity, and Hodge theorems are quoted, not proved. The cited external
sources are therefore theorem dependencies rather than optional references.

## Chern character and Todd class, printed pp.431–432

Using the splitting principle from §3, write the total Chern class of a
finite locally free sheaf `E` in formal roots `a_i`. Symmetric formal
power-series expressions in those roots descend to universal rational
polynomials in the Chern classes.

Hartshorne defines

`ch(E)=sum_i exp(a_i)`, and
`td(E)=prod_i a_i/(1-exp(-a_i))`

in the rational Chow ring. The low-degree expansions include

`ch(E)=r+c_1+(c_1^2-2c_2)/2+(c_1^3-3c_1c_2+3c_3)/6+...`,

and

`td(E)=1+c_1/2+(c_1^2+c_2)/12+...`.

For a line bundle `O(D)`, `ch(O(D))=exp(D)`.

## Hirzebruch–Riemann–Roch and specializations, printed pp.432–434

Theorem 4.1 states Hirzebruch–Riemann–Roch. For a smooth projective
`n`-fold `X` and finite locally free `E`,

`chi(E)=deg(ch(E)*td(T_X))_n`.

Hirzebruch proved the complex theorem; Hartshorne cites the generalized
Grothendieck proof over an arbitrary algebraically closed field through
Borel–Serre.

For a smooth curve, HRR specializes to

`chi(O(D))=deg D+1-g`.

For a smooth surface, `c_1(T_X)=-K` and

`td(T_X)=1-K/2+(K^2+c_2)/12`.

Thus

`chi(O_X(D))=D.(D-K)/2+(K^2+c_2)/12`,

and at `D=0` one obtains the Noether formula

`12*(1+p_a)=K^2+c_2`.

This is the proof source of Remark V.1.6.1. The previously untagged surface
HRR/Noether leaf is reconciled to this Appendix source unit and remains a
source blocker.

## Surface in projective fourspace, printed pp.433–434

For a smooth degree-`d` surface `X subset P^4`, the Euler sequence gives
`c(T_(P^4))=(1+h)^5`. Comparing the tangent-normal exact sequence gives

`c_1(N)=5H+K`,

`c_2(N)=10H^2-c_2(X)+5H.K+K^2`.

The self-intersection formula gives `deg c_2(N)=d^2`. Combining this with
Noether's formula yields

`d^2-10d-5H.K-2K^2+12+12p_a=0`.

Exercise 6.9 contains optional applications and is not required by later
running text.

## Nakai–Moishezon and higher Hodge index, printed pp.434–435

Theorem 5.1 states the general Nakai–Moishezon criterion. For `X` proper over
an algebraically closed field and `D` Cartier, `D` is ample exactly when

`D^(dim Y).Y>0`

for every positive-dimensional closed integral subscheme `Y`. Hartshorne
warns that this uses the elementary Cartier-on-subscheme intersection theory,
not the smooth moving-lemma theory developed in §§1–2. He cites Nakai,
Moishezon, and Kleiman.

For a smooth projective complex variety, algebraic cycles have singular-
cohomology classes and hence a notion of homological equivalence. Theorem 5.2
is the higher Hodge-index theorem: if `dim X=2k`, `Y` has codimension `k`,
the class of `Y.H` vanishes, and the class of `Y` does not, then

`(-1)^k*deg(Y.Y)>0`.

Hartshorne cites Weil's analytic Hodge theory. He also says that homological
and numerical equivalence agree for divisors on a smooth complex surface,
recovering the surface theorem. Grothendieck's positive-characteristic and
numerical standard-conjecture discussion is historical conjectural context,
not a claimed theorem leaf.

## Ktheory and generalized Riemann–Roch, printed pp.435–436

On a smooth quasi-projective variety, finite locally free resolutions identify
coherent-sheaf K0 with vector-bundle K0. Whitney multiplicativity extends
Chern classes to virtual bundles, tensor product makes K0 a ring, and

`ch:K0(X)->A(X) tensor Q`

is a ring homomorphism. Pullback of bundles gives contravariant K0
functoriality and commutes with `ch`.

For a proper morphism, Hartshorne defines

`f_!([F])=sum_i (-1)^i [R^i f_*F]`.

This is K-theoretic pushforward, not ordinary sheaf pushforward.

Theorem 5.3 is Grothendieck–Riemann–Roch: for a smooth projective morphism
`f:X->Y` of smooth quasi-projective varieties,

`ch(f_!(x))=f_*(ch(x)*td(T_f))`.

Hartshorne then records the SGA6 extension to projective lci morphisms over a
Noetherian base with an ample invertible sheaf, Jouanolou's integral formula
for closed immersions of smooth varieties, and Baum–Fulton–MacPherson's
singular Riemann–Roch. Each needs its cited proof source.

## Exercise disposition, printed pp.436–437

- **Exercise 6.1 — OUT.** Its alternate family formulation of rational
  equivalence is not used later.
- **Exercise 6.2 — ADOPTED.** It proves that proper generically finite
  pushforward between normal varieties preserves linear equivalence of Weil
  divisors, the codimension-one input needed for axiom A3.
- **Exercise 6.3 — ADOPTED.** The running computation of the Chow ring of
  projective space cites the direct projection proof that a degree-`d`
  subvariety is rationally equivalent to `d` times a linear space.
- **Exercises 6.4–6.5 — OUT.** The ruled-surface and point-blowup Chow-group
  examples have no later running dependency.
- **Exercise 6.6 — ADOPTED.** Appendix C uses the identity
  `c_n(T_X)=Delta^2` in its functional-equation discussion.
- **Exercises 6.7–6.10 — OUT.** The threefold RR, parity, projective-four-
  space applications, and abelian-threefold obstruction have no later
  included running dependency. The “See Exercise 6.9” after Example 4.1.3 is
  an optional application pointer.

Thus exactly Exercises 6.2, 6.3, and 6.6 are adopted.

## External proof sources and blockers

- Hirzebruch, *Topological Methods in Algebraic Geometry*, I §4.4, supplies
  the complex characteristic-class formalism and HRR; Borel–Serre supplies
  the algebraic Riemann–Roch source cited by Hartshorne.
- Nakai [1], Moishezon [1], and Kleiman [1] supply the general ampleness
  criterion and its restricted intersection formalism.
- Weil, *Variétés Kählériennes*, Theorem 8, supplies higher Hodge index; the
  cycle-class and surface comparison also need exact analytic sources.
- SGA6 and Manin [1] supply generalized GRR; Jouanolou [1] supplies the
  integral closed-immersion formula; Baum–Fulton–MacPherson and Fulton [2]
  supply singular Riemann–Roch.

The roadmap isolates ten explicit blocker roots: HRR, Cartier powers on a
singular ambient scheme, Nakai–Moishezon, cycle classes, higher Hodge index,
the surface homological/numerical comparison, GRR, SGA6 lci GRR, Jouanolou,
and singular RR.

## Pinned Mathlib audit and false friends

The pinned checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). No leaf in this
scope is an exact pinned-Mathlib result.

`AlgebraicGeometry.AlgebraicCycle` defines locally finite cycles and a
weighted pushforward, but has no rational equivalence, Chow group, pullback,
intersection product, degree, or Chern class. `MonoidLocalization`'s
Grothendieck group is abstract group completion, not coherent-sheaf or
vector-bundle K0. Symmetric-polynomial, Bernoulli/power-series, homological
Euler-characteristic, and topological-cohomology APIs are infrastructure or
false friends; they do not provide Chern character, Todd class, HRR, GRR,
Nakai–Moishezon, or Hodge index.

## Representation choices and warnings

- Work in the rational Chow ring for `ch`, `td`, HRR, and GRR. Jouanolou's
  integral refinement is a separate theorem.
- Truncate formal characteristic-class series above the dimension of the
  variety.
- Represent `f_!` by alternating higher-direct-image classes in K0, not by
  ordinary sheaf pushforward.
- General Nakai uses repeated Cartier intersection with an integral
  subscheme and does not assume the full smooth moving lemma.
- Retain the complex field, even dimension, middle codimension, primitive
  condition, and sign in higher Hodge index.
- Separate proved Hodge theory from Grothendieck's conjectural
  positive-characteristic discussion.

## Result-to-article map

| Source result | Roadmap article |
|---|---|
| Formal Chern-root calculus | `intersection-theory/riemann-roch/characteristic-classes/formal-chern-root-calculus.md` |
| Chern character | `intersection-theory/riemann-roch/characteristic-classes/chern-character.md` |
| Todd class | `intersection-theory/riemann-roch/characteristic-classes/todd-class.md` |
| Low-degree expansions | `intersection-theory/riemann-roch/characteristic-classes/chern-todd-low-degree-expansions.md` |
| Line-bundle Chern character | `intersection-theory/riemann-roch/characteristic-classes/line-bundle-chern-character.md` |
| Hirzebruch–Riemann–Roch | `intersection-theory/riemann-roch/characteristic-classes/hirzebruch-riemann-roch.md` |
| Curve specialization | `intersection-theory/riemann-roch/specializations/curve-hrr-specialization.md` |
| Surface tangent Chern data | `intersection-theory/riemann-roch/specializations/surface-tangent-chern-data.md` |
| Projective-four-space tangent Chern classes | `intersection-theory/riemann-roch/specializations/projective-four-space-tangent-chern.md` |
| Surface normal-bundle Chern classes | `intersection-theory/riemann-roch/specializations/surface-p4-normal-bundle-chern.md` |
| Surface-in-`P^4` numerical relation | `intersection-theory/riemann-roch/specializations/surface-p4-numerical-relation.md` |
| Cartier powers against integral subschemes | `intersection-theory/riemann-roch/positivity/cartier-power-integral-subscheme-intersection.md` |
| Nakai–Moishezon | `intersection-theory/riemann-roch/positivity/nakai-moishezon-proper-scheme.md` |
| Homological cycle class | `intersection-theory/riemann-roch/positivity/homological-cycle-class.md` |
| Higher Hodge index | `intersection-theory/riemann-roch/positivity/higher-hodge-index.md` |
| Surface homological/numerical comparison | `intersection-comparisons/surface-divisor-homological-numerical-equivalence.md` |
| Smooth K0 comparison | `intersection-theory/riemann-roch/k-theory/smooth-k0-vector-bundle-coherent-comparison.md` |
| Chern classes on K0 | `intersection-theory/riemann-roch/k-theory/chern-classes-on-k0.md` |
| Chern character ring map | `intersection-theory/riemann-roch/k-theory/chern-character-ring-hom.md` |
| K0 pullback | `intersection-theory/riemann-roch/k-theory/k0-pullback.md` |
| Proper K0 pushforward | `intersection-theory/riemann-roch/k-theory/proper-k0-pushforward.md` |
| Grothendieck–Riemann–Roch | `intersection-theory/riemann-roch/k-theory/grothendieck-riemann-roch.md` |
| SGA6 lci GRR | `intersection-theory/riemann-roch/k-theory/sga6-lci-grothendieck-riemann-roch.md` |
| Jouanolou integral formula | `intersection-theory/riemann-roch/k-theory/jouanolou-integral-closed-immersion-rr.md` |
| Singular Riemann–Roch | `intersection-theory/riemann-roch/k-theory/baum-fulton-macpherson-singular-rr.md` |

## Adopted-exercise map

| Source result | Roadmap article |
|---|---|
| Exercise 6.2 | `intersection-theory/chow/cycles/exercises/proper-generically-finite-divisor-pushforward.md` |
| Exercise 6.3 | `intersection-theory/exercises/projective-cycle-rational-equivalent-linear-space.md` |
| Exercise 6.6 | `intersection-theory/chern-classes/exercises/diagonal-self-intersection-top-chern.md` |
