# Hartshorne IV.5, the canonical embedding

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Chapter IV, §5. The section begins after the final IV.4 exercises on printed
p.340. Its running text occupies pp.341–347 and its exercises occupy
pp.348–349 immediately before §6.

Chapter IV's standing convention remains in force: `X` is an integral,
proper, regular one-dimensional scheme over an algebraically closed field,
and its genus is `g`. Canonical divisors are chosen representatives of the
canonical class and assertions involving them are invariant under linear
equivalence.

## Canonical maps, printed pp.341–343

For `g=0` the canonical system is empty and for `g=1` it is the zero system.
Lemma 5.1 says that for `g>=2` the canonical system has no base points, hence
defines the canonical morphism.

Proposition 5.2 characterizes its being a closed immersion: the canonical
divisor is very ample exactly when `X` is not hyperelliptic. A
nonhyperelliptic curve of genus at least three therefore has its canonical
embedding in `P^(g-1)`, with degree `2g-2`.

For genus three the canonical model is a plane quartic, and every nonsingular
plane quartic is canonical. For genus four it is a degree-six curve in `P^3`,
contained in a unique irreducible quadric and an additional irreducible cubic;
the curve is their complete intersection. Conversely every nonsingular
quadric-cubic complete intersection is a canonical genus-four curve, and
Bertini supplies such examples.

Proposition 5.3 treats the hyperelliptic case. The `g^1_2` is unique, the
canonical map is the degree-two map to `P^1` followed by the `(g-1)`-uple
embedding, and every effective canonical divisor is a sum of `g-1` fibres of
this unique pencil.

## Clifford's theorem, printed pp.343–345

Lemma 5.5 proves

`dim|D| + dim|E| <= dim|D+E|`

for effective divisors by the finite-fibre addition morphism between their
complete linear systems.

Clifford's theorem states that an effective special divisor satisfies

`dim|D| <= deg(D)/2`.

Equality occurs exactly for `D=0`, `D=K`, or for a hyperelliptic curve when
`|D|` is a multiple of the unique `g^1_2`. Hartshorne follows Saint-Donat:
the inequality combines Lemma 5.5 with Riemann–Roch, while the equality case
uses induction through the common part of effective representatives of `D`
and `K-D`.

## Trigonal and canonical examples, printed pp.345–346

The text introduces `g^r_d` notation and trigonal curves. It quotes
Kleiman–Laksov: every curve has a `g^1_d` for `d >= g/2+1`, while for smaller
`d` some curves do not. This implies nonhyperelliptic curves exist in every
genus at least three.

For genus three, projection of a canonical plane quartic from a point gives
many `g^1_3`s. A nonhyperelliptic genus-four canonical curve has two such
pencils when its unique quadric is smooth and one when it is a quadric cone.
For genus five, a `g^1_3` is equivalent to a trisecant of the canonical model.
A nonsingular complete intersection of three quadrics has no trisecant and
hence no `g^1_3`; projection from one point gives the stated `g^2_4` example.

The Kleiman–Laksov theorem is quoted without proof and needs an exact adopted
proof source.

## Moduli of curves, printed pp.346–347

Hartshorne defines a fine moduli variety `M_g` as one carrying a universal
flat family with unique pullback maps. Such a fine object cannot exist in this
form because a nontrivial isotrivial family would have constant classifying
map. The adopted III.9.10 node constructs a nonproduct family but does not
show all fibres are isomorphic, so a stronger construction remains a source
obligation.

Mumford's coarse moduli theorem gives, for `g>=2`, a variety whose closed
points are isomorphism classes and to which every flat family has a
fibrewise-classifying morphism. For genus one with a section, the affine
`j`-line is the coarse moduli variety; rationality of `j` in Weierstrass
coefficients supplies the family map.

Deligne–Mumford prove `M_g` irreducible and quasi-projective of dimension
`3g-3`. Under the characteristic-not-two hypothesis used by the branch-cover
method of Exercise 2.2, the hyperelliptic locus is irreducible of dimension
`2g-1`; for genus two it is all of `M_2`. In characteristic zero, for genus
three it has dimension five, while nonhyperelliptic plane quartics give the
six-dimensional complementary stratum after quotienting the
fourteen-dimensional equation space by the eight-dimensional projective
linear group. The characteristic-zero finiteness result of Exercise 5.2 is
needed for this fibre dimension.

## Exercise disposition, printed pp.348–349

- **Exercise 5.1 — OUT.** A hyperelliptic curve is never a complete
  intersection in projective space.
- **Exercise 5.2 — ADOPTED.** For a characteristic-zero curve of genus at
  least two, `Aut X` is finite. Hyperelliptic automorphisms permute the branch
  points of the unique double cover; nonhyperelliptic automorphisms permute
  the finite hyperosculation set of the canonical embedding. Running Example
  5.5.6 uses this finiteness.
- **Exercise 5.3 — OUT.** The genus-four hyperelliptic,
  nonhyperelliptic, and unique-`g^1_3` families have dimensions seven, nine,
  and eight, with the last irreducible.
- **Exercise 5.4 — OUT.** A nonhyperelliptic genus-four curve with two
  `g^1_3`s has a plane-quintic model with two nodes and conversely; with one
  `g^1_3` it has a plane-quintic model with a tacnode, while its least nodal
  plane-model degree is six.
- **Exercise 5.5 — OUT.** For nonhyperelliptic genus-five curves: the
  three-quadric canonical complete intersections form a twelve-dimensional
  family; having a `g^1_3` is equivalent to a one-nodal plane-quintic model,
  an irreducible eleven-dimensional family; and in that case the conics
  through the node recover the canonical system and its unique trisecant
  cubic surface.
- **Exercise 5.6 — OUT.** A smooth plane quintic has no `g^1_3`, and not
  every nonhyperelliptic genus-six curve is a smooth plane quintic.
- **Exercise 5.7 — OUT.** Canonical plane-quartic automorphisms come from
  `PGL_3`; the stated Klein quartic has automorphism group of order 168 when
  the characteristic is not three; and a general genus-three curve has no
  nonidentity automorphism.

The excluded exercises have only exercise-chain or see-also appearances
later in Chapters IV–V; none is a dependency of included running text.

## External sources and blockers

- Saint-Donat [1], §1, is Hartshorne's proof source for Clifford equality.
- Kleiman–Laksov [1] is required for the quoted gonality theorem.
- Mumford [1], Theorem 5.11, is required for coarse moduli existence.
- Deligne–Mumford [1] is required for irreducibility, quasi-projectivity, and
  dimension of `M_g`.

The latter three mathematical packages and the missing genuinely isotrivial
family are four explicit source roots for this section.

## Pinned Mathlib audit and false friends

The pinned checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). It has no exact
canonical-curve, hyperelliptic canonical-map, Clifford, trigonal,
Brill–Noether, or curve-moduli theorem. Existing project Riemann–Roch, Serre
duality, linear-system, quadric, complete-intersection, and projective
cohomology nodes are the relevant infrastructure.

`LinearAlgebra.CliffordAlgebra` is unrelated to Clifford's theorem for curve
divisors. Number-field declarations called canonical embeddings, explicit
Weierstrass models, generic `ProjectiveSpectrum`, and
`Polynomial.hilbertPoly` do not formalize canonical curves or their moduli.
No IV.5 leaf is marked as an exact Mathlib result.

## Result-to-article map

| Source result | Roadmap article |
|---|---|
| Hyperelliptic linear-series criterion | `curves/canonical-curves/canonical-embedding/hyperelliptic-linear-series-criterion.md` |
| Lemma 5.1 | `curves/canonical-curves/canonical-embedding/canonical-system-basepoint-free.md` |
| Proposition 5.2 and canonical embedding | `curves/canonical-curves/canonical-embedding/canonical-very-ample-iff-nonhyperelliptic.md` |
| Example 5.2.1 | `curves/canonical-curves/canonical-embedding/genus-three-canonical-plane-quartic.md` |
| Genus-four unique quadric | `curves/canonical-curves/canonical-embedding/genus-four-canonical-quadric.md` |
| Genus-four cubic and complete intersection | `curves/canonical-curves/canonical-embedding/genus-four-canonical-complete-intersection.md` |
| Converse and existence | `curves/canonical-curves/canonical-embedding/quadric-cubic-complete-intersection-converse.md` |
| Proposition 5.3, unique pencil | `curves/canonical-curves/canonical-embedding/hyperelliptic-pencil-unique.md` |
| Canonical factorization | `curves/canonical-curves/canonical-embedding/hyperelliptic-canonical-factorization.md` |
| Canonical divisors on a hyperelliptic curve | `curves/canonical-curves/canonical-embedding/hyperelliptic-canonical-divisors.md` |
| Lemma 5.5 | `curves/canonical-curves/clifford/linear-system-dimension-superadditive.md` |
| Clifford inequality | `curves/canonical-curves/clifford/clifford-inequality.md` |
| Clifford equality induction | `curves/canonical-curves/clifford/clifford-equality-induction.md` |
| Clifford equality classification | `curves/canonical-curves/clifford/clifford-equality-classification.md` |
| Trigonal notation | `curves/canonical-curves/gonality/trigonal-linear-series.md` |
| Kleiman–Laksov theorem | `curves/canonical-curves/gonality/kleiman-laksov-gonality-threshold.md` |
| Genus-three trigonal examples | `curves/canonical-curves/gonality/genus-three-trigonal-systems.md` |
| Genus-four trigonal examples | `curves/canonical-curves/gonality/genus-four-trigonal-rulings.md` |
| Genus-five trisecant criterion | `curves/canonical-curves/gonality/genus-five-trisecant-criterion.md` |
| Genus-five no-trisecant example | `curves/canonical-curves/gonality/genus-five-three-quadric-no-trisecant.md` |
| Genus-five tetragonal projection | `curves/canonical-curves/gonality/genus-five-tetragonal-projection.md` |
| Fine moduli definition and obstruction | `curves/canonical-curves/moduli/fine-moduli-obstruction.md` |
| Mumford coarse moduli | `curves/canonical-curves/moduli/coarse-moduli-curves.md` |
| Elliptic j-line comparison | `curves/canonical-curves/moduli/elliptic-j-line-coarse-moduli.md` |
| Deligne–Mumford theorem | `curves/canonical-curves/moduli/deligne-mumford-moduli.md` |
| Hyperelliptic locus | `curves/canonical-curves/moduli/hyperelliptic-locus-dimension.md` |
| Genus-three strata | `curves/canonical-curves/moduli/genus-three-moduli-strata.md` |
| Exercise 5.2 | `curves/canonical-curves/moduli/curve-automorphism-group-finite.md` |
