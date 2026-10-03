# Hartshorne V.4, the cubic surface in projective three-space

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Chapter V, §4. The running text occupies printed pp.395–406. Exercises
4.1–4.12 begin on pp.406–408, and Exercises 4.13–4.16 finish on p.409
immediately before §5.

The section constructs anticanonically embedded Del Pezzo surfaces by blowing
up points of the plane, specializes to a smooth cubic surface, determines its
27 lines and their symmetry, and computes its ample cone.

## Assigned and unassigned basepoints, printed pp.395–396

For a complete surface linear system `|D|` and assigned points, including
infinitely near points and assigned multiplicities, Hartshorne identifies its
members with the complete system on the blown-up surface whose divisor class
is the pullback of `D` minus the corresponding exceptional classes. Remaining
basepoints on that model are called unassigned basepoints.

Very ampleness is reformulated as absence of unassigned basepoints before and
after assigning one further ordinary or infinitely near point. Equivalently,
for every pair `P,Q`, including `Q` infinitely near `P`,

`dim|D-P-Q|=dim|D|-2`.

This language must retain proximity multiplicities: an ordinary point is
assigned with multiplicity at least the sum of the assigned multiplicities
infinitely near it.

## Conics and the quadratic transformation, printed pp.396–398

Proposition 4.1 proves that conics through at most four assigned points, no
three collinear, have no unassigned basepoints; one point may be infinitely
near another. Corollary 4.2 computes the dimension and uniqueness of the conic
through five points, including the corresponding tangent-direction variants.

One assigned point gives the cubic-scroll embedding of the one-point blowup.
Three assigned coordinate points give the quadratic plane transformation

`(x_0:x_1:x_2) |-> (x_1*x_2:x_0*x_2:x_0*x_1)`.

Its graph is the common blowup of the three coordinate points in the source
and target planes. It blows down the three joining lines and exchanges them
with the exceptional curves.

## Cubic systems and the six-point construction, printed pp.399–401

Proposition 4.3 proves that cubics through at most seven assigned points have
no unassigned basepoints when no four are collinear and no seven lie on a
conic. The conclusion also permits one infinitely near point. Corollaries
4.4–4.5 compute the dimensions, general irreducibility, and the unique ninth
basepoint of a pencil through eight points.

Theorem 4.6 strengthens the hypotheses to no three collinear and no six on a
conic and proves that the cubic system through at most six ordinary points is
very ample on the blowup. Corollary 4.7 embeds the `r`-point blowup into
`P^(9-r)` as a degree-`9-r` surface with

`omega_X ~= O_X(-1)`.

Hartshorne calls such an embedded surface a Del Pezzo surface. He quotes the
classification that every Del Pezzo surface is obtained from this construction
or is the quadratic Veronese embedding of a smooth quadric. In particular,
every smooth cubic surface is the blowup of six suitably positioned plane
points. This requires the cited Manin/Nagata source.

Remark 4.7.2 argues by a parameter count that almost every cubic surface
arises from the construction. The count by itself does not establish
dominance or the required fibre dimension; the statement is isolated as a
source blocker.

## The marked cubic surface and its divisor lattice, printed pp.401–402

Fix six plane points with no three collinear and not all six on a conic, and
write `l` for the pulled-back line and `e_i` for the six exceptional classes.
Proposition 4.8 gives

`Pic X ~= Z*l direct-sum direct-sum_i Z*e_i`,

with `l^2=1`, `e_i^2=-1`, and all other basis intersections zero. The
hyperplane class is `h=3l-sum e_i` and `K=-h`. For
`D~a*l-sum b_i*e_i`,

`deg D=3a-sum b_i`, `D^2=a^2-sum b_i^2`,

and

`p_a(D)=(D^2-deg D)/2+1`.

An irreducible nonexceptional curve is the strict transform of a plane curve
of degree `a` with multiplicity `b_i` at the six points.

## The 27 lines, printed pp.402–405

Theorem 4.9 lists the 27 lines:

- the six exceptional curves `E_i`;
- the fifteen strict transforms `F_ij` of lines through pairs of basepoints;
- the six strict transforms `G_i` of conics through the five points other than
  `P_i`.

They have square minus one and are exactly the irreducible curves of negative
self-intersection. Exhaustivity follows from the degree and square equations,
Cauchy–Schwarz, and the resulting bound `a<3`.

Remark 4.9.1 describes Schläfli's double-six and quotes the external theorem
that five suitable lines meeting a sixth uniquely complete a double-six,
which lies on a unique smooth cubic surface.

Proposition 4.10 proves that any ordered six mutually skew lines can serve as
the exceptional sextuple of another plane blowdown. The proof uses relabeling
and quadratic transformations, checks that the transformed six points remain
in the required general position, and iterates.

The incidence configuration then has a unique labeling after choosing an
ordered skew sextuple. Counting such sextuples gives automorphism-group order

`27*16*10*6*2=51840`.

Hartshorne states that this group is the Weyl group `E6` and has a simple
normal subgroup of index two. Exercise 4.11(b,c) supplies the Coxeter
presentation and order comparison; the simple-subgroup assertion still needs
the external Manin source.

## The ample cone, printed pp.405–406

Theorem 4.11 proves, for a divisor `D` on the cubic surface, equivalence of:

1. `D` is very ample;
2. `D` is ample;
3. `D^2>0` and `D.L>0` for every line;
4. `D.L>0` for every line.

Lemma 4.12 builds a standard basis of basepoint-free divisor classes and an
anticanonical very ample class. Proposition 4.10 lets one greedily choose a
skew sextuple ordered by its intersections with `D`; the resulting numerical
inequalities put `D` in the positive cone generated by those standard classes.

Corollary 4.13 translates the ample cone into the inequalities
`b_i>0`, `a>b_i+b_j`, and `2a>sum_(i!=j)b_i`, and Bertini gives smooth
irreducible members. Example 4.13.1 constructs a degree-seven genus-five
space curve.

## Exercise disposition, printed pp.406–409

- **Exercises 4.1–4.10 — OUT.** They develop further quadratic-transform,
  Pascal, genus-bound, and effective-cone consequences but are not inputs to
  later included running proofs. Exercise 4.14 is likewise only “further
  information” for the earlier IV.6 table.
- **Exercise 4.11(b,c) — ADOPTED; (a) OUT.** Running Remark 4.10.1 uses the
  type-`E6` Coxeter presentation and order comparison to identify the
  27-line configuration group. The type-`A_n` warmup in (a) is not needed.
- **Exercise 4.15(b,c,e) — ADOPTED; (a,d) OUT.** Preservation of general
  position, dense extension over an uncountable field, and the infinite
  `(-1)`-curve construction supply the example cited in running Remark V.5.8.1.
  The six-, seven-, and eight-point classifications in (a,d) are not needed.
- **Exercise 4.16 — OUT.** The explicit Fermat-cubic lines and automorphisms
  have no later running dependency.

No other V.4 exercise clause is adopted.

## Later-use and field warning

Remark V.5.8.1 states that blowing up at least nine general plane points can
give infinitely many exceptional curves. The adopted construction is
source-supported over an uncountable algebraically closed field: part (c)
uses that such a variety is not a countable union of proper closed subsets.
For more than nine points, choose each additional point outside the countable
union of the existing exceptional curves as well as all general-position bad
loci; their strict transforms retain square minus one. The roadmap does not
silently extend this proof to an arbitrary countable algebraically closed
field.

## External sources and blockers

- Manin [3], §24, or Nagata [5], I, Theorem 8, is required for the full Del
  Pezzo classification and the assertion that every smooth cubic is a
  six-point plane blowup.
- Hilbert–Cohn-Vossen [1], §25, is required for Schläfli double-six completion
  and unique cubic containment.
- Manin [3], §§25–26, is required for the simple index-two subgroup of the
  `E6` configuration group beyond the adopted Coxeter/order exercise.
- Remark 4.7.2's dominance claim needs a genuine family morphism and fibre-
  dimension argument; the printed parameter subtraction alone is not a proof.

These are four explicit source or representation blockers.

## Pinned Mathlib audit and false friends

The pinned checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). No V.4 leaf is an
exact pinned-Mathlib result.

Mathlib has general root-system and Weyl-group infrastructure, including
`RootPairing.WeylGroup`, but no type-`E6` Coxeter presentation, order `51840`,
27-line configuration action, or simple index-two subgroup. It has no cubic
surface, Del Pezzo surface, 27-line theorem, assigned-basepoint cluster, or
quadratic-plane-transformation geometry. These abstract APIs are
infrastructure, not whole-leaf matches.

## Representation choices and warnings

- Represent assigned ordinary and infinitely near basepoints as clusters with
  proximity multiplicities; a list of independent points loses essential
  conditions.
- Identify the strict-transform system on the blowup with the appropriate
  pullback-minus-exceptional divisor class.
- Hartshorne's Del Pezzo is an embedded degree-`d` surface in `P^d` with
  `omega_X=O_X(-1)`. Keep this distinct from the modern abstract definition
  that `-K_X` is ample until the anticanonical embedding is constructed.
- Distinguish automorphisms of the abstract 27-line incidence configuration
  from automorphisms of an individual cubic surface.
- Do not formalize “almost all cubics” from a bare dimension count.
- Retain the uncountable-field hypothesis in the infinite-exceptional-curve
  construction.

## Result-to-article map

| Source result | Roadmap article |
|---|---|
| Assigned/unassigned basepoint interface | `surfaces/cubic-surfaces/assigned-systems/assigned-unassigned-basepoint-api.md` |
| Linear systems on blowups | `surfaces/cubic-surfaces/assigned-systems/blowup-linear-system-correspondence.md` |
| Very ampleness via unassigned basepoints | `surfaces/cubic-surfaces/assigned-systems/very-ample-unassigned-basepoint-criterion.md` |
| Proposition 4.1 and Corollary 4.2 | `surfaces/cubic-surfaces/assigned-systems/conic-assigned-points-system.md` |
| Example 4.2.3, quadratic transformation | `surfaces/cubic-surfaces/assigned-systems/quadratic-transformation-conic-morphism.md` |
| Common blowup for the quadratic transformation | `surfaces/cubic-surfaces/assigned-systems/quadratic-transformation-common-blowup.md` |
| Proposition 4.3 | `surfaces/cubic-surfaces/assigned-systems/cubic-system-no-unassigned-basepoints.md` |
| Corollaries 4.4–4.5 | `surfaces/cubic-surfaces/assigned-systems/cubic-pencil-dimension-irreducibility-ninth-point.md` |
| Theorem 4.6 | `surfaces/cubic-surfaces/assigned-systems/general-cubic-system-very-ample.md` |
| Corollary 4.7 | `surfaces/cubic-surfaces/construction/anticanonical-point-blowup-embedding.md` |
| Embedded Del Pezzo definition and examples | `surfaces/cubic-surfaces/construction/embedded-del-pezzo-definition-examples.md` |
| Del Pezzo classification | `surfaces/cubic-surfaces/construction/embedded-del-pezzo-classification.md` |
| Generic cubic dominance claim | `surfaces/cubic-surfaces/construction/generic-cubic-construction-dominance.md` |
| Marked six-point cubic convention | `surfaces/cubic-surfaces/construction/cubic-marked-blowup-convention.md` |
| Cubic Picard group | `surfaces/cubic-surfaces/construction/cubic-surface-picard-group.md` |
| Cubic intersection lattice | `surfaces/cubic-surfaces/construction/cubic-surface-intersection-lattice.md` |
| Hyperplane and canonical classes | `surfaces/cubic-surfaces/construction/cubic-surface-hyperplane-canonical-classes.md` |
| Degree, square, and genus formulas | `surfaces/cubic-surfaces/construction/cubic-divisor-degree-square-genus.md` |
| Plane strict-transform dictionary | `surfaces/cubic-surfaces/construction/cubic-plane-strict-transform-dictionary.md` |
| The 27 candidate lines | `surfaces/cubic-surfaces/lines/twenty-seven-line-candidates.md` |
| Candidate self-intersections | `surfaces/cubic-surfaces/lines/cubic-lines-self-intersection.md` |
| Negative curves are lines | `surfaces/cubic-surfaces/lines/cubic-negative-curves-are-lines.md` |
| Exhaustivity of the 27 lines | `surfaces/cubic-surfaces/lines/twenty-seven-lines-exhaustive.md` |
| Schläfli double-six incidence | `surfaces/cubic-surfaces/lines/schlafli-double-six-incidence.md` |
| Double-six completion and unique cubic | `surfaces/cubic-surfaces/lines/schlafli-double-six-completion.md` |
| Moving a line to an exceptional position | `surfaces/cubic-surfaces/lines/line-to-exceptional-cremona.md` |
| General position after a Cremona step | `surfaces/cubic-surfaces/lines/cremona-transformed-six-points-general.md` |
| Proposition 4.10 | `surfaces/cubic-surfaces/lines/six-skew-lines-blowdown.md` |
| Incidence configuration | `surfaces/cubic-surfaces/lines/twenty-seven-lines-incidence-configuration.md` |
| Unique labeling from an ordered skew sextuple | `surfaces/cubic-surfaces/lines/ordered-skew-sextuple-unique-labeling.md` |
| Configuration automorphism transitivity | `surfaces/cubic-surfaces/lines/line-configuration-automorphism-transitivity.md` |
| Configuration automorphism order | `surfaces/cubic-surfaces/lines/line-configuration-automorphism-order.md` |
| Weyl `E6` identification and simple subgroup | `surfaces/cubic-surfaces/configuration-consequences/line-configuration-weyl-e6.md` |
| Standard basepoint-free basis | `surfaces/cubic-surfaces/ample-cone/cubic-standard-basepointfree-basis.md` |
| Lemma 4.12 | `surfaces/cubic-surfaces/ample-cone/cubic-numerical-very-ampleness-lemma.md` |
| Greedy skew sextuple | `surfaces/cubic-surfaces/ample-cone/cubic-greedy-skew-sextuple.md` |
| Theorem 4.11 | `surfaces/cubic-surfaces/ample-cone/cubic-line-positivity-ampleness-equivalence.md` |
| Corollary 4.13 | `surfaces/cubic-surfaces/ample-cone/cubic-ample-cone-smooth-members.md` |
| Example 4.13.1 | `surfaces/cubic-surfaces/ample-cone/cubic-degree-seven-genus-five.md` |
| Exercise 4.11(b,c) | `surfaces/cubic-surfaces/exercises/e6-line-configuration-group.md` |
| Exercise 4.15(b,c) | `surfaces/cubic-surfaces/exercises/general-position-dense-extension.md` |
| Exercise 4.15(e) and V.5 consequence | `surfaces/cubic-surfaces/exercises/infinitely-many-exceptional-curves-general-blowups.md` |

## Reused prerequisite map

| Source result | Existing roadmap article |
|---|---|
| Example 4.2.2, cubic scroll from conics through one point | `schemes/projective-geometry/blowups/blowup-plane-conic-system-embedding.md` |
