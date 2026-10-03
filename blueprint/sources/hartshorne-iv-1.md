# Hartshorne IV.1, the Riemann–Roch theorem

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Chapter IV, §1, printed pp.294–298. Printed p.299 begins Exercise 1.10 and §2;
Exercise 1.10 is outside this source unit. The roadmap adopts every running
claim, together with Exercises 1.5, 1.7, and 1.8 because later included text
uses them.

Throughout, `k` is algebraically closed. A *curve* means an integral proper
regular one-dimensional `k`-scheme. A *point* means a closed point, so its
residue field is `k`; this is why divisor degrees are unweighted sums and why
the skyscraper sheaf at one point has Euler characteristic one. Formalization
must not silently generalize these formulas to a non-algebraically-closed
field without inserting residue degrees.

## Curves and genus, printed p.294

Hartshorne recalls that a complete nonsingular curve is equivalently an
integral scheme of dimension one, proper over `k`, with regular local rings.
It is projective by II.6.7. More general one-dimensional schemes are not
included in the unqualified word “curve.”

Proposition 1.1 identifies the three genus invariants

`p_a(X) = dim_k H^1(X,O_X) = dim_k H^0(X,omega_X) = p_g(X)`.

The arithmetic-genus equality is III Exercise 5.3; the geometric-genus
equality is Serre duality, III.7.12.2. The existing Chapter III roadmap leaf
already states this theorem and should be reused rather than duplicated. The
Chapter IV notation `g(X)` is defined to be their common nonnegative value.

Remark 1.1.1 states that every `g >= 0` occurs: take a nonsingular irreducible
divisor of type `(g+1,2)` on a nonsingular quadric surface. The existing
quadric arithmetic-genus and smooth-existence leaves already decompose III
Exercise 5.6, so this remark also requires no duplicate article.

## Divisors, sections, and the degree lemma, printed pp.294–295

A divisor on a curve is a finite integer combination of closed points. Its
degree is the sum of coefficients; principal divisors have degree zero, so
degree descends to the divisor class group. Regularity identifies Weil and
Cartier divisors, and `D |-> O_X(D)` identifies `Cl(X)` with `Pic(X)`.

The complete linear system `|D|` is the set of effective divisors linearly
equivalent to `D`, identified with the closed points of

`(H^0(X,O_X(D)) - {0}) / k^*`.

Write `l(D)=dim_k H^0(X,O_X(D))`. Use an integer-valued projective dimension
for `|D|`: it is `l(D)-1`, including the value `-1` when `l(D)=0`. Natural
subtraction must not turn the empty system into dimension zero.

Lemma 1.2 says that `l(D)>0` implies `deg D>=0`. If also `deg D=0`, then
`D~0` and `O_X(D)~=O_X`. Its proof chooses the effective representative
supplied by a nonzero section.

The divisor, degree, Picard, and linear-system constructions are reviews of
II §§6–7. The Chapter IV leaves specialize and connect their APIs rather than
introduce competing definitions.

## Canonical divisors and Riemann–Roch, printed pp.295–296

Because `X` is regular of dimension one, `Omega[X/k]` is invertible. Its
first exterior power is itself, so it is the canonical sheaf; through the
smooth-canonical/dualizing comparison it is also the sheaf used by Serre
duality. A *canonical divisor* is any divisor `K` with
`O_X(K)~=omega_X`; it is a representative, not canonical chosen data.

For every closed point `P`, regularity makes `P` an effective Cartier
divisor and gives

`0 -> O_X(-P) -> O_X -> k(P) -> 0`.

Tensoring by `O_X(D+P)` gives

`0 -> O_X(D) -> O_X(D+P) -> k(P) -> 0`.

Additivity of Euler characteristic and `chi(k(P))=1` imply

`chi(O_X(D+P)) = chi(O_X(D)) + 1`.

Induction through the free divisor group, starting from
`chi(O_X)=1-g`, proves

`chi(O_X(D)) = deg D + 1 - g`.

Serre duality identifies `H^1(X,O_X(D))` with the dual of
`H^0(X,omega_X tensor O_X(-D))`, yielding Theorem 1.3:

`l(D) - l(K-D) = deg D + 1 - g`.

Remark 1.3.1 compares this with the Hilbert-polynomial formula for an embedded
curve and a hyperplane section. Remark 1.3.8 cites Serre,
*Groupes Algébriques et Corps de Classes*, Chapter II, and Fulton,
*Algebraic Curves*, for alternative proofs. Stacks Project §53.5, tag `0B5B`,
especially Riemann–Roch Lemma 53.5.2, tag `0BS6`, is adopted supplementary
prior art. Its proper Gorenstein statement is stronger than the running source
and is not silently substituted for Hartshorne's regular-curve theorem.

## Consequences of Riemann–Roch, printed pp.296–297

Remark 1.3.2 solves the asymptotic linear-system problem:

- if `deg D<0`, then `dim|nD|=-1` for every `n>0`;
- if `deg D=0`, then `dim|nD|` is zero or `-1` according as `nD~0` or not;
- if `deg D>0`, then for all sufficiently large `n`,
  `dim|nD| = n*deg D-g`.

Example 1.3.3 applies Riemann–Roch to `K` and proves
`deg K=2g-2`. Example 1.3.4 defines the index of speciality as `l(K-D)` and
proves every divisor of degree greater than `2g-2` is nonspecial.

Example 1.3.5 proves that a curve has genus zero if and only if it is rational,
equivalently isomorphic to `P^1`. The reverse implication uses two distinct
closed points, Riemann–Roch for their difference, Lemma 1.2, and II.6.10.1.
Stacks Proposition 53.10.4, tag `0C6U`, is supplementary prior art.

Hartshorne calls a curve of genus one *elliptic* without choosing a base
point. Example 1.3.6 proves its canonical divisor is linearly trivial.
Example 1.3.7 then fixes `P_0` and proves

`X(k) -> Pic^0(X),  P |-> O_X(P-P_0)`

is a bijection, transporting the abelian-group structure to the set of closed
points. Here `Pic^0(X)` means the kernel of the divisor-degree homomorphism,
not yet the identity component of a Picard scheme. This result constructs a
group on points; it does not yet prove the group operations are morphisms.

## Exercise disposition, printed pp.297–298

Exercises 1.5, 1.7, and 1.8 are adopted.

- Exercise 1.5 proves `dim|D| <= deg D` for an effective divisor, with equality
  exactly for `D=0` or `g=0`. It is used in IV §5.
- Exercise 1.7(a) proves every genus-two curve is hyperelliptic via its
  basepoint-free canonical `g^1_2`. Exercise 1.7(b) proves that the quadric
  curves from Remark 1.1.1 are hyperelliptic in every genus. Exercise 1.7 is
  used in IV §§2, 3, and 5.
- Exercise 1.8 gives the normalization quotient, the arithmetic-genus defect
  formula, the genus-zero regularity criterion, and the value one of the local
  defect at a node or ordinary cusp. It is used repeatedly in IV §§2–3 and V
  §§3 and 5.

Exercises 1.1–1.4, 1.6, and 1.9 are **OUT** for this adopted fine scope: no
later included proof dependency requiring them was found in the audit.
Exercises 1.1–1.2 feed the exercise-only affineness chain 1.3–1.4. Exercise
1.9 is the singular/Gorenstein extension of Riemann–Roch but has no later
identified use here. Exercise 1.10 begins on printed p.299 and is outside the
source boundary.

For Exercise 1.8, let `nu : X_tilde -> X` be the normalization. There is an
exact sequence

`0 -> O_X -> nu_*O_X_tilde -> directSum_P (Otilde_P/O_P) -> 0`,

with only finitely many nonzero finite-length summands. Define
`delta_P=length(Otilde_P/O_P)`. Then

`p_a(X)=p_a(X_tilde)+sum_P delta_P`.

If `p_a(X)=0`, all defects vanish, normalization is an isomorphism, and the
regular curve is `P^1`. The node/cusp calculation `delta_P=1` is retained but
is not ready: Hartshorne's hint factors through invariance under analytic
isomorphism and the node/cusp material in I Exercises 5.6 and 5.14, none of
which has an adopted proof-level representation in the current roadmap.
Stacks §53.19, tag `0C46`, is useful nodal-curve context but does not by itself
supply the ordinary-cusp comparison.

## Pinned Mathlib audit and representation risks

The audited checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). No exact pinned
declaration was found for scheme-level curve Riemann–Roch, the genus
equalities, canonical-divisor degree, genus-zero or genus-one classification,
the `X(k) ~= Pic^0(X)` bijection, or normalization delta invariants. Mathlib's
Weierstrass elliptic-curve API is not an implementation of an abstract proper
regular curve. No new article in this subtree is an exact Mathlib leaf.

The principal representation risks are:

- bridge the scheme-level Chapter IV curve to the existing classical
  `ProjectiveNonsingularCurveCat` without identifying them definitionally;
- reuse the II.6–7 divisor and Picard APIs rather than create parallel groups;
- keep `dim|D|` integer-valued so the empty system has dimension `-1`;
- represent a canonical divisor by existence plus a chosen representative
  only where needed;
- distinguish the degree-zero subgroup from a Picard scheme;
- distinguish Hartshorne's unpointed genus-one curve from Mathlib's pointed
  Weierstrass data.

Except for the node/cusp defect calculation, the running and adopted exercise
statements have adequate proof sources. Dependencies on planned Chapter II–III
articles create ordinary DAG blockage, not additional `not_ready` roots.

## Result-to-article map

| Source claim | Roadmap article |
|---|---|
| Curve, point, and genus convention | `curves/riemann-roch/curve-convention.md` |
| Divisor sections, `l(D)`, and integer `dim|D|` | `curves/riemann-roch/curve-divisor-sections.md` |
| Lemma 1.2 | `curves/riemann-roch/nonzero-sections-nonnegative-degree.md` |
| Canonical differential and divisor | `curves/riemann-roch/curve-differentials-canonical-divisor.md` |
| Point-divisor exact sequence | `curves/riemann-roch/point-divisor-exact-sequence.md` |
| Euler-characteristic degree formula | `curves/riemann-roch/curve-euler-characteristic-degree.md` |
| Theorem 1.3 | `curves/riemann-roch/riemann-roch.md` |
| Remark 1.3.1 | `curves/riemann-roch/embedded-curve-hilbert-riemann-roch.md` |
| Remark 1.3.2 | `curves/riemann-roch/curve-linear-system-asymptotics.md` |
| Example 1.3.3 | `curves/riemann-roch/canonical-divisor-degree.md` |
| Example 1.3.4 | `curves/riemann-roch/high-degree-divisor-nonspecial.md` |
| Example 1.3.5 | `curves/riemann-roch/genus-zero-iff-projective-line.md` |
| Example 1.3.6 | `curves/riemann-roch/genus-one-canonical-trivial.md` |
| Example 1.3.7 | `curves/riemann-roch/elliptic-points-picard-zero.md` |
| Exercise 1.5 | `curves/riemann-roch/effective-divisor-linear-system-dimension-bound.md` |
| Exercise 1.7(a) | `curves/riemann-roch/genus-two-canonical-hyperelliptic.md` |
| Exercise 1.7(b) | `curves/riemann-roch/hyperelliptic-curves-all-genera.md` |
| Exercise 1.8 sequence and defects | `curves/riemann-roch/normalization-delta-quotient.md` |
| Exercise 1.8(a) | `curves/riemann-roch/arithmetic-genus-normalization-formula.md` |
| Exercise 1.8(b) | `curves/riemann-roch/arithmetic-genus-zero-nonsingular-rational.md` |
| Exercise 1.8(c) | `curves/riemann-roch/node-cusp-delta-one.md` |

Proposition 1.1 reuses the existing Chapter III genus-equality article;
Remark 1.1.1 reuses the existing quadric arithmetic-genus and smooth-existence
articles.
