# Hartshorne IV.2, Hurwitz's theorem

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Chapter IV, §2, printed pp.299–306. The running text occupies pp.299–303;
the exercises begin on p.304 and continue through p.306.

Chapter IV uses a fixed algebraically closed field `k`. A curve is an
integral, proper, regular one-dimensional `k`-scheme, hence projective. A
point means a closed point. These conventions are essential below: residue
fields at points are `k`, and the purely inseparable genus statement is not
valid over an arbitrary imperfect field.

## Finite maps, ramification, and the different, pp.299–301

For a finite morphism `f : X -> Y` of curves, Hartshorne defines

`deg f = [K(X) : K(Y)]`.

For `P : X`, `Q=f(P)`, and a uniformizer `t` at `Q`, the ramification index is

`e_P = v_P(f^#t)`.

It is independent of the uniformizer. The point is ramified when `e_P>1`,
unramified when `e_P=1`, and `Q` is then a branch point. Since the residue
fields are both `k`, this agrees with the pointwise unramified condition from
III Exercise 10.3. A finite curve map is flat by III.9.7, so an everywhere
unramified map is étale. In characteristic zero all ramification is tame. In
characteristic `p>0`, it is tame when `p` does not divide `e_P` and wild when
`p` divides `e_P`.

The divisor pullback recalled from II.6 is

`f^*Q = sum_(P maps to Q) e_P P`.

It is compatible with pullback of invertible sheaves and multiplies divisor
degrees by `deg f`.

A finite curve map is separable when `K(X)/K(Y)` is separable. Proposition
2.1 gives the exact sequence

`0 -> f^* Omega_Y -> Omega_X -> Omega_(X/Y) -> 0`.

Separability is exactly what makes the first map nonzero at the generic point;
it must not be dropped.

For uniformizers `t` at `Q` and `u` at `P`, define `dt/du` by

`f^*(dt) = (dt/du) du`.

Proposition 2.2 says that `Omega_(X/Y)` is torsion, supported exactly at the
ramification points, and

`(Omega_(X/Y))_P ~= O_(X,P)/(dt/du)`.

Writing `d_P = length((Omega_(X/Y))_P)`, one has

`d_P = v_P(dt/du)`.

Only finitely many `d_P` are nonzero. If the ramification is tame,
`d_P=e_P-1`; if it is wild, `d_P>e_P-1`. The integers `d_P` are the local
different exponents. Stacks Project §53.12 identifies the corresponding
effective Cartier divisor with the divisor cut out by the different.

Hartshorne defines the ramification divisor

`R = sum_P d_P P`.

Proposition 2.3 gives, for canonical divisors,

`K_X ~ f^*K_Y + R`.

Corollary 2.4, usually called Riemann–Hurwitz, states

`2g(X)-2 = deg(f) * (2g(Y)-2) + deg R`.

If all ramification is tame, then `deg R = sum_P (e_P-1)`.

## Frobenius and purely inseparable maps, pp.301–302

For a characteristic-`p` scheme, absolute Frobenius is the identity on the
topological space and the `p`th-power map on the structure sheaf. If
`X -> Spec k` is a `k`-scheme, Hartshorne writes `X^p` for the same abstract
scheme with its structural map twisted by Frobenius on `k`; absolute
Frobenius becomes a `k`-linear map

`X^p -> X`.

This is Hartshorne's orientation. It must not silently be reversed to match a
different modern convention for relative Frobenius.

For a curve over algebraically closed characteristic `p`, this `k`-linear
Frobenius is finite of degree `p` and corresponds to `K -> K^(1/p)`.

Proposition 2.5 says that if a finite curve map `f : X -> Y` induces a purely
inseparable extension of degree `p^r`, then, after identifying `X` with the
appropriate Frobenius twist of `Y`, `f` is the composite of `r` `k`-linear
Frobenius maps. Thus `X` and `Y` are isomorphic as abstract schemes and
`g(X)=g(Y)`. Algebraic closedness, hence perfection, is essential. Stacks
§53.13 gives counterexamples to genus invariance over imperfect fields.

For one Frobenius step, every point has ramification index `p`, the map on
absolute differentials is zero, and `Omega_(X/Y) ~= Omega_X`. This is an
inseparable example: the relative differential sheaf is not torsion and the
ramification divisor defined above is unavailable.

## Consequences, pp.302–303

- For a finite separable map, `deg R` is even.
- A finite étale covering is trivial when it is a finite disjoint union of
  copies of the base. A scheme is simply connected when it has no nontrivial
  finite étale covering. Riemann–Hurwitz proves `P^1` is simply connected.
- Every finite map of curves satisfies `g(X) >= g(Y)`. The proof factors its
  function-field extension into a purely inseparable part, which preserves
  genus, followed by a separable part, where Riemann–Hurwitz applies. For a
  separable map with `g(Y) >= 1`, equality occurs only for degree one, or for
  an unramified map to a genus-one curve. Higher-degree self-maps of `P^1`
  show why the positive-genus restriction is necessary.
- Lüroth's theorem over algebraically closed `k` follows: every nonconstant
  intermediate field `k subset L subset k(t)` is `k`-isomorphic to a rational
  function field. Mathlib proves the stronger statement over every field.

## Exercise disposition, pp.304–306

- **Exercise 2.1 — OUT.** Simple connectedness of projective space has no
  later numbered use located.
- **Exercise 2.2 — ADOPTED.** The characteristic-not-two classification
  of genus-two curves by six branch points is reused in the §5 moduli
  discussion. It should split into the canonical double cover, the converse
  equation, `PGL_2` normalization, and the `S_6` quotient.
- **Exercise 2.3 — PARTIALLY ADOPTED.** Parts (a), (e), and only the nine-flex
  conclusion of (g) are used in running Example IV.4.8.3. Parts (b)–(d), (f),
  the collinearity add-on in (g), and (h) remain out of scope.
- **Exercises 2.4–2.5 — OUT.** Their later references occur only in excluded
  exercise or see-also chains, not in included running text.
- **Exercise 2.6 — PARTIALLY ADOPTED.** Parts (a)–(b), divisor pushforward and
  preservation of linear equivalence, are used in running Lemma IV.4.9 on
  p.322.
  Parts (c)–(d) are out; the excluded Exercise 2.7 is their only identified
  consumer.
- **Exercise 2.7 — OUT.** The classification of étale double
  covers by `Pic(Y)[2]` has no later running-text citation located.

No exercise leaves are created in the IV.2 running-text chapter.

## External proof sources

- Stacks Project §53.12, tag `0C1B`, covers Riemann–Hurwitz. Exact useful
  tags are `0C1C` (generically étale), `0C1D` (the formula), `0C1E`
  (uniformizer differentials), and `0C1F` (different exponents and tame
  ramification).
- Stacks Project §53.13, tag `0CCV`, treats inseparable maps. Tag `0CCZ`
  identifies purely inseparable maps of proper smooth curves with iterated
  relative Frobenius over the appropriate hypotheses; tag `0CD2` gives the
  separable–inseparable factorization of an arbitrary curve map.
- Mathlib's pinned ramification-index development is authored by Thomas Browning;
  `RingTheory/DedekindDomain/Different.lean`, authored by Andrew Yang,
  supplies the different ideal and its unramified criterion. These are local
  algebra prior art, not scheme-level IV.2 results.

## Pinned Mathlib audit and representation boundary

The audited checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). Useful primitives
include `Ideal.ramificationIdx`, `Ideal.sum_ramification_inertia`,
`IsDedekindDomain.differentIdeal`, and `not_dvd_differentIdeal_iff`, together
with Kähler-differential and étale APIs. No exact declaration was found for a
curve ramification divisor, Riemann–Hurwitz, or scheme Frobenius.

The local-to-scheme bridges still required are: identifying the valuation
definition of `e_P` with Mathlib's ideal ramification index; gluing local
different exponents to the Fitting/different divisor; constructing absolute
Frobenius and Hartshorne's twist orientation; and transporting purely
inseparable field factorizations through the curve/function-field
equivalence. These are implementation roots, not reasons to assert that a
source theorem is false or mathematically unresolved.

The sole exact upstream running result is Lüroth's theorem:
`RatFunc.Luroth.algEquiv` in
`Mathlib/FieldTheory/RatFunc/Luroth.lean`.

## Result-to-article map

| Source claim | Roadmap article |
|---|---|
| Finite-map degree and flatness | `curves/ramification/finite-curve-morphism-flat-degree.md` |
| Ramification index | `curves/ramification/ramification-index-bridge.md` |
| Proposition 2.1 | `curves/ramification/separable-differential-exact-sequence.md` |
| `dt/du` | `curves/ramification/local-differential-ratio.md` |
| Proposition 2.2(a) | `curves/ramification/finite-ramification-support.md` |
| Proposition 2.2(b) | `curves/ramification/relative-differential-stalk-length.md` |
| Proposition 2.2(c) | `curves/ramification/tame-wild-different-exponent.md` |
| Ramification divisor | `curves/ramification/ramification-divisor.md` |
| Proposition 2.3 | `curves/ramification/canonical-divisor-ramification-formula.md` |
| Corollary 2.4 | `curves/ramification/riemann-hurwitz.md` |
| Frobenius definitions | `curves/ramification/scheme-frobenius-twist.md` |
| Example 2.4.3 | `curves/ramification/curve-frobenius-finite-degree.md` |
| Proposition 2.5 factorization | `curves/ramification/purely-inseparable-frobenius-factorization.md` |
| Proposition 2.5 genus conclusion | `curves/ramification/purely-inseparable-genus-invariance.md` |
| Example 2.5.1 | `curves/ramification/frobenius-everywhere-ramified.md` |
| Example 2.5.2 | `curves/ramification/ramification-degree-even.md` |
| Example 2.5.3 | `curves/ramification/projective-line-etale-simply-connected.md` |
| Example 2.5.4 | `curves/ramification/finite-curve-map-genus-monotonicity.md` |
| Example 2.5.5 | `curves/ramification/luroth-theorem.md` |
