# Hartshorne III.9, flat morphisms and families

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Chapter III, §9. The running text occupies printed pp.253–266 (zero-based PDF
indices 267–280), and the exercises continue through printed p.268 (PDF
indices 280–282). This roadmap adopts the running mathematics and only the
later-used part of Exercise 9.10 described below.

The section uses three notions that must remain distinct in Lean:

- an algebraic module being flat over a ring;
- an `O_X`-module being flat over a base scheme at each stalk; and
- a scheme morphism being flat because its structure sheaf is flat over the
  target.

Likewise, `X_y` always denotes the scheme-theoretic fibre. Hartshorne's
`X^(t)` in the definition of an algebraic family is instead the reduced
variety underlying a fibre subject to a multiplicity-one condition.

## Flat modules and flat morphisms, pp.253–255

Proposition 9.1A gives the finitely-generated-ideal criterion for flatness,
base change, transitivity, locality on prime localizations, the two short
exact sequence closure rules, and finite-flat freeness over a Noetherian
local ring. Examples 9.1.1–3 specialize this to localization, Noetherian adic
completion, and torsion-free modules over a PID.

The definition on p.254 says that an `O_X`-module `F` is flat over `Y` at
`x` when `F_x` is flat over `O_{Y,f(x)}`. Proposition 9.2 proves the open
immersion, base-change, transitivity, affine-module, and coherent locally-free
criteria. Mathlib already defines flat scheme morphisms, but has no matching
definition for an arbitrary module sheaf flat over a base.

## Cohomology and flat base change, pp.255–256

Proposition 9.3 constructs natural isomorphisms

`u^* R^i f_* F ≅ R^i g_* v^* F`

for a separated finite-type morphism of Noetherian schemes and a flat base
change `u`. Remark 9.3.1 records the natural comparison map without flatness.
Corollary 9.4 identifies fibre cohomology with cohomology after tensoring by
the residue field. When `Y=Spec A`, the notation `F tensor k(y)` is implemented
by associating the `A`-module `k(y)` to a quasicoherent module on `Y`, pulling
it back to `X`, and tensoring with `F`; it is not an unrelated constant sheaf.

## Dimensions, associated points, and flat limits, pp.256–261

Proposition 9.5 is the local dimension formula

`dim_x X_y = dim_x X - dim_y Y`.

Corollary 9.6 compares equidimensionality of the total space with pure
dimension of every fibre. Proposition 9.7 characterizes flatness over a
regular integral curve by requiring every associated point of `X` to map to
the generic point. Its proof uses the Noetherian theorem that every zero
divisor lies in an associated prime. The roadmap therefore makes `X` locally
Noetherian explicit; without that source hypothesis one must replace
associated points by weakly associated points.

Proposition 9.8 takes the scheme-theoretic closure of a flat family over a
punctured regular curve and asserts that it is the unique flat extension. The
proof's assertion that closure creates no vertical associated points needs a
separate proof.

Examples 9.7.1, 9.7.2, and 9.8.2 are retained as explanatory counterexamples,
not separate roadmap leaves. Examples 9.8.3–4 supply one formal target: the
flat projection degeneration of a twisted cubic whose special fibre has an
embedded point. Example 9.8.3 cites Hartshorne I, Exercise 3.14, projection
from a point. That exercise was previously outside the adopted fine scope; the
projection construction is therefore stated inside the degeneration leaf as
a second cited source obligation rather than used silently.

Example 9.8.5 proves that a relative effective Cartier divisor over a
nonsingular curve is flat exactly when every fibrewise intersection divisor
is defined. It uses the theorem that a two-element regular sequence may be
permuted. Hartshorne cites Matsumura, *Commutative Algebra*, Theorem 28,
p.102; pinned Mathlib explicitly lists regular-sequence permutability as
future work.

Remark 9.8.1 interprets Proposition 9.8 as the key valuative step in
properness of connected components of the Hilbert scheme. Hilbert-scheme
existence and representability are not adopted here, so this remark is
recorded as deferred rather than promoted to a theorem leaf.

## Hilbert polynomials and projective families, pp.261–263

Theorem 9.9 first proves the coherent-sheaf statement on relative projective
space over a local Noetherian domain. For coherent `F`, the following are
equivalent:

1. `F` is flat over the base;
2. `H^0(P^n_A,F(m))` is finite free for every sufficiently large `m`;
3. the Hilbert polynomial of every fibre is independent of the point.

The closed-subscheme theorem follows by applying this to the structure sheaf.
Its proof uses the standard affine Cech complex, Serre vanishing, eventual
exactness of twisted global sections, and the finite-module freeness criterion
from II.8.9. The existing coherent-sheaf Hilbert-polynomial roadmap leaf is
not ready, so every leaf whose statement needs that object is also not ready.

Corollary 9.10 applies dimension, degree, and arithmetic-genus formulas to
scheme-theoretic fibres, which may be nonreduced. The existing Chapter I
degree leaf covers projective algebraic sets, not arbitrary closed subschemes.
The roadmap therefore inserts an explicit not-ready bridge from the coherent
fibre Hilbert polynomial to these three scheme-theoretic invariants.

Corollary 9.10 makes fibre dimension, degree, and arithmetic genus constant in
a flat projective family over a connected Noetherian base. The `r` in the
leading-coefficient formula is the common fibre dimension.

## Normal families and Hironaka's lemma, pp.263–265

Hartshorne defines an algebraic family of varieties using irreducible reduced
fibres of the expected dimension and a multiplicity-one condition at the
generic point. Theorem 9.11 proves that an algebraic family of normal
varieties over a nonsingular curve is already a flat family of schemes.

Lemma 9.12 states Hironaka's local algebra lemma. For a local Noetherian domain
essentially of finite type over a field, if `tA` has one minimal associated
prime `p`, `t` generates the maximal ideal of `A_p`, and `A/p` is normal, then
`p=tA` and `A` is normal. The proof uses finite normalization and the depth-two
consequence of normality.

Corollary 9.13 asserts constancy of the Hilbert polynomial and arithmetic
genus in an algebraic family of normal projective varieties. Its reduction
asserts without proof that two closed points of the parameter variety can be
joined by the image of one nonsingular curve or a finite chain of such images.
That source obligation is kept visible in the corollary leaf.

## Infinitesimal deformations, pp.265–266

Example 9.13.1 defines an infinitesimal deformation over the dual numbers as
a flat `D`-scheme together with a chosen identification of its closed fibre,
and obtains one from a tangent vector to the base of a marked flat global
family. Example 9.13.2 identifies dual-number flat deformations with
square-zero extensions. The extension category and compatibility with the
closed-fibre marking are a separate not-ready representation root. For a
nonsingular scheme, Hartshorne then claims classification by `H^1(X,T_X)`.
This is ordinary tangent-sheaf cohomology via III, Exercise 4.10; it is not
cotangent-complex `H1Cotangent` and must not be represented as such. The
classification remains not ready with that earlier exercise.

Remark 9.13.3 is contextual discussion of deformation theory and creates no
additional theorem target.

## Exercise disposition, pp.266–268

Exercise 9.10(b) is adopted because IV p.347 cites Exercise 9.10 for the
existence of a nontrivial family of curves all of whose fibres are isomorphic.
The printed exercise only explicitly asks for a proper flat morphism over
`A^2`, with central fibre `P^1`, which is not a product over any neighbourhood
of the origin. The roadmap records that mismatch and does not strengthen the
exercise silently; the leaf is not ready until a construction and the exact
later-used consequence are specified.

Exercises 9.1–9.9 and 9.10(a),(c) have no later running-text citation and are
outside the adopted scope. Exercise 9.11, on the plane-projection genus bound
for a nonsingular projective curve, continues onto printed p.268 and is also
explicitly **OUT**: no later running-text dependency was found.

## Pinned Mathlib audit

The audited checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). Exact stable
primitives used as whole roadmap results are:

- `Module.Flat.iff_lift_lsmul_comp_subtype_injective` in
  `Mathlib/RingTheory/Flat/Tensor.lean`;
- `Module.Flat.trans` and `Module.Flat.baseChange` in
  `Mathlib/RingTheory/Flat/Stability.lean`;
- `IsLocalization.flat` in `Mathlib/RingTheory/Flat/Localization.lean`;
- `AdicCompletion.flat_of_isNoetherian` in
  `Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean`;
- `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout` in
  `Mathlib/RingTheory/Flat/TorsionFree.lean`;
- `AlgebraicGeometry.Flat.iff_flat_stalkMap`,
  `AlgebraicGeometry.Flat.isStableUnderBaseChange`, and
  `AlgebraicGeometry.Flat.comp` in
  `Mathlib/AlgebraicGeometry/Morphisms/Flat.lean`.

The open-immersion flatness fact is an anonymous/generated typeclass instance,
so it is useful prior art but is not marked `mathlib: true` here. Likewise,
source-shaped iff or multi-clause wrappers are project leaves even when their
two directions are already easy consequences of stable upstream declarations.

Mathlib's `Polynomial.hilbertPoly` only treats the coefficient polynomial of
`p/(1-X)^d` in characteristic zero. It is not a Hilbert polynomial for a
graded module, coherent sheaf, or projective fibre. No exact pinned result was
found for higher-direct-image flat base change, scheme associated points, the
flat fibre-dimension formula, Theorem 9.9, Hironaka's lemma, or deformation
classification.
