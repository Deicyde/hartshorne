# Hartshorne III.7, Serre duality

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Chapter III, §7. The printed section boundary is pp.239–250 (zero-based PDF
indices 253–264): the running text begins on p.239 and ends on p.249, the
exercises continue through p.250, and §8 begins later on p.250. Page
references below are printed pages. The adopted scope is the running text
through p.249 together with Exercise 7.4(a),(c),(d), now required by V.1.8(a).

## Scope and exercise dispositions

The roadmap adopts every running definition, theorem, corollary, and
mathematically substantive remark through Remark 7.15. Exercise 7.1 is out:
it is not cited later in the book. Exercise 7.2 is excluded under the strict
exercise policy even though IV, Exercise 2.6(c), cites it, because its finite
duality chain is conditional on the separately unadopted Exercise 6.10.
Exercise 7.3 and Exercise 7.4(b) remain out. Exercise 7.4(a),(c),(d) are
adopted for V Exercise 1.8(a): the `dlog` Picard class and the point-trace /
codimension-one divisor-class comparison. Those parts do not require the
excluded Exercise 7.3.

## Duality on projective space, pp.239–241

For `X=Pⁿ_k`, Theorem 7.1 identifies the canonical sheaf with
`O_X(-n-1)`, chooses a trace isomorphism `Hⁿ(X,ω_X)≅k`, proves that

`Hom_X(F,ω_X) × Hⁿ(X,F) ⟶ k`

is perfect for every coherent `F`, and extends this to functorial isomorphisms
`Extⁱ_X(F,ω_X)≅H^(n-i)(X,F)ᵛ`. The proof uses III.5.1 for twists,
II.5.18 for finite twisted-free presentations, and III.1.3A for the universal
delta-functor argument.

The existence of the chosen trace is immediate from III.5.1(c). It does not
require the intrinsic normalization of Remark 7.1.1. That remark separately
gives the intrinsic trace generator as the class of the standard Čech cocycle

`(x₁⋯xₙ)⁻¹ d(x₁/x₀)∧⋯∧d(xₙ/x₀)`.

Hartshorne says only that one can show this generator is invariant under a
change of homogeneous coordinates. The roadmap therefore separates the ready
trace-choice theorem from a not-ready coordinate-invariant-normalization
node.

## Dualizing sheaves and projective existence, pp.241–242

A dualizing sheaf on a proper `n`-dimensional scheme over `k` is a coherent
module `ω°_X` with a trace `Hⁿ(X,ω°_X)→k` whose induced pairing
represents the dual of top cohomology on coherent modules. Proposition 7.2
proves uniqueness with its trace by uniqueness of representing objects.

For a closed immersion `X⊂Pᴺ` of codimension `r`, Lemma 7.3 proves
`𝓔xtⁱ_P(O_X,ω_P)=0` for `i<r`. It combines eventual global
generation, the eventual global/sheaf Ext comparison of III.6.9,
projective-space duality, and cohomological-dimension vanishing. Lemma 7.4
then identifies

`Hom_X(G,𝓔xtʳ_P(O_X,ω_P)) ≅ Extʳ_P(G,ω_P)`.

Proposition 7.5 defines `ω°_X=𝓔xtʳ_P(O_X,ω_P)` and obtains its trace
from the identity. This construction is independent of the embedding by
Proposition 7.2, once the trace is included.

Stacks Project, Lemma 48.27.1, tag
[0FVV](https://stacks.math.columbia.edu/tag/0FVV), is the adopted modern
existence and representability source. Section 48.15, tag
[0BQV](https://stacks.math.columbia.edu/tag/0BQV), supplies the ambient
projective-space and closed-immersion derived calculations. These modern
references supplement rather than replace Hartshorne's classical construction.

## Cohen–Macaulay duality, pp.243–244

Let `X` be an arbitrary projective scheme of dimension `n` over an
algebraically closed field `k`, equipped with a dualizing sheaf and a fixed
very ample `O_X(1)`. These are the common hypotheses of Theorem 7.6; neither
Cohen–Macaulayness nor equidimensionality is a common hypothesis. The theorem
first constructs natural maps

`θᵢ : Extⁱ_X(F,ω°_X) ⟶ H^(n-i)(X,F)ᵛ`.

To avoid an informal negative cohomological degree, the project-authored Lean
specification uses `HBelow n i F`, equal to `H^(n-i)(X,F)` when `i≤n` and
the zero `k`-module otherwise.

Theorem 7.6(b) proves equivalence of:

1. `X` is Cohen–Macaulay and equidimensional of dimension `n`;
2. for every finite locally free `F`, `Hⁱ(X,F(-q))=0` for `i<n` and
   sufficiently large `q`;
3. every `θᵢ` is an isomorphism for every coherent `F`.

Both Cohen–Macaulayness and equidimensionality occur together only in
condition (1). The roadmap does not put equidimensionality into conditions
(2) or (3), and does not replace condition (1) by a Gorenstein assumption.
The local algebra uses III.6.8–6.10A, III.6.12A, III, Exercise 6.6, and
II.8.21A. Corollary 7.7 specializes to finite locally free modules. Stacks tags
[0FVZ](https://stacks.math.columbia.edu/tag/0FVZ) and
[0FW0](https://stacks.math.columbia.edu/tag/0FW0) give the corresponding
Cohen–Macaulay duality and vector-bundle pairing.

## ESZ and connected ample divisors, pp.244–245

Corollary 7.8 is the Enriques–Severi–Zariski vanishing theorem: on a normal
projective scheme of dimension at least two over the algebraically closed
field in force, `H¹(X,F(-q))=0` for a finite locally free `F` and `q≫0`.
The adopted proof source is the stronger Stacks Lemma 33.48.2, tag
[0FD8](https://stacks.math.columbia.edu/tag/0FD8), specialized to this field
hypothesis and stated for a coherent sheaf whose closed stalks have depth at
least two.

Corollary 7.9 uses this vanishing and the exact sequence for the thickened
divisor `qD` to show that the support of an effective ample divisor on an
integral normal projective variety of dimension at least two is connected.
Remark 7.9.1 combines connectedness with II.8.18 to make the regular Bertini
hyperplane sections irreducible.

## Koszul calculation and the canonical sheaf, pp.245–247

Proposition 7.10A defines the homological Koszul complex and states that a
regular sequence gives a resolution of the quotient. Hartshorne cites
Matsumura, *Commutative Algebra*, Theorem 43, p.135, and Serre, *Algèbre
locale—Multiplicités*, IV.A. Stacks Sections 15.29 and 15.31, tags
[0621](https://stacks.math.columbia.edu/tag/0621) and
[062D](https://stacks.math.columbia.edu/tag/062D), are adopted detailed
sources.

The Koszul sheaf-Ext calculation is stated with a finite locally free target,
so the defining regular sequence remains regular on that target; no vanishing
claim is made for an arbitrary target module. Theorem 7.11 then calculates
the dualizing sheaf of a codimension-`r` local
complete intersection `X⊂P`:

`ω°_X ≅ ω_P|_X ⊗ (∧ʳ(I/I²))ᵛ`.

The determinant factor records exactly how the top Koszul term changes under
a new local generating regular sequence. Stacks Lemmas 48.15.5–6, tags
[0BQZ](https://stacks.math.columbia.edu/tag/0BQZ) and
[0BR0](https://stacks.math.columbia.edu/tag/0BR0), are the adopted detailed
Ext calculation.

Corollary 7.12 identifies the dualizing and canonical sheaves on a
nonsingular projective variety. Stacks Lemma 48.15.7, tag
[0BRT](https://stacks.math.columbia.edu/tag/0BRT), is the adopted modern
source. Remarks 7.12.1–3 give the dualizing trace on the canonical sheaf,
equality of arithmetic and
geometric genus for a nonsingular projective curve, and
`p_g-p_a=dim H¹(X,O_X)` for a nonsingular projective surface. Corollary 7.13
gives `H^q(X,Ωᵖ_X)≅H^(n-q)(X,Ω^(n-p)_X)ᵛ`.

## Residues on curves, pp.247–248

Theorem 7.14.1 characterizes the residue map
`res_P:Ω_(K/k)→k` at a closed point by regularity, exact-differential,
and logarithmic-derivative rules; specifically
`res_P(f⁻¹df)=v_P(f)·1_k`. With a uniformizer, a rational differential has a
finite negative Laurent principal part, and its residue is the coefficient
of `t⁻¹dt`. Theorem 7.14.2 states the global residue theorem. The residue sum
descends through the differential principal-parts resolution, whose middle
term is the constant sheaf with value `Ω_(K/k)` and whose direct sum ranges
over closed points, to a trace `H¹(X,Ω_X)→k`.

Hartshorne does not prove existence, parameter independence, the global
residue theorem, or perfectness of the repartition pairing. The adopted
sources are Serre, *Groupes algébriques et corps de classes*, Chapter II,
and Tate, “Residues of differentials on curves,” *Ann. Sci. ÉNS* (4) 1
(1968), 149–159. The roadmap separates the not-ready perfect-pairing theorem,
which says that the residue trace makes the canonical sheaf dualizing, from
the formal trace-uniqueness corollary. The construction nodes remain not ready
until their proofs are translated into an explicit project specification.

## Kodaira vanishing, pp.248–249

Remark 7.15 states Kodaira vanishing for a nonsingular projective complex
variety and an ample invertible sheaf. Hartshorne cites Kodaira [1], Wells,
Chapter VI, §2, Mumford [3], and Ramanujam [1]. Mumford [3], *Pathologies
III*, is retained as Hartshorne's historical reference, including the
positive-characteristic pathology context, but is not adopted as the
implementation proof specification. This result is recorded but remains not
ready: neither an analytic Dolbeault/Hodge formalization nor a specific
modern algebraic proof stack has been adopted.

## Pinned Mathlib audit

The audited checkout is commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). Useful exact
primitives include `Scheme.Modules` and its abelian structure in
`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`;
`CategoryTheory.Abelian.Ext`, `Ext.mk₀`, `Ext.homEquiv₀`, and `Ext.comp` in
`Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean`;
`CategoryTheory.Sheaf.H`, `H.equiv₀`, `H.map`, and `functorH` in
`Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean`; and
`LinearMap.IsPerfPair` in
`Mathlib/LinearAlgebra/PerfectPairing/Basic.lean`.

`RingTheory.Sequence.IsRegular` is in
`Mathlib/RingTheory/Regular/RegularSequence.lean`, while
`projectiveDimension_quotient_eq_length` is in
`Mathlib/RingTheory/Regular/ProjectiveDimension.lean`. The former file
explicitly lists Koszul regularity, Koszul complexes, and depth as future
work. `KaehlerDifferential`, its universal derivation `D`, and the universal
linear equivalence are in `Mathlib/RingTheory/Kaehler/Basic.lean`, but no
scheme differential sheaf or residue theory is present.

No exact pinned declaration was found for a dualizing sheaf or complex,
Serre duality, sheaf Ext, a Koszul complex, Cohen–Macaulay depth, ESZ,
Kodaira vanishing, or residues of algebraic differentials. Accordingly no
leaf in this chapter is marked `mathlib: true`.

Active but unpinned upstream work includes Nailin Guan's Koszul PRs
[#43706](https://github.com/leanprover-community/mathlib4/pull/43706),
[#43708](https://github.com/leanprover-community/mathlib4/pull/43708),
[#43710](https://github.com/leanprover-community/mathlib4/pull/43710), and
[#43711](https://github.com/leanprover-community/mathlib4/pull/43711), depth
PR [#26214](https://github.com/leanprover-community/mathlib4/pull/26214),
and Cohen–Macaulay PR
[#26218](https://github.com/leanprover-community/mathlib4/pull/26218);
Raphael Douglas Giles's Ext-module PR
[#42716](https://github.com/leanprover-community/mathlib4/pull/42716);
Junyan Xu's sheaf-module monoidal PR
[#42860](https://github.com/leanprover-community/mathlib4/pull/42860); and
Joël Riou's differential-sheaf draft
[#17471](https://github.com/leanprover-community/mathlib4/pull/17471).

## Remaining source obligations

- Give a complete coordinate-invariance proof for the trace cocycle of
  Remark 7.1.1.
- Reconcile III.6's global and sheaf Ext models, injective-resolution
  comparison, and eventual comparison with `Scheme.Modules` and with the
  base-field module structure on Ext. The III.7 proof uses the eventual
  comparison directly and requires no spectral-sequence dependency.
- Fix a complete Lean-level source for the residue construction,
  parameter independence, finite-morphism compatibility, global residue
  theorem, and repartition perfectness.
- Choose either an analytic or an algebraic formalization route for Kodaira
  vanishing; the historical references alone do not determine one.
