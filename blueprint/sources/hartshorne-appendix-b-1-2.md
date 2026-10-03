# Hartshorne Appendix B, sections 1–2

The primary source is the repository PDF, *Algebraic Geometry* (1977),
Appendix B overview and §§1–2, printed pp.438–441. Section 2 ends with Chow's
theorem and the reference to Exercise B.6.6. Section 3 begins immediately
afterward on p.441 and is outside this source unit.

All algebraic schemes are of finite type over `C`. Analytic spaces are
Grauert complex analytic spaces and may be nonreduced. Projective GAGA does
not assume the scheme is smooth or reduced.

## Complex analytic spaces, printed pp.438–439

A complex analytic space is a locally ringed space locally isomorphic to a
closed analytic subspace of a polydisc. For a polydisc `U subset C^n` and
holomorphic functions `f_1,...,f_q`, the local model has their common zero
set and structure sheaf `O_U/(f_1,...,f_q)`. Nilpotents are explicitly
allowed. Coherent analytic modules and their cohomology are part of the
Grauert/Gunning–Rossi framework quoted by Hartshorne.

For an affine finite-type scheme

`Spec C[x_1,...,x_n]/(f_1,...,f_q)`,

use the same equations as holomorphic functions on `C^n`. Compatibility with
localization and independence of presentation permit affine analytifications
to glue. This gives a functor from finite-type `C`-schemes to complex analytic
spaces.

Analytify a coherent algebraic sheaf by analytifying a local finite free
presentation and taking its analytic cokernel. Independence of presentation,
coherence, and gluing are required claims.

There is a continuous map `phi:X^h->X`, bijective onto the closed algebraic
points, together with `phi^(-1)O_X->O_(X^h)`. For coherent `F`,

`F^h ~= phi^*F`.

Derived cohomology therefore has natural comparison maps

`alpha_i:H^i(X,F)->H^i(X^h,F^h)`.

No isomorphism is asserted before GAGA.

## Basic comparison properties, printed p.439

Hartshorne cites Serre for the following finite-type comparisons:

- separated iff the analytification is Hausdorff;
- Zariski connected iff analytically connected;
- reduced iff analytically reduced;
- smooth over `C` iff the analytification is a complex manifold;
- a morphism is proper iff its analytification is topologically proper;
- a scheme is proper over `C` iff its analytification is compact.

These are quoted, not proved in the appendix.

## The comparison questions and the nonproper example, printed p.440

Questions Q1–Q5 ask whether spaces, coherent sheaves, their isomorphisms, and
cohomology algebraize or are reflected by analytification. All answers are
negative for unrestricted finite-type schemes.

Serre's example uses an elliptic curve `C`, the unique indecomposable ruled
surface of invariant zero, and its square-zero section `C_0`. For
`U=X-C_0` and `U'=(A^1-{0})^2`, Hartshorne quotes

`U^h ~= U'^h`, `U` nonaffine, `U^h` Stein,
`Pic(U)~=Pic(C)`, and `Pic(U^h)~=Z`.

Thus analytification can identify nonisomorphic algebraic spaces and
nonisomorphic algebraic line bundles. Hartshorne refers to his separate
paper for the proof.

## Projective GAGA and Chow, printed pp.440–441

For a projective `C`-scheme `X`, Serre's GAGA theorem states:

1. analytification is an equivalence from algebraic coherent sheaves on `X`
   to coherent analytic sheaves on `X^h`;
2. every comparison map `alpha_i` is an isomorphism.

The proof uses analytic cohomology of `O(q)` on projective space, Cartan A/B,
an embedding into projective space, and finite resolutions by sums of twists.
Hartshorne also quotes the SGA 1, XII extension from projective to proper
schemes over `C`.

Chow's theorem says every compact analytic subspace of complex projective
space is the analytification of a closed algebraic subscheme. This is a
scheme-theoretic statement retaining analytic nilpotents.

Exercise B.6.6 proves that every analytic morphism between analytifications
of projective schemes algebraizes uniquely. It answers Q2 and supplies the
uniqueness assertion used at the start of §3.

## Exercise disposition, printed pp.447–448

- **Exercises B.6.1–B.6.5 — OUT.** They provide counterexamples and affine-
  curve rigidity but have no later included running-text consumer under the
  final whole-book exercise policy.
- **Exercise B.6.6 — ADOPTED.** Section 2 explicitly leaves projective Q2 to
  it, and §3 uses the resulting uniqueness of algebraization. It has the sole
  Appendix-B exercise leaf.

## Representation and source blockers

The project currently has no category of possibly nonreduced complex analytic
spaces, coherent analytic sheaves, or analytic sheaf cohomology. A model must
include holomorphic germ sheaves, quotient analytic subspaces, locally ringed
space gluing, and analytic properness. Complex points with a topology or a
smooth-manifold structure are insufficient.

Exact proof passages are required from Serre's GAGA paper, Gunning–Rossi or a
modern analytic-space source, SGA 1 XII, Chow, and Hartshorne's ruled-surface
counterexample paper. Cartan A/B and analytic projective-space twist
cohomology are separate analytic roots.

Pinned Mathlib has complex analytic functions and isolated manifold examples,
but no Grauert analytic spaces, coherent analytic sheaves, scheme
analytification, GAGA, or Chow theorem. No roadmap leaf is an exact Mathlib
result.

## Representation warnings

- Preserve nilpotents in both algebraic and analytic spaces.
- Keep analytic and Zariski topologies distinct.
- The comparison map is bijective only onto closed algebraic points.
- `F^h` is analytic scalar extension, not plain inverse image.
- GAGA covers arbitrary projective schemes and coherent sheaves.
- Chow algebraizes analytic subspaces, not only reduced subsets.
- Keep projective GAGA separate from the quoted proper extension.

## Result-to-article map

| Source result | Roadmap article |
|---|---|
| Polydisc holomorphic sheaf | `transcendental-methods/analytic-spaces/polydisc-holomorphic-structure-sheaf.md` |
| Closed analytic subspace | `transcendental-methods/analytic-spaces/closed-analytic-subspace.md` |
| Complex analytic space | `transcendental-methods/analytic-spaces/complex-analytic-space.md` |
| Coherent analytic sheaf | `transcendental-methods/analytic-spaces/coherent-analytic-sheaf.md` |
| Affine analytification | `transcendental-methods/analytification/affine-finite-type-analytification.md` |
| Presentation independence | `transcendental-methods/analytification/affine-presentation-independence.md` |
| Localization compatibility | `transcendental-methods/analytification/localization-open-compatibility.md` |
| Scheme gluing | `transcendental-methods/analytification/scheme-analytification-gluing.md` |
| Analytification functor | `transcendental-methods/analytification/analytification-functor.md` |
| Closed-point comparison | `transcendental-methods/analytification/closed-points-comparison-map.md` |
| Locally ringed-space map | `transcendental-methods/analytification/analytification-locally-ringed-space-map.md` |
| Coherent-sheaf analytification | `transcendental-methods/analytification/coherent-sheaf-analytification.md` |
| Pullback comparison | `transcendental-methods/analytification/coherent-analytification-pullback-comparison.md` |
| Analytic derived cohomology | `transcendental-methods/analytification/analytic-derived-cohomology.md` |
| Cohomology comparison map | `transcendental-methods/analytification/algebraic-analytic-cohomology-comparison-map.md` |
| Separated/Hausdorff | `transcendental-methods/comparison/separated-iff-hausdorff.md` |
| Connectedness | `transcendental-methods/comparison/connected-iff-analytic-connected.md` |
| Reducedness | `transcendental-methods/comparison/reduced-iff-analytic-reduced.md` |
| Smooth/manifold | `transcendental-methods/comparison/smooth-iff-complex-manifold.md` |
| Proper morphisms | `transcendental-methods/comparison/proper-morphism-iff-analytic-proper.md` |
| Proper/compact | `transcendental-methods/comparison/proper-scheme-iff-compact.md` |
| Serre counterexample | `transcendental-methods/comparison/serre-nonproper-ruled-counterexample.md` |
| Analytic projective twists | `transcendental-methods/gaga/projective-space-analytic-twist-cohomology.md` |
| GAGA coherent equivalence | `transcendental-methods/gaga/projective-gaga-coherent-equivalence.md` |
| GAGA cohomology | `transcendental-methods/gaga/projective-gaga-cohomology-comparison.md` |
| Proper GAGA | `transcendental-methods/gaga/proper-gaga-extension.md` |
| Chow theorem | `transcendental-methods/gaga/chow-analytic-subspace-algebraization.md` |
