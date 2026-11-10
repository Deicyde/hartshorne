---
article_id: af_d0d7a6b55a03a721e62350f4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.smoothOfRelativeDimension_iff_flat_and_geometric_fiber Hartshorne.smoothOfRelativeDimension_iff_baseChange_isRegularAt Hartshorne.finrank_fibre_relativeDifferentials_pullback_snd Hartshorne.finrank_fibre_modulesPullback Hartshorne.finrank_fibre_eq_of_iso
---

# Smoothness and geometrically regular fibres

Let $f : X \to Y$ be a morphism of finite-type schemes over a field. Then $f$
is smooth of relative dimension $n$ if and only if it is flat and, for every
$y \in Y$, the fibre after base change to an algebraic closure of $k(y)$ is
regular and equidimensional of dimension $n$.

## Depends on

- [Smoothness and regularity over an algebraically closed field](smooth-over-algebraically-closed-iff-regular.md)
- [Smooth relative-dimension calculus](smooth-relative-dimension-calculus.md)
- [The fibre of a morphism](../../../schemes/fiber-products/scheme-fiber.md)

## Proof depends on

- [Flat morphisms with smooth fibres are smooth](flat-smooth-fibers-smooth.md)
- [Base change for differential sheaves](../../../schemes/differentials/scheme-differentials/relative-differentials-base-change.md)
- Faithfully flat descent of local freeness of Kähler differentials along an
  algebraic closure of a residue field.

## Sources

- [Hartshorne III.10, Theorem 10.2, pp.269–270](../../../../sources/hartshorne-iii-10.md#smoothness-and-geometric-fibres-pp268270)
- [Stacks Project, Lemma 29.35.3, tag 01V8](../../../../sources/hartshorne-iii-10.md#smoothness-and-geometric-fibres-pp268270)
