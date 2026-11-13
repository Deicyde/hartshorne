---
article_id: af_7db5ec1a9029123711d00706
declaration: theorem
origin: cited
lean: Hartshorne.IsIdealOfDefinition.reconstruction
statement: formalized
proof: formalized
---

# Reconstruction from infinitesimal reductions

Let $\widehat{X}$ be a Noetherian formal scheme, $J$ an ideal of definition, and
$F$ a coherent formal module. For nonnegative integer $n$, set

$F_n = F / J^{n+1} F$.

Then $F_n$ is coherent on the scheme
$(\widehat{X} ,\mathcal{O}_{\widehat{X}} /J^{n+1})$, and the canonical map

$F \longrightarrow \lim _n F_n$

is an isomorphism.

## Depends on

- [Coherent modules on a Noetherian formal scheme](coherent-formal-module.md)
- [Ideals of definition](../formal-neighborhoods/ideal-of-definition.md)

## Proof depends on

- [Completion of a coherent module](completed-coherent-module.md)
- [Powers of an ideal of definition](../formal-neighborhoods/powers-of-ideal-of-definition.md)
- [Thickenings of an affine formal scheme](../formal-neighborhoods/affine-formal-thickenings.md)
- [Completion and ordinary sheaf tensor product](scheme-completion-tensor-comparison.md)
- [Scheme completions are formal schemes](../formal-neighborhoods/completion-is-formal-scheme.md)
- [Pullback preserves quasi-coherence](../../modules-and-quasicoherent/pullback-quasicoherent.md)
- Locality on a finite formal-affine cover.

## Sources

- [Hartshorne II.9, Proposition 9.6(a) (pp.197–198)](../../../../sources/hartshorne-ii-9.md#coherent-modules-on-formal-schemes)
