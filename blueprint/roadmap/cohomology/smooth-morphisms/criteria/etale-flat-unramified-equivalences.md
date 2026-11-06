---
article_id: af_9afe784f58dca3e19b05a327
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.etale_tfae_finiteTypeOverField Hartshorne.HartshorneUnramified
---

# Étale, flat-unramified, and differential criteria

Let $f : X \to Y$ be a morphism of schemes of finite type over a field. Define
Hartshorne-unramified to mean that for every $x \in X$, with $y=f(x)$,

$m_y \mathcal{O}_{X,x} = m_x$

and $k(x)/k(y)$ is separable algebraic. Then the following are equivalent:

1. $f$ is étale, equivalently smooth of relative dimension zero;
2. $f$ is flat and $\Omega_{X/Y}=0$;
3. $f$ is flat and Hartshorne-unramified.

Only the local finiteness half of the finite-type hypotheses is used: it makes $f$ locally of
finite presentation, which is all the equivalences require.

## Depends on

- [The relative differential sheaf](../../../schemes/differentials/scheme-differentials/relative-differentials.md)
- [The stalk criterion for flat morphisms](../../flat-families/flatness/flat-morphism-stalk-criterion.md)

## Proof depends on

- [The universal property of the relative differential sheaf](../../../schemes/differentials/scheme-differentials/relative-differentials-universal.md)
- Étale morphisms are smooth of relative dimension zero and equivalently flat and formally unramified.
- The stalkwise criterion for formal unramifiedness, including residue-field separability.

## Sources

- [Hartshorne III.10, Exercise 10.3, p.275](../../../../sources/hartshorne-iii-10.md#exercise-disposition-pp275276)
- [Stacks Project, Lemma 29.37.15, tag 02GU](../../../../sources/hartshorne-iii-10.md#exercise-disposition-pp275276)
