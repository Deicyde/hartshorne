---
article_id: af_7366ce782734f3f77e702dc7
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.ClosedConormal.closedImmersion_conormal_exact
---

# The conormal sequence of a closed immersion

Let $Z \hookrightarrow X \to Y$ be a closed subscheme with ideal sheaf $J$.  Construct the
natural right-exact sequence on $Z$

$J/J^{2} \to i^* \Omega_{X/Y} \to \Omega_{Z/Y} \to 0$,

where $i : Z \hookrightarrow X$ and $i^* \Omega_{X/Y}$ is canonically identified with
$\Omega_{X/Y} \otimes _[\mathcal{O} _X] \mathcal{O} _Z$.

The left term is the conormal sheaf of the immersion.  The statement does not
claim that its first map is injective.

## Depends on

- [The relative differential sheaf](relative-differentials.md)
- [The conormal sheaf of an immersion](immersion-conormal-sheaf.md)
- [The conormal exact sequence](../kaehler-differentials/kahler-conormal-exact-sequence.md)
- [Closed immersions and closed subschemes](../../subschemes-and-dimension/closed-immersions.md)
- [Tensor products of module sheaves](../../modules-and-quasicoherent/module-tensor-product.md)
- [Pushforward, pullback, and their adjunction](../../modules-and-quasicoherent/module-push-pull-adjunction.md)

## Proof depends on

- [The transitivity sequence for differential sheaves](relative-differentials-transitivity.md)
- [Closed subschemes of an affine scheme](../../subschemes-and-dimension/affine-closed-subschemes.md)
- Stalkwise exactness and sheaf quotients.

## Sources

- [Hartshorne II.8, Proposition 8.12, printed p. 176](../../../../sources/hartshorne-ii-8.md)
