---
article_id: af_572e68b826e8320afd8b7c41
declaration: theorem
origin: cited
lean: Hartshorne.moduleSheaves_enoughInjectives
statement: formalized
proof: formalized
---

# Module sheaves have enough injectives

For a ringed space $(X,\mathcal{O}_X)$, every sheaf of $\mathcal{O}_X$-modules admits a
monomorphism into an injective object of the category of $\mathcal{O}_X$-modules.

The construction embeds each stalk into an injective $\mathcal{O}_{X,x}$-module and
maps the sheaf into the product of the corresponding skyscraper module
sheaves. The main result is enough injectives for the module-sheaf category;
the stalkwise construction is proof data.

## Depends on

- [Sheaves of modules](../../schemes/modules-and-quasicoherent/sheaves-of-modules.md)

## Proof depends on

- [Exactness is detected on stalks](../../schemes/sheaves/stalkwise-exactness.md)
- [Direct image of a sheaf](../../schemes/sheaf-functors/direct-image.md)

## Sources

- [Hartshorne III.2, Propositions 2.1A and 2.2, printed pp. 206–207](../../../sources/hartshorne-iii-1-2.md#enough-injectives-and-cohomology-printed-pp-206208)
