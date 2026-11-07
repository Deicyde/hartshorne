---
article_id: af_3743230b14283596cc3b7225
declaration: definition
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Ringed.moduleSheafHomData
---

# The sheaf Hom of module sheaves

For $\mathcal{O} _X$-modules $F$ and $G$, make the sheaf
$U \mapsto \operatorname{Hom} _{\mathcal{O} _U}(F|_U, G|_U)$ into an $\mathcal{O} _X$-module by pointwise scalar
multiplication.  Its global sections are naturally the morphisms $F \longrightarrow G$ in
the category of $\mathcal{O}_X$-modules, and restriction is induced by restricting module morphisms.

Pointwise addition and scalar multiplication make the sheaf of
local morphisms into a sheaf of modules.

## Depends on

- [Sheaves of modules](sheaves-of-modules.md)
- [The sheaf of local morphisms](../sheaf-functors/sheaf-hom.md)

## Proof depends on

- Restriction of a module sheaf and of a module-sheaf morphism to an open
  subspace.

## Sources

- [Hartshorne II.5, sheaf Hom on printed p. 109](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
