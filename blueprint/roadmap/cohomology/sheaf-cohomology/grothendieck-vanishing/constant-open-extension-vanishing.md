---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-1-4]
---

# Vanishing for `Z_U`

Let `X` be irreducible noetherian with `topologicalKrullDim X = n`, and
assume Grothendieck vanishing is known for all proper closed subspaces of
`X`. For every open `U ⊆ X`, one has `Hⁱ(X,Z_U)=0` for `i>n`.

This parameterized induction step is the unique main result. For `Y=X\\U`,
use `0 ⟶ Z_U ⟶ Z ⟶ Z_Y ⟶ 0`, flasqueness of `Z`, closed-pushforward
cohomology, and strict dimension drop on `Y`.

## Depends on

- [Sheaf cohomology and the Ext model](../sheaf-cohomology.md)
- [Open extension by zero](../../../schemes/sheaf-functors/open-extension-by-zero.md)

## Proof depends on

- [Dimension drops on proper closed subsets](proper-closed-dimension-drop.md)
- [The open–closed extension exact sequence](../open-closed-extension-exact-sequence.md)
- [Closed pushforward preserves cohomology](../closed-pushforward-cohomology.md)
- [Flasque closure in short exact sequences](../flasque-short-exact-closure.md)
- [Flasque sheaves are acyclic](../flasque-sheaf-acyclic.md)
- [The long exact sequence of sheaf cohomology](../sheaf-cohomology-long-exact-sequence.md)

## Sources

- [Hartshorne III.2, proof of Theorem 2.7, Step 5, printed p. 211](../../../../sources/hartshorne-iii-1-2.md#grothendieck-vanishing-proof-printed-pp-210211)
