---
article_id: af_d77aa4b8be24b9adcbe9f1da
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.moduleSheafCohomology Hartshorne.moduleSheafCohomologyIso Hartshorne.moduleSheafCohomologyIso_naturality Hartshorne.moduleSheafCohomologyNatIso Hartshorne.moduleSheafCohomologyNatIso_δ Hartshorne.moduleSheafCohomologyModule Hartshorne.moduleSheafCohomologyModuleNatIso Hartshorne.moduleSheafCohomologyModuleNatIso_δ Hartshorne.moduleSheafCohomologyModule_δ_smul Hartshorne.ModuleCohomology.toSheaf_preservesFiniteColimits
---

# Module and abelian-sheaf cohomology agree

For a ringed space $(X,\mathcal{O}_X)$, the right derived functors of global sections
computed in the category of $\mathcal{O}_X$-modules are naturally isomorphic, after forgetting
module structure, to the cohomology of the underlying abelian sheaf.

The comparison also equips every $H^{n}(X,F)$ with its natural
$\Gamma (X,\mathcal{O}_X)$-module structure, functorially and compatibly with exact sequences.

## Depends on

- [Module sheaves have enough injectives](module-sheaves-enough-injectives.md)
- [Sheaf cohomology](sheaf-cohomology.md)
- [The long exact sequence of sheaf cohomology](sheaf-cohomology-long-exact-sequence.md)

## Proof depends on

- [Injective module sheaves are flasque](injective-module-sheaf-flasque.md)
- [Flasque sheaves are acyclic](flasque-sheaf-acyclic.md)
- [Acyclic resolutions compute derived functors](../derived-functors/acyclic-resolution-comparison.md)

## Sources

- [Hartshorne III.2, Proposition 2.6 and Remark 2.6.1, printed p. 208](../../../sources/hartshorne-iii-1-2.md#enough-injectives-and-cohomology-printed-pp-206208)
