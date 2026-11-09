# Module and abelian-sheaf cohomology agree

## Supporting implementation references

- `SheafOfModules O_X`

## Lean written, not recorded (2026-11-09)

Module `Hartshorne.Cohomology.ModuleCohomologyComparison` proves the comparison isomorphism and
the module-valued derived functors: `Hartshorne.moduleSheafCohomologyNatIso`,
`Hartshorne.moduleSheafCohomologyIso`, `Hartshorne.moduleSheafCohomologyIso_naturality`,
`Hartshorne.moduleSheafCohomology`, `Hartshorne.moduleSheafCohomologyModuleNatIso`,
`Hartshorne.moduleSheafCohomologyModule`, `Hartshorne.ModuleCohomology.toSheaf_preservesFiniteColimits`.
Independent review found the statement's clause "functorially and compatibly with exact sequences"
only half covered: nothing shows that the connecting maps are `Γ(X, 𝒪_X)`-linear or that the
comparison commutes with them. Remaining goal: δ-compatibility of `moduleSheafCohomologyModuleNatIso`
with `rightDerivedδ` (module-valued, after `forget₂`) and `sheafCohomologyδ`; `acyclicResolutionIso`
has no δ lemma yet (alternatively rebuild through `compIso` / `δ_compIso_hom` in
SheafCohomologyExtComparison). Or a Roadmap restatement dropping "compatibly with exact sequences"
if the book (Remark III.2.6.1, p.208) does not state it; then record the names above.
