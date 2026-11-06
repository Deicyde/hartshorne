# Sheaf tensor, symmetric, and exterior operations

## Status

Partial. The degree-$r$ powers and their compatibility with restriction to open subschemes are
formalized, sorry-free, in `Hartshorne.Scheme.SheafTensorOperations`; the sheaves of algebras
$T(F)$, $S(F)$, $\bigwedge(F)$ are not yet constructed, so the article is not recorded.

## Supporting implementation references

- `F : X.Modules`; the module works over a general ringed space as `SheafOfModules (ringCatSheafOf R)`,
  like `Hartshorne.moduleSheafTensor`, and the restriction statements are for schemes.

## Checked declarations

- `Hartshorne.moduleSheafTensorPower`, `Hartshorne.moduleSheafSymmetricPower`,
  `Hartshorne.moduleSheafExteriorPower`: sheafifications of $U\mapsto T^r_{\mathcal O_X(U)}F(U)$,
  $\operatorname{Sym}^r$, $\bigwedge^r$ (with units `...Unit`).
- `Hartshorne.ModuleSheafMultilinear` with predicates `IsSymmetric`, `IsAlternating`; universal
  properties `...HomEquiv`, `..._universal`, universal maps `...Multilinear`.
- `Hartshorne.moduleSheafTensorPowerRestrictIso` (and symmetric/exterior analogues) for an open
  immersion of schemes, with `..._multilinear` compatibility with the universal maps; built on
  `Hartshorne.SheafTensorOperations.sheafificationRestrictHom` being an isomorphism.

## Remaining goal

Construct the tensor, symmetric, and exterior algebras of $F$ as sheaves of $\mathcal O_X$-algebras
by sheafifying $U\mapsto T(F(U))$, $S(F(U))$, $\bigwedge(F(U))$, and identify their homogeneous
degree-$r$ components with the powers above.

## Mathlib gaps

- No monoidal structure on sheaves of modules over a varying sheaf of rings, and no statement that
  sheafification of presheaves of modules is monoidal, $a(P\otimes Q)\cong a(aP\otimes aQ)$; this
  is what is needed to sheafify the multiplication of a presheaf of algebras.
- No sheafification of presheaves of algebras over a varying sheaf of rings.
- `SymmetricAlgebra` has no grading and is not related to `SymmetricPower` (whose universal
  property is a Mathlib TODO); `SymmetricPower` also forces the ring and the index type into the
  same universe, so the powers use a quotient of the tensor power instead.

## Next route

Prove $a(P\otimes Q)\cong a(aP\otimes aQ)$ from stalks: the presheaf map
$P\otimes Q\to aP\otimes aQ$ is an isomorphism on stalks by the stalk computation for presheaf
tensor products already used for the module tensor product, and a morphism of sheaves of abelian
groups that is an isomorphism on stalks is an isomorphism. Then sheafify the multiplication of the
presheaf of algebras, check associativity and unitality by uniqueness of maps out of
sheafifications, and obtain the degree-$r$ components from the direct-sum decompositions of the
algebras (Mathlib has these for the tensor and exterior algebras, not for the symmetric algebra).
