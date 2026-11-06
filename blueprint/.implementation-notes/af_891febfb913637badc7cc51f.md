# Raw pushforward of cycles

## Status

Partially formalized; not recorded in the article frontmatter. The generator
formula and the linear extension compile without `sorry` in
`Hartshorne.Intersection.RawCyclePushforward`. The codimension reindexing of
the target is missing because it needs the dimension-codimension formula,
which is neither formalized nor reachable from this article's dependencies.

## Checked declarations

- `Hartshorne.rawCyclePushforwardCoeff f x`: for `Y = closure {x}`, zero if
  `topologicalKrullDim (closure (f '' Y)) < topologicalKrullDim Y`, and
  otherwise `f.residueDegree x`, the degree of `κ(f x) → κ(x)`.
- `Hartshorne.rawCyclePushforward_closure_image_eq`: the closure of the image
  of `closure {x}` is `closure {f x}`, so its generic point is `f x`.
- `Hartshorne.rawCyclePushforwardGenerator f x`: the coefficient times the
  cycle of `closure {f x}`.
- `Hartshorne.rawCyclePushforwardUngraded f r :
  codimensionCycles X r →+ AlgebraicCycle X' ℤ`: the linear extension
  (through `Hartshorne.codimensionCyclesToFinsupp` and
  `Finsupp.liftAddHom`), with `rawCyclePushforwardUngraded_apply` giving the
  finite-sum formula.

Function fields: the cycle group records an irreducible closed subset by its
generic point. The function field of the reduced induced structure on
`closure {x}` is the residue field `κ(x)`, so `[K(Y):K(closure f(Y))]` is the
residue degree. The finite-dimension value of `Module.finrank` is the actual
degree in Hartshorne's setting: for varieties over `k` with
`dim closure f(Y) = dim Y`, both function fields are finitely generated over
`k` with the same transcendence degree (affine-varieties/dim-fg-domain), so the
extension is finite.

## Missing prerequisite

Reindexing means mapping `Z^r(X)` to `Z^{r + dim X' - dim X}(X')` for varieties
`X, X'` over a field. If `x` has codimension `r` in `X` and
`dim closure {f x} = dim closure {x}`, then
`codim closure {f x} = dim X' - dim closure {x} = r + dim X' - dim X`. Both
equalities are the dimension-codimension formula
(schemes/subschemes-and-dimension/dimension-codimension-formula.md) applied
in `X'` and in `X`. When the index `r + dim X' - dim X` is negative, the
same formula shows that every generator has a dimension drop, so the map is
zero.

- schemes/subschemes-and-dimension/dimension-codimension-formula.md is not
  formalized. Its own note records a missing link to
  affine-varieties/dim-formula-catenary.
- It is not reached from this article's "Depends on" list
  (codimension-cycle-group, scheme-theoretic-image,
  function-field-integral-scheme). It would have to be added there.
  Reindexing also needs the variety setting: integral schemes of finite type
  over a field.

## Next route

Once the formula is reachable, define the graded map
`codimensionCycles X r →+ codimensionCycles X' s`, where `s` is the natural
number `r + dim X' - dim X` (and the map is zero when that integer is
negative), by restricting the codomain of `rawCyclePushforwardUngraded`.
Support membership follows from the two applications of the formula above.
