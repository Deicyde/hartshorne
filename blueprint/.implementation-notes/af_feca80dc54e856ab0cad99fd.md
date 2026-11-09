# The differential principal-parts resolution

## Status (42981-w29, frontier/w29b): not started in Lean; Roadmap return

No Lean has been written for this node. The article takes for granted the inclusions
`Ω_{X,P} ⊆ Ω_{K/k}` and a principal-parts decomposition over the closed points of a scheme
curve. Neither is in the project or in the DAG, and each is a substantial development of its own.

## Missing prerequisites

- **Stalks of the sheaf of differentials.** We need `(Ω_{X/k})_x ≅ Ω_{𝒪_{X,x}/k}`, and at the
  generic point of an integral `X`, `(Ω_{X/k})_η ≅ Ω_{K/k}`. For a locally free sheaf on an
  integral scheme, we also need the injectivity of sections over a nonempty open, and of stalks,
  into the generic stalk. This is what makes `Ω_X ⟶ Ω_K` and `Ω_K/Ω_{X,P}` meaningful. The
  project has the affine identification `Ω_{Spec B/Spec A} ≅ (Ω_{B/A})~`
  (affine-relative-differentials), but it has no stalk or generic-stalk statement, and no node
  for one.
- **Principal parts over the closed points of a scheme curve.** The plain-text item "the general
  curve principal-parts decomposition over closed points" has no node. The existing `ℙ¹`
  resolution (projective-line-principal-parts-resolution) is built on Chapter-I varieties
  (`Variety`, `regularSheaf`, `locallyFiniteSumSheaf` on `X.carrier`), not on schemes. It cannot
  be reused for a scheme curve without a scheme version of the locally finite sum of skyscrapers
  and of "a nonzero rational section has finitely many poles".
- **Canonical sheaf of a curve as `Ω_{X/k}`.** `canonicalSheaf f` is `⋀^{dim X} Ω_{X/k}`.
  Comparing it with `Ω_{X/k}` needs `⋀^1 E ≅ E` for module sheaves; whether the project has this
  is not yet checked.

## Suggested route once the prerequisites exist

1. Define `Ω_K` as the constant sheaf with value `Ω_{K/k}` (`Hartshorne.constantSheaf`), and the
   map `Ω_X ⟶ Ω_K` that sends a section to its generic germ.
2. Define the target as the coproduct of the skyscrapers `i_{P,*}(Ω_{K/k}/Ω_{X,P})` over closed
   points, presented as locally finite families. The map from `Ω_K` takes principal parts. Its
   support is locally finite because a rational differential has finitely many poles: write
   `ω = f · ω₀` with `ω₀` a local generator.
3. Check exactness on stalks with `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`. Injectivity
   comes from local freeness of rank one on an integral scheme. Exactness in the middle and
   surjectivity are stalkwise statements about `Ω_{K/k}/Ω_{X,P}`.
4. Show flasqueness: a constant sheaf on an irreducible space is flasque, and so are skyscraper
   sums. Then `H¹(X, Ω_X)` is the cokernel on global sections, using
   `sheafCohomology_isZero_of_isFlasque`.
