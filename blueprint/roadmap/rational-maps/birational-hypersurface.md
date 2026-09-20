---
article_id: af_282371bb38115fa34ae6b5a5
declaration: theorem
origin: cited
source_units: [chapter-i-section-4]
statement: formalized
proof: formalized
lean: Hartshorne.exists_birational_projective_hypersurface
---

# Every variety is birational to a hypersurface

Any variety `X` of dimension `r` in Hartshorne's four concrete classes — hence
carrying the affine-open-basis and separatedness witnesses used by §4 — is
birational to a hypersurface `Y` in `ℙ^{r+1}` (Proposition 4.9).

This is as much of a normal form as birational geometry provides, and it is a
clean illustration of what [Theorem 4.4](rational-map-function-field.md) buys:
the entire proof happens in field theory, and geometry only appears at the two
ends.

## The proof

`K = K(X)` is a finitely generated extension of `k` of transcendence degree `r`,
by Theorem 3.2(d) and Proposition 1.7. Then:

- `k` is algebraically closed, hence perfect, so `K/k` is separably generated
  ([Theorem 4.8A](separably-generated.md)); take a separating transcendence base
  `x₁,…,x_r`, so `K` is a finite separable extension of `k(x₁,…,x_r)`;
- by the primitive element theorem there is a single `y` with
  `K = k(x₁,…,x_r, y)`;
- `y` is algebraic over `k(x₁,…,x_r)`, so it satisfies a polynomial relation
  whose coefficients are rational functions in the `xᵢ`. Clearing denominators
  gives an irreducible `f(x₁,…,x_r, y) = 0`;
- `f` cuts out a hypersurface in `𝔸^{r+1}` whose function field is `K`, so by
  [Corollary 4.5](birational-criterion.md) it is birational to `X`;
- its [projective closure](projective-closure.md) in `ℙ^{r+1}` is the required
  `Y`, birational to the affine hypersurface and hence to `X`.

Two small things are worth pinning down. Classically, irreducibility after
clearing denominators is the Gauss-lemma step from
`k(x₁,…,x_r)[y]` to `k[x₁,…,x_r,y]`. The formal proof packages the same
argument through ideals: evaluation at `x₁,…,x_r,y` has prime kernel, the
dimension formula makes that kernel height one, and the height-one prime
theorem for a polynomial UFD supplies an irreducible generator `f`. The
quotient is then shown to have fraction field `K`; the coordinate-ring
dimension theorem computes the dimension of `Z(f)` from this identification.
Finally, the projective-closure theorem identifies its closure literally with
the projective zero set of the homogenisation of `f`.

## Depends on

- [The birational criterion](birational-criterion.md)
- [Separably generated field extensions](separably-generated.md)
- [The projective closure of an affine variety](projective-closure.md)

## Proof depends on

- [Hypersurfaces and codimension one](../affine-varieties/hypersurface-dimension.md)
- [The function field is the fraction field](../morphisms/function-field-is-fraction-field.md)
- [Dimension of a finitely generated domain](../affine-varieties/dim-fg-domain.md)
- [Dimension in projective space](../projective-varieties/projective-dimension.md)

## Sources

- [Hartshorne I.4, Proposition 4.9 (p. 27)](../../sources/hartshorne.md#i4)
