---
article_id: af_1d074f70439f06a033485b4c
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# Divisors in a nonpencil linear system are connected

Let `X` be a normal projective variety over an algebraically closed field and
let `b` be a basepoint-free linear system of effective Cartier divisors. Let
`f : X -> P^n` be the morphism determined by `b`. If

`dim f(X) >= 2`,

then every divisor belonging to `b` is connected.

The dimension hypothesis is Hartshorne's meaning of “not composite with a
pencil.” This is the connectedness promised in III Remark 10.9.1; it does not
assert smoothness or irreducibility of every member.

## Depends on

- [Stein factorization](stein-factorization.md)
- [Linear systems](../../../schemes/projective-geometry/linear-systems-ampleness/linear-system-api.md)
- [Morphisms from generated invertible sheaves](../../../schemes/projective-geometry/linear-systems-ampleness/morphism-from-generated-line-bundle.md)
- [Projective-morphism calculus](../../../schemes/proper-and-projective/projective-morphism-calculus.md)
- [Normal schemes](../../../schemes/normalization-and-exercises/normal-scheme.md)
- [Ampleness restricts to closed subschemes](../../projective-cohomology-exercises/ample-restricts-to-closed-subscheme.md)
- [Finite-surjective descent of ampleness](../../projective-cohomology-exercises/ample-finite-surjective-descent.md)
- [Connected support of an ample divisor](../../serre-duality/duality-applications/ample-divisor-support-connected.md)

## Proof depends on

- In the Stein factorization of `f`, the finite intermediate variety is
  integral, normal, projective, and has dimension `dim f(X)`.
- Pullback of a hyperplane to that intermediate variety is an effective ample
  Cartier divisor and hence has connected support.
- A proper surjective map with connected fibres has connected inverse image
  of every connected closed subset.

## Sources

- [Hartshorne III.11, Exercise 11.3, pp.280–281](../../../../sources/hartshorne-iii-11-12.md#exercise-11-disposition-pp280281)
- [Hartshorne III.10, Remark 10.9.1](../../../../sources/hartshorne-iii-10.md#homogeneous-spaces-kleiman-and-bertini-pp272275)
