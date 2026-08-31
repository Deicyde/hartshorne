---
declaration: theorem
origin: cited
---

# The standard affine charts

Let `Hᵢ = Z(xᵢ)` and `Uᵢ = ℙⁿ ∖ Hᵢ`. The map `φᵢ : Uᵢ → 𝔸ⁿ` sending
`(a₀,…,aₙ)` to `(a₀/aᵢ, …, aₙ/aᵢ)` with the `i`-th entry omitted is a
homeomorphism for the induced Zariski topology on `Uᵢ` and the Zariski topology
on `𝔸ⁿ` (Proposition 2.2).

The proof is the dehomogenisation/homogenisation pair. Taking `i = 0` and
`A = k[y₁,…,yₙ]`, define `α : S^h → A` by `α(f) = f(1, y₁, …, yₙ)` and
`β : A → S^h` by `β(g) = x₀^{deg g} · g(x₁/x₀, …, xₙ/x₀)`. Then `α` and `β`
carry closed sets to closed sets in either direction, which makes `φ` a closed
bijection with closed inverse.

This is the key result of §2 and the most-used result of Chapter I: it is what
lets every local question about a projective variety be answered affinely. It is
upgraded from a homeomorphism to an isomorphism of varieties in §3, once
morphisms exist.

## Depends on

- [The Zariski topology on projective space](projective-zariski-topology.md)
- [The Zariski topology on affine space](../affine-varieties/zariski-topology.md)

## Sources

- [Hartshorne I.2, Proposition 2.2 (pp. 10-11)](../../sources/hartshorne.md#i2)
