# Stacks Project: Nagata and Japanese rings

This project adopts the Stacks Project's *Commutative Algebra*,
[Section 10.162, Nagata rings](https://stacks.math.columbia.edu/tag/032E), as a
proof source for the general-field normalization input used in Hartshorne
II.5, Theorem 5.19.

## Finite-type algebras over a field

[Proposition 10.162.16 (Tag 0335)](https://stacks.math.columbia.edu/tag/0335)
states that fields are Nagata and that finite-type ring extensions of Nagata
rings are Nagata; it also records that these rings are universally Japanese.
Consequently, a finitely generated algebra domain `A` over an arbitrary field
is Nagata.

By the definitions in Section 10.162 and the preceding Japanese-ring section,
a Nagata domain is `N-2` (Japanese): for every finite extension `L` of its
fraction field, the integral closure of `A` in `L` is finite as an `A`-module.
Applying this definition to the preceding proposition gives exactly the
general-field finiteness theorem required in the proof of Hartshorne II.5.19.

The roadmap uses only this implication. It does not adopt the full theory of
Nagata rings as a separate formalization milestone.
