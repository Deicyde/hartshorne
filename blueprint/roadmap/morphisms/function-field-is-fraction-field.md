---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.isFractionRing_functionField Hartshorne.exists_dim_eq_trdeg_functionField Hartshorne.coordToRational Hartshorne.coordToRational_injective Hartshorne.isUnit_coordToRational Hartshorne.RationalRep.rel_of_eqOn Hartshorne.RationalRep.inv Hartshorne.instCommRingFunctionField
---

# The function field is the fraction field

For an affine variety `Y`, `K(Y)` is the fraction field of `A(Y)`, and its
transcendence degree over `k` is `dim Y`. This is Theorem 3.2(d).

`K(Y)` first has to be a ring at all. The construction copies the one for
`𝒪_{P,Y}`, with the difference Hartshorne flags: there is no distinguished point
keeping the domains from separating, so nonemptiness of `r.U ∩ s.U` comes from
irreducibility instead. Every operation therefore carries that hypothesis, where
the germ operations do not.

## The three clauses of a localisation

A nonzero element of `A(Y)` becomes a unit: it does not vanish identically, so
the open set where it is nonzero is nonempty and its reciprocal is regular
there.

Every rational function is a fraction: by the definition of regular it is `g/h`
on some nonempty open set.

The map is injective, so an equality needs no denominator to witness it. As with
the local ring, this is easier than Hartshorne's phrasing suggests: a polynomial
function has domain all of `Y`, so a zero class means zero everywhere.

The middle clause is where irreducibility does real work. `h · z = g` holds on
the open set where the local description was taken, and Hartshorne's
identification demands agreement on the whole overlap;
`RationalRep.rel_of_eqOn`, the identity principle in the form this needs, closes
the gap. It is the same step that made the relation transitive to begin with.

## The transcendence degree

`dim Y = dim A(Y)` is Proposition 1.7 and `dim A(Y) = trdeg_k Frac A(Y)` is
Theorem 1.8A(a), so `trdeg_k K(Y) = dim Y` follows.

The statement fixes the ambient space as `𝔸ⁿ` for a natural number `n` rather
than an arbitrary finite index type. That is not cosmetic: Theorem 1.8A(a)
compares `A(Y)` with a polynomial ring over `k` and needs the two to share a
universe, which forces the index type into `k`'s.

## Depends on

- [The function field](function-field.md)
- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)

## Proof depends on

- [Regular functions are continuous](regular-function-continuous.md)
- [Dimension is the dimension of the coordinate ring](../affine-varieties/dim-eq-coordinate-ring-dim.md)
- [Dimension of a finitely generated domain](../affine-varieties/dim-fg-domain.md)

## Sources

- [Hartshorne I.3, Theorem 3.2(d) (p. 17)](../../sources/hartshorne.md#i3)
