# The dense nonsingular locus

## Prior implementation guidance

The generic fiber of `Ω[X/k]` has dimension `dim X` because the function field
is finitely generated and separably generated over the perfect field `k`.
The free locus then gives a neighborhood of the generic point.  Equivalently,
after the smooth/regular comparison, one may use Mathlib's dense smooth locus.
