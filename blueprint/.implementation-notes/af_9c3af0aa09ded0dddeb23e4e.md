# Sheaves on projective schemes

## Prior implementation guidance

This milestone builds the graded-module layer over Mathlib's existing `Proj`,
then twisting sheaves, graded global sections, reconstruction, very ampleness,
and projective finiteness. The order is intentional: no twist or `Gamma_*`
claim precedes the standard-chart and stalk formulas for the associated
graded-module sheaf.
