# Fibres of the differential sheaf on an affine chart

## Candidate Lean

- `Hartshorne.finrank_fibre_relativeDifferentials_affine`
  (`Hartshorne.Scheme.Differentials.RelativeDifferentialsAffineFibre`): the statement, with the
  point given as `U.2.fromSpec y` for `y : Spec Γ(X, U)`.
- `Hartshorne.finrank_fibre_eq_of_iso_tilde` (same module): the fibre of `G ≅ M~` at `y` has
  dimension `dim κ(y) ⊗_R M`.

The first is currently recorded on the III.10 bridge differential-criterion-smooth-scheme-over-field;
the second is unrecorded. The record commit records both here and drops the first from the bridge.
