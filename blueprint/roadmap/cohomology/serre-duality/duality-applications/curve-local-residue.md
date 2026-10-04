---
article_id: af_e76aa6830ed04bb8b3b29446
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-6-7]
not_ready: true
---

# Local residues on a nonsingular curve

Let `X` be a complete nonsingular curve over an algebraically closed field
`k`, with function field `K`. For every closed point `P` there is a unique
`k`-linear map

`res_P : Ω_(K/k) →ₗ k`

which vanishes on regular differentials, sends `fⁿ df` to zero for
`n≠-1`, and sends `f⁻¹df` to `v_P(f)·1_k`. Equivalently, with a
uniformizer `t`, write the finite negative Laurent principal part as
`Σ_(i<0) a_i t^i dt`, with only finitely many nonzero `a_i`, plus a regular
differential. Its residue is `a_(-1)`.

This remains not ready until parameter independence, especially in positive
characteristic, is fixed in an implementable construction.

## Depends on

- [Complete nonsingular curves are projective](../../../schemes/divisors/curve-divisors/complete-nonsingular-curve-projective.md)
- [Nonsingular curve local rings are DVRs](../../../nonsingular-curves/nonsingular-curve-local-ring-dvr.md)
- [The relative differential sheaf](../../../schemes/differentials/scheme-differentials/relative-differentials.md)
- [The function field of a projective variety](../../../morphisms/projective-rings/projective-function-field.md)

## Proof depends on

- A precise Laurent principal-part decomposition in the completed DVR.
- Parameter independence of the coefficient of `t⁻¹dt`.

## Sources

- [Hartshorne III.7, Theorem 7.14.1, p.247](../../../../sources/hartshorne-iii-7.md#residues-on-curves-pp247248)
- Serre, *Groupes algébriques et corps de classes*, Chapter II
- Tate, “Residues of differentials on curves,” *Ann. Sci. ÉNS* (4) 1 (1968), 149–159
