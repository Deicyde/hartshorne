---
article_id: af_7ec2c8292f28cc6598a1a58e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.IsQuasiProjVariety.birational_nonsingular_projective
---

# Projective models of curves

Every curve is birational to a nonsingular projective curve.

This is Corollary 6.11.  Apply [Theorem I.6.9](function-field-projective-model.md) to the curve's function field, then
use the function-field criterion for birationality.  The curve-dimension theorem gives transcendence degree one. No
separability hypothesis is required.

## Depends on

- [Curves](../nonsingular-curves/curve.md)
- [Birational maps](../rational-maps/birational-map.md)
- [Intrinsic nonsingularity](../nonsingular-varieties/intrinsic-nonsingularity.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)

## Proof depends on

- [Nonsingular projective models of function fields](function-field-projective-model.md)
- [Birational varieties have isomorphic function fields](../rational-maps/birational-function-fields.md)

## Sources

- [Hartshorne I.6, Corollary 6.11 (p. 45)](../../sources/hartshorne.md#i6-projective-models)
