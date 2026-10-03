---
declaration: theorem
origin: cited
source_units: [chapter-iv-section-4]
---

# Pointed automorphism groups

Let `(X,P_0)` be an elliptic curve over an algebraically closed field of
characteristic different from two. Its pointed automorphism group is finite
of order

- `2` if `j` is neither `0` nor `1728`;
- `4` if `j=1728` and the characteristic is not three;
- `6` if `j=0` and the characteristic is not three;
- `12` in characteristic three when `j=0=1728`.

## Depends on

- [Degree-two maps are equivalent](elliptic-degree-two-maps-equivalent.md)
- [The Legendre S3 action](legendre-s3-action.md)
- [The special models with j zero and 1728](elliptic-special-j-models.md)

## Proof depends on

- A pointed automorphism descends to an automorphism of `P^1` preserving the
  branch set; the kernel is the order-two deck group.
- Compute stabilizers of the Legendre parameter under `S_3`, keeping the
  characteristic-three collision separate.

## Sources

- [Hartshorne IV.4, Corollary 4.7, p.321](../../../../sources/hartshorne-iv-4.md)
