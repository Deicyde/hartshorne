## README.md

### Mathlib boundary

The pinned Mathlib already contains the exact
`IsRegularLocalRing.iff_finrank_cotangentSpace` criterion,
`MvPolynomial.pderiv`, the polynomial Kähler basis and its partial-derivative
coordinate formula, and a local Jacobian criterion for formal smoothness. It
also has `Scheme.Hom.isOpen_smoothLocus` and
`Scheme.Hom.dense_smoothLocus_of_perfectField`. It does not identify those
scheme-theoretic notions with this project's classical point-set varieties or
their germ local rings. The roadmap therefore reuses the local-algebra
primitives but follows Hartshorne's explicit Jacobian-minor and
birational-hypersurface proof for Theorem 5.3.
