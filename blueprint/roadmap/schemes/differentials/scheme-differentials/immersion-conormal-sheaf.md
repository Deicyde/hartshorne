---
article_id: af_16b35b95a8072241ce2a54a1
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.immersionConormalSheaf Hartshorne.immersionConormalPushforwardIso Hartshorne.immersionIdealSheaf Hartshorne.idealSheafSqQuotient Hartshorne.idealSheafSqQuotientToPushforward Hartshorne.isIso_idealSheafSqQuotientToPushforward
---

# The conormal sheaf of an immersion

Let $i : Z \to X$ be an immersion. Use its canonical factorization
$Z \to U \hookrightarrow X$ as a closed immersion $i'$ followed by an open immersion. If $I$
is the ideal sheaf of $i'$, define the conormal sheaf $N^*_i$ on $Z$ to be
$i'^*I$. Expose its canonical identification with $I/I^{2}$ after pushforward:

$i'_*N^*_i \cong I/I^{2}$.

The construction must use the actual ideal sheaf; it may not define the
diagonal conormal sheaf to be the relative differential sheaf.

## Depends on

- [Open immersions and open subschemes](../../subschemes-and-dimension/open-immersions.md)
- [Closed immersions and closed subschemes](../../subschemes-and-dimension/closed-immersions.md)
- [Ideal sheaves of closed immersions](../../coherent-sheaves/closed-immersion-ideal-sheaf.md)
- [Tensor products of module sheaves](../../modules-and-quasicoherent/module-tensor-product.md)

## Proof depends on

- [Pullback preserves quasi-coherence](../../modules-and-quasicoherent/pullback-quasicoherent.md)
- [Tilde commutes with tensor products](../../modules-and-quasicoherent/affine-tilde/tilde-tensor-compatibility.md)
- Restriction and quotient compatibility for module sheaves.
- Stacks Project, tags $01R1$–$01R3$, for the conormal sheaf
  and its $I/I^{2}$ description.

## Sources

- [Hartshorne II.8, definition of the differential sheaf as a diagonal conormal sheaf (pp. 175–176)](../../../../sources/hartshorne-ii-8.md#modules-and-sheaves-of-differentials)
- [Adopted Stacks sources for scheme differentials](../../../../sources/hartshorne-ii-8.md#external-proof-sources-and-unresolved-obligations)
