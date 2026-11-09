---
article_id: af_4dd6c82bd1666d3dba104198
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.isLocallyFactorial_of_isRegularLocalRing Hartshorne.RegularLocalFactorial.uniqueFactorizationMonoid_of_isRegularLocalRing
---

# Regular schemes are locally factorial

Let $X$ be a scheme whose local rings are regular local rings. Then every
local ring of $X$ is a UFD, so $X$ is locally factorial.

The proof uses the algebraic theorem that every regular local ring
is a unique factorization domain. The resulting comparison of Weil
and Cartier divisors is treated separately.

For a regular local ring $(A, m)$ the proof is by induction on $\dim A$. A
regular local ring is a domain, and if $\dim A \le 1$ it is a field or a
discrete valuation ring. Otherwise choose $x \in m \setminus m^2$. Then $A/(x)$
is regular, hence a domain, so $x$ is a prime element, and by Nagata's
criterion $A$ is a UFD as soon as $A[1/x]$ is. Every localization of $A[1/x]$
at a prime is a localization of $A$ at a prime other than $m$, hence regular of
smaller dimension and a UFD by induction. So a height-one prime $P$ of
$A[1/x]$ is locally principal, hence an invertible (so projective) ideal. Since $P$ is the
localization of a finitely generated $A$-module, which has a finite free
resolution, $P$ is stably free, and an invertible stably free ideal is
principal. Hence $A[1/x]$, and therefore $A$, is a UFD.

## Depends on

- [Locally factorial schemes](locally-factorial-schemes.md)

## Proof depends on

- [A regular local ring is an integral domain](../../../nonsingular-varieties/regular-local-ring-domain.md)
- [Localizations of regular local rings](../../differentials/kaehler-differentials/regular-localization.md)
- [Finitely generated modules over a regular local ring](../../../cohomology/ext-groups/homological-dimension/regular-local-finite-module-projective-dimension.md)
- [Regular hypersurface quotients of a regular local ring](../../differentials/canonical-bertini/regular-hypersurface-local-criterion.md)
- Matsumura [2], Theorem 48, p.142, as cited by Hartshorne.

## Sources

- [Hartshorne II.6, Remark 6.11.1A on printed p.142](../../../../sources/hartshorne-ii-6.md#external-source-obligations)
