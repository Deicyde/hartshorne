---
article_id: af_58bc07c9d789c1d638b2c07f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.isRegularLocalRing_iff_free_kaehlerDifferential Hartshorne.free_of_finrank_residueField_eq_finrank_fractionField Hartshorne.free_kaehlerDifferential_of_isRegularLocalRing Hartshorne.isRegularLocalRing_of_free_kaehlerDifferential Hartshorne.free_kaehlerDifferential_of_isRegularLocalRing_of_isDomain Hartshorne.finrank_cotangentSpace_eq_finrank_residueField_tensor_kaehlerDifferential Hartshorne.exists_ringKrullDim_eq_trdeg_of_essFiniteType
---

# The regular-local differential criterion

Let $(B, \mathfrak{m})$ be a local ring containing a field $k$ such that
$k \to B/\mathfrak{m}$ is an isomorphism. Assume that $k$ is perfect and that
$B$ is a localization of a finitely generated $k$-algebra. Then
$\Omega_{B/k}$ is a free $B$-module of rank $\dim B$ if and only if $B$ is a
regular local ring.

As a supporting lemma, prove Hartshorne 8.9: if a finite module over a
Noetherian local domain has the same finite dimension $r$ after tensoring with
the residue field and the fraction field, then it is free of rank $r$.

The rank must be $\dim B$ itself: it is not enough that $\Omega_{B/k}$ be free
of some rank $r$. For example, if $k$ is perfect of characteristic $p>0$ and
$B=k[x]/(x^p)$, a finitely generated local $k$-algebra with residue field $k$, then $d(x^p)=0$, so $\Omega_{B/k}=B\,dx$ is free of rank $1$,
while $\dim B=0$ and $\dim_k(\mathfrak m/\mathfrak m^2)=1$, so $B$ is not
regular.

If $\Omega_{B/k}$ is free of rank $\dim B$, then
$\dim_k(\mathfrak m/\mathfrak m^2)=\dim_k(\Omega_{B/k}\otimes_B k)=\dim B$ by
the local cotangent comparison, so $B$ is regular. Conversely, let $B$ be
regular of dimension $r$. Then $B$ is a domain, and
$\Omega_{B/k}\otimes_B k$ has dimension $r$. If $K$ is the quotient field of
$B$, then $\Omega_{B/k}\otimes_B K=\Omega_{K/k}$; since $k$ is perfect, $K$ is
separably generated over $k$, so this has dimension
$\operatorname{trdeg}_k K$. Write $B$ as the localization of a finitely
generated $k$-algebra $A$ that is a domain at a prime $\mathfrak p$. The
condition $B/\mathfrak m\cong k$ makes $\mathfrak p$ maximal, and Theorem
I.1.8A gives
$\dim B=\operatorname{ht}\mathfrak p=\dim A=\operatorname{trdeg}_k K=r$.
Since $\Omega_{B/k}$ is a finite $B$-module, Lemma 8.9 makes it free of rank
$r$.

## Depends on

- [Finiteness of differentials](finite-type-differentials-finite.md)
- [Differentials of finitely generated field extensions](field-differentials-dimension.md)
- [The local cotangent space via differentials](local-cotangent-via-differentials.md)
- [Regular local rings](../../../nonsingular-varieties/regular-local-rings.md)

## Proof depends on

- [A regular local ring is an integral domain](../../../nonsingular-varieties/regular-local-ring-domain.md)
- [Dimension of a finitely generated domain](../../../affine-varieties/dim-fg-domain.md)
- [The dimension formula for a finitely generated domain](../../../affine-varieties/dim-formula-catenary.md)
- Perfectness makes the fraction field separably generated over $k$.
- Nakayama's lemma and localization into the fraction field.

## Sources

- [Hartshorne II.8, Theorem 8.8 and Lemma 8.9, printed pp. 174–175](../../../../sources/hartshorne-ii-8.md)
