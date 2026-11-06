---
article_id: af_e7796a770635c750fe8f5d98
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.flat_iff_isSMulRegular_and_flat_quotSMulTop
---

# The non-zero-divisor local criterion for flatness

Let $A \to B$ be a local homomorphism of Noetherian local rings, let $M$ be a
finite $B$-module, and let $t$ be a nonunit and non-zero-divisor of $A$. Then
$M$ is flat over $A$ if and only if multiplication by $t$ is injective on $M$
and $M/tM$ is flat over $A/tA$.

The hypothesis that $A$ is local is kept as in the source but is not needed in
the proof: because $A \to B$ is a local homomorphism, the nonunit $t$ already
maps into the maximal ideal of $B$.

## Depends on

- [The finitely generated ideal criterion for flatness](../flat-families/flatness/flat-module-fg-ideal-criterion.md)

## Proof depends on

- The local criterion of flatness in Bourbaki, *Algèbre commutative*, III §5,
  or Altman–Kleiman V §3, as adopted in the source notes.

## Sources

- [Hartshorne III.10, Lemma 10.3A, p.270](../../../sources/hartshorne-iii-10.md#tangent-criterion-pp270271)
