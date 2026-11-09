---
article_id: af_a1e3f0fa0e273a17ac6a5d1c
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.SerreRegularity.isRegularLocalRing_of_hasProjectiveDimensionLE
---

# Serre's criterion for regularity

Let $(A, \mathfrak m, k)$ be a Noetherian local ring such that
$\operatorname{pd}_A(k) < \infty$. Then $A$ is a regular local ring.

The proof is by induction on an integer $n$ with $\operatorname{pd}_A(k) \le n$.
If $n = 0$, then $k$ is projective, hence free, so $\mathfrak m = 0$ and $A$ is a
field. In general, if $\mathfrak m = 0$ there is nothing to prove. If
$\mathfrak m$ is an associated prime of $A$, a minimal free presentation shows
that every finitely generated $A$-module of finite projective dimension is
free; in particular $k$ is free, so $\mathfrak m = 0$. Otherwise, by prime
avoidance there is a non-zero-divisor $x \in \mathfrak m \setminus \mathfrak m^2$.
Put $\bar A = A/xA$. The change of rings for projective dimension gives
$\operatorname{pd}_{\bar A}(\mathfrak m/x\mathfrak m) < n$, and since
$x \notin \mathfrak m^2$ the residue field $k$ of $\bar A$ is a direct summand of
$\mathfrak m/x\mathfrak m$. Hence $\operatorname{pd}_{\bar A}(k) < n$, so $\bar A$
is regular by induction, and then $A$ is regular because $x$ is a
non-zero-divisor in $\mathfrak m$.

## Depends on

- [Regular local rings](../../../nonsingular-varieties/regular-local-rings.md)
- [Projective-dimension bounds detected by Ext](projective-dimension-ext-criterion.md)

## Proof depends on

- [Lifting regularity from a regular hypersurface quotient](../../../schemes/differentials/local-complete-intersections/regular-local-lift-from-regular-quotient.md)
- Prime avoidance, minimal free presentations over a local ring, and the
  change of rings $\operatorname{pd}_{A/xA}(N/xN) \le \operatorname{pd}_A(N)$
  for a non-zero-divisor $x$ on $A$ and on $N$.
- Matsumura, *Commutative Ring Theory*, Theorem 19.2 (Serre's theorem).

## Sources

- [Hartshorne II.8, Theorem 8.14A, printed p.177](../../../../sources/hartshorne-ii-8.md#nonsingular-varieties-and-bertini):
  Hartshorne does not state this criterion; it is the second half of Serre's
  proof of the localization theorem for regular local rings, which Hartshorne
  cites there from Matsumura [2], p.139.
