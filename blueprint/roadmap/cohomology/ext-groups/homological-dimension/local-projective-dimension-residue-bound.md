---
article_id: af_25e490d6392f90bdc61e56b0
declaration: theorem
origin: background
---

# Projective dimension over a local ring is bounded by that of the residue field

Let $(A, \mathfrak m, k)$ be a Noetherian local ring and let $n \ge 0$ be an
integer with $\operatorname{pd}_A(k) \le n$. Then every finitely generated
$A$-module $M$ has $\operatorname{pd}_A(M) \le n$.

By the Ext criterion for projective dimension it suffices to show
$\operatorname{Ext}^i_A(M, L) = 0$ for all $i > n$ and all finitely generated
$A$-modules $L$. The hypothesis gives this vanishing for $M = k = A/\mathfrak m$.
Since $M$ has a finite filtration whose quotients are of the form
$A/\mathfrak q$ with $\mathfrak q$ prime, and the vanishing passes through
short exact sequences, it suffices to treat $M = A/\mathfrak q$. Argue by
descending induction on $\mathfrak q$. If $\mathfrak q \ne \mathfrak m$, choose
$x \in \mathfrak m \setminus \mathfrak q$. Multiplication by $x$ gives a short
exact sequence
$0 \to A/\mathfrak q \xrightarrow{x} A/\mathfrak q \to A/(\mathfrak q + xA) \to 0$,
and $A/(\mathfrak q + xA)$ is filtered by quotients $A/\mathfrak q'$ with
$\mathfrak q' \supsetneq \mathfrak q$, for which the vanishing holds by
induction. The long exact Ext sequence then shows that multiplication by $x$
is surjective on the finitely generated module
$\operatorname{Ext}^i_A(A/\mathfrak q, L)$ for $i > n$, so this module
vanishes by Nakayama's lemma.

## Depends on

- [Projective-dimension bounds detected by Ext](projective-dimension-ext-criterion.md)

## Proof depends on

- Prime filtrations of finitely generated modules over a Noetherian ring,
  finiteness of Ext between finitely generated modules, and Nakayama's lemma.
- For a finitely generated module $M$ over a Noetherian ring, vanishing of
  $\operatorname{Ext}^{n+1}_A(M, L)$ for every finitely generated $L$ already
  gives $\operatorname{pd}_A(M) \le n$.
- Matsumura, *Commutative Ring Theory*, §19 (the global dimension of a
  Noetherian local ring is $\operatorname{pd}_A(k)$).

## Sources

- [Hartshorne II.8, Theorem 8.14A, printed p.177](../../../../sources/hartshorne-ii-8.md#nonsingular-varieties-and-bertini):
  Hartshorne does not state this result; it is a step in Serre's proof of the
  localization theorem for regular local rings, which Hartshorne cites there.
- [Hartshorne III.6, Proposition 6.11A, printed p.237](../../../../sources/hartshorne-iii-6.md#quoted-homological-algebra-printed-pp236237):
  together with the computation of $\operatorname{pd}_A(k)$ it gives the
  finitely generated case of the bound in Proposition 6.11A(a).
