---
article_id: af_575e619ae8ec073c42a7444a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.isClosed_eqLocus Hartshorne.eq_of_eqOn_isOpen
---

# Regular functions are continuous

A regular function $f : Y \to k$ is continuous when $k$ carries the Zariski
topology of $\mathbb{A} ^{1}$ (Lemma 3.1). Consequently, if two regular functions on a
variety agree on some nonempty open subset then they agree everywhere
(Remark 3.1.1).

Hartshorne's proof has two steps. First, closedness is local, and on an open $U$
where $f = g/h$ one has $f^{-1}(\{a\})\cap U=Z(g-ah)\cap U$, so every fibre is closed.
Second, the closed sets of $\mathbb{A} ^{1}$ are the finite sets, so closed fibres give
continuity.

The formalized result here is that the agreement locus of two regular
functions is closed, together with the identity principle. Continuity into
the Zariski topology on the base field is quoted above as Hartshorne's
source statement; that additional conclusion is not claimed as formalized
by this article. Every later use in §§1–3 is of the identity principle.

The identity principle carries far more weight than its proof suggests: it
establishes the quotient relations used for germs and rational functions and
shows that Hartshorne's whole-overlap germ relation agrees with the usual
near-a-point relation. Bundling the resulting maps as algebra embeddings and
proving the intersection theorem are separate work.

## Depends on

- [Regular functions on a quasi-affine variety](regular-function-quasi-affine.md)
- [Affine and quasi-affine varieties](../affine-varieties/affine-variety.md)

## Sources

- [Hartshorne I.3, Lemma 3.1 and Remark 3.1.1 (p. 15)](../../sources/hartshorne.md#i3)
