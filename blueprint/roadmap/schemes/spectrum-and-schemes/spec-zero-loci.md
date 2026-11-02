---
article_id: af_9bae5c6b234e1ce731b2c015
declaration: instance
origin: cited
mathlib: true
mathlib_declaration: PrimeSpectrum.zariskiTopology
mathlib_file: Mathlib/RingTheory/Spectrum/Prime/Topology.lean
---

# The Zariski topology on Spec

For a commutative ring $A$, let $\operatorname{Spec} A$ be its prime ideals and
$V(\mathfrak{a} ) = \{\mathfrak{p} | \mathfrak{a} \le \mathfrak{p} \}$.  The identities
$V(\mathfrak{a} \mathfrak{b} ) = V(\mathfrak{a} ) \cup V(\mathfrak{b} )$ and $V(\bigcup i, \mathfrak{a} i) = \bigcap i, V(\mathfrak{a} i)$ make these sets the
closed sets of a topology.  Moreover,
$V(\mathfrak a)\subseteq V(\mathfrak b)\quad\Longleftrightarrow\quad\mathfrak b\subseteq\sqrt{\mathfrak a}$, and the principal opens $D(f)$ form a basis.

## Depends on

- Nothing in this roadmap.

## Sources

- [Hartshorne II.2, Lemma 2.1 and the following basis observation (p. 70)](../../../sources/hartshorne-ii-2.md#opening-and-lemma-21)
