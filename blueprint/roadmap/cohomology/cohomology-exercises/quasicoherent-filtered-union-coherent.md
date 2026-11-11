---
article_id: af_a5beb3c9ba1e532bb2a22aaa
declaration: theorem
origin: cited
lean: Hartshorne.isFiltered_coherentSubobject_and_nonempty_isColimit Hartshorne.CoherentSubobject Hartshorne.coherentSubobjectCocone Hartshorne.exists_coherentSubobject_mem_range
statement: formalized
proof: formalized
---

# Quasi-coherent sheaves are filtered unions of coherent subsheaves

Let $X$ be a Noetherian scheme. Then any quasi-coherent $\mathcal{O}_X$-module
$F$ is the union of its coherent subsheaves: for every open $U \subseteq X$,
every section of $F$ over $U$ is a section of some coherent subsheaf of $F$.
Equivalently, the coherent subsheaves of $F$ form a filtered system whose
colimit is $F$.

## Depends on

- [Noetherian schemes and finite affine covers](../../schemes/first-properties/noetherian-scheme.md)

## Proof depends on

- [The affine-local criterion for coherence](../../schemes/modules-and-quasicoherent/coherent-affine-local-criterion.md)
- [Abelian closure of quasi-coherent sheaves](../../schemes/modules-and-quasicoherent/quasicoherent-abelian-closure.md)
- [Extension of coherent sheaves](../../schemes/coherent-sheaves/coherent-extension.md)

## Sources

- [Hartshorne II.5, Exercise 5.15(e), p.127](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
- [Its use in Hartshorne III, Exercise 4.8(a)](../../../sources/hartshorne-iii-3-4.md#adopted-exercises-and-later-use)
