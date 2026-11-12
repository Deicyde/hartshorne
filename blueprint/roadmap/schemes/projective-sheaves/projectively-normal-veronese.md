---
article_id: af_b83793cbddc5ebfa01ddcafe
declaration: theorem
origin: cited
lean: Hartshorne.ProjectivelyNormalVeronese.exists_isProjectivelyNormal_image_projDupleMap Hartshorne.ProjectivelyNormalVeronese.exists_isProjectivelyNormal_projDupleEmbedding_of_saturated Hartshorne.ProjectivelyNormalVeronese.exists_isIntegrallyClosed_veroneseSubring Hartshorne.ProjectivelyNormalVeronese.exists_mem_algebraMap_eq_sectionToFraction Hartshorne.ProjectivelyNormalVeronese.isIntegrallyClosed_veroneseSubring Hartshorne.ProjectivelyNormalVeronese.projDupleMap Hartshorne.ProjectivelyNormalVeronese.projDupleEmbedding Hartshorne.ProjectivelyNormalVeronese.projQuotientι_comp_projDupleMap Hartshorne.ProjectivelyNormalVeronese.projDupleEmbedding_eq Hartshorne.ProjectivelyNormalVeronese.dupleIdeal Hartshorne.ProjectivelyNormalVeronese.dupleQuotientEquiv
statement: formalized
proof: formalized
---

# Projectively normal Veronese embeddings

Let $k$ be algebraically closed and let $X \subseteq \mathbb{P}^r_{k}$ be connected and normal.
For all sufficiently large $d$, the $d$-uple embedding of $X$ is projectively
normal.

The proof first uses eventual recovery to show equality between the
homogeneous coordinate ring and its integral-closure section ring in all
sufficiently large degrees, then passes to a sufficiently high Veronese
subring.

## Depends on

- [Normal schemes](../normalization-and-exercises/normal-scheme.md)
- [The projective-normality criterion](projective-normality-criterion.md)

## Proof depends on

- [The projective section ring is the integral closure](projective-section-ring-integral-closure.md)
- [Eventual recovery from graded sections](proj-eventual-section-recovery.md)
- [Veronese Proj and twists](veronese-proj-twist.md)
- [Saturation of projective ideals](projective-ideal-saturation.md)
- A sufficiently high Veronese subring of a graded normal domain is normal.

## Sources

- [Hartshorne II.5, Exercise 5.14(b,c) (p.126)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
