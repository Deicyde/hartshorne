---
article_id: af_fc163557346aca575b9a0fd2
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.projRatClass_mem_localRingRange_iff
---

# Membership of a homogeneous fraction in a local ring

Let $Y$ be a quasi-projective variety, let $P\in Y$, and let $g,h$ be
homogeneous polynomials of the same degree whose fraction defines a class
$[g/h]\in K(Y)$. If $g(P)\ne 0$, then

$$[g/h]\in\mathcal{O}_{P,Y}\quad\Longleftrightarrow\quad h(P)\ne 0,$$

where the local ring is viewed inside $K(Y)$ through its canonical injection.

The forward direction says that a fraction with a nonvanishing numerator
and a vanishing denominator cannot represent a regular germ at $P$. For
the reverse direction, $g/h$ is regular on the projective open where $h$
is nonzero. The hypothesis $g(P)\ne 0$ rules out cancellation and is
essential for the equivalence.

## Depends on

- [The function field of a projective variety](../morphisms/projective-rings/projective-function-field.md)
- [Global regular functions are the intersection of the local rings](../morphisms/global-functions/global-regular-intersection-local-rings.md)

## Proof depends on

No additional project-local proof prerequisites.

## Sources

- [Hartshorne I.6, proof of Lemma 6.4 (p. 41)](../../sources/hartshorne.md#i6-local-structure-and-point-separation)
