---
article_id: af_0bfcbd42273250dba6a2230e
declaration: theorem
lean: Hartshorne.openExtensionByZero_properties
statement: formalized
proof: formalized
origin: cited
---

# Restriction, stalks, and characterization of open extension by zero

Let $j : U \hookrightarrow X$ be an open immersion and $F$ a sheaf on $U$. There is a
canonical isomorphism

$r_F : j^*j_!F \cong F$.

The stalk of $j_!F$ is $F_{x}$ at every $x \in U$ and zero at every $x \notin U$.
Moreover, if a sheaf $G$ on $X$ has zero stalk outside $U$ and is equipped
with an isomorphism $\rho : j^*G \cong F$, there is a unique isomorphism
$e : j_!F \cong G$ satisfying

$$\rho\circ j^*(e)=r_F.$$

The fixed isomorphism $\rho$ and the displayed compatibility are essential:
without them, a nontrivial automorphism of $F$ contradicts uniqueness.

## Depends on

- [Open extension by zero](open-extension-by-zero.md)
- [Open extension by zero is left adjoint to restriction](open-extension-by-zero-adjunction.md)
- [Restriction preserves stalks](restriction-stalk.md)

## Proof depends on

- [Sheafification preserves stalks](../sheaves/associated-sheaf-stalks.md)
- [Isomorphisms are detected on stalks](../sheaves/stalkwise-isomorphism.md)

## Sources

- [Hartshorne II.1, Exercise 1.19(b), p. 68](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)
