---
article_id: af_dc6feac9cb3e2d0a0bbd53e9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.supportedSectionsMap Hartshorne.mayerVietorisSC_mono_f Hartshorne.mayerVietorisSC_exact Hartshorne.mayerVietorisSC_shortExact_of_isFlasque Hartshorne.cohomologyWithSupportsBiprod Hartshorne.mayerVietorisι Hartshorne.mayerVietorisπ Hartshorne.mayerVietorisδ Hartshorne.mayerVietorisι_mono Hartshorne.mayerVietoris_exact₂ Hartshorne.mayerVietoris_exact₃ Hartshorne.mayerVietoris_exact₁
---

# Mayer–Vietoris with supports

For closed subsets $Y_{1},Y_{2} \subseteq X$ and an abelian sheaf $F$, there is a natural
long exact sequence

$$
\cdots\longrightarrow H^n_{Y_1\cap Y_2}(X,F)
\longrightarrow H^n_{Y_1}(X,F)\oplus H^n_{Y_2}(X,F)
\longrightarrow H^n_{Y_1\cup Y_2}(X,F)
\longrightarrow H^{n+1}_{Y_1\cap Y_2}(X,F)\longrightarrow\cdots.
$$

The supporting input is the natural exact sequence of closed-
support functors

$0 \longrightarrow \Gamma _{Y_{1}\cap Y_{2}} \longrightarrow \Gamma _{Y_{1}} \oplus \Gamma _{Y_{2}} \longrightarrow \Gamma _{Y_{1}\cup Y_{2}}$,

with the sign convention chosen so consecutive maps compose to zero.

## Depends on

- [The localization sequence for cohomology with supports](cohomology-with-supports.md)

## Proof depends on

- [The long exact sequence of right derived functors](../derived-functors/right-derived-long-exact-sequence.md)
- Exactness of the displayed natural sequence of support functors.

## Sources

- [Hartshorne III.2, Exercise 2.4, printed p. 212](../../../sources/hartshorne-iii-1-2.md#adopted-exercises-printed-pp-212213)
