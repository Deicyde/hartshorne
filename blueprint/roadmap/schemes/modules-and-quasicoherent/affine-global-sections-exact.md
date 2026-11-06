---
article_id: af_305fb0c8dc6dbf812dd169a5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.affine_globalSections_shortExact Hartshorne.modulesGlobalSections
---

# Exactness of affine global sections

Let $X$ be affine and let
$0 \longrightarrow F' \longrightarrow F \longrightarrow F'' \longrightarrow 0$ be an exact sequence of $\mathcal{O} _X$-modules.  If $F'$
is quasi-coherent, then

$0 \longrightarrow \Gamma (X,F') \longrightarrow \Gamma (X,F) \longrightarrow \Gamma (X,F'') \longrightarrow 0$

is exact.  This is Proposition 5.6; unlike the later affine-vanishing theorem,
it does not assume that $F$ or $F''$ is quasi-coherent.

## Depends on

- [Sheaves of modules](sheaves-of-modules.md)
- [Quasi-coherence by local presentations](quasicoherent-local-presentations.md)

## Proof depends on

- [Quasi-coherent sections on principal opens](quasicoherent-principal-open-localization.md)
- [Global sections are left exact](../sheaf-functors/global-sections-left-exact.md)
- Lift the target section on finitely many principal opens, multiply by common
  powers to make the lifts glue, and use a unit-ideal combination of those
  powers to obtain a global lift.

## Sources

- [Hartshorne II.5, Proposition 5.6 on printed pp. 113–114](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
