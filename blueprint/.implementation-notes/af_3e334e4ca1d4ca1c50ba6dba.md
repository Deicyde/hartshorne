# The zero scheme of a section of a locally free sheaf

## Partial progress

The module `Hartshorne.Intersection.SectionZeroScheme` (sorry-free, axioms only
`propext`, `Classical.choice`, `Quot.sound`; not recorded in the article
frontmatter) gives the module-level part of the definition, for any
$\mathcal{O}_X$-module $E$ and global section $s$:

- `Hartshorne.sectionDualMap s : Ringed.moduleSheafDual (R := X.sheaf) E ⟶ Ringed.structureModule X.sheaf`, the dual
  map $s^\vee : E^\vee \to \mathcal{O}_X$, $\psi \mapsto \psi(s|_U)$ on an open
  $U$. Its formula is `Hartshorne.sectionDualMap_app`.
- `Hartshorne.sectionDualImage s` (an object of `SheafOfModules (ringCatSheafOf X.sheaf)`, as is `Hartshorne.sectionDualCokernel s`) and the monomorphism
  `Hartshorne.sectionDualImageι s` into $\mathcal{O}_X$: the image
  $\operatorname{image}(s^\vee)$ (abelian image in the category of
  $\mathcal{O}_X$-modules), with `Hartshorne.sectionDualMap_factor`.
- `Hartshorne.sectionDualCokernel s`, the cokernel
  $\mathcal{O}_X/\operatorname{image}(s^\vee)$.

## Blocker

To define $Z(s)$ as a closed subscheme one must turn the ideal subsheaf
$\operatorname{image}(s^\vee) \hookrightarrow \mathcal{O}_X$ into Mathlib's
`Scheme.IdealSheafData` (affine ideals $I(U)$ with
$I(D(f)) = I(U)_f$), then take `IdealSheafData.subscheme`. Two pieces are
missing:

1. The bridge from quasi-coherent ideal subsheaves to `IdealSheafData`: the
   article `schemes/coherent-sheaves/module-ideal-sheaf-data`
   (af_8763f99884b849b82e0825eb) is still planned, with no Lean. Proving the
   basic-open compatibility for this one ideal is the same work (quasi-coherence
   of the image on affine opens plus the tilde description of its sections).
2. Quasi-coherence of $E^\vee$ (or directly of the image) for $E$ locally free
   of finite rank. The project has `Hartshorne.isQuasicoherent_image`
   (reachable through module-ideal-sheaf-data), but not "locally free implies
   quasi-coherent" nor "the dual of a finite locally free module is locally
   free". The dependency list does not reach an article providing these.

## Next route

Once the bridge exists: show `(Ringed.moduleSheafDual (R := X.sheaf) E).IsQuasicoherent` for finite
locally free $E$ (the dual frames `IsLocalFrame.dual` give local freeness of
$E^\vee$; a free module of finite rank is quasi-coherent), so the image is
quasi-coherent by `isQuasicoherent_image`; apply the bridge to
`sectionDualImageι s` to get the `IdealSheafData` $\mathcal{I}_s$; define
$Z(s) = \mathcal{I}_s$`.subscheme` with closed immersion `subschemeι`. The
"equivalently" clause is then `ker_subschemeι` (the ideal of $Z(s)$ is
$\mathcal{I}_s$) together with the bridge's identification of $\mathcal{I}_s$
with $\operatorname{image}(s^\vee)$, i.e. the exactness of
$E^\vee \to \mathcal{O}_X \to i_*\mathcal{O}_{Z(s)} \to 0$. The associated cycle
is `Hartshorne.closedSubschemeFundamentalCycle` of `subschemeι`, which needs
`[IsNoetherian X]` and a codimension index $r$.

A route avoiding the general bridge: on an open $W$ with a frame
$e_1,\dots,e_r$ of $E$ and $s|_W=\sum a_i e_i$, the image of $s^\vee$ on every
open $V\subseteq W$ is the ideal $(a_1|_V,\dots,a_r|_V)$. One can define $I(U)$
for affine $U$ as the sections of $\mathcal{O}_X$ lying locally in these ideals
and prove $I(D(f)) = I(U)_f$ directly (partition of unity on $U$ for the
finitely generated local ideals, then gluing after multiplying by a power of
$f$). This is essentially the bridge specialized to locally finitely generated
ideals.
