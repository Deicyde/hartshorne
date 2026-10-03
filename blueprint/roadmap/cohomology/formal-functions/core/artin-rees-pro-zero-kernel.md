---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# The Artin–Rees kernel system is pro-zero

Let `A` be Noetherian, let `a` be an ideal, and let `R` be a finite submodule
of a finite `A`-module `E`. Define

`K_n = (R intersect a^(n+1) E) / a^(n+1) R`.

For every `n`, there is `n' >= n` such that the transition map
`K_(n') -> K_n` is zero. Consequently `lim K_n = 0`, and the same conclusion
holds for the associated coherent kernel sheaves on a quasi-compact
Noetherian scheme, for a coherent ambient module and a coherent ideal sheaf.

The pro-zero assertion is the unique main result. It is stronger than merely
having zero intersection of all powers.

## Depends on

- [The Artin–Rees induced topology theorem](../../affine-cohomology/artin-rees-induced-topology.md)
- [Inverse systems and the Mittag–Leffler condition](../../../schemes/formal-schemes/inverse-systems/inverse-system-mittag-leffler.md)

## Proof depends on

- Artin–Rees gives, for every `n`, an `n'` with
  `R intersect a^(n'+1)E <= a^(n+1)R`.
- A finite affine cover makes the sheafwise choice of `n'` uniform.

## Sources

- [Hartshorne III.11, final Artin–Rees step in Theorem 11.1, p.279](../../../../sources/hartshorne-iii-11-12.md#infinitesimal-fibres-and-formal-functions-pp276279)
