---
article_id: af_c6bf0d8d37f0cc07eedc10f3
declaration: def
origin: cited
source_units: [chapter-i-section-6-normalization]
---

# Discrete valuation rings of a function field

Let `K/k` be a field extension.  Define the type `C_K` of discrete valuation
rings of `K/k` to consist of valuation subrings `R ⊆ K` such that `R` is a
discrete valuation ring and contains the image of `k`.

For a valuation subring, containing `k` is equivalent to its associated
valuation being trivial on every nonzero element of `k`; record that
equivalence so this definition interoperates with
`Valuation.IsTrivialOn`.  Also define the predicates that `x : K` has a pole
at `R`, meaning `x ∉ R`, and that `x` vanishes at `R`, meaning
`x ∈ 𝔪_R`.

Use valuation *subrings*, not chosen valuation maps: `C_K` identifies points
which have the same local ring, exactly as Hartshorne does.

## Depends on

No project-local statement prerequisites.

## Sources

- [Hartshorne I.6, definition of `C_K` and of valuation rings of `K/k` (pp. 39--42)](../../sources/hartshorne.md#i6-normalization-and-finite-poles)
