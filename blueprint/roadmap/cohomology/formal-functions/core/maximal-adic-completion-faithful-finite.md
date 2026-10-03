---
declaration: theorem
origin: background
source_units: [chapter-iii-sections-11-12]
---

# Faithfulness of maximal-adic completion on finite modules

Let `(A,m)` be a Noetherian local ring and let `u : M -> N` be a map of
finite `A`-modules. If the induced map on maximal-adic completions is
surjective, then `u` is surjective. In particular, if the completion of a
finite module `M` is zero, then `M=0`.

The unique main result is reflection of surjectivity. Reflection of zero is
its cokernel specialization and is the form used after formal functions.

## Depends on

- [Adic completion of rings and modules](../../../schemes/formal-schemes/adic-completion/adic-completion.md)
- [Exactness of finite-module completion](../../../schemes/formal-schemes/adic-completion/finite-module-completion-exact.md)
- [Finite-module completion as tensor product](../../../schemes/formal-schemes/adic-completion/finite-module-completion-tensor.md)

## Proof depends on

- Exact completion identifies the completed cokernel of `u` with the
  cokernel of the completed map.
- Reduction of a zero completion modulo `m` gives `Q/mQ=0`; Nakayama's lemma
  gives `Q=0` for the finite cokernel `Q`.

## Sources

- [Hartshorne III.12, faithful-completion step in Proposition 12.10, pp.289–290](../../../../sources/hartshorne-iii-11-12.md#semicontinuity-grauert-and-base-change-pp287291)
