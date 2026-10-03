# Zeta functions and the Weil conjectures

Hartshorne Appendix C defines the zeta function of a finite-type scheme over a
finite field, states the Weil theorem package, lists the étale–ℓ-adic interface,
and derives rationality and the functional equation from Frobenius traces and
Poincaré duality before quoting Deligne's weight theorem.

The fine roadmap has 69 leaves: one exact pinned-Mathlib foundation and 68
project targets. Sixteen leaves are explicitly marked not ready for a
representation or proof source. In particular, Mathlib's pro-étale `Z_ℓ`
construction is not treated
as the missing comparison with classical `Q_ℓ` cohomology. Hartshorne's
suppressed Tate twists, connectedness conditions, fixed-point transversality,
Frobenius convention, and good-reduction hypotheses are restored.

- [Zeta functions over finite fields](zeta/README.md)
- [Foundations of étale and ℓ-adic cohomology](etale-cohomology/foundations/README.md)
- [Formal properties of ℓ-adic cohomology](etale-cohomology/properties/README.md)
- [Comparison with singular cohomology](etale-cohomology/comparison/README.md)
- [Cycle classes](etale-cohomology/cycle-classes/README.md)
- [Frobenius and point counts](frobenius/README.md)
- [Linear-algebra identities](linear-algebra/README.md)
- [Cohomological deductions](deductions/README.md)
- [The Weil theorem package](weil/README.md)
- [The projective-line verification](examples/README.md)

Appendix C §2 is historical exposition and Exercises 5.1–5.7 have no later
consumer, so neither generates theorem leaves under the approved exercise
policy.

## Sources

- [Appendix C §1 source notes](../../sources/hartshorne-appendix-c-1.md)
- [Appendix C §3 source notes](../../sources/hartshorne-appendix-c-3.md)
- [Appendix C §4 source notes](../../sources/hartshorne-appendix-c-4.md)
