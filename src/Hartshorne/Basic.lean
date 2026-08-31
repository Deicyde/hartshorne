/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Conventions

Hartshorne, *Algebraic Geometry*, Chapter I.

Hartshorne fixes an algebraically closed field `k` for the whole of Chapter I
and leaves that hypothesis implicit in every statement. A Lean development
cannot, so each result carries the hypotheses it actually needs: `[Field k]`
throughout, `[IsAlgClosed k]` only where algebraic closedness is used, and
`[Finite σ]` only where the polynomial ring must be Noetherian or the
Nullstellensatz is invoked. Keeping them separate records which parts of the
chapter survive over a general field, which is information the book discards.

Affine `n`-space is the function type `σ → k`. Taking an arbitrary index type
rather than `Fin n` costs nothing and matches `MvPolynomial`, which this
development builds on.
-/

namespace Hartshorne

/-- Affine `σ`-space over `k`. For `σ = Fin n` this is Hartshorne's `𝔸ⁿ`.

This is reducible: it is a readability device for statements, not a new type,
and every lemma about function types applies to it unchanged. -/
abbrev AffineSpace (k σ : Type*) : Type _ := σ → k

end Hartshorne
