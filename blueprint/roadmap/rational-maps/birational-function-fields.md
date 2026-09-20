---
article_id: af_35d6b1a76e6551ec3a67f837
declaration: theorem
origin: cited
source_units: [chapter-i-section-4]
statement: formalized
proof: formalized
lean: Hartshorne.birational_iff_nonempty_functionField_algEquiv
---

# Birational varieties have isomorphic function fields

For separated varieties `X` and `Y` carrying affine-open-basis witnesses, the
following are equivalent:

- `X` and `Y` are birationally equivalent;
- `K(X) ≃ₐ[k] K(Y)`.

A birational map and its inverse induce inverse pullbacks on function fields.
In the other direction, an algebra equivalence and its inverse correspond by
Theorem 4.4 to dominant rational maps in opposite directions.  Faithfulness of
that correspondence turns the two inverse identities on function fields into
the two inverse identities of rational maps.

This is the function-field `(i) ⇔ (iii)` part of Corollary 4.5.

## Depends on

- [Birational maps](birational-map.md)
- [Rational maps and function fields](rational-map-function-field.md)

## Proof depends on

- [The function field is functorial for dominant morphisms](../morphisms/function-field-functorial.md)

## Sources

- [Hartshorne I.4, Corollary 4.5 (p. 26)](../../sources/hartshorne.md#i4)
