---
article_id: af_839950afb5ef3e558ee775a5
declaration: theorem
origin: cited
source_units: [chapter-iii-section-10]
---

# Kleiman's general-translate theorem

Let `X` be a homogeneous space for a group variety `G` over an algebraically
closed field of characteristic zero. For morphisms from nonsingular varieties
`Y -> X` and `Z -> X`, there is a nonempty open `V subset G` such that for
every `sigma : V(k)`, the fibre product `Y^sigma times_X Z` is nonsingular and
either empty or has dimension exactly

`dim Y + dim Z - dim X`.

In the nonempty case the dimension formula implies
`dim Y + dim Z >= dim X`; all finitely many connected components have that
dimension.

## Depends on

- [The homogeneous action family is smooth](homogeneous-action-family-smooth.md)
- [Fibres of the general-translate incidence scheme](general-translate-incidence-fiber.md)
- [Generic smoothness for finitely many regular components](generic-smoothness-finite-components.md)
- [Smoothness and regularity over an algebraically closed field](criteria/smooth-over-algebraically-closed-iff-regular.md)

## Proof depends on

- Apply generic smoothness to the incidence projection `W -> G`, then identify
  its fibres with translated intersections.

## Sources

- [Hartshorne III.10, Theorem 10.8, pp.273–274](../../../sources/hartshorne-iii-10.md#homogeneous-spaces-kleiman-and-bertini-pp272275)
- [Kleiman, general-translate transversality (1974)](../../../sources/hartshorne-iii-10.md#homogeneous-spaces-kleiman-and-bertini-pp272275)
