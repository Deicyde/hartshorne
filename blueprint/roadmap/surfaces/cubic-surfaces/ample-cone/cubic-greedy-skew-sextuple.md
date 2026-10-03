---
declaration: theorem
origin: cited
source_units: [chapter-v-section-4]
---

# The greedy skew-sextuple marking

Suppose a divisor `D` has positive intersection with every line on the marked
cubic surface.  Choose `E'_6` with minimum `D`-intersection, then choose
`E'_5` with minimum intersection among the lines skew to `E'_6`, and choose
`E'_4,E'_3` similarly.  Of the three lines remaining skew to these four, take
the two which are mutually skew as `E'_1,E'_2`, ordered so that
`D.E'_1>=D.E'_2`.  In the blowup marking for which this ordered sextuple is
`E_1,...,E_6`, write

`D ~ a*l-sum_i b_i*e_i`.

Then

`b_1 >= b_2 >= ... >= b_6 > 0`

and

`a-b_1-b_2 >= b_3`, hence `a>=b_1+b_2+b_5`.

## Depends on

- [Six mutually skew lines give another plane blowup marking](../lines/six-skew-lines-blowdown.md)
- [The incidence configuration of the twenty-seven lines](../lines/twenty-seven-lines-incidence-configuration.md)
- [The cubic-surface intersection lattice](../construction/cubic-surface-intersection-lattice.md)

## Proof depends on

- The line `F_12` is available as a candidate when the third line is chosen,
  so minimality gives `D.F_12>=D.E_3`.

## Sources

- [Hartshorne V.4, completion of the proof of Theorem 4.11, p.406](../../../../sources/hartshorne-v-4.md)
