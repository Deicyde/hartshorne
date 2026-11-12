---
article_id: af_22776d0fa8f18f49063c6e2d
declaration: theorem
origin: cited
lean: Hartshorne.hasseWeilZetaSeries_projectiveLine
statement: formalized
proof: formalized
---

# The zeta function of the projective line

As both a formal series at the origin and its displayed rational
representative,

$Z(\mathbb{P}^1,t)=1/((1-t)\cdot (1-q\cdot t))$.

## Depends on

- [The formal Hasse–Weil zeta series](hasse-weil-zeta-formal-series.md)
- [The projective-line point count](projective-line-point-count.md)

## Proof depends on

- Use $\sum _{(r\ge 1)} a^r\cdot t^r/r=-\log (1-a\cdot t)$ in rational formal power series and
  exponentiate the contributions for $a=1$ and $a=q$.

## Sources

- [Hartshorne Appendix C.1, projective-line zeta calculation, p.450](../../../sources/hartshorne-appendix-c-1.md)
