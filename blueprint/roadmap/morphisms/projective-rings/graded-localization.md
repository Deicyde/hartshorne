---
article_id: af_90818c4c3f8c5cdc256259f3
declaration: abbrev
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.gradedLocalization Hartshorne.gradedLocalizationAway
---

# Graded localization

Let $S$ be a graded ring and let $\mathfrak p$ be a homogeneous prime.
Invert the homogeneous elements outside $\mathfrak p$ and give a
homogeneous fraction the degree

$$\deg(a/b)=\deg a-\deg b.$$

The degree-zero part is denoted $S_{(\mathfrak p)}$. It is a local ring
whose maximal ideal is the contraction of $\mathfrak p$ from the graded
localization. If $S$ is a domain, $S_{((0))}$ is a field: the inverse of a
nonzero degree-zero fraction $a/b$ is $b/a$.

For a homogeneous element $f$, write $S_{(f)}$ for the degree-zero part
of $S_f$. If $f$ has degree one and $f\notin\mathfrak p$, then

$$S_{(\mathfrak p)}\cong(S_{(f)})_{\mathfrak q},$$

where $\mathfrak q$ is the contraction of the maximal ideal. A fraction
$g/f^n$ belongs to $\mathfrak q$ exactly when $g\in\mathfrak p$.
Degree one is essential to rewriting fractions with a power of $f$ in
the denominator. Homogeneity of $\mathfrak p$ allows any required
annihilating scalar to be replaced by a homogeneous component outside
$\mathfrak p$.

When $S$ is a domain and $\mathfrak p=(0)$, this identifies $S_{((0))}$
with the fraction field of $S_{(f)}$.

## Depends on

- [Homogeneous ideals](../../projective-varieties/homogeneous-ideal.md)
- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)

## Sources

- [Hartshorne I.3, definition of $S_{(\mathfrak p)}$ and $S_{(f)}$ (p. 18)](../../../sources/hartshorne.md#i3)
