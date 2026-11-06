---
article_id: af_698047ca13215ffae1ff86c3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.projectiveLine_principalPartsResolution
---

# The principal-parts resolution on $\mathbb{P}^{1}$

Let $X=\mathbb{P}^{1}$ over an algebraically closed field, $K$ its function field, and
$K_X$ the constant sheaf. There is a natural short exact sequence

$0\longrightarrow\mathcal{O}_X\longrightarrow K_X\longrightarrow\bigoplus_{P\in X}i_{P,*}\left(K/\mathcal{O}_{X,P}\right)\longrightarrow0$,

and the final map is surjective on global sections. The unique main result is
this augmented principal-parts resolution, including global surjectivity.

## Depends on

- [The constant sheaf](../../schemes/sheaves/constant-sheaf.md)
- [Skyscraper and closed extension by zero](../../schemes/sheaf-functors/closed-extension-by-zero.md)
- [The function field of a projective variety](../../morphisms/projective-rings/projective-function-field.md)

## Proof depends on

- [Exactness is detected on stalks](../../schemes/sheaves/stalkwise-exactness.md)

## Sources

- [Hartshorne II.1.21(d,e), adopted for III.2 Exercise 2.2](../../../sources/hartshorne-iii-1-2.md#adopted-exercises-printed-pp-212213)
