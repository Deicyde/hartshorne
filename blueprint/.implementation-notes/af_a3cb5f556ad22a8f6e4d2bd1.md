# Degree of an ambient hypersurface section

## Supporting implementation references

- `deg(V.X) = deg(V) * deg(X)`

## Status: blocked on a missing scheme-to-classical bridge

The scheme setting of the dependencies is: $\mathbb{P}^n_k = \operatorname{Proj} k[x_0,\dots,x_n]$,
$\iota : X \to \mathbb{P}^n_k$ a closed immersion with $X$ satisfying $(*)$, $V$ a prime divisor of
$\mathbb{P}^n_k$ with homogeneous equation $f$ of degree $d$, and degrees of points measured as the
projective degree of the classical zero set $Z(\mathfrak p)$ of the homogeneous prime. Bézout
(Theorem I.7.7) is stated for the classical projective variety $Y = Z(\mathfrak p_X)$, where
$\mathfrak p_X$ is the homogeneous prime of the image of the generic point of $X$, with
$i(Y,H;Z) = \operatorname{length}_{S_{\mathfrak P}} (S/(I(Y)+I(H)))_{\mathfrak P}$ for the full
(not homogeneous) localization at the homogeneous prime $\mathfrak P = I(Z)$.

### Checked partial results (module `Hartshorne.Scheme.ProjectiveIntersectionDegree`)

- The chosen equation $f$ of a prime divisor $V$ of $\mathbb{P}^n_k$ is a prime element, of positive
  degree.
- For $n \ge 1$ and $k$ algebraically closed, $\deg V = \deg f$.

### Missing prerequisites (each a genuine piece of mathematics)

1. Scheme-to-classical dictionary for an integral closed subscheme of $\mathbb{P}^n_k$ ($k$
   algebraically closed): $\iota$ is a homeomorphism onto the closure of $\iota(\eta)$, i.e. onto
   the relevant homogeneous primes containing $\mathfrak p_X$, preserving specialization; hence
   $\operatorname{coheight}_X(x)$ equals the length of chains of homogeneous primes between
   $\mathfrak p_X$ and $\mathfrak P_x$, and $\dim X = \dim Z(\mathfrak p_X)$. Together with the
   projective Nullstellensatz ($I(Z(\mathfrak p)) = \mathfrak p$, $I(Z(f)) = (f)$) and Krull's
   principal ideal theorem this identifies the prime divisors of $X$ contained in $V$ with the
   irreducible components of $Z(\mathfrak p_X) \cap Z(f)$, $Y \mapsto Z(\mathfrak P_Y)$, compatibly
   with degrees. The roadmap's planned article on closed subschemes of $\mathbb{P}^r_A$ defined by
   homogeneous ideals is related but not the same statement.
2. Local multiplicity comparison: for a prime divisor $Y$ of $X$ with homogeneous prime
   $\mathfrak P$, $\operatorname{ord}_Y(f/g|_X) = \operatorname{length}_{S_{\mathfrak P}}
   (S/(\mathfrak p_X + (f)))_{\mathfrak P}$. Ingredients: the stalk of $X$ at $Y$ is
   $S_{(\mathfrak P)}/(\mathfrak p_X)_{(\mathfrak P)}$ (kernel of the stalk map of the closed
   immersion of an integral scheme); the order in the discrete valuation ring is the length of
   $\mathcal O_{X,Y}/(f/g)$, which is the length of the degree-zero localization
   $(S/(\mathfrak p_X+(f)))_{(\mathfrak P)}$ over $S_{(\mathfrak P)}$; and for a graded module $M$
   and a relevant homogeneous prime $\mathfrak P$ with a linear form $x_i \notin \mathfrak P$,
   $\operatorname{length}_{S_{(\mathfrak P)}} M_{(\mathfrak P)} =
   \operatorname{length}_{S_{\mathfrak P}} M_{\mathfrak P}$, because $S_{\mathfrak P}$ is a
   localization of $S_{(\mathfrak P)}[x_i, x_i^{-1}]$, flat local over $S_{(\mathfrak P)}$ with
   $\mathfrak m S_{\mathfrak P}$ maximal, and $M_{\mathfrak P} \cong S_{\mathfrak P} \otimes
   M_{(\mathfrak P)}$. Mathlib supplies the flat local length formula
   (`IsLocalRing.length_baseChange`), but not the Laurent-polynomial description of $S_{x_i}$ or
   the tensor identification.

### Statement scope

The degree formula needs $\dim X \ge 1$: for $X$ a closed point not on $V$, $V\cdot X = 0$ while
$\deg V \cdot \deg X = \deg f \ge 1$. Hartshorne's use of Theorem I.7.7 assumes this implicitly.

### Next route

Once (1) and (2) exist, the proof is: reindex $\sum_Y \operatorname{ord}_Y(f/g)\deg Y$ over the
components of $Z(\mathfrak p_X)\cap Z(f)$ by (1), rewrite each coefficient by (2), apply Bézout
with $r = \dim X$, and use $\deg V = \deg f$ (checked above).
