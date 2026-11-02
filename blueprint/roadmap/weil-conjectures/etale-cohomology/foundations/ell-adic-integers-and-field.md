---
article_id: af_e3cca5b53e68a242841d754a
declaration: structure
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.EllAdicCoefficientPackage
---

# The ℓ-adic integers and coefficient field

For a prime $\ell$, the ring of $\ell$-adic integers is

$$\mathbb{Z}_\ell=\varprojlim_r\mathbb{Z}/\ell^r\mathbb{Z}.$$

Its fraction field is the field of $\ell$-adic numbers:

$$\mathbb{Q}_\ell=\operatorname{Frac}(\mathbb{Z}_\ell).$$

The coefficient system includes the reduction maps
$\mathbb{Z}_\ell\to\mathbb{Z}/\ell^r\mathbb{Z}$ and the scalar-extension
map $\mathbb{Z}_\ell\hookrightarrow\mathbb{Q}_\ell$.

## Depends on

No project-local geometric prerequisite.

## Proof depends on

- The universal properties of the $\ell$-adic integers, their fraction
  field, and the coefficient-reduction maps.
- Inverse limits of the reduction system $\mathbb{Z}/\ell^r\mathbb{Z}$.

## Sources

- [Hartshorne Appendix C §3, ℓ-adic coefficient rings, p.453](../../../../sources/hartshorne-appendix-c-3.md#definition-and-coefficients-printed-p453)
