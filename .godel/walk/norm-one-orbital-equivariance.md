# Norm-one equivariance and the orbital supports

**Printed passage.** Masullo, *The Music of the Primes*, §1.2.11,
printed p. 20, claim in the paragraph beginning “The eigen-property
of the eigendistributions.” Masullo names the conjugate character
$\overline{\chi}_S$ and says that the support matters modulo the
norm-one S-ideles, not just the S-units, giving the quotient stacks
in the diagram. The paragraph was read with raster OCR, and the
conjugation bar and norm-one group were inspected in pixel crops
rendered from p. 20 of the [pinned PDF](../sources/masullo/README.md),
SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The chapter Markdown and PDF layout extraction were checked
separately; the layout extraction drops the conjugation bar. This
record ends before the paragraph about Deninger's flow.

**Equivariance check.** Put $G^1=\ker(|\cdot|_{F,S})$ in the
S-ideles, and use left translation $\rho(g)f(x)=f(g^{-1}x)$.
Masullo's (5.1.3.2) and (5.5.1.1) use the transpose convention,
in which an eigendistribution of weight $c$ takes $\rho(g)f$ to
$c(g)$ times its value on $f$. In the Fourier–Mellin family of
(7.3.1.14), the weight on Fourier-side tests is
$\overline{\chi}_S|\cdot|_{F,S}^{1-s}$. It is constant in $s$ on
$G^1$, so differentiation in $s$ preserves this scalar. For
$g\in G^1$, Fourier transformation takes $\rho(g)$ to
$\rho(g^{-1})$ with no norm factor. The pulled-back jets thus have
weight $\chi_S|_{G^1}$ on original tests in the transpose
convention, or $\overline{\chi}_S|_{G^1}$ for the contragredient
action using inverse translation. Likewise, all Laurent
coefficients of a fixed Mellin component have the same transpose
weight on $G^1$, since multiplication by the translating weight
is constant in the norm-twist parameter there. This argument makes
no assertion that a higher jet is a full-idele eigenvector. A
nonzero scalar character preserves the support of a distribution:
Translation carries its support to the translated support, while
nonzero scalar multiplication leaves it unchanged.

**Open identification.** This calculation explains why the support
of these equivariant functionals is a norm-one-invariant locus.
It does not identify the functionals as a basis of the introductory
orbital quotient, or locate their supports on the one-zero strata.
One still needs to match the jets to the actual quotient and show
that their pullbacks annihilate every ambient Schwartz–Bruhat test
compactly supported in $D_{F,S}$ away from the indicated strata.
The [geometric stack calculation](individual-orbital-loci.md) is
independent of that analytic vanishing. Masullo's Theorem 7.3.1.6
uses saturation, trivial S-class group, and its stated character
choices. Theorem 8.3.0.1 additionally uses a global character
unramified outside S. Its supported ambient representative does
not provide the required vanishing: The union of one-zero strata
has empty ambient interior, as explained in the
[finite orbital dual support audit](finite-orbital-dual-support.md).

The character and stack interpretation are Masullo's. The
translation and differentiation check, and the separation of
invariance from localization, are the reviewer's. The Chapter 5,
7, and 8 readings are provisional, from chapter Markdown rather
than rendered later pages. No Lean declaration is used to
establish or refute this passage.
