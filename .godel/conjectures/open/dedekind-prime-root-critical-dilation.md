---
evidence_revision: a954fef4e3a0db9c2124fbeb457b881886b18b47
---

# A rational-prime root-count comparison for Dedekind zeta

Fix one monic irreducible nonconstant polynomial $f$ in
$\mathbb Z[T]$, and let $K=\mathbb Q[T]/(f)$. This includes
linear $f$. A good prime is a rational prime not dividing
$\operatorname{disc}(f)$; $N_f(p)$ counts distinct roots in
$\mathbb F_p$. For an integer $m\ge2$ let
$h_m=\mathbf{1}_{[0,\log 2]}^{*m}$ in the log variable. Set

$$B_m(X)=\sum_{p\ {\rm good}}N_f(p)\log p\,
 h_m(\log(p/X))-X,\qquad
 S_m(X)=\sum_{p\ {\rm good}}\log p\,h_m(\log(p^2/X)).$$

**Proposition to test:** For each such fixed $f$, all
nontrivial zeros of $\zeta_K$ have real part $1/2$ if and
only if there exist an integer $m\ge2$ and $A\ge1$ with

$$\sqrt 2\,B_m(X)-B_m(2X)\le S_m(X)
\qquad\text{for every real }X\ge A.$$

The order is fixed before $X$ varies. Neither $K/\mathbb Q$
Galois, Artin holomorphy, a real-axis zero-free premise,
nor uniformity in $f$ is assumed.

**Source and payoff:** This is an operator extension of the
[critical prime-square allowance](../closed/critical-dilation-prime-square-allowance.md)
at the evidence revision and its
[real-character precursor](../closed/real-character-prime-spline-dilation-comparison.md)
at `25e564b06ce948bd41fbc69aa73f1df306a7f043`. Neither
landing asserts the extension. It would encode Dedekind
zero location using one polynomial's rational-prime root
counts, including ordinary RH when $f$ is linear.

**Discriminating test:** Derive both transforms from the
Dedekind Euler factors on rational primes, tracking the
square coefficient by the Frobenius cycle counts, including
degree-two primes. Check the coefficient on good split and
inert primes in a quadratic example, and the centering in
the linear case. Separate the finite excluded primes,
including index primes, from all exponents at least three.
Extract the square-scale term with fixed-field Chebotarev
and partial summation, and test its cancellation and the
central-zero cancellation against the allowance. Derive
the fixed-order spline contour shift with the pole at one
and account for trivial and archimedean terms. Test whether
the noncentral zero budget contracts below the allowance
for one fixed order. For the converse, transform the
nonnegative tail directly, keeping the centering integral
separate from the entire finite-prime-sum correction. Test
the pole cancellation at one, all open-half-plane zero
residues, and the real-abscissa Landau step.
