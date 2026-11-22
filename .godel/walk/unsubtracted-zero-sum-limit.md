# The unsubtracted zero-sum limit

**Status: Open as a formal finding.** Masullo, *The Music of the
Primes*, printed p. 29, claim in §1.4.3, paragraph beginning “A
similar reasoning,” including the display and closing parenthesis.
The chapter Markdown and layout extraction located the passage in the
[digest-verified edition](../sources/masullo/README.md). Raster OCR
checked the prose. Direct inspection of rendered crops checked the
order factor and summation index, the character and cutoff factors,
the exponent $\rho-1/2$, and the reference to the complement of
$\mathbf C_I$. Other transcription details follow the extraction.

Masullo claims that as $\varepsilon\to0$ and
$h\to 1_{(1,\infty)}$, the displayed zero sums for the mollified tests
have a holomorphic limit on $\operatorname{Int}K\setminus\mathbf C_I$.
The index is restricted to zeros of $L(s,\chi)$ whose shifted
parameters $\rho-1/2$ belong to the fixed strip, with weights
$N(\rho)$. This is a separate assertion from the preceding
[Archimedean subsequence](archimedean-montel-subsequence.md). Smoothness
at fixed cutoff controls each zero series, not its behavior as the
support approaches norm one. Even in the trivial rational isotype,
replacing each Mellin integral by its limit $(z-(\rho-1/2))^{-1}$
does not justify a limit after the sum. Montel would need local bounds
uniform in the cutoffs and would in itself only give subsequences.

## A full-width rational control

Use $F=\mathbb Q$, $\chi=1$, and the allowed interval
$I=[-1/2,1/2]$, whose interior contains the shifted parameters of
all nontrivial zeta zeros. Take a real $z_*>1$ inside an admissible
closed disc $K$. Use nonnegative smooth additive mollifiers of mass
one and radius $\varepsilon_n<1/2$ tending to zero, and any of the
increasing cutoffs $0\le h_n\le1$ of §1.4.2. The profiles $a_n(t)$
vanish on a neighborhood of $t=1$ for each $n$. For $t>1$, they tend
to $t^{-z_*}$ and satisfy $0\le a_n(t)\le 2^{z_*}t^{-z_*}$, since
$t-u\ge t/2$ on the mollifier support. Set $f_n(x)=a_n(e^x)$.

For each smooth compact $f_n$, the project's accepted
[`Masullo.rationalIdeleRadial_explicit_formula`](../../Proofs/Theorems/RationalIdeleRadialExplicitFormula.lean)
gives an absolutely convergent full-order zero sum on actual
rational quotient Haar. It equals the two polar moments minus the
normalized real and finite terms. At this width its zero sum is
exactly the one in the paragraph, because the compact isotype is
trivial and the width excludes no nontrivial zeta zeros. The two
moments are bounded by integrating $2^{z_*}e^{-(z_*\mp1/2)x}$
on $x>0$. The normalized finite term is bounded by
$2^{z_*}\sum_{m\ge2}\Lambda(m)m^{-z_*-1/2}$.

The checked negative logarithmic Fourier pairing equals the
normalized half-Haar real term via `real_log_profile_fourier_eq_neg_gamma`
and `real_log_profile_haar_log_tendsto_neg_gamma`. The log cutoff
can be discarded for each $f_n$ because its support is bounded away
from zero and its contact and counterterm both vanish. The two signs
of the real multiplicative Haar measure give $\int_0^\infty H(x)f_n(x)\,dx$,
where

$$H(x)=\frac{e^{x/2}}2\left(\frac{1}{e^x-1}+\frac{1}{e^x+1}\right).$$

Thus this calculation uses the correct signed real kernel, not the
repeated $|1-t|$ in §1.4.3. Fatou on $(0,1)$ gives divergence to
$+\infty$, since $H(x)e^{-z_*x}\sim 1/(2x)$ as $x\downarrow0$.
Consequently the zero sums themselves tend to $-\infty$ at $z_*$.
This uses the [checked fixed-test scalar explicit formula](../obligations/rational-explicit-formula.md#checked-rational-radial-idelic-explicit-formula),
not Masullo's opening strip-restricted geometric trace. It is an
analytic control, not a new Lean theorem about the parameter limit.
It gives no conclusion about narrower strips or zero location.

## What a replacement needs

A replacement needs a summably controlled limit with a norm-one
normalization that also works in the other terms of the trace identity.
The project's [conditional rational argument](../obligations/trace-to-zeros.md#fixed-parameter-subtraction-over-the-rationals)
uses smooth cutoffs of $e^{-zx}-e^{-z_0x}$ in log norm. Vanishing to
first order at zero gives uniform weighted $L^1$ bounds on the
profiles and their second derivatives, and hence a summable
quadratic ordinate bound, using the zeta zero count. The limit uses
a difference of two resolvents per zero. Lean's
`Masullo.cutoffTest_uniform` and
`Masullo.tendsto_positiveLaplaceTest_cutoffTest` bound those
subtracted scalar profiles and give their individual Laplace limits;
they do not validate the printed mollified family or a geometric
trace identity. This project subtraction, not Masullo's argument,
changes the test and the proposed limit.
