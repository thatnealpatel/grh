# The Archimedean Montel subsequence

**Status: Open as a formal finding.** Masullo, *The Music of the
Primes*, printed p. 29, claim in §1.4.3, from “By Montel’s Theorem”
through “so is the limit.” Chapter Markdown and layout extraction
located the passage in the [digest-verified edition](../sources/masullo/README.md).
Raster OCR checked the prose, and direct inspection of rendered pixel
crops checked the subsequence and compact-disc wording and the repeated
real and complex denominators. Other details of the display follow the
extraction. The next paragraph, “A similar reasoning,” concerns a
different limit, of the zero sums.

Masullo asserts that one sequence of the mollifier and cutoff parameters
makes both displayed Archimedean sums converge uniformly on each compact
disc inside $K$, with holomorphic limits. The preceding approximation
requires the selected parameters still to satisfy $\varepsilon\to0$
and $h\to1_{(1,\infty)}$. For each fixed compact cutoff and fixed
mollifier, the parameter dependence is holomorphic: On the integration
support the singularities are avoided, and the mollifier samples
$t^{-z}$ in a bounded range of log norms. This is not a bound that
persists as the support approaches norm one.

Montel on $\operatorname{Int}K$ would give a common subsequence by
successive extraction from the two families if each were locally bounded
in modulus there. The [preceding bound check](archimedean-montel-bound.md)
shows why even a finite-valued subsequential limit fails for the requested
approximation in a rational instance. Use $F=\mathbb Q$, $\chi=1$, an
admissible closed disc centered at a real $z_*>\max(1,\sup I)$, and
nonnegative mollifiers and cutoffs. The two signs add in the repeated
real display because it prints $|1-t|$ for both. If the profiles $a_n$
along a selected sequence retain the required pointwise limit on $t>1$,
then Fatou on $(1,2)$ gives

$$
\liminf_n\int_1^\infty a_n(t)\frac{t^{-1/2}}{t-1}\,dt
\ \ge\ \int_1^2\frac{t^{-z_*-1/2}}{t-1}\,dt=+\infty.
$$

Thus no such sequence has even pointwise finite convergence at the
center of this disc. The obstruction uses the project's rational Fatou
argument, not an objection to Montel itself. The missing step for a
replacement is a normalization at norm one, used consistently in the
full trace identity, with bounds uniform on compact parameter sets. The
[conditional rational repair](../obligations/trace-to-zeros.md#fixed-parameter-subtraction-over-the-rationals)
uses a difference of exponentials vanishing to first order in log norm
at zero, and obtains local uniform convergence by domination, without
Montel. `Masullo.cutoffTest_uniform` in
[CutoffProfiles.lean](../../Proofs/Lemmas/CutoffProfiles.lean) bounds
weighted scalar integrals of that subtracted profile and its second
derivative at fixed decay parameters, uniformly over cutoff scales. It
is not a declaration about normality of the printed family or a trace
identity. No new Lean result or zero-location conclusion is claimed.
