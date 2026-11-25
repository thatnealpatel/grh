# Masullo's circle: Two calculations of one trace

**Claim.** A trace of a smoothed rotation operator can be read either
from whole-turn scales or from its action on Fourier modes. The
agreement makes a support condition in one reading into cancellation
in the other.

**Small example.** Identify each positive $x$ with $2x$. The coordinate
$u=\log_2 x\bmod 1$ turns multiplication into rotation on the circle.
Choose a smooth weight $\varphi$ supported between $1.4$ and $1.6$, and
average the rotations given by the scales in that support.

- **By scales:** There are no powers of $2$ in the support, so none of
  the rotations makes a whole turn. The periodized kernel is zero on
  the diagonal, and the trace vanishes.
- **By Fourier modes:** Each rotation changes a wave's phase but
  leaves its frequency alone. The weighted average therefore acts
  by one multiplier per mode. Poisson summation says the sum of those
  multipliers vanishes, not that each multiplier vanishes.

With the manuscript's Mellin measure $dt/t$ and general scale base
$\gamma>1$, the log period is $\log\gamma$. The sum of the Mellin
samples equals $\log\gamma\,\sum_k\varphi(\gamma^k)$; the scale sum as
printed omits that factor. The support-based vanishing is unchanged.

**What it does not show.** This is a toy calculation, not a proof of
the global trace formula. The latter compares a local expression to
a sum over zeros inside a strip. The downstream reconstruction isolates
an unproved step: At every positive strip width, the omitted zero
terms would have to sum to zero for every test vanishing on the
norm-one classes. Its separation theorem says that at each width
this requires absence of omitted zeros for the character family of
the reconstruction, not just cancellation under one probe.

**Source.** Masullo, *The Music of the Primes*, §1.2.8, PDF pp. 16–17;
for the separate global claim, Theorem 12.5.1.1, PDF pp. 519–520.
See `RiemannMasullo/Ch12_TraceGeometric/Sec5.lean` in the
[downstream formalization](https://github.com/mccorvie/riemann-masullo)
for `traceFormula_exteriorZeros` and `hasSum_exteriorZeros_iff_isEmpty`.
