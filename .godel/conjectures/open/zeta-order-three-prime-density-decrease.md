---
evidence_revision: a08d9dfe9adc87383319f9e970b60bd443cfcca2
---

# Arbitrarily late decreases of the cubic prime density

Put $a=\log 2$, $h_3=\mathbf{1}_{[0,a]}^{*3}$, and
$U_3(X)=X^{-1}\sum_p(\log p)h_3(\log(p/X))$ for real
$X>0$, with rational primes only. The spline is globally
$C^1$ and the prime sum is locally finite.

**Proposition to test:** Unconditionally, for every real
$A>0$ there exists a real $X>A$ with $U_3'(X)<0$.

**Source and payoff:** This operator proposition tests the
cubic version of the signed derivative argument in the
[order-four continuous criterion](../closed/zeta-prime-only-continuous-density.md),
not a result of that landing. On RH it would separate cubic
continuous nondecrease from both cubic eventual doubling
and quartic continuous increase. The
[order-three doubling criterion](../closed/zeta-prime-only-doubling-density.md)
at `d5301e8af8a5b4a76db76248f3264d9c9b5a394c` supplies
the converse needed off RH. The
[signed phase precedent](zeta-order-two-prime-comparison.md)
at `9328b646effbe6e2cc0559c62e40521bab600b48` supplies
a recurrence method for a different fixed-step comparison.
The proposition is not a biconditional with RH.

**Discriminating test:** Put $g=-h_3'-h_3$,
$\Phi(s)=(2^s-1)/s$, $G(s)=(s-1)\Phi(s)^3$, and
$k=\Phi(1/2)$. Independently derive the full smoothed
explicit formula for $x>1$, checking all residues and
the receding left edge. Under RH use it to test the signed
zero phase at $x=3/2$ against $-1/4$. Evaluate the finite
Mangoldt sum, with actual prime-power weights, and a finite
trivial-zero sum using rigorous enclosures and a proved
one-sided remainder. Verify the square contribution to the
large-$X$ prime-only derivative, control higher powers,
and use absolute convergence and simultaneous recurrence
if the seed is strict. Off RH, check that nonnegative
derivative on a tail would imply eventual doubling for
every real starting point, contradicting its converse.
