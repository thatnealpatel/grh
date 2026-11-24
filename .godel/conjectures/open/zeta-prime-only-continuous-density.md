---
evidence_revision: d5301e8af8a5b4a76db76248f3264d9c9b5a394c
---

# Continuous monotonicity of the order-four prime-only density

Put $a=\log 2$ and $h_4=\mathbf{1}_{[0,a]}^{*4}$, with
ordinary convolution in the log variable. For real $X>0$ let
$P_4(X)=\sum_p(\log p)h_4(\log(p/X))$, over rational primes
only, and $U_4(X)=P_4(X)/X$.

**Proposition to test:** Ordinary RH is equivalent to the
existence of a real $A\ge1$ such that $U_4(Y)\ge U_4(X)$ for
all real $Y\ge X\ge A$, without a minimum step, centering, or
prime-square allowance.

**Source and payoff:** The [order-three doubling criterion](../closed/zeta-prime-only-doubling-density.md)
at `d5301e8af8a5b4a76db76248f3264d9c9b5a394c` supplies a
low-ordinate certificate and the nonnegative-tail mechanism.
The [order-three prime comparison](../closed/zeta-order-three-prime-comparison.md)
at `d6e80ee6c70053b0089a7f7b1301bb767d3ab266` supplies the
inverse-square zero identity. Neither asserts continuous
monotonicity. This would give a prime-only RH criterion at
arbitrarily small real steps, not a statement of least order.

**Discriminating test:** Check the derivative at all knots
and use the signed kernel $g=-h_4'-h_4$ directly, not a
derivative of an asymptotic remainder. For
$\Phi(s)=(2^s-1)/s$ and $k=\Phi(1/2)$, check inversion and the
shift of $(s-1)\Phi(s)^4$, including absolute convergence,
horizontal edges, and the residue at one. Use fixed-weight
PNT and partial summation to test the putative $+1/4$ square
margin in $(X^2 U_4'(X))/(\sqrt X k^4)$ and bound higher powers.
On RH test the absolute zero budget with $|1-\rho|=|\rho|$, the
low-ordinate exclusion, and $C=2+\gamma_E-\log(4\pi)$ against
that margin. Conversely, test the weighted PNT limit and
whether monotonicity implies a nonnegative tail $X-P_4(X)$
to which Landau applies, including the Mellin endpoint,
pole cancellation, real-axis regularity, and zero visibility.
