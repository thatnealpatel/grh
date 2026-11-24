---
evidence_revision: d5301e8af8a5b4a76db76248f3264d9c9b5a394c
outcome: established
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

## Adjudication

**Yes.** On RH, $U_4'(X)>(k^4/100)X^{-3/2}$ for every sufficiently
large real $X$. Conversely, even weak nondecrease on a real tail
forces RH. The forward implication is not an interpolation of the
order-three doubling inequalities.

### Compute the derivative before estimating it

Writing $u_+=\max(u,0)$, successive integration against the interval
indicator gives the spline
$$h_4(t)=\frac16\sum_{j=0}^4(-1)^j\binom4j(t-ja)_+^3.$$
It is globally $C^2$, including at the ends of its support. The prime
sum is locally finite, so at *every* real $X>0$,
$X^2U_4'(X)=\sum_p(\log p)g(\log(p/X))$, where $g=-h_4'-h_4$.
Integration by parts with no boundary term gives
$$G(s)=\int g(t)e^{st}dt=(s-1)\Phi(s)^4.$$

Assume RH. First sum $g$ over all $p^j$, each with weight $\log p$.
Fourier inversion on $\Re s=2$ gives the integral of
$-(\zeta'/\zeta)(s)X^sG(s)\,ds/(2\pi i)$: The Euler series and
inversion integral converge absolutely, and $g$ is continuous.
The log-derivative estimates at `e29848af48be97061090219fcb2ea99e27079367`,
lines 80–84 of the [prime formula](dedekind-prime-root-critical-dilation.md),
are independent of the kernel. Indeed, taking real parts in the
Hadamard logarithmic derivative at $2+it$, with Stirling and the Euler
series there, gives $\sum_\rho(1+(t-\Im\rho)^2)^{-1}\ll\log(3+|t|)$.
Subtract the product derivative there from the one at $\sigma+it$
for $1/4\le\sigma\le2$. Zeros at ordinate distance greater than one
cost at most a constant times that same sum. On the left vertical
the remaining $O(\log(3+|t|))$ zeros are at distance at least $1/4$.
For the horizontal edges select heights in successive unit intervals
avoiding nearby ordinates by $c/\log(3+|t|)$: The local count leaves
space for small fixed $c$. Removing the completion factors gives
$O(\log(3+|t|))$ for $\zeta'/\zeta$ on the left and
$O(\log^2(3+|t|))$ on the selected edges. The new $G$ still decays
as $O((1+|t|)^{-3})$ across the strip. Thus the edges vanish for
fixed $X$, and the left integral is absolutely $O(X^{1/4})$.
The pole at one contributes nothing since $G(1)=0$. No trivial
zeros are crossed. The full sum is
$-\sum_\rho X^\rho G(\rho)+O(X^{1/4})$, absolutely summed with
multiplicities by the local count.

For squares set $T=\sqrt X$ and integrate $g(2\log v)$ against
$d\vartheta(Tv)$ on $[1,4]$. PNT gives $\vartheta(Tv)=Tv+o(T)$
uniformly there. The weight has fixed bounded variation, so partial
summation gives the square term as
$$T\int_1^4g(2\log v)dv+o(T)=\tfrac T2 G(1/2)+o(T)=-Tk^4/4+o(T).$$
The $j\ge3$ terms total $O(X^{1/3}\log^2(2X))$ in absolute value:
Use $p\le(16X)^{1/3}$, $j\le\log(16X)/\log 2$, and boundedness of
$g$. Subtracting the powers from the full sum gives
$$\frac{X^2 U_4'(X)}{\sqrt X\, k^4}
=\frac14+\sum_\rho(1-\rho)(\Phi(\rho)/k)^4 X^{i\Im\rho}+o(1).$$
This estimates the derivative itself, not the derivative of an
asymptotic remainder.

### The unbounded multiplier fits within the margin

The [inverse-square identity](zeta-order-three-prime-comparison.md),
lines 49–61 at the cited revision, follows by subtracting the product
logarithmic derivatives of $\xi$ at one and zero. On RH,
$1-\rho=\bar\rho$, so it gives $\sum_\rho|\rho|^{-2}=
2+\gamma_E-\log(4\pi)=C$, counting both signs. Lines 89–133 of the
[doubling criterion](zeta-prime-only-doubling-density.md) at the
evidence pin exclude ordinates up to 14 by an argument count, not just
by locating a critical-line zero. With $r=\sqrt2$, $|2^\rho|=r$ and
$|1-\rho|=|\rho|>14$. The absolute oscillation, uniformly in $X$, is
at most
$$\left(\frac{1+r}{k}\right)^4\sum_\rho|\rho|^{-3}
\le\left(\frac{3+2r}{2}\right)^4\frac C{14}<0.238.$$
For an independent reproducible check, use FLINT at 128 bits:
`acb_dirichlet_zeta_nzeros` on the exact real ball $14$ returns
exactly $0$. Evaluate $C$ with `arb_const_euler`, `arb_const_pi`,
and the real-ball logarithm; raise $(3+2\sqrt2)/2$ to the fourth
power and multiply by $C/14$. The enclosure lies strictly between
$0.23796810$ and $0.23796812$. Hence the bound leaves more than
$0.012$ below $1/4$. Absorbing the real-tail $o(1)$ proves the
stated derivative bound and strict increase, with no minimum step.

### Nondecrease forces RH

Unconditionally, partial summation with the fixed weight $h_4(\log v)$
on $[1,16]$ and $\vartheta(Xv)=Xv+o(X)$ gives
$U_4(X)\to\int h_4(t)e^t dt=\Phi(1)^4=1$. Nondecrease implies
$U_4(X)\le1$ at each $X\ge A$, hence $H(X)=X-P_4(X)\ge0$ there.
Take $A\ge1$. For $Q(s)=\sum_p(\log p)p^{-s}$, put
$R(s)=\sum_{j\ge2}Q(js)$. The full Mellin integral of a single
prime's spline is $p^{-s}\Phi(s)^4$ by $t=\log(p/X)$. Thus for
$\Re s>1$, absolute convergence and $Q=-\zeta'/\zeta-R$ give
$$\int_A^\infty H(X)X^{-s-1}dX
=\frac{A^{1-s}}{s-1}+\Phi(s)^4\left(\frac{\zeta'}{\zeta}(s)+R(s)\right)
 +\int_0^A P_4(X)X^{-s-1}dX.$$
The endpoint integral is entire: Only $p\le16A$ occur, and
$P_4(X)=0$ below $1/8$. For $\Re s\ge\sigma>1/2$, the majorant
$\sum_p(\log p)p^{-2\sigma}/(1-2^{-\sigma})$ gives normal convergence
of $R$. The residues at one cancel since $\Phi(1)^4=1$.
The continuation is regular at every real $s>1/2$ by the Euler
product above one and the positive paired eta series below one.
Any zero with $\Re\rho>1/2$ would give a pole: $|2^\rho|>1$
prevents a zero of $\Phi$ there.

If the nonnegative tail had convergence abscissa $b>1/2$, then
$b\le1$ and the continuation would be regular near $b$. Choose
$u=b+\epsilon$ close enough that its Taylor series reaches
$b-\epsilon$. In powers of $u-s$, its coefficients are the integrals
of $H(X)X^{-u-1}(\log X)^j/j!$, nonnegative since $X\ge A\ge1$.
Summing by monotone convergence at $s=b-\epsilon$ gives a finite
integral there, contradicting the abscissa. Thus the defining
integral is holomorphic throughout $\Re s>1/2$, excluding every
such pole. The functional equation yields RH.

This criterion neither proves unconditional monotonicity nor
identifies a least spline order or an effective threshold.
