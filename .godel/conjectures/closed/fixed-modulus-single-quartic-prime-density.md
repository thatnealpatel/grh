---
evidence_revision: 76d66112fa30b3a9cc28d24759ac6f8fe78f9e94
outcome: established
---

# One positive quartic prime density and fixed-modulus GRH

Fix an integer $q\ge2$. Set $h_4=\mathbf 1_{[0,\log 2]}^{*4}$
with ordinary real convolution, and for real $X>0$ let
$$P(X)=\sum_{p\nmid q}(\log p)h_4(\log(p/X)),\qquad
P_1(X)=\sum_{p\equiv1\bmod q}(\log p)h_4(\log(p/X)).$$

**Proposition to test:** All nontrivial zeros of every
primitive Dirichlet $L$-function inducing a character
modulo $q$, including $\zeta$, lie on $\Re s=1/2$ if and
only if there exist an integer $M\ge1$ and a real $A\ge1$
such that the single real density $W(X)/X$ is nondecreasing
for all real $X\ge A$, where
$$W=(M+\sqrt 2)P-P_1.$$
The two assigned prime weights are $M+\sqrt 2-1$ in the
identity class and $M+\sqrt 2$ elsewhere, both positive.
The same formula applies when $q=2$ and only the identity
class occurs. No zero simplicity or disjointness is assumed.

**Source and payoff:** This operator proposal uses the
order-four class derivative bound of the [simultaneous criterion](../closed/fixed-modulus-one-extra-vote-prime-density.md)
at the evidence revision and the RH derivative margin of the
[quartic zeta criterion](../closed/zeta-prime-only-continuous-density.md)
at `a08d9dfe9adc87383319f9e970b60bd443cfcca2`.
Neither source asserts this criterion. The payoff is one
monitored density instead of all class comparisons, not
unconditional increase or a baseline uniform in $q$.

**Discriminating test:** Check that the strict total derivative
margin dominates the two-sided identity-class derivative
bound for some $M$. In the converse, use the fixed-modulus
PNT limit to center the nonnegative deficit on a real tail.
Without simultaneous conservation, derive its tail Mellin
transform, check the endpoint, power terms, pole at one, and
imprimitive factors, and test whether the uniform character
coefficients of the identity class and the irrational total
weight prevent pole cancellation at arbitrary coincident
zeros. Test the sign at a real zero using zeta nonvanishing,
then apply the nonnegative-tail convergence-abscissa argument
with these real poles allowed. Check holomorphy in the full
open right half of the critical strip and reflection in the
inducing primitive family.

## Adjudication

**One density suffices.** Put $b=M+\sqrt2$, $d=\varphi(q)$, and
$\Phi(s)=\int_0^{\log 2}e^{st}dt$. On joint GRH, lines 44–58 and
85–119 of the pinned zeta criterion give $(P/X)'>cX^{-3/2}$ on a
real tail, with $c=\Phi(1/2)^4/100$: Once $X$ exceeds the prime
divisors of $q$, $P$ agrees with the all-prime spline. Lines 172–182
of the simultaneous criterion give $|(P_1/X)'|\le C_q X^{-3/2}$
on a real tail, including at knots, by applying the class estimate
to $-h_4'-h_4$. Choose an integer $M\ge1$ with $bc>C_q$. Then
$(W/X)'>(bc-C_q)X^{-3/2}>0$ throughout the common tail.

Conversely, keep the single witness $M,A$. Fixed-modulus PNT and
partial summation against $h_4(\log v)$ on $1\le v\le16$ give
$P/X\to\Phi(1)^4=1$ and $P_1/X\to1/d$. Thus $W/X$ increases
weakly to $\lambda=b-1/d$, so $H=\lambda X-W\ge0$ for $X\ge A$.
No sign for any individual class deficit follows or is needed.

Take $B\ge A$. Write $u_\chi=b\mathbf1_{\chi=\chi_0}-1/d$ for
characters modulo $q$, including the principal $\chi_0$. For every
prime $p$, the weight in $W$ is $\sum_\chi u_\chi\chi(p)$, by
orthogonality at the identity, with all characters zero on nonunits.
For $\Re s>1$, the substitution $t=\log(p/X)$ gives the whole-window
Mellin integral $p^{-s}\Phi(s)^4$. The Euler series for $-L'/L$
contains primes *and* their higher powers, so the transform of the
negative prime sum in $H$ has a plus sign on both terms below:
$$
\begin{aligned}
F(s)&=\int_B^\infty H(X)X^{-s-1}\,dX\\
&=\lambda\frac{B^{1-s}}{s-1}+\int_0^B W(X)X^{-s-1}\,dX
 +\Phi(s)^4\sum_\chi u_\chi\left(\frac{L'}{L}(s,\chi)+R_\chi(s)\right),\\
R_\chi(s)&=\sum_{p,j\ge2}(\log p)\chi(p)^j p^{-js}.
\end{aligned}
$$
The endpoint is entire: Only $p\le16B$ occur, and the windows vanish
for $X<1/8$. The powers converge normally on $\Re s\ge\sigma>1/2$
by the majorant $\sum_p(\log p)p^{-2\sigma}/(1-2^{-\sigma})$.
The finite Euler factors removed from primitive functions do not
vanish for $\Re s>0$. This gives meromorphic continuation to
$\Re s>1/2$. At one, $L(s,\chi_0)$ has a simple pole, and the
nonprincipal functions are nonzero (Dirichlet nonvanishing at one).
The residue is $\lambda-u_{\chi_0}\Phi(1)^4=0$.

At a family zero $\rho$ in this half-plane the residue is
$$\Phi(\rho)^4\left(bm_\zeta(\rho)-\frac1d\sum_\chi m_\chi(\rho)\right),$$
with $m_\chi$ the zero order, zero for a nonvanishing function.
The principal order is $m_\zeta$, and $\Phi(\rho)\ne0$ because
$|2^\rho|>1$. If $m_\zeta>0$, the first term in parentheses is
irrational and the second rational. Otherwise the parentheses are
strictly negative. Every such zero therefore produces a simple pole,
regardless of coincidences. On $(1/2,1)$, pairing successive terms
of the alternating eta series gives $\eta(\beta)>0$, so
$\zeta(\beta)=\eta(\beta)/(1-2^{1-\beta})\ne0$. Since
$\Phi(\beta)>0$, any real pole there has **negative residue**.
Above one the Euler products do not vanish. These exhaust the
possible real singularities in the continuation half-plane.

Let $\alpha$ be the convergence abscissa of the nonnegative tail.
Since $H=O(X)$, $\alpha\le1$. Suppose $\alpha>1/2$. The integral
is holomorphic to its right and agrees there with the continuation
by meromorphic uniqueness. A negative-residue pole at $\alpha$
would force $F(u)\to-\infty$ as real $u\downarrow\alpha$, whereas
$F(u)\ge0$. If regular there, take $u=\alpha+\epsilon$ with
$\epsilon>0$ so small that the Taylor disk at $u$ reaches strictly
past $v=\alpha-\epsilon$. By convergence slightly left of $u$, the
coefficient of $(u-s)^j$ is the integral against $H(X)X^{-u-1}$
of $(\log X)^j/j!$. These coefficients are nonnegative since
$B\ge1$. Monotone convergence at $s=v$ sums them with their powers
to the defining integral at $v$, finite by the Taylor expansion.
This contradicts the definition of $\alpha$.

Thus $\alpha\le1/2$ (also allowing $-\infty$). The defining
integral is holomorphic throughout $\Re s>1/2$, excluding every
zero pole found above. A nontrivial zero left of the line would
reflect by the primitive functional equation to one right of it
for the conjugate character, still inducing a character modulo $q$.
This proves joint GRH from the one comparison. For $q=2$ the only
coefficient is $b-1>0$, so the same argument includes this case.
