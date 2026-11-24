---
evidence_revision: 1f653917b9a8d55a730e17252832825d03236891
outcome: established
---

# One neutral order-six prime density and fixed-modulus GRH

Fix an integer $q\ge2$ and write $d=\varphi(q)$,
$a=\log 2$, $h=\mathbf 1_{[0,a]}^{*6}$, and $t_p=\log(p/X)$.
Derivatives of $h$ are ordinary derivatives in its log
argument. For an integer $M\ge1$ define
$$W_M(X)=\sum_{p\nmid q}(\log p)
 \left[Mh(t_p)+\mathbf1_{p\equiv1\bmod q}
               (h''(t_p)-h(t_p))\right].$$

**Proposition to test:** All nontrivial zeros of every
primitive Dirichlet $L$-function inducing a character modulo
$q$, including $\zeta$, lie on $\Re s=1/2$ if and only if
some integer $M\ge1$ makes both windows $Mh$ and
$(M-1)h+h''$ nonnegative everywhere and makes $W_M(X)/X$
nondecreasing for all real $X$ on a full tail. Seek strict
positivity of the derivative on the forward tail. The claim
includes $q=2$ and permits $M$ and the tail to depend on $q$.

**Source and payoff:** This is an operator proposal, not a
claim of the [irrational quartic criterion](../closed/fixed-modulus-single-quartic-prime-density.md)
at the evidence revision. The [class derivative estimate](../closed/fixed-modulus-one-extra-vote-prime-density.md)
at `76d66112fa30b3a9cc28d24759ac6f8fe78f9e94` and the
[positive zeta derivative margin](../closed/zeta-prime-only-continuous-density.md)
at `a08d9dfe9adc87383319f9e970b60bd443cfcca2` provide inputs.
The proposed payoff is an integer differential polynomial
in one window, and a single density with limit $M$ without
a residue-class correction. It does not assert a criterion
with two integer multipliers of the same unchanged kernel.

**Discriminating test:** Check the support ends and a finite
bound for the negative part of $h''/h$. Transport the
quartic derivative margin by exact convolution and chain
rule; use the fixed-character contour calculation on the
actual derivative kernel $-(h''-h)'-(h''-h)$ with the pole,
zero sum, and prime powers treated separately. For the
converse, derive the Mellin transform of $MX-W_M$ on the
nonnegative tail, checking the lower endpoint, higher
powers, removed Euler factors, and the residue at one.
Determine whether $(s^2-1)$ prevents cancellation at every
coincident nonreal zero, and whether the sign at a real
zero suffices for the nonnegative-tail abscissa argument.

## Adjudication

**The equivalence holds for each fixed $q$, with strictly positive
forward derivative on a full real tail.** The separating multiplier
is $s^2-1$: It vanishes at the mean, has nonzero imaginary part at
nonreal zeros to the right of the line, and is negative at possible
real zeros there. These are three distinct uses of its value.

Write $K_f(s)=\int_{\mathbb R} f(t)e^{st}dt$,
$\Phi(s)=\int_0^a e^{st}dt$, and $k=h''-h$. Successive convolution
gives $h(t)=\sum_{j=0}^6(-1)^j\binom6j(t-ja)_+^5/120$. This is
$C^4$, supported on $[0,6a]$, and strictly positive on $(0,6a)$ by
convolution of positive interiors. On $[0,a]$ it equals $t^5/120$;
reflection gives the last piece. Thus $h''\ge0$ on both end pieces,
and $-h''/h$ has a finite maximum on $[a,5a]$. Any sufficiently
large integer $M$ makes both specified windows nonnegative everywhere.

### Forward derivative

For $h_m=\mathbf1_{[0,a]}^{*m}$, put
$U_m(X)=X^{-1}\sum_p(\log p)h_m(\log(p/X))$. Convolution gives
$$U_{m+1}(X)=\int_0^a e^v U_m(Xe^v)\,dv.$$
For $m=4,5$ the sums are locally finite and continuously
differentiable, including at knots. Consequently a real-tail bound
$U_m'(Y)>c_mY^{-3/2}$ passes to
$$U_{m+1}'(X)=\int_0^a e^{2v}U_m'(Xe^v)\,dv
 >c_m X^{-3/2}\int_0^a e^{v/2}\,dv.$$
Joint GRH includes RH, so the pinned zeta margin (lines 44–58 and
85–119) starts this recursion with $c_4=\Phi(1/2)^4/100$.
Thus $c_6=\Phi(1/2)^6/100$ works. Primes dividing $q$ contribute
nothing once $X$ exceeds them.

Let $V(X)=X^{-1}\sum_{p\equiv1\bmod q}(\log p)k(t_p)$.
Exactly $X^2V'(X)=\sum_{p\equiv1\bmod q}(\log p)g(t_p)$, where
$g=-k'-k$. Compact support and regularity give, without boundary terms,
$$K_h=\Phi^6,\qquad K_k=(s^2-1)\Phi^6,\qquad
 K_g=(s-1)(s^2-1)\Phi^6.$$
In particular $K_g(1)=0$, and $K_g=O((1+|\Im s|)^{-3})$ uniformly
on $1/4\le\Re s\le2$, since $\Phi(s)=(2^s-1)/s$ there.

To apply the contour argument of the class derivative pin (lines
102–147 and 172–182) to this new $g$, invert $K_g$ at $\Re s=2$
against $X^s(-L'/L)(s,\chi)$ for each character modulo $q$. Absolute
inversion for the continuous $g$ gives its sum over $p^j$ with weights
$(\log p)\chi(p)^j$. Shift to $1/4$. Under joint GRH the pinned
kernel-independent log-derivative bounds are logarithmic on the left
edge and squared logarithmic on selected horizontal edges. Cubic decay
makes the left integral $O_q(X^{1/4})$ and the horizontals vanish at
fixed $X$. No trivial zero is crossed; the removed Euler factors have
bounded log derivatives here. The principal pole contributes zero.
The zero terms $-X^\rho K_g(\rho)$ total $O_q(\sqrt X)$ absolutely,
since the local count with multiplicity is $O_q(\log(3+|\Im\rho|))$
per unit interval. The squares cost at most
$\|g\|_\infty\vartheta(8\sqrt X)=O(\sqrt X)$. For $j\ge3$, use
$p\le(64X)^{1/3}$ and $j\le\log(64X)/\log 2$ to get
$O(X^{1/3}\log^2(2X))$. Averaging the remaining genuine-prime sums
over the characters selects the identity class, so
$|V'(X)|\le C_qX^{-3/2}$ eventually. Enlarge the window witness $M$
until $Mc_6>C_q$. Then $(W_M/X)'=MU_6'+V'>0$ throughout the common
tail. This is a bound for the actual derivative.

### Converse from the same single density

Fixed-modulus PNT and partial summation with the fixed $C^1$ weights
$h(\log v)$ and $k(\log v)$ on $[1,64]$ give
$W_M(X)/X\to M K_h(1)+K_k(1)/d=M$, since $\Phi(1)=1$.
For the witness of nondecrease, $H(X)=MX-W_M(X)\ge0$ on its tail.
Take $B\ge1$ on that tail. Put
$$u_\chi(s)=M\mathbf1_{\chi=\chi_0}+(s^2-1)/d,\qquad
 R_\chi(s)=\sum_p\sum_{j\ge2}(\log p)\chi(p)^j p^{-js}.$$
Here $\chi_0$ is principal. Orthogonality at the identity and the
substitution $t=\log(p/X)$ (full-window integral $p^{-s}K_f(s)$)
give, initially by absolute convergence on $\Re s>1$,
$$
\begin{aligned}
 F(s)&=\int_B^\infty H(X)X^{-s-1}dX \\
 &=\frac{MB^{1-s}}{s-1}+\int_0^B W_M(X)X^{-s-1}dX
 +\Phi(s)^6\sum_{\chi\bmod q}u_\chi(s)
 \left(\frac{L'}{L}(s,\chi)+R_\chi(s)\right).
\end{aligned}
$$
Both signs inside the parentheses are positive: The prime-only series
is $-L'/L-R_\chi$, and $H$ subtracts $W_M$. The endpoint is entire,
since only $p\le64B$ occur and $W_M=0$ below $1/32$. The power tail
converges normally on $\Re s\ge\sigma>1/2$, dominated by
$\sum_p(\log p)p^{-2\sigma}/(1-2^{-\sigma})$. Removed Euler factors
are nonzero there. This is a meromorphic continuation to $\Re s>1/2$.
At one the principal pole gives residue $-M$, canceling $+M$; all
nonprincipal $L$-functions are nonzero at one.

At a family zero $\rho$ there, let $S=\sum_\chi m_\chi(\rho)>0$
count all orders of the inducing functions. The residue is
$$\Phi(\rho)^6\left[M m_\zeta(\rho)+(\rho^2-1)S/d\right].$$
The prefactor cannot vanish since $|2^\rho|>1$. If $\rho$ is nonreal,
the **bracket** has imaginary part $2\Re\rho\,\Im\rho\, S/d\ne0$,
regardless of coincidences. For real $1/2<\beta<1$, the paired eta
series is positive, so $\zeta(\beta)\ne0$. Then $\Phi(\beta)>0$ and
$\beta^2-1<0$, giving a strictly negative residue. There are no real
zeros above one by the Euler product. Thus on the real half-line in
question the only possible singularities are simple negative-residue
poles, not necessarily an empty set a priori.

Let $\alpha$ be the abscissa of convergence of the nonnegative tail.
It is at most one by the PNT bound $H=O(X)$. If $\alpha>1/2$, a pole
at $\alpha$ would force $F(u)\to-\infty$ for real $u\downarrow\alpha$,
contrary to the integral's sign (it agrees with the continuation to
the right of $\alpha$). If regular there, take $u=\alpha+\epsilon$
so close that the Taylor disk about $u$ contains $v=\alpha-\epsilon$.
The coefficients of $(u-s)^j$ are the integrals of
$H(X)X^{-u-1}(\log X)^j/j!$, nonnegative since $B\ge1$; convergence
slightly to the left of $u$ justifies differentiation. At $v$, monotone
convergence sums these moments with their powers to the defining
integral at $v$, finite by Taylor convergence. This contradicts the
abscissa. Hence the defining integral is holomorphic on $\Re s>1/2$,
excluding every visible zero there. A nontrivial zero to the left
would reflect to the right for a conjugate inducing primitive function,
still in the family. This proves joint GRH from the single witness.

For $q=2$ only $\chi_0$ occurs and only $p=2$ is omitted; neither
argument needs a second character. The integer multiplies a spline
alongside its differential perturbation, not two constant multiples
of one shape. No uniform choice in $q$ or unconditional tail sign
is asserted.
