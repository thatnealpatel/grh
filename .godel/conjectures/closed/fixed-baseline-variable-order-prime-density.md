---
evidence_revision: 1730648dc8b4e56903937bcef70dfa857183cec2
outcome: established
---

# One explicit baseline with variable spline order

Fix $M=10^{15}$, $a=\log 2$, and an integer $q\ge2$. For
each integer $m\ge8$, let $h_m=\mathbf 1_{[0,a]}^{*m}$,
$k_m=4h_m^{(4)}-5h_m''+h_m$, and $t_p=\log(p/X)$, with
ordinary log derivatives. For every real $X>0$ let

$$W_{q,m}(X)=\sum_{p\nmid q}(\log p)
  [Mh_m(t_p)+\mathbf1_{p\equiv1\bmod q}k_m(t_p)].$$

**Proposition to test:** For every fixed $q\ge2$, joint
GRH for the primitive functions inducing the characters
modulo $q$, including zeta, is equivalent to existence of
one integer $m\ge8$ and real $A\ge1$ such that $W_{q,m}/X$
is nondecreasing on the entire real interval $[A,\infty)$.
For all the specified orders the two windows $Mh_m$ and
$Mh_m+k_m$ should be nonnegative everywhere and the
unconditional mean should be $M$. Seek strictly positive
forward derivative on the tail. The same formula applies
at $q=2$; order and onset may depend on $q$.

**Source and payoff:** This is an operator proposal, not
the [order-six criterion](../closed/fixed-modulus-neutral-order-six-prime-density.md)
at the evidence pin, which fixes the order and enlarges
the baseline depending on $q$. Inputs are the
[quartic derivative margin](../closed/zeta-prime-only-continuous-density.md)
at `a08d9dfe9adc87383319f9e970b60bd443cfcca2` and the
[unconditional low-zero certificate](../closed/zeta-prime-only-doubling-density.md)
at `d5301e8af8a5b4a76db76248f3264d9c9b5a394c`.
The payoff is to replace the modulus-dependent baseline
with this one explicit integer, not to prove joint GRH
or obtain a modulus-uniform order or onset.

**Discriminating test:** Bound the interior and end
pieces of the order-eight windows and propagate by
positive convolution. Apply the derivative formula to
$g_m=-k_m'-k_m$, with multiplier $(s-1)Q(s)\Phi(s)^m$,
$Q(s)=(4s^2-1)(s^2-1)$ and $\Phi(s)=\int_0^a e^{st}dt$.
Check exact central-zero cancellation and evaluate squares
using PNT on precisely the reduced classes with $b^2=1$.
Test summable domination of noncentral zeros by the
order-eight bound: First choose $m$ at fixed $q$, then
absorb the fixed-order errors as $X$ grows, comparing with
the transported quartic margin. In the converse, check
pole cancellation at one, noncancellation at coincident
zeta zeros using the unconditional certificate, negative
real residues, and the nonnegative-tail abscissa argument.

## Adjudication

**The fixed baseline works.** The order-six proof (lines 101–108 at
its pin) absorbs an $O_q(1)$ budget by increasing $M$. Instead, we
get a budget tending to zero with the order, in units in which the
baseline derivative retains the same positive lower bound.

### The assigned weights and their limit

Write $D=d/dt$. Repeated interval convolution gives
$$h_8(t)=\sum_{j=0}^8(-1)^j\binom8j(t-ja)_+^7/7!.$$
Each $h_l$ is symmetric about $la/2$. The tent $h_2$ decreases with
distance from its midpoint. Inductively, for $t\le(l+1)a/2$, $t$ is
no farther than $t-a$ from $la/2$, so $h_{l+1}'=h_l(t)-h_l(t-a)\ge0$
there. Hence $h_8\ge h_8(a)=a^7/7!$ on $[a,7a]$. On this interval,
for $i=2,4$, termwise differentiation bounds $|D^ih_8|$ by
$$C_i=\sum_{j=0}^8\binom8j(7-j)_+^{7-i}/(7-i)!,$$
since $a<1$. These are $242689/120$ and $11521/6$, respectively.
Since $a>1/2$, even $M/(2^7 7!)-5C_2-4C_4=781241032475/504>0$.
On $[0,a]$, $h_8=t^7/7!$ and
$k_8=t^3(4/3!-5t^2/5!+t^4/7!)\ge5t^3/8$. Reflection handles the
last piece because all derivatives in $k_8$ are even. Both assigned
weights vanish off the support. Positive convolution preserves both
inequalities for every higher order, since it commutes with the
indicated derivatives.

For $K_f(s)=\int f(t)e^{st}dt$, integration by parts gives
$K_{h_m}=\Phi^m$ and $K_{k_m}=Q\Phi^m$. Partial summation by the
fixed-class PNT at $p=Xv$ on $1\le v\le2^m$ gives, with $d=\varphi(q)$,
$$\lim_{X\to\infty} W_{q,m}(X)/X=M\Phi(1)^m+Q(1)\Phi(1)^m/d=M.$$
Here $\Phi(1)=1$, primes dividing $q$ eventually drop out, and no
zero hypothesis is used.

### Joint GRH gives a positive derivative

Let $U_l=X^{-1}\sum_p(\log p)h_l(t_p)$ and $\kappa=\Phi(1/2)$.
Convolution gives $U_{l+1}(X)=\int_0^a e^vU_l(Xe^v)dv$. From $l=4$
onwards the prime sum is locally finite and continuously
differentiable. The derivative therefore integrates $e^{2v}U_l'(Xe^v)$.
Since $Xe^v\ge X$, the pinned RH margin (quartic card, lines 44–58
and 85–119) propagates, multiplying by $\int_0^a e^{v/2}dv=\kappa$
at each step. Thus $X^{3/2}U_m'(X)>\kappa^m/100$ on the quartic tail.

Let $V=X^{-1}\sum_{p\equiv1\bmod q}(\log p)k_m(t_p)$ and
$g=-k_m'-k_m$. Since $h_m$ is $C^{m-2}$, at every real $X>0$,
$$X^2V'(X)=\sum_{p\equiv1\bmod q}(\log p)g(t_p),\qquad
 G(s)=K_g(s)=(s-1)Q(s)\Phi(s)^m.$$
To sum over prime powers, invert $G$ against $X^s(-L'/L)(s,\chi)$
on $\Re s=2$, then shift to $1/4$. Indeed $\Phi(s)=(2^s-1)/s$, so
$G=O_m((1+|\Im s|)^{5-m})$ across the strip, at worst cubic decay.
Lines 115–141 of `fixed-modulus-one-extra-vote-prime-density.md` at
`76d66112fa30b3a9cc28d24759ac6f8fe78f9e94` give the needed
kernel-independent bounds under the line hypothesis: Logarithmic on
the left vertical, squared logarithmic at zero-avoiding heights,
and $O_q(\log(3+|t|))$ zeros per unit interval with multiplicity.
Thus inversion and the zero sum converge absolutely, the horizontals
vanish for fixed $X$, and the left edge costs $O_{q,m}(X^{1/4})$.
No removed Euler factor or trivial zero meets the strip. The pole at
one contributes zero, and each zero contributes **minus** $X^\rho
G(\rho)$ with its multiplicity. In particular every central term is
exactly zero.

Averaging over all $d$ characters selects $p^j\equiv1\bmod q$.
To recover $X^2V'$, subtract the powers with $j\ge2$. For squares
use $T=\sqrt X$ and precisely the reduced classes
$B_q=\{b:b^2=1\pmod q\}$. Partial summation against $g(2\log v)$,
of bounded variation on the fixed interval $[1,2^{m/2}]$, and PNT
in each such class give their total as
$$T\frac{|B_q|}{d}\int_1^{2^{m/2}}g(2\log v)dv+o_{q,m}(T)
 =T\frac{|B_q|}{2d}G(1/2)+o_{q,m}(T)=o_{q,m}(T).$$
It is the signed main coefficient, not the absolute square sum, that
vanishes. For $j\ge3$ use $p\le(2^mX)^{1/3}$, $j\ll_m\log(2X)$,
and bounded $g$, giving $O_m(X^{1/3}\log^2(2X))$.

For $\rho=1/2+i\gamma$, set $r_\gamma=|\Phi(\rho)|/\kappa$.
For every $\gamma\ne0$ this is strictly less than one by the strict
triangle inequality for the integral with nonconstant phase. Hence
$$\frac{X^{3/2}|V'(X)|}{\kappa^m}\le D_{q,m}+o_{q,m}(1),\qquad
 D_{q,m}=\frac1d\sum_\chi\sum_{\gamma\ne0}
 |(\rho-1)Q(\rho)|r_\gamma^m.$$
The zero budget is independent of $X$. Its order-eight terms are
$O((1+|\gamma|)^{-3})$ and summable by the local count. They dominate
at every greater order, so $D_{q,m}\to0$ by dominated convergence
for this fixed $q$. Choose $m$ with $D_{q,m}<M/400$. Only now take
$X>q$ so large that the error in baseline units is below $M/400$ on
the whole tail. There $(W_{q,m}/X)'=MU_m'+V'>(M/200)\kappa^m X^{-3/2}$.
No estimate uniform in both $m$ and $X$ is required.

### Nondecrease forces joint GRH

Fix a witnessing order. By the unconditional limit,
$H(X)=MX-W_{q,m}(X)\ge0$ on the witness tail $[A,\infty)$.
Write $u_\chi=M\mathbf1_{\chi=\chi_0}+Q(s)/d$ for principal $\chi_0$,
and $R_\chi=\sum_p\sum_{j\ge2}(\log p)\chi(p)^j p^{-js}$.
For $\Re s>1$, absolute convergence, character orthogonality, and
the substitution $t=\log(p/X)$ give
$$\begin{aligned}
 F(s)&=\int_A^\infty H(X)X^{-s-1}dX\\
 &=\frac{MA^{1-s}}{s-1}+\int_0^A W_{q,m}(X)X^{-s-1}dX
 +\Phi(s)^m\sum_\chi u_\chi(s)\big[(L'/L)(s,\chi)+R_\chi(s)\big].
\end{aligned}$$
The plus signs follow because the prime-only series is $-L'/L-R_\chi$
and the deficit subtracts it. The endpoint is entire: Only primes
up to $2^mA$ enter and the sum vanishes below $2^{1-m}$. The series
$R_\chi$ converges normally for $\Re s\ge\sigma>1/2$ by the majorant
$\sum_p(\log p)p^{-2\sigma}/(1-2^{-\sigma})$. Removed Euler factors
are nonzero there. This continuation is regular at one: The principal
logarithmic derivative supplies residue $-M$, canceling $+M$.

At a zero $\rho$ with $1/2<\Re\rho<1$, write $S>0$ for the sum of
family multiplicities, one term per character. The residue is
$$\Phi(\rho)^m[M m_\zeta(\rho)+Q(\rho)S/d].$$
The prefactor cannot vanish since $|2^\rho|>1$. At a real $\beta$ in
the strip, zeta is nonzero by the positive paired eta series; then
$Q(\beta)<0$ and $\Phi(\beta)>0$, so the residue is negative. At a
nonreal zero not shared by zeta, $Q$ has no nonreal root. At a shared
zero $s=\sigma+it$, the bracket cannot vanish unless
$$\Im Q(s)=2\sigma t[8(\sigma^2-t^2)-5]=0.$$
This forces $t^2=\sigma^2-5/8<3/8$. The pinned low-zero certificate
(lines 89–133) excludes such zeta zeros unconditionally: It counts
zeros of $\xi$ in a rectangle by the argument principle, not just
zeros on the line.

There is also a short independent check on the possible cancellation
locus. Euler summation gives $\zeta(s)=1/(s-1)+1/2+E(s)$ with
$|E(s)|\le |s|/(2\sigma)$, by integrating the periodic first
Bernoulli function against $s x^{-s-1}$ from one to infinity. On the
locus, $|s-1|^2=2\sigma(\sigma-1)+3/8\le3/8$ and $|s|/\sigma<\sqrt2$.
Thus $|(s-1)\zeta(s)-1|\le\sqrt{3/8}(1+\sqrt2)/2<1$. In particular
no coincidence in this test relies on assuming RH in the converse.

The nonnegative integral has convergence abscissa $\alpha\le1$.
If $\alpha>1/2$, its continuation at the real point $\alpha$ is either
regular or a simple pole of negative residue (there are no zeros on
$\Re s=1$ by classical Dirichlet nonvanishing). The latter is
impossible since $F(u)\ge0$ for real $u>\alpha$. In the regular case
choose $u=\alpha+\epsilon$ so close that its Taylor disk reaches
$v=\alpha-\epsilon$. The coefficients in $u-s$ are the integrals of
$H(X)X^{-u-1}(\log X)^j/j!$, nonnegative for $X\ge A\ge1$;
convergence slightly left of $u$ justifies differentiation. Summing
at $v$ by monotone convergence gives a finite integral there, contrary
to the abscissa. Thus the integral is holomorphic on $\Re s>1/2$.
It cannot have any of the visible zero poles. Functional-equation
reflection stays in the primitive family, so joint GRH follows.

At $q=2$ the single principal character suffices and only the prime
$2$ is omitted. This isolates the baseline dependence; it neither
proves GRH nor gives a modulus-uniform order, onset, or optimal $M$.
