---
evidence_revision: f5fbeb09e9b972565848e25ac295f3341a537afd
outcome: established
---

# Prescribe logarithmic order at the fixed baseline

**Proposition to test:** There is an absolute $C\ge1$
such that for every integer $q\ge2$, set
$m=\max(8,\lceil C\log(2q)\rceil)$. Joint GRH for the
primitive functions inducing all characters modulo $q$,
including zeta, is equivalent to eventual nondecrease
of $W_{q,m}(X)/X$ for every real $X$ on a full tail.
Use exactly the window at the evidence pin: $M=10^{15}$,
$a=\log 2$, $h_m=\mathbf1_{[0,a]}^{*m}$,
$k_m=4h_m^{(4)}-5h_m''+h_m$, and

$$W_{q,m}(X)=\sum_{p\nmid q}(\log p)
  [Mh_m(\log(p/X))+\mathbf1_{p\equiv1\bmod q}k_m(\log(p/X))].$$

On joint GRH seek eventual strict derivative positivity.
The beginning of the tail may depend on $q$ and $m$.

**Source and payoff:** The operator proposes strengthening
[the fixed-baseline criterion](../closed/fixed-baseline-variable-order-prime-density.md)
at the evidence pin, whose fixed-$q$ dominated convergence
provides no order in $q$. A bound uniform in $q$ for the
normalized zero budget would prescribe a single order
without changing the window, proving GRH, or promising a
uniform onset. The inputs are the quartic derivative
margin at `a08d9dfe9adc87383319f9e970b60bd443cfcca2`,
the contour argument at
`76d66112fa30b3a9cc28d24759ac6f8fe78f9e94`, and the
converse inputs in the fixed-baseline card, including
`d5301e8af8a5b4a76db76248f3264d9c9b5a394c`.

**Discriminating test:** Put $L=\log(2q)$. Under joint
GRH, derive or refute an absolute $O(\sqrt L)$ family
average of $\sum_\gamma \exp(-bL\gamma^2)$ for some
fixed absolute $b>0$. Check the explicit-formula signs,
conductor, gamma integral, and single zeta pole pair.
Test orthogonality of the primitive inducing values at
all $p^j$, including $p^e\Vert q$, where ordinary
orthogonality modulo $q$ does not apply directly. Then
combine the Gaussian with the central zero of $(s-1)Q(s)$,
quadratic decay of the normalized box transform near zero,
and an absolute per-unit zero count for its remote tail.
Test whether the resulting bound gives $D_{q,m}<M/400$
simultaneously for the prescribed orders. Check that the
pinned forward remainders need only be fixed-$q,m$ and
that its converse applies to this same prescribed order.

## Adjudication

**One absolute $C$ suffices.** At the evidence pin, lines 128–140
consume a normalized zero budget $D_{q,m}<M/400$. They obtain it
only after fixing $q$. We prove, under the forward hypothesis, the
absolute bound
$$D_{q,m}\ll \sqrt{L/m}+L\theta^{m-8},\qquad L=\log(2q),$$
for $m\ge8$ at least an absolute multiple of $L$, with a fixed
$0<\theta<1$. All zero sums below count multiplicities.

### Price a Gaussian before estimating the individual ordinates

Write $d=\varphi(q)$, and let $\eta=\chi^*$ be the primitive inducer
of a character modulo $q$, with conductor $c\mid q$ and parity
$\epsilon$. Use the primitive completion $E(s)$ with factors
$(c/\pi)^{(s+\epsilon)/2}\Gamma((s+\epsilon)/2)$. Write $\Xi=E$
except for zeta, where $\Xi=s(s-1)E$. To see that the unit-interval
count has an *absolute* constant, subtract the order-one Hadamard
logarithmic derivatives of $\Xi$ at $2+iT$ and $-1+iT$. The constant
and all product corrections cancel. The functional equation makes
the second derivative ratio minus the conjugate of the first. Since
$\rho=1/2+i\gamma$ on GRH, dividing the difference by two gives
$$\sum_\gamma\frac{3/2}{(3/2)^2+(T-\gamma)^2}
 =\Re\frac{\Xi'}{\Xi}(2+iT)\ll \log(2c(2+|T|)).$$
The difference series converges absolutely by order one. The bound
uses the absolute Euler series at two, Stirling for the two possible
gamma factors, and the bounded pole-removal terms for zeta. Each
ordinate within one of $T$ costs at least an absolute constant.

For $f(t)=e^{-Lt^2}$ take $\widehat f(u)=\int f(t)e^{-itu}dt
=\sqrt{\pi/L}\,e^{-u^2/(4L)}$. The primitive explicit formula is
$$\begin{aligned}
\sum_\gamma f(\gamma)={}&\mathbf1_{c=1}\,2e^{L/4}\\
 &+\frac1{2\pi}\int_{\mathbb R} f(t)\left[\log(c/\pi)+
 \Re\psi\!\left(\frac{1/2+\epsilon+it}{2}\right)\right]dt\\
 &-\frac1{2\pi}\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
  (\eta(n)+\overline{\eta(n)})\widehat f(\log n).
\end{aligned}$$
Indeed integrate $f((s-1/2)/i)E'(s)/E(s)$ on the two edges at
$2$ and $-1$, closing at zero-avoiding heights. For each fixed
conductor the local count permits separation $\gg_c1/\log(3+|T|)$;
subtracting the product derivative at $2+iT$ then gives at most
squared logarithmic growth across the horizontals (distant terms
are bounded by the displayed Cauchy kernel sum). Gaussian decay
kills these edges. The residues count zeros **minus** the poles at
zero and one for zeta, giving the positive pole pair above. Evenness
and reflection change the left integral into another right integral
for $\bar\eta$. Moving the gamma terms to the center crosses no
gamma pole. The Euler derivative on the right has a minus sign;
shifting the test integral for each $n^{-s}$ gives the displayed
Fourier factor. The resulting series converges absolutely at each
fixed $q$ by Gaussian decay in $\log n$.

For each prime $p$, remove its full local factor from $q$, writing
$q=p^e r$ with $p\nmid r$ (allow $e=0$). In the CRT decomposition,
exactly the characters with trivial local character at $p^e$ have
inducing conductor coprime to $p$. The others contribute zero at
$p^j$. The survivors correspond once each to **all** characters
modulo $r$. Since $p$ is a unit there, the inducing value agrees
with the value modulo $r$. Hence ordinary orthogonality *there* gives
$$\frac1d\sum_{\chi\bmod q}\chi^*(p^j)
 =\frac{\varphi(r)}{d}\mathbf1_{p^j\equiv1\bmod r}\ge0.$$
This includes $r=1$ and all good primes. Thus every averaged prime
term, including its conjugate, has nonpositive sign in the formula.
As a finite check, at $q=72$ enumerate characters using generators
$-1,5$ modulo $8$ and $2$ modulo $9$. Descend each value table to
the least divisor through which it factors, extending by zero on
nonunits there. The unnormalized sums at $2^j$ are $6$ for $6\mid j$
and zero otherwise; at $3^j$ they are $4$ for even $j$ and zero
otherwise (checked for $1\le j\le12$). The CRT argument, not this
finite check, gives the all-modulus sign.

Discard the prime term. The conductor costs $O(L/\sqrt L)$, and
the gamma integral is $O(1/\sqrt L)$ since $|\psi|\ll\log(2+|t|)$
on both lines and $L\ge\log 4$. Only the principal character gives
the pole pair. Its average $2(2q)^{1/4}/d$ is bounded absolutely:
$\varphi(q)\ge\sqrt{q/2}$ by multiplication of the prime-power
factors ($\varphi(p^h)/p^{h/2}\ge1$ for odd $p$, and at least
$1/\sqrt2$ for $p=2$). This proves
$$\frac1d\sum_\chi\sum_{\gamma_{\chi^*}}e^{-L\gamma^2}\ll\sqrt L.$$
No spacing or central nonvanishing is required.

### Transfer to the exact window

Put $\Phi(s)=\int_0^a e^{sv}dv$, $\kappa=\Phi(1/2)$,
$r(t)=|\Phi(1/2+it)|/\kappa$, and $Q(s)=(4s^2-1)(s^2-1)$.
For independent $Y,Y'$ with density $e^{v/2}/\kappa$ on $[0,a]$,
$1-r(t)^2=\mathbb E[1-\cos(t(Y-Y'))]\ge t^2\operatorname{Var}(Y)/2$
for $|t|\le1$, since $a<1$ and $1-\cos u\ge u^2/4$ there. Thus
$r(t)\le e^{-c_0t^2}$ for an absolute $c_0>0$. On this interval
$|(\rho-1)Q(\rho)|\ll |t|$ for $\rho=1/2+it$. When $c_0m\ge2L$,
maximizing $|t|e^{-c_0mt^2/2}$ bounds the summand by
$O(m^{-1/2})e^{-Lt^2}$. The Gaussian estimate gives the first
term of our budget; central zeros cost zero in the actual budget.

For $|t|\ge1$, $r(t)\le\theta<1$ by strict triangle inequality,
continuity, and decay of $\Phi(s)=(2^s-1)/s$. The order-eight
summand is $O((1+|t|)^{-3})$. Sum this bound over unit intervals
using the absolute local count above: The sum is $O(L)$ even before
averaging. The other $m-8$ powers give $\theta^{m-8}$. This proves
the claimed estimate for the exact $D_{q,m}$ of lines 131–133.
Choose $C\ge\max(1,2/c_0)$ large enough: The first term with its
absolute constant costs $O(C^{-1/2})$, and
$\sup_{L\ge\log4} L\theta^{CL-8}\to0$ as $C\to\infty$. Together
they cost strictly less than $M/400$ for every prescribed order.

At the evidence pin, lines 89–95 propagate the quartic margin by
positive convolution, giving $X^{3/2}U_m'>\kappa^m/100$. Lines
97–133 price the derivative of the identity-class term $V$ using
$G=(s-1)Q\Phi^m$. This time the Euler series are **imprimitive**,
so orthogonality selects exactly the reduced identity class. The
signed square main coefficient is $|\{b\bmod q:b^2=1\}|G(1/2)/(2d)=0$;
the higher powers and left contour are $o_{q,m}(\sqrt X)$ in
$X^2V'$. The removed factors have no zeros in the contour strip,
so the nontrivial zero budget is precisely the inducing one just
bounded. After fixing $q$ and its prescribed $m$, take $X>q$ on
a full tail with the normalized remainder below $M/400$. There
$$ (W_{q,m}/X)'>(M/200)\kappa^m X^{-3/2}>0.$$

Conversely, nondecrease for this $m$ supplies a witnessing order
in lines 144–197 of the evidence pin. In particular, the unconditional
limit is $M$, the Mellin deficit is nonnegative on the tail, and
the off-line residue test depends on $m$ only through the nonzero
factor $\Phi(\rho)^m$. No order selection is needed in that direction.
This prescribes the order, not the onset, and does not decide GRH.
