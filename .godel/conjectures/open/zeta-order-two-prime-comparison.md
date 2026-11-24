---
evidence_revision: e29848af48be97061090219fcb2ea99e27079367
---

# The fixed order-two ordinary RH prime comparison

Let $h_2(t)=\max(0,\log 2-|t-\log 2|)$, and let the sums
run over all rational primes. For real $X>0$ set

$$B_2(X)=\sum_p (\log p)h_2(\log(p/X))-X,\qquad
S_2(X)=\sum_p (\log p)h_2(\log(p^2/X)).$$

**Proposition to test:** RH for ordinary zeta holds if and
only if there exists a real $A\ge1$ such that, for every
real $X\ge A$,

$$\sqrt2 B_2(X)-B_2(2X)\le S_2(X).$$

**Source and payoff:** This is an operator sharpening of the
linear case of the [Dedekind root-count comparison](../closed/dedekind-prime-root-critical-dilation.md)
at the evidence revision. The landing allows a choice of
order $m\ge2$ in its forward proof. Its fixed-order converse
already applies at $m=2$. A forward proof at order two would
give the exact log-tent criterion, with unchanged centering
and square allowance.

**Discriminating test:** Under RH, write $D(s)=\sqrt2-2^s$,
$\Phi(s)=(2^s-1)/s$, and $k=\Phi(1/2)$. Compare the
absolute zero sum $\sum_\rho |D(\rho)\Phi(\rho)^2|$, with
both signs and multiplicities, against $k^2/2$. First try
the bound $|D|\le2\sqrt2$ with the exact weighted sum of
$|2^\rho-1|^2/|\rho|^2$. If needed, use a trigonometric
majorant and explicit-formula cosine sums, or certified
low-zero savings from the exact inverse-square total. A
strict margin suffices by the landing's asymptotic; failure
of a sufficient bound does not refute the proposition.

## Adjudication of the fixed-order test

Write $E_2$ for the eventual inequality above. **$E_2$ is false,
including under RH.** Under RH there are violations for arbitrarily
large real $X$, with a positive margin on the $\sqrt X$ scale. Without
RH the landing's fixed-order converse rules out $E_2$. Thus order two
does not give the proposed criterion. The card stays open as worded:
The literal proposition $\mathrm{RH}\iff E_2$ is now equivalent to
$\neg\mathrm{RH}$, not proved false. Deciding that truth value would
require deciding RH; no further zero-budget estimate can do it.
The landing's existential choice of order is unaffected.

### A signed test at a recurrent phase

Put $a=\log 2$, $r=\sqrt2$, and $K=k^2/2=6-4r$. Under RH define

$$F(t)=-\sum_\rho D(\rho)\Phi(\rho)^2 e^{it\Im\rho},$$

including conjugates and multiplicities. Lines 72–93 of the linked
landing give, for linear $f$ and $m=2$,

$$\frac{rB_2(X)-B_2(2X)-S_2(X)}{\sqrt X}=F(\log X)-K+o(1).$$

All primes are good. The square term removed from the full Euler sum
is $K\sqrt X+o(\sqrt X)$ and cancels in the dilation. The allowance
on the right is not dilated and still costs $K$. The pole at one has
already supplied exactly the subtracted $X$.

The certificate below gives $F(-2a)>0.4516$. This is not an
application of the asymptotic at $X=1/4$. The series is real and
uniformly absolutely convergent by the inverse-square zero sum. For
any finite set of ordinates there are unbounded positive shifts
$q$ with all $e^{iq\Im\rho}$ arbitrarily near one, by simultaneous
Dirichlet approximation (multiples suffice in the exact-period case).
Truncate with uniformly small tail and recur on that finite set.
Thus $\limsup_{t\to\infty}F(t)\ge F(-2a)$, with no independence
assumption. The normalized excess has limsup greater than $0.1084$.
Lines 95–110 of the landing apply to this very order for the converse.

### Reproducible bound without zero locations

Use $G(s)=4^{-s}D(s)\Phi(s)^2=\int g(u)e^{su}\,du$ and
$w(t)=g(t)+e^{-t}g(-t)$. Then $F(-2a)=-2\sum_\rho G(\rho)$ under
RH. For $C=\log\pi+\gamma_E$, the completed-zeta explicit formula is

$$\sum_\rho G(\rho)=E-\tfrac12 Cw(0)+J-P,\qquad
 E=\int_0^\infty e^tw(t)\,dt,\quad P=\sum_n\Lambda(n)w(\log n),
 \quad J=\int_0^\infty\frac{w(0)-w(t)}{e^{2t}-1}\,dt.$$

Indeed, shifting the $\xi'/\xi$ integral from $c>1$ to $1-c$ and
reflecting gives the right-line kernel $G(s)+G(1-s)$, the transform
of $w$. The horizontal integrals vanish on zero-avoiding heights as
in the landing: The transform is $O((1+|\Im s|)^{-2})$ on the strip.
Expand the completed logarithmic derivative on the right as
$1/(s-1)-C/2+\int_0^\infty(1-e^{-st})/(e^{2t}-1)\,dt+\zeta'/\zeta(s)$
by the digamma expansion. Fourier inversion gives the four terms in
order. The inner absolute integral costs $O(\log(2+|s|))$ by splitting
at $1/|s|$ and $1$, so the exchange with the vertical integral is valid.

Here $g(t)=r h_2(t+2a)-h_2(t+a)$, so $w(0)=-2a$. On $[0,a]$ one has
$w(t)=t-a+e^{-t}((r+1)t-a)$, on $[a,2a]$ it is
$r(2a-t)e^{-t}$, and beyond $2a$ it is zero. Consequently

$$E=a-1+(2r-1)a^2/2,\qquad
 P=ra^2/2+(r/3)(\log3)(2a-\log3).$$

Only $2$ and $3$ contribute; $4$ has zero weight. An independent
one-sided calculation of $J$ uses $w(t)\ge w(0)$ for every $t\ge0$.
Truncating $(e^{2t}-1)^{-1}=\sum_{n\ge1}e^{-2nt}$ therefore bounds
$J$ **from above**, with no numerical tail estimate. For $b>0$ set

$$I_b=(1-2^{-b})/b,\qquad L_b=(1-(1+ba)2^{-b})/b^2.$$

These integrate $e^{-bt}$ and $te^{-bt}$ over $[0,a]$. With $c=b+1$,
the integral of $(w(0)-w(t))e^{-bt}$ over the positive half-line is

$$d_b=-2a/b-(L_b-aI_b)-(r+1)L_c+aI_c-r2^{-c}(aI_c-L_c).$$

For reproduction, evaluate the following finite expression with
160-bit real balls, initializing $a=\log(2)$, $r=\sqrt 2$, and $C$
from real-ball constants and all indices as exact integers:

$$F(-2a)\ \ge\ -2\left(E+Ca+\sum_{n=1}^{512}d_{2n}-P\right)
 \ \in\ (0.45164364069,0.45164364070).$$

The interval encloses the finite lower bound, not the full zero sum.
In particular the **true** absolute budget is at least $F(-2a)>K$;
no certified low-zero savings could make it small enough.

For the requested relaxed budget, apply the same formula to
$G(s)=(2^s-1)(2^{1-s}-1)/(s(1-s))$. On RH its zero sum is exactly
$Z_2=\sum_\rho |2^\rho-1|^2/|\rho|^2$. The product of the two
interval transforms gives $w(t)=2(2e^{-t}-1)$ on $[0,a]$ and zero
beyond, with no prime contribution even at $2$. Integration gives
$Z_2=4\log(3/2)-\log(3/4)-C$. Thus $2rZ_2\in(0.53060,0.53061)$,
whereas $K\in(0.34314,0.34315)$. The obstruction to the eventual
sign is the recurring **signed** excess, not that failed upper bound.
