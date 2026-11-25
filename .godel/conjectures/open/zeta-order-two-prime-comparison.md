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

This fixes the spline order in the linear case of the
[Dedekind root-count comparison](../closed/dedekind-prime-root-critical-dilation.md),
whose forward proof allows the order to vary.

## Adjudication

Write $E_2$ for the eventual inequality. **$E_2$ is unconditionally
false:** RH gives arbitrarily large violations by the signed sum below,
and the fixed-order converse $E_2\Rightarrow\mathrm{RH}$ excludes $E_2$
off RH. The literal $\mathrm{RH}\iff E_2$ is therefore equivalent to
$\neg\mathrm{RH}$ and remains open. The choice-of-order result is unaffected.

### The recurring excess on RH

Put $a=\log 2$, $r=\sqrt2$, $D(s)=r-2^s$, and
$\Phi(s)=(2^s-1)/s$ with its removable value at zero. On RH put
$F(t)=-\sum_\rho D(\rho)\Phi(\rho)^2 e^{it\Im\rho}$ over the nontrivial
zeros with multiplicities.
Since $h_2=\mathbf 1_{[0,a]}^{*2}$, the linked shift (lines 72–91)
gives the full Euler sum as $X-\sum_\rho X^\rho\Phi(\rho)^2+O(X^{1/4})$;
$\Phi(1)^2=1$ gives the exact centering. Removing exponents $j\ge3$ costs
$O(X^{1/3}\log^2(2X))$. By partial summation with PNT,
$S_2(X)/\sqrt X\to \tfrac12\int h_2(t)e^{t/2}\,dt=6-4r=:K$.
The removed square sum cancels to leading order under dilation; the
undilated allowance does not. Thus as real $X\to\infty$,

$$\frac{rB_2(X)-B_2(2X)-S_2(X)}{\sqrt X}=F(\log X)-K+o(1).$$

The conjugate-paired series converges uniformly absolutely by the
inverse-square zero sum. For any finite truncation and any fine partition
of its phase torus, infinitely many integer times land in one box.
Differences from its first visit give unbounded positive shifts with all
retained phases near one.
The uniformly small tail then gives $\limsup_{t\to\infty}F(t)\ge F(-2a)$.
The certificate below and $K<0.343146$ give excess greater than
$0.04996\sqrt X$ for arbitrarily large real $X$.

### A 32-term certificate, without zero locations

Set $G(s)=4^{-s}D(s)\Phi(s)^2=\int_{\mathbb R} g(t)e^{st}\,dt$,
where $g(t)=r h_2(t+2a)-h_2(t+a)$. On RH, $4^{-\rho}=e^{-2ia\Im\rho}/2$,
so $F(-2a)=-2\sum_\rho G(\rho)$. Put $w(t)=g(t)+e^{-t}g(-t)$ and
$C=\log\pi+\gamma_E$. Then

$$\sum_\rho G(\rho)=E-\tfrac12 Cw(0)+J-P,\quad
E=\int_0^\infty e^tw(t)\,dt,\quad
J=\int_0^\infty\frac{w(0)-w(t)}{e^{2t}-1}\,dt,\quad
P=\sum_n\Lambda(n)w(\log n).$$

Indeed, shift the $G\xi'/\xi$ integral from $\Re s=2$ to $-1$ and
reflect by the completed-zeta functional equation. The horizontal edges
vanish by the linked zero-avoiding height bound (and reflection) and
$G=O(|\Im s|^{-2})$ on the strip. The resulting right-line kernel
$G(s)+G(1-s)$ is the transform of $w$. Use
$\xi'/\xi(s)=(s-1)^{-1}-C/2+\int_0^\infty(1-e^{-st})/(e^{2t}-1)\,dt+
\zeta'/\zeta(s)$ and invert. The absolute inner gamma integral is
$O(\log(2+|s|))$ on that line, so the exchange is integrable.

For $t\ge0$, $w(t)=t-a+e^{-t}((r+1)t-a)$ on $[0,a]$,
$r(2a-t)e^{-t}$ on $[a,2a]$, and zero thereafter. Thus $w(0)=-2a$
and $w(t)>w(0)$ for $t>0$ (on the first interval each summand is
at least $-a$, with $t-a>-a$). Integration and the weights at $2,3$
give $E=a-1+(2r-1)a^2/2$ and
$P=ra^2/2+r(\log 3)(2a-\log 3)/3$; the weight at $4$ is zero.
Truncating $(e^{2t}-1)^{-1}=\sum_{n\ge1} e^{-2nt}$ gives
$J<\sum_{n=1}^{32}d_{2n}$, where $d_b$ integrates $(w(0)-w(t))e^{-bt}$
over $t\ge0$. The factor $-2$ reverses the inequality. In the code,
$I_b=\int_0^a e^{-bt}dt$ and $L_b=\int_0^a te^{-bt}dt$; splitting the
integral at $a$ and $2a$ gives `d(b)`.

The finite lower bound lies in $(0.39310681495,0.39310681496)$,
so $F(-2a)>0.39310681$. The real-ball calculations and exact-integer
inputs avoid untracked rounding.

```python
from sage.all import RealBallField
R = RealBallField(160)
a, r, l = R(2).log(), R(2).sqrt(), R(3).log()
C = R.pi().log() + R.euler_constant()
E, P = a-1+(2*r-1)*a*a/2, r*a*a/2+r*l*(2*a-l)/3

def IL(b):
    u = R(2)**(-b)
    return (1-u)/b, (1-(1+b*a)*u)/b**2

def d(b):
    c = b+1
    I, L = IL(b)
    i, j = IL(c)
    return -2*a/b-L+a*I-(r+1)*j+a*i-r*R(2)**(-c)*(a*i-j)

bound = -2*(E+C*a+sum(d(2*n) for n in range(1, 33))-P)
assert R(39310681495)/10**11 < bound < R(39310681496)/10**11
assert 6-4*r < R(343146)/10**6
```

### The fixed-order converse

If $E_2$ holds, the slack $H=S_2-rB_2+B_2(2\,\cdot)$ is nonnegative on
$[A,\infty)$, $A\ge1$. In the linked argument (lines 95–110) set
$Q(s)=\sum_p(\log p)p^{-s}$ and $R(s)=\sum_{j\ge2}Q(js)$, so that
$Q=-\zeta'/\zeta-R$ on $\Re s>1$. The tail transform there is

$$\int_A^\infty H(X)X^{-s-1}dX=
\Phi(s)^2[Q(2s)+D(s)(\zeta'/\zeta(s)+R(s))]
+D(1)A^{1-s}/(s-1)+E_A(s).$$

The entire correction is $E_A=-I_{S_2}(A,s)+rI_U(A,s)-2^s I_U(2A,s)$,
where $U=B_2+X$ and $I_V(b,s)=\int_0^b V(X)X^{-s-1}dX$;
only the dilated prime sum changes endpoint. The Euler remainders are
holomorphic for $\Re s>1/2$, and the centering tail cancels the pole at
$1$ since $\Phi(1)=1$. Each zero $\rho$ in that half-plane gives a pole
of residue $m_\rho D(\rho)\Phi(\rho)^2$ ($m_\rho$ its multiplicity):
$D\Phi^2$ never vanishes there and is negative at real zeros.

A convergence abscissa $b>1/2$ cannot be a pole (negative divergence
contradicts $H\ge0$). Nor can it be regular: the Taylor series from
$b+\epsilon$ would reach $b-\epsilon$ for small $\epsilon>0$, and its
nonnegative log moments would give convergence there by monotone
convergence. Thus the integral is holomorphic on $\Re s>1/2$, excluding
the zero poles. Reflection gives RH.
