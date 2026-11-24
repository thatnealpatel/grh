---
evidence_revision: 69d5d30993da9b1de65d9d7930f06a86664cfa0b
outcome: established
---

# Test explicit constants for the discounted triangular sign

Let $h=\mathbf1_{[0,\log 2]}*\mathbf1_{[0,\log 2]}$ and
$K(s)=((2^s-1)/s)^2$ with the removable value at zero.
For integers $q\ge2$ let $d=\varphi(q)$,
$L_q=\lceil\log(2q)\rceil$, and
$\delta_q=1/(\sqrt2\,10^6 L_q)$. Use natural logarithms and
$$H(X)=(1-\delta_q/d)X-\sum_{p\nmid q}(\log p)
(1-\delta_q\mathbf1_{p\equiv1\bmod q})h(\log(p/X)).$$

**Proposition to test:** For every $q\ge2$, joint GRH for the
primitive inducers modulo $q$, including zeta, implies
$H(X)\ge\sqrt X/25$ for every real $X\ge2^{512}$. For each
fixed integer $B\ge1$, joint GRH for this family is equivalent
to $H(n^B)\ge0$ for every positive integer $n$ with
$n^B\ge2^{512}$.

**Source and payoff:** The [discounted sign criterion](../closed/order-two-log-discount-sampled-sign.md)
at the evidence revision proves an existential forward onset
and a qualitative all-$B$ converse. The [triangular divisor card](../closed/triangular-weighted-character-zero-divisors.md)
at `6596fa6e00f481978d7f2792eec2b3dde99a8a29` supplies
the compact triangular shift. The requested strengthening
fixes the discount, threshold, and margin, with no unspecified
forward size constants and no finite-test interpretation.

**Discriminating test:** Derive exact full Mangoldt identities
with kernels $K$ and $K(s/2)/2$ by sending left lines to
minus infinity after their horizontal edges vanish. Check the
trivial residues, all real knots, the prime-square lower and
upper bounds at $\sqrt X$, and the higher-power losses by
monotone estimates at the fixed threshold. Use the completed
log-derivative difference at $2,-1$ and average primitive
zero bounds, then charge omitted Euler factors and prime
powers. Compare the resulting rational budget against the
zeta margin and $1/25$ with the exact discount. Check that
irrationality and the sampled eventual-sign premises still
apply to the pinned Landau converse.

## Adjudication

**The specified constants work.** Write $Y=\sqrt X$ and use the
exact split at lines 60–65 of the evidence revision:
$$H=X-P_{\rm all}+P_{\rm bad}-\delta_q(X/d-P_1).$$
Here $P_{\rm bad}\ge0$ counts the excluded primes dividing $q$;
$P_1$ counts primes in the identity class. We bound the ordinary
term from below and the discrepancy in absolute value.

### Exact full sums

For $g(v)=h(v)$ or $h(2v)$, its transform $F(s)=\int g(v)e^{sv}dv$
is $K(s)$ or $K_2(s)=K(s/2)/2$, respectively. For any primitive
inducer of conductor $r$ and each real $U\ge2$,
$$\sum_m\Lambda(m)\chi^*(m)g(\log(m/U))
=\mathbf1_{r=1}UF(1)-\sum_\rho U^\rho F(\rho)-\sum_\tau U^\tau F(\tau).$$
The sums count nontrivial zeros $\rho$ and trivial zeros $\tau$ with
order. On $\Re s=2$ the Euler series is absolute, and Fourier
inversion of the continuous $e^{2v}g(v)$ uses an integrable transform.
Thus the integral of $U^s F(s)(-L'/L)(s)$ with measure $ds/(2\pi i)$
gives the left side even when an integer meets any knot.

To remove the vertical remainder in triangular-card lines 85–109,
first fix $J\ge1$ and shift to $\sigma_J=-2J-1/2$. The pinned
unit-height count allows upper and lower heights at distance
$\gg_r 1/\log(2+|t|)$ from nearby ordinates. Compare the completed
log derivative to its value at $2+it$ by the Hadamard difference:
The nearby terms cost $O_r(\log^2(2+|t|))$ and the distant ones
cost $O_{r,J}(\log(2+|t|))$ by the reciprocal-square weight.
Use $\xi$ for the zeta product. Removing the completion by Stirling
at those heights preserves horizontal vanishing since $F$ decays
quadratically on this fixed strip. On the left line the functional
equation uses the absolutely bounded dual Euler series and gamma
derivatives. The left gamma argument $(s+a)/2$ for parity $a$ has
real part $-J\pm1/4$: The cotangent in digamma reflection has
modulus one, and both right-half-plane digammas are bounded by
$O(\log(2+J+|t|))$ by Stirling. This uses the meromorphic gamma
completion in the zeta functional equation. Thus $|L'/L|\ll
\log(2r(2+J+|t|))$ with absolute constant. Both kernels are at
most $8/|s|^2$ there; rescaling $t=|\sigma_J|u$ bounds the integral
by $O(U^{\sigma_J}(1+\log(2r(2+J)))/|\sigma_J|)$, tending to zero.
No constant from either limit is spent in the budget.

The pole at one contributes positively, and zeros negatively. By
the functional equation and nonvanishing at and to the right of one,
the trivial zeros are simple at the nonpositive gamma poles of the
appropriate parity, except that zeta has only negative even ones.
The nontrivial sum is absolute by the unit count. The absolute
trivial sum is less than $10$: The possible zero at zero costs less
than one, and each $-k<0$ costs at most $2U^{-k}/k^2$.

### Lower bound at the stated onset

Under RH use $D_0=\sum_\rho |\rho|^{-2}=2+\gamma_E-\log(4\pi)$
from evidence lines 121–130. Set $k=K_2(1)=6-4\sqrt2$ and
$w=(3+2\sqrt2)D_0$. Then $k-w>0.07248$ (lines 132–142).
An independent rational check: Use $p=314159/10^5<\pi$ by the
four-term lower arctangent sum at $1/5$ and the one-term upper
sum at $1/239$ in Machin's identity. Put
$f(x)=2\sum_{j=0}^9((x-1)/(x+1))^{2j+1}/(2j+1)<\log x$ for $x>1$.
Then $D=2+\sum_{j=1}^{4096}1/j-15 f(2)-f(p/2)>D_0$ since
$H_{4096}^{\rm harm}-\log4096>\gamma_E$. With $t=1414214/10^6>\sqrt2$,
exact rational evaluation gives $46314<10^6D<46315$ and
$73204<10^6(6-4t-(3+2t)D)<73205$.

Write $Q_2=\sum_p(\log p)h(2\log(p/Y))$ for exactly the squares
at scale $X$. In the ordinary full sum $K(1)=1$ and on RH
$|K(\rho)|\le(3+2\sqrt2)/|\rho|^2$. Adding back powers gives
$X-P_{\rm all}\ge -wY-10+Q_2$. At scale $Y$ the ordinary full
$K_2$ sum differs from $kY$ by at most $10D_0\sqrt Y+10$, since
$|\rho|^2|K_2(\rho)|\le2(2^{1/4}+1)^2<10$. To obtain its prime
part $Q_2$, the removed powers $p^j\le2Y$, $j\ge2$, have total
weight at most $\sqrt{2Y}\log^2(2Y)/\log 2$: Bound the bases,
exponents per base, and weight per exponent separately using $h<1$.
Consequently $(X-P_{\rm all})/Y\ge k-w-E$, where
$$E\le 10/\sqrt Y+20/Y+\sqrt2\log^2(2Y)/(\sqrt Y\log2)
\le (10+2\cdot257^2)/2^{128}+20/2^{256}<1/1000.$$
Indeed $Y\ge2^{256}$ and $2/\log(2Y)-1/2<0$ is the logarithmic
derivative of the last variable term with respect to $\log Y$.
Also $Q_2\le kY+10\sqrt Y+10<2Y$. At scale $X$ all powers with
$j\ge3$ cost at most $(4X)^{1/3}\log^2(4X)/\log2$. Its ratio to
$Y$ decreases since $2/\log(4X)-1/6<0$ and at $2^{512}$ is less
than $2\cdot514^2/2^{85}<1$.

### Uniform cost of the discount

For a primitive nonprincipal character let $D_\chi$ denote the
completed log derivative. The functional equation with conjugation
gives $D_\chi(-1)=-\overline{D_\chi(2)}$ also for a complex character.
On GRH the Hadamard difference at $2,-1$ sums $3/(9/4+\gamma^2)$
over its zeros $1/2+i\gamma$ and equals $2\Re D_\chi(2)$.
Since $(1/4+\gamma^2)^{-1}\le9/(9/4+\gamma^2)$,
$$\sum_\rho |\rho|^{-2}\le3\big(\log(r/\pi)+\psi((2+a)/2)
                 +2\Re (L'/L)(2)\big)<3(\log r+5).$$
Here both $\psi(1)$ and $\psi(3/2)$ are less than one, and the
Euler series costs at most $\sum_{n\ge2}(\log n)/n^2<2$ by the term
at two plus the integral from two. With $\ell=\log(2q)>1$, $r\le q$,
and $3+2\sqrt2<6$, each full $K$ zero sum over nontrivial zeros
costs at most $108Y\ell$; zeta satisfies this separately by $D_0<1$.

Average the full sums with coefficients $1/d$; only zeta supplies
$X/d$. Each imprimitive restriction costs at most
$\sum_{p\mid q}(\log p+\log4)\le3\log q$, by counting exponents
in $[X,4X]$. After restriction the character average selects exactly
the identity class of each power. Removing its powers costs at most
$Q_2+Y<3Y$. Including the trivial sums gives
$$|X/d-P_1|\le108Y\ell+10+3\log q+3Y<200Y\ell.$$
As $L_q\ge\ell$, the exact discount and the favorable $P_{\rm bad}$
now give $H(X)/Y>0.07248-0.001-200/10^6=0.07128>1/25$.

### Why the sampled converse is unchanged

Fix $q,B$, without GRH. Lines 153–206 of the evidence revision
apply: The full-sum expansion of $H$ has grouped coefficients
$c_z=K(z)(m_\zeta(z)-\delta_q S(z)/d)$, where $S(z)>0$ sums
all family orders there. The remainder is $O_q(Y)$: Even off RH
the ordinary full $K_2$ sum is $O(Y)$ by absolute summability
and $\Re\rho<1$, and hence bounds the squares. The higher powers,
trivial terms, and omitted Euler factors obey the bounds above.
No coefficient vanishes since $K(z)\ne0$ in the open strip and
$\delta_q$ is irrational. At real $z>1/2$ in the strip, the paired
eta series rules out zeta and $c_z<0$.

If all $\Re z\le a$, the split-cell argument continues
$B\sum_n H(n^B)n^{-1-Bs}$ to $\Re s>b=\max(1/2,a-1/B)$ with
simple residues $c_z$ there. It requires only moments of $|c_z|$
of orders strictly less than one, supplied by quadratic decay and
the unit count. Discard the finite prefix before nonnegativity.
If the tail's real abscissa were greater than $b$, a pole there
would have negative residue, impossible from the right; a regular
point contradicts Landau's theorem for nonnegative coefficients.
The convergent series therefore excludes every pole to the right
of $b$. Starting at $a=1$, repeat with $a=b$ and the *same* series;
in at most $\lceil B/2\rceil$ steps no zero has real part greater
than $1/2$. Reflection within the family gives joint GRH. Thus even
an eventual nonnegative tail suffices in reverse; the forward
bound gives every sample from the specified threshold. This is
an infinite sign criterion, not a finite test of GRH.
