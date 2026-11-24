---
evidence_revision: 6596fa6e00f481978d7f2792eec2b3dde99a8a29
outcome: established
---

# Test the order-two sign with an identity-class discount

**Proposition to test:** With natural logarithms, put
$h=\mathbf1_{[0,\log 2]}*\mathbf1_{[0,\log 2]}$ and
$K(s)=((2^s-1)/s)^2$, with the removable value at zero. For
$q\ge2$ let $d=\varphi(q)$, $L_q=\lceil\log(2q)\rceil$, and
$\delta_q=1/(\sqrt2 A L_q)$. Define
$$H(X)=(1-\delta_q/d)X-\sum_{p\nmid q}(\log p)
 (1-\delta_q\mathbf1_{p\equiv1\bmod q})h(\log(p/X)).$$
Do there exist an absolute positive integer $A$ and absolute
$X_0\ge2$, $c>0$ such that, for all integers $q\ge2$, $B\ge1$,
joint GRH for the primitive inducers modulo $q$, including
zeta, is equivalent to $H(n^B)\ge0$ for every positive
integer $n$ with $n^B\ge X_0$? Under that fixed-$q$ hypothesis,
require $H(X)\ge c\sqrt X$ on all real $X\ge X_0$. Conversely,
require only an arbitrary eventual tail of sampled signs.

**Source and payoff:** The pinned [triangular divisor card](../closed/triangular-weighted-character-zero-divisors.md)
gives the order-two expansion and a split-cell strip argument
for exact-value recovery. The [prior sign card](../closed/fixed-baseline-polynomial-sample-sign.md)
at `50cd94ded63eeaaaaecd31993cb28f211002139f` gives a
Landau obstruction for a different window, growing order,
and modulus-dependent onset. This is a proposed use of the
triangular expansion for one-sidedness, not a claim of either
landing. No monotonicity or named zero recovery is required.

**Discriminating test:** Split off the ordinary zeta deficit
and nonnegative bad-prime correction. Check the ordinary
prime-square constant, derive the inverse-square zero total
from the completed zeta product, and certify the margin
against the full zero-mass bound. Bound the smoothed identity
class discrepancy by $C\sqrt X\log(2q)$ with absolute $C$:
Check the primitive completed log-derivative difference,
left contour, trivial residue, imprimitive factors, and
prime powers under joint GRH for this $q$ only. Choose $A$
after this bound and check the uniform onset.

For the reverse direction, compute all grouped zero residues
and check their visibility and sign at real zeros without
GRH. Use the split-cell sub-first moment bound to continue
the same positive-tail sample Dirichlet series one strip at
a time. Check whether Landau excludes its real abscissa in
each strip and hence excludes every visible pole there,
including intermediate cut issues and abscissa $-\infty$.

## Adjudication

**Yes.** The ordinary square bias pays for all the zeta zeros with
room to spare. The class discount spends only a fixed fraction of
that room. In the converse, one excludes poles instead of subtracting
pole terms, so the nonnegative tail remains available at every cut.

### An absolute error bound for the identity class

Write $P_1,P_{\rm all},P_{\rm bad}$ for the sums with weight
$(\log p)h(\log(p/X))$ over the identity class, all primes, and
primes dividing $q$, respectively. The exact split is
$$H=X-P_{\rm all}+P_{\rm bad}-\delta_q(X/d-P_1),$$
where $P_{\rm bad}\ge0$. We need a conductor-uniform version of the
full prime-power shift at lines 69–109 of the triangular card, not
its $O_q(1)$ estimate for each fixed modulus.

For a primitive inducer of conductor $r$, let $D$ be the logarithmic
derivative of the entire order-one completion (use $\xi$ for zeta).
At $2+it$ the Euler series, the conductor term, and Stirling give
$|D|\ll\log(2r(2+|t|))$ absolutely. The functional equation gives the
same bound at $-1+it$ via the dual completion. In the Hadamard
difference the unknown constant and genus-one corrections disappear.
For $z=\beta+i\gamma$, put $y=t-\gamma$. Its real contribution is
$$\frac{2-\beta}{(2-\beta)^2+y^2}+
  \frac{1+\beta}{(1+\beta)^2+y^2}\gg (1+y^2)^{-1},$$
uniformly since $0<\beta<1$. Thus the sum of the latter weights,
counting orders, is $O(\log(2r(2+|t|)))$. On GRH, at $t=0$ this
gives $\sum_z|K(z)|\le(\sqrt2+1)^2\sum_z |z|^{-2}\ll\log(2r)$,
since $|z|^2=1/4+\gamma^2$.

For the full primitive sum $T_\chi=\sum_m\Lambda(m)\chi^*(m)
h(\log(m/X))$, inversion on $\Re s=2$ uses $X^sK(s)(-L'/L)(s)$.
Indeed $K(s)=\int h(v)e^{sv}dv$ decays quadratically in height on
$-1/2\le\Re s\le2$, and $h$ is continuous at its knots. Shift to
$-1/2$. The unit count just proved allows heights tending to each
infinity at distance $\gg_r1/\log(2+|t|)$ from nearby ordinates:
Exclude intervals of that radius in each unit interval. Comparing
$D$ to $D(2+it)$ on these horizontals costs $O_r(\log^2(2+|t|))$
from zeros within height one, and $O(\log(2r(2+|t|)))$ from the
others by the reciprocal-square difference. Removing the gamma and
conductor terms preserves vanishing of the horizontal integrals for
fixed $r,X$. On the left vertical the uncompleted functional equation,
the dual Euler series at $3/2$, and the gamma derivatives give
$|L'/L|\ll\log(2r(2+|t|))$ absolutely: The left gamma arguments
have real part $-1/4$ or $1/4$, away from poles. Hence for $X\ge1$,
$$T_\chi=\mathbf1_{r=1}X-\sum_z K(z)X^z
          +O(1+X^{-1/2}\log(2r)).$$
Here $K(1)=1$; the possible trivial zero at zero for an even
nonprincipal inducer is simple by the functional equation and
nonvanishing at one, so costs only $K(0)$. The fixed-conductor
constants on the discarded edges do not occur in this error.

Average with coefficients $1/d$ to project to the identity. Restoring
the imprimitive restrictions costs $O(\log(2q))$ even before averaging:
For each $p\mid q$ the support $[X,4X]$ allows at most
$1+\log4/\log p$ exponents, and $h$ is bounded. After projection,
removing all squares costs $O(\theta(2\sqrt X))=O(\sqrt X)$; the
higher powers cost $O(X^{1/3}\log(2X))$ by Chebyshev, summing over
$j\le\log_2(4X)$. Thus on the stated joint GRH,
$$|X/d-P_1|\le C\sqrt X\log(2q)\qquad(X\ge2)$$
with absolute $C$: Each zero sum costs $O(\sqrt X\log(2r))$ and
$r\le q$, with no factor $d$ after averaging.

### The ordinary margin and its quantifiers

Apply the same formula with $r=1$ to $X-P_{\rm all}$. The zero terms
now have plus sign. Adding back squares gives
$\sqrt X\int_1^2 h(2\log u)du+o(\sqrt X)$ by partial summation and
ordinary PNT for $\theta$; the integral is $K(1/2)/2$. The higher
powers are $o(\sqrt X)$ by the preceding estimate. On RH the absolute
zero budget in units of $\sqrt X$ is at most $(3+2\sqrt2)D_0$ with
$$D_0=\sum_z|z|^{-2}=2+\gamma_E-\log(4\pi).$$
Indeed the Hadamard difference $(\xi'/\xi)(1)-(\xi'/\xi)(0)$ sums
$1/[z(1-z)]$ over **all** zeros with multiplicities. RH gives
$1-z=\bar z$. Symmetry identifies the difference with $2\xi'/\xi(1)$;
logarithmically differentiating
$\xi=s\pi^{-s/2}\Gamma(s/2)((s-1)\zeta(s))/2$ at one gives the
displayed value, using $((s-1)\zeta(s))'|_{s=1}=\gamma_E$ and
$\psi(1/2)=-\gamma_E-2\log2$.

Here is an independent rational lower bound for
$M=6-4\sqrt2-(3+2\sqrt2)D_0$, where $6-4\sqrt2=K(1/2)/2$.
Set $p=16\sum_{j=0}^3(-1)^j/((2j+1)5^{2j+1})-4/239$; Machin's
formula and the alternating bounds give $3.14159<p<\pi$. Write
$f(x)=2\sum_{j=0}^7 u^{2j+1}/(2j+1)$, $u=(x-1)/(x+1)$, so
$f(x)<\log x$ for $x>1$. Since $H_{2048}^{\rm harm}-\log 2048$
exceeds $\gamma_E$, use
$$D_+=2+\sum_{j=1}^{2048}1/j-14 f(2)-f(p/2)>D_0.$$
With $t=1414214/10^6>\sqrt2$, exact fraction arithmetic gives
$6-4t>0.34314$ and $(3+2t)D_+<0.27066$. Thus $M>0.07248$ without
any zero ordinates as inputs.

Fix $m=0.07248$ and choose the positive integer $A$ so that
$C/(\sqrt2 A)\le m/4$. Since $L_q\ge\log(2q)$, this controls the
discount for every $q$. The baseline gives
$(X-P_{\rm all})/\sqrt X\ge M+o(1)$, whose only asymptotic error
concerns ordinary primes and zeta. Take one $X_0\ge2$ beyond which
that loss is at most $m/4$. The split now gives $H(X)\ge(m/2)\sqrt X$
on the whole real interval, hence at every required sample. Neither
$X_0$ nor $A$ is chosen from modulus-dependent asymptotics.

### Eventual sign excludes poles of the same series

Fix $q,B$ without GRH. For the discounted weight the character
coefficients are $\mathbf1_{\chi=\chi_0}-\delta_q/d$. Using the
full shift above, grouping equal zeros, and adding back powers and
bad Euler factors yields
$$H(X)=\sum_z c_zX^z+R_q(X),\quad R_q(X)=O_q(\sqrt X),\qquad
c_z=K(z)(m_\zeta(z)-\delta_q S(z)/d).$$
The principal mean cancels exactly, $S(z)>0$ sums all family orders
at $z$, and the power bounds needed no GRH. The unit count and
quadratic decay give $\sum |c_z|(1+|z|)^v<\infty$ for every $v<1$.
No zero is hidden: $K(z)\ne0$ in the open strip and $\delta_q$ is
irrational whereas $d m_\zeta(z)/S(z)$ is rational. At a real
$1/2<z<1$ the paired eta series is positive, so $m_\zeta(z)=0$
and $c_z<0$. There are no zeros on $\Re z=1$ by nonvanishing.

Assume $\Re z\le a$ for every zero, initially $a=1$. For $\Re s>a$
the series $F=B\sum_n H(n^B)n^{-1-Bs}$ allows absolute exchange
with the zero sum. Put $b=\max(1/2,a-1/B)$. On $\Re s>b$ the
$R_q$ series is holomorphic. For $u=1+B(s-z)$ subtract
$\int_n^{n+1}x^{-u}dx$ from $n^{-u}$ and call $B$ times the summed
differences $E_z$. On each compact, $\Re u\ge\eta>0$ uniformly.
Each difference equals $u\int_n^{n+1}(n+1-x)x^{-u-1}dx$, giving
holomorphy for fixed $z$. Split at $L=\lceil1+|u|\rceil$ and take
$e=\min(\eta/2,1/2)$. The head costs $O_B(L^{1-e})$ by bounding
values and integrals separately by $n^{-e}$. The tail costs at most
$B|u|L^{-\Re u}/\Re u$. Thus $E_z=O((1+|z|)^{1-e})$ on the compact.
The moment of order $1-e$ gives normal convergence of $\sum c_zE_z$.
The removed integral on the original half-plane is $B/(u-1)=1/(s-z)$.
Consequently $F$ continues to $\Re s>b$ as the remainder series plus
$\sum c_z(E_z+1/(s-z))$. The pole sum is normal off its locally finite
pole set. Every zero there gives a simple pole of residue $c_z$.

Under the sampled premise, discard a finite Dirichlet polynomial from
$F$ to obtain a nonnegative tail with frequencies $B\log n$. Its
abscissa $\alpha$ is at most $a$. If $\alpha>b$, the continuation
at real $\alpha$ cannot have a pole: Its residue would be negative,
contrary to nonnegativity from the right. Nor can it be regular:
Take a real center $r>\alpha$ near enough that its Taylor disk reaches
$v<\alpha$. The Taylor coefficients in $r-s$ are nonnegative moments
of the frequencies divided by factorials. Summing at $v$ and exchanging
nonnegative sums yields convergence of the tail at $v$, a contradiction.
Hence $\alpha\le b$, also covering an entire tail ($\alpha=-\infty$).
On $\Re s>b$ the convergent tail plus the finite polynomial is
holomorphic and agrees by uniqueness with the meromorphic continuation.
All visible poles there are therefore impossible.

Reset $a=b$ without changing $F$: No zero term had to be removed.
An intermediate cut is inside the next open strip. After at most
$\lceil B/2\rceil$ cuts, every family zero has real part at most $1/2$;
the functional equation within the family supplies the opposite bound.
This proves the converse for any eventual sampled sign, not for a
finite sample set. It neither assumes a rightmost zero nor imposes a
sign between samples. No derivative or named-divisor recovery is used.
