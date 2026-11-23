# Crossing the each-prime Weil window at second order

**Result.** Write $L=\log q$, $B=\log L$, $c=3/5$, $A=2+a/B$, and $b=\log(AL)$, with $0\le a<c$ fixed. As $q$ tends to infinity through primes, except for a fraction $O(\exp(-\delta L/B))$ of its primitive characters, for some fixed $\delta>0$,

$$
 Q_\chi(h)\ \ge\ (c-a-o(1))\frac{L}{B}\,\|h\|_2^2
 \qquad(h\in C_c^\infty(-b,b;\mathbb C)). \tag{1}
$$

The same lower bound holds relative to the Cauchy Gram matrix for **all** right-hand Pick blocks on distinct real nodes $m\ge B^3$, $\sum 1/m\le b$. Normalizations are those of the [each-prime theorem](prime-conductor-window.md); there are no moment or parity restrictions on the tests. The exceptional set is common to all tests and blocks at that prime. This crosses $A=2$ by order $1/B$, **not** by a fixed amount. The [dyadic result](dyadic-conductor-window.md) reaches fixed $A=2.1$ with another average over conductors; we do not take that average.

The decision is to estimate only a *weighted slice* of the prime shifts up to a height slightly greater than $q$. Its signed cost on the middle band is smaller than what removing that same slice saves in the unsigned Schur bound. A strict constant saving there suffices: Only the high band needs second-order precision.

## One finite operator for the tests and the blocks

Set $Y=q\exp(cL/B)$ and $Z=q^\alpha$, where the fixed $0<\alpha<1$ will be chosen near 1. Put $d=Z^{-1/2}$, $D_0=2b+B^{-5/4}$, $D=D_0+2d$, $X=e^D$, and $E=\sqrt X=AL+o(L/B)$. Translate compact inputs into $[0,2b]$ and zero-extend. Their explicit formula is the conductor and Gamma multiplier $L+g_j(y)$ minus the form of

$$T_\chi=\sum_{n\le X}\frac{\Lambda(n)}{\sqrt n}\big(\chi(n)U_{\log n}+\overline{\chi(n)}U_{-\log n}\big),\qquad (U_s h)(x)=h(x+s).$$

The enlargement is exact for those tests because the added shifts have zero correlation. For either parity $j$, $g_j\ge-O(1)$ and $g_j(y)\ge\log |y|-O(1)$ for $|y|\ge1$. Normalize $\|h\|_2=1$. All full-line prime-operator norms below are $O(E)$ by partial summation, including operators with weights bounded by 1.

For the block claim take instead a normalized exponential polynomial on $[0,\infty)$, extended by zero. Its full formula has the same multiplier and all prime shifts. The [block tail estimate](../adhoc/prime-translation-norm.md#4-a-whole-block-conductor-estimate) gives $\|1_{[s,\infty)}h\|_2\le\exp(H_0-\eta s)$, where $\eta=B^{3/2}$ and

$$H_0/\eta=\eta^{-1}\sum_m\log((m+\eta)/(m-\eta))\le 2b+O(\eta^2 B^{-6} b)=2b+O(B^{-2}).$$

Thus $v=1_{[0,D_0]}h$ has $\|h-v\|_2\le e^{-B^{1/4}/2}=o(1/B)$. Each omitted correlation above $X$ costs at most $e^{H_0} n^{-\eta}$. Partial summation with $\psi(t)=\sum_{n\le t}\Lambda(n)\ll t$ gives $\sum_{n>X}\Lambda(n)n^{-\eta-1/2}\ll X^{1/2-\eta}$ uniformly for $\eta\ge2$ (the integral factor is $(\eta+1/2)/(\eta-1/2)$). Hence omitting these shifts costs $O(Ee^{H_0-\eta D})=o(L/B)$ in the original unit form. In both settings we now have the same finite operator, with an input within $o(1/B)$ of a unit-ball function supported in $[0,D_0]$. The Gamma form is always evaluated on the original frequency pieces, never on an abrupt spatial truncation.

## A length-weighted moment for the slice

Use $w(r)=r e^{-2r/3}$ for $0\le r\le12$ and zero otherwise. Write $I_0=\int w^2$, $I_1=\int e^{-r}w^2$, $R=I_1/I_0$, and $M=\int r e^{-r}w(r)\,dr$. The scalar **forward** slice with prime coefficients $b_p=w(D-\log p)(\log p)/\sqrt p$ is $S_\chi(t)=\sum b_p\chi(p)p^{it}$. We prove that, outside the asserted exceptional fraction,

$$\sup_{|t|\le4Y}|S_\chi(t)|\le .428 E. \tag{2}$$

Let $k=\lfloor\log(qY)/(D+\log R)\rfloor$. Expand the $k$th power with coefficients $d_n\ge0$ supported up to $N=\lfloor X^k\rfloor$. For $j=0,1$, multinomials give $\sum n^j d_n^2\le k!(\sum p^j b_p^2)^k$: Each multinomial coefficient is at most $k!$, and its coefficient data are unique by factorization. By PNT and partial summation on the fixed log slice,

$$\sum b_p^2=(1+o(1))D I_0,\qquad \sum p b_p^2=(1+o(1))XD I_1.$$

Indeed the prime measure $\sum (\log p)\delta_p$ is replaced by Lebesgue measure against these piecewise smooth weights on $[Xe^{-12},X]$; the remaining $\log p$ equals $D+O(1)$ throughout. In particular the effective length ratio here is $XR$, not $X$.

Averaging over the characters of this *single* modulus gives

$$\mathbb E_\chi\int_{-5Y}^{5Y}|S_\chi|^{2k}\ll (\log(2N))^2\left(Y\sum d_n^2+q^{-1}\sum n d_n^2\right).$$

To see the weights, split at powers of 2 and pay $O(\log(2N))$ by Cauchy-Schwarz before integrating. Within $J<n\le2J$ the diagonal costs $10Y\sum d_n^2$; each surviving off-diagonal integral is bounded by $4J/|n-m|$ with $q\mid n-m$. Use $2d_nd_m\le d_n^2+d_m^2$ and sum the reciprocal multiples of $q$. Summing the blocks proves the display. Here $\log N=O(L)$, $k\sim L/B$, and $(XR)^k\le qY$, so the whole moment is at most $Y k! (D I_0)^k\exp(o(k))$.

By partial summation $|S'_\chi|\ll ED$. A peak exceeding $v_* E$ for $|t|\le4Y$ therefore costs an interval of length $D^{-2}$ at level $(v_*-O(1/D))E$ inside $[-5Y,5Y]$. Halving the peak would lose the needed constant. By Stirling the critical level in units of $E$ is

$$\frac{Y^{1/(2k)}\sqrt{k D I_0/e}}{E}=e^{c/4}\sqrt{2/(eA)}(I_0 I_1)^{1/4}+o(1).$$

In detail, $\log Y/(2k)=D/4+(\log R)/4+c/4+o(1)$ by $D=2B+O(1)$, while $kD=(2+o(1))L$. For $J(u)=[2-e^{-12u}((12u)^2+24u+2)]/u^3$, the integrals $(I_0,I_1,M)$ are $(J(4/3),J(7/3),J(5/3))$. Thus the limiting critical level is less than $.426$ (use $I_0<.844$, $I_1<.158$), while $M>.4319$. Markov with $v_*=.428$ proves (2) with exceptional fraction $\exp(-\Omega(k))$; the interval factor $D^2$ is $\exp(o(k))$. The principal character was included only in the averaging. Adding prime powers to the forward slice changes (2) by $O(D)=o(E)$, by partial summation for squares and absolute convergence for higher powers.

At the lower cutoff we use the elementary [each-prime moment estimate](prime-conductor-window.md#cancellation-below-a-frequency-cutoff): The **whole** finite multiplier is $o(L)$ uniformly on $|y|\le 2Z$ except for a fraction $q^{-(1-\alpha)/2+o(1)}$. Its proof applies verbatim since it only needs $D=2B+O(1)$, $E\asymp L$. Take the union of the two exceptional sets.

## What deleting the slice saves on the whole spatial interval

Let $T^{(\varepsilon)}$ denote the unsigned symmetric shifts on an interval of length $D$ after weighting each coefficient by $1-\varepsilon w(D-\log n)$, for $0\le\varepsilon\le1/2$. These weights are nonnegative. Uniformly in $D$ large we claim

$$\|T^{(\varepsilon)}\|/E\le 1-\varepsilon M+O(\varepsilon^2)+o(1/B). \tag{3}$$

In particular at $\varepsilon=0$ the high band has error $o(1/B)$. We give a discrete Schur proof; replacing atomic prime translations by a continuous kernel in operator norm would not be justified.

Use coordinates $0\le x\le D$, $s=D-x$, $f(x)=e^{-x/2}$, $u(x)=\int_0^\infty e^{-z} w(x+z)\,dz$. Then $0\le u\le1$, $\int_0^\infty e^{-z}u(z)\,dz=M$, and $u,w$ have bounded variation. Put $F(x)=f(x)(1-\varepsilon u(x))$ and take the positive Schur weight $W(x)=F(x)+F(s)$. In $T^{(\varepsilon)}F(x)$ the forward shifts cost at most $O(1+D)f(x)$ since $\sum_{n\le X}\Lambda(n)/n\ll 1+D$. The backward shifts cost exactly

$$f(x)\sum_{n\le e^x}\Lambda(n)\,[1-\varepsilon w(s+x-\log n)] [1-\varepsilon u(x-\log n)]$$

away from endpoints of measure zero. For $x\ge D/4$ partial summation replaces the sum by the integral in $dn$ from $1$ to $e^x$, with error $O(e^x e^{-c_1\sqrt D})$ by the classical quantitative PNT. Indeed the factors have uniformly bounded suprema and total variation under log translation, and $\sup_{t\le e^x}|\psi(t)-t|\ll e^x e^{-c_1\sqrt D}$ for these $x$. When $x<D/4$ the cost and the integral are each $O(e^{D/4})$ before the factor $f(x)$. In the main integral put $z=x-\log n$ and enlarge $0\le z\le x$ to $z\ge0$ by positivity. Dividing by $e^x$ gives an upper bound

$$\int_0^\infty e^{-z}(1-\varepsilon w(s+z))(1-\varepsilon u(z))\,dz =1-\varepsilon(u(s)+M)+O(\varepsilon^2)\le (1-\varepsilon M+C\varepsilon^2)(1-\varepsilon u(s))$$

with an absolute $C$. Since $f(x)e^x=Ef(s)$, adding the reflected row gives $T^{(\varepsilon)}W\le E W[1-\varepsilon M+C\varepsilon^2+O(e^{-c_1\sqrt D}+(1+D+e^{D/4})/E)]$. Here $W\ge(f(x)+f(s))/2$. Weighted Schur for symmetric nonnegative translations proves (3). The first variation $M$ is obtained from a correction to the *weight*, not from estimating only a trial function.

## Recombination without paying twice for the slice

Take smooth real low and high cutoffs $l,r$ as in the [two-band proof](prime-conductor-window.md#recombining-the-two-frequency-ranges-without-losing-the-support-bound), $l^2+r^2=1$, $r=0$ on $[-1,1]$, $r=1$ off $[-2,2]$. Split $h$ by the three Fourier multipliers $l(y/Z)$, $r(y/Z)l(y/Y)$, and $r(y/Y)$; write the pieces as $h_l,h_m,h_h$. Their squares sum to 1 since $Y>2Z$. Both multiplier forms and squared norms add exactly. The middle and high pieces have $o(1/B)$ spatial leakage in norm outside $I=[-d,D_0+d]$, uniformly per original unit input. Indeed replace the input by its supported approximation at $o(1/B)$ in norm. The high multiplier is identity plus a smooth compactly supported multiplier at scale $Y$; the middle one equals $l(y/Y)+(r(y/Z)-1)$, a sum of smooth compactly supported multipliers at scales $Y,Z$. The Schwartz kernel tails at distances $\ge d$ have $L^1$ norm $O_N((Zd)^{-N})$. Spatial truncation of either piece thus costs $o(L/B)$ in any of our finite prime forms.

For $v=h_m$, split $T_\chi$ into the residual of (3) with phases, and $\varepsilon$ times the signed symmetric slice. The residual on $1_I v$ is bounded above by the unsigned norm times $\|v\|^2$, by taking absolute values. For the slice let $C_\chi$ be its full-line forward operator (with prime powers). On $I$ every active shift connects a point within 12 of the left endpoint to a point within 12 of the right. Take a smooth cutoff $0\le L_0\le1$ equal to 1 on $[-1,13]$ and supported in $[-2,14]$, and its reflection $R_0(x)=L_0(D_0-x)$. Their supports are disjoint for large $q$. The slice form on $1_I v$ equals

$$2\Re\langle L_0 1_I v, C_\chi R_0 1_I v\rangle$$

with the inner product conjugate-linear first. Remove $1_I$ at cost $o(L/B)$ by leakage. Each of $L_0v,R_0v$ has norm outside the *Fourier* band $|y|\le4Y$ at most $O_N(Y^{-N})\|v\|$: The transform of $v$ is supported in $|y|\le2Y$ and the transform of either cutoff has uniformly rapidly decaying $L^1$ tails. Project both factors onto the wider band, use (2) there, and bound the error by the global $O(E)$ norm. Since $2\|L_0v\|\|R_0v\|\le\|v\|^2$ by disjointness, the cost is at most $(.428+o(1))E\|v\|^2+o(L/B)$, with **one** forward supremum, not two.

As $M>.4319$, first choose $\varepsilon>0$ fixed sufficiently small in (3). The whole middle prime cost is then at most $(1-\gamma)E\|h_m\|^2+o(L/B)$ for some fixed $\gamma>0$. Choose $\alpha<1$ with $1+\alpha>2(1-\gamma)$. The middle conductor plus Gamma term is at least $((1+\alpha)L-O(1))\|h_m\|^2$, so this piece has a positive fixed margin in units of $L$. The low piece costs $o(L)\|h_l\|^2$ in primes and also has a fixed margin. On the high piece use (3) at zero and $\log|y|\ge\log Y$: Its net coefficient is at least

$$L+\log Y-O(1)-(1+o(1/B))E=(c-a-o(1))L/B.$$

Summing the three estimates, including the additive errors per unit input, proves (1) and the block assertion. No exceptional set or frequency partition here is selected from the test vector.

## Next arithmetic test for a fixed gain

This proof does not bound the full sharp prime sum up to $T=q^{6/5}$. A direct use of [Chen, Gupta, and Li, Theorem 1.1](https://arxiv.org/abs/2507.08296v2) after powering and splitting into dyadic blocks cannot prove the desired count: At $X=(2.1L)^2$ every block $(N,2N]$ is supported on $X$-smooth integers. After the required coefficient normalization $|a_n|\le1$, its peak is at most $\Psi(2N,X)\le (2N)^{1/2}\prod_{p\le X}(1-p^{-1/2})^{-1}=N^{1/2}q^{o(1)}$ by partial summation. At a nonempty threshold $U$ the first term $N^2/U^2$ alone is therefore $\ge Nq^{-o(1)}$. The theorem requires $N\ge(qT)^{2/3}=q^{22/15}$. One time per distinct primitive character poses no separation problem. The issue is the stated bound, not a lower bound on the number of actual witnesses.

A concrete alternative target is a **two-product count**. For this paragraph reset $X=(2.1L)^2$, take $k=\lfloor(5/2)L/\log X\rfloor$, $N=X^k=q^{5/2+o(1)}$, and $V=L/B$. Let $\mathcal S$ consist of the integers that are products of $k$ primes in $[X/B^4,X]$, repetitions allowed. Count ordered distinct $n,m\in\mathcal S$ with $q\mid n-m$ and $0<|n-m|\le 2N/T$. A bound $O(q^{13/10-\xi})$ for some $\xi>0$, **uniform in prime $q$**, would suffice. Indeed the discarded small primes cost $O(\sqrt X/B^2)=o(V)$. The retained $k$th power has each coefficient, divided by $(V/4)^k$, at most $k!(\log X)^k(4/V)^k/\sqrt n\le q^{o(1)}N^{-1/2}$, since $k\asymp V$ and $n\ge N B^{-4k}=Nq^{-o(1)}$. A peak of the original prime sum above $V$ costs an interval of length $q^{-o(1)}$ above $V/4$ for the retained sum. Weight the time integral by $(\sin(t/(2T))/(t/(2T)))^2$, bounded below near $[-T,T]$, with transform $O(T)$ supported on $|y|\le1/T$. Orthogonality bounds the number of bad characters by $q^{1+o(1)}T/N$ times the diagonal count plus the indicated off-diagonal count (that is, the factor multiplies both counts). The diagonal is at most $N^{1/2}q^{o(1)}$ by the same smooth-number bound, so it costs only $q^{.95+o(1)}$. The prefactor is $q^{-.3+o(1)}$. It is the off-diagonal saving, not the smoothing or the diagonal estimate, that is missing. Neither this count nor positivity at fixed $A=2.1$ for most characters of each prime is asserted.

**Handoff update:** The [reduced-gap estimate](sparse-pair-gap.md) disposes of the pairs with $|n-m|/(q\gcd(n,m))\le q^{9/100}$ at cost $q^{259/200+o(1)}$. Test the remaining large reduced gaps, uniformly in prime $q$. Applying the same one-divisor row bound to the whole range gives $q^{7/5+o(1)}$, which is insufficient.
