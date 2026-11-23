# How far apart can clusters of biased prime ratios be tested?

Fix $c,a,\epsilon>0$. Use the frozen band $I=[e^{-8}X,X]$, $D=\log X$, $cD\le d\le 4D$, and the prime-pair sum $Z_d$ of the [dispersion note](prime-pair-dispersion.md). Put $L=X/D$ and $H=X^{(\log D)/4}$, with natural logarithms. In **every interval of length $H$**, the heights at which at least $\epsilon D$ shifts have $|Z_d|>a$ are covered by $O_{c,a,\epsilon}(1)$ intervals of length $O_{c,a,\epsilon}(L)$. This holds even for fixed arbitrary phases on the edges. The earlier second moment gave boundedly many clusters on the scale $X^2/D^3$. The new range exceeds every fixed power of $X$, but still permits a cluster at the named center.

The key is to majorize a *squared linear combination of evaluation vectors*, not a signed exponential sum over pairs of primes. Cancellation on progressions is needed for the majorant only, and at differences of heights, not at the center.

## A majorant with small off-diagonal Gram entries

Odd shifts are empty. For even $d$ write $G(d)=d/\varphi(d)$. We construct $v_d(n)\ge0$ on $I$ dominating every prime edge weight $w_{d,p}$. For $V_d(s)=\sum_n v_d(n)e^{is\log(1+d/n)}$, uniformly for $|s|\le H$ and $\tau=|s|d/X$,

$$ |V_d(s)|\ll \frac{G(d)^2}{1+\tau}+o(1). \tag{1} $$

Use $z=X^{1/8}$ and $v_d(n)=(8D^2/X)1_I(n)\sum_{m\mid n(n+d)}\lambda_m^+$. Use the weights in [Ford, *Sieve methods*, Lemma 2.2 and proof of Theorem 2.4](https://ford126.web.illinois.edu/sieve2023.pdf), specifically (2.8) and (2.10). They are supported on squarefree $m\le z$, have $|\lambda_m^+|\le1$, and the divisor sum dominates the indicator of no prime factor $\le z$. If $\rho(m)$ counts roots of $n(n+d)=0\pmod m$, it is multiplicative on these moduli, and $g(p)=\rho(p)/p$ is $1/p$ for $p\mid d$ and $2/p$ otherwise. The sieve hypothesis $(\Omega_0)$ holds with $\kappa=2$, $\delta=1/3$ (including $p=2$). Its main coefficient $\sum_m\lambda_m^+\rho(m)/m$ is nonnegative and $\ll\prod_{p\le z}(1-g(p))\ll G(d)^2/D^2$. The last bound compares with $\prod_{p\le z}(1-1/p)^2$ and uses Mertens' estimate. Every genuine pair in the band survives.

If $\tau\le X^{1/8}$, summation against the progression counting function gives the same integral $m^{-1}\int_I e^{is\log(1+d/x)}dx$ in every root class, with error $O(1+\tau)$ by total variation. The integral is $O(X/(1+\tau))$ by the first derivative bound for integrals (monotone phase derivative of magnitude $\asymp\tau/X$ for $s\ne0$). The normalized total error is $\ll (D^2/X)(1+\tau)z(1+\log z)=o(1)$, since $\rho(m)\le 2^{\omega(m)}\le d_2(m)$, the divisor count. This includes $s=0$.

For $X^{1/8}<\tau\le Hd/X$, take $k=\lfloor(\log D)/(2\log 2)\rfloor\ge3$. On a progression $n=r+my$ use $f(y)=s\log(1+d/n)/(2\pi)$, and $Y=|I|/m\asymp X/m$. The sum with $e(f)=e^{2\pi if}$ includes at most one extra endpoint. Writing the logarithm as $\int_0^d(n+w)^{-1}dw$ gives lower and upper bounds $\lambda,\Lambda$ for $|f^{(k)}|$ of the form

$$ \lambda= k!\,\tau(m/X)^k e^{-O(k)},\qquad \Lambda/\lambda\le e^{O(k)}. $$

The constants are absolute; the derivative has constant sign, so negate $f$ if needed. In particular $Y>k+1$, $\Lambda/(\lambda Y)\le X^{-3/4}$, $\lambda Y^k\ge X^{1/9}$, and $\Lambda^2/\lambda\le X^{-1}$ eventually. For the last bound use $m/X\le X^{-7/8}$, $\log\tau\le D(\log D)/4$, $7/(16\log 2)>1/4$, and $\log k!=O(k\log k)$. [J. Arias de Reyna, *Explicit van der Corput's $d$-th derivative estimate*, Theorem 11](https://arxiv.org/abs/2407.02094) bounds the sum divided by $Y$ by an absolute constant times the maximum of

$$ (\Lambda/(\lambda Y))^{2/2^k},\quad (\Lambda^2/\lambda)^{1/(2^k-2)},\quad (\lambda Y^k)^{-2/2^k}. $$

Since $2^k\le\sqrt D$, this is $O(e^{-c_0\sqrt D})$ for an absolute $c_0>0$. Crucially the cost per root class retains the factor $1/m$ in $Y$: After normalization the total is $O(D^2 e^{-c_0\sqrt D}\sum_{m\le z}d_2(m)/m)+o(1)=o(1)$. This proves (1). An unsigned upper sieve bound on the number of pairs alone gives no such Fourier estimate for the majorant, much less for the primes.

## From differences to the cluster count

Delete $G(d)>P$ for a fixed sufficiently large $P=P(\epsilon)$: At most $\epsilon D/2$ shifts are lost by the bounded mean of $G(d)^2$ (expand over squarefree divisors as in the dispersion note). On each retained shift $V_d(0)\le C_P$. View the prime sum as the inner product of the evaluation vector $(\sqrt{v_d(n)} e^{-iu\lambda_{d,n}})_n$ with a fixed vector of squared norm $\sum_p w_{d,p}^2/v_d(p)\le A_d\le C_P$, supported on the genuine positive-weight edges. Fixed phases only change this vector, not the Gram matrix. For any $N$ heights separated by $KL$ in the same interval of length $H$, its off-diagonal entries are bounded by $C_P/(1+cK)+o(1)$, by (1). Choose $K$ so these are at most $a^2/(2C_P)$ for large $X$. The squared evaluations sum to at most $C_P(C_P+(N-1)a^2/(2C_P))$, by the row sum bound and duality. Applying this only at the heights where the shift is large gives $N\le 2C_P^2/a^2$. Counting incidences over $d$ now bounds the size of any $KL$-separated family with $\epsilon D$ large shifts by $O_{a,\epsilon}(1)$. A maximal such family gives the cover.

At $X=(3\log(t/2))^2$ the cutoff changes by $o(1)$ even on $[t-H,t+H]$, since $H=t^{o(1)}$; endpoint and weight errors are $O(D^2/X)$ per sum. Enlarge the frozen shift range by fixed factors and lower $a$ slightly for the moving version. In particular for $t=2q^{3/5}$ an interval of heights of length $H$ near $t$ contains at most $O_{a,c,\epsilon}(q^{2/5}X/D)$ integer conductors with this simultaneous bias, by the mean value theorem. This is a local estimate, not an improvement to the dyadic power exponent. Failure of the common dip forces the center itself into this cover. It does not force two separated members, let alone more than the bounded number allowed. The estimate applies unchanged to a twisted isolated cluster; it is not an estimate of signed close-tuple cancellation at an isolated genuine one.
