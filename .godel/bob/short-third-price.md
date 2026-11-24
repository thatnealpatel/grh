# Trade the twelfth radial cutoff for one short harmonic

Suppose a sufficiently large real high-endpoint failure passes the **order-eleven** signed screen $S_{11}\ge-.00014$ defined below. At the original height $t=2q^{3/5}$, one more *short* prime measurement $C_3\ge-.72$ then forces a right zeta zero at scaled depth $>1.95$. If instead $C_3<-.72$, there must be a right zero at depth $>1.40$ around **$3t$, not necessarily $t$**. Thus the disjunction needs the signed screen, but no premise about $C_3$. It is not the unconditional two-height disjunction in [the common-filter test](common-filter-pair.md).

Use $R=(9/5)\log q$, $V=R^2$, $D=\log V$, $d=D(\beta-1/2)$, and the centered windows of radius $(2/\epsilon)\log D$, including the centers. Fix sufficiently small $\epsilon>0$ before taking $q$ large. Write $z=D-\log p$, $u=|\cos((t/2)\log p)|$, $d\mu=V^{-1}\sum_p (\log p)\delta_{D-\log p}$. Denote Chebyshev polynomials by $L_j$ to distinguish them from the translated measurements $T_j$. Set

$$C_3=\int z_+ L_6(u)\,d\mu=V^{-1}\sum_{p\le V}(\log p)\log(V/p)\cos(3t\log p).$$

This uses an unshifted, **unsmoothed** short ramp. It is not a third radial order, and being on the same primes does not make it recoverable from the measured first sum. For the long measurements use exactly the [phase-shifted weights](phase-shifted-cutoff.md#the-two-measurements) at $(N,h,b)=(6,1/10,1/25)$ at $t$. With $v_k=\sqrt{2/13}\sin((k+1)\pi/13)$ for $0\le k\le11$, put $s_j=2\sum_{k=0}^{11-j} v_kv_{k+j}$ and $S_{11}=\sum_{j=2}^{11}s_j T_j/\cosh(jc)$ at $c=1.95$. Dropping the last term of the order-twelve screen without changing the coefficients would be a different measurement.

**Joint price.** For $|l|<6$ let $r_l=(6-|l|)/36$, $y_l=l/10+1/25$, $f(z)=\sum_l r_l e^{-y_l/2}(z+y_l)_+$, and $I=\sum_l r_l e^{-|l|/20}$. The failure gives $\int z_+ u\,d\mu\ge8/9-o(1)$. By the [first-order smoothing bound](masked-cutoff.md#five-shifts-and-their-first-price), $T_1=\int f L_2(u)\,d\mu+o_*(1)$, where errors have arbitrarily small limsup in the stipulated order. For $\lambda=3.48$, $\eta=.0147$, define

$$H(z)=\min_{0\le x\le1}\{f(z)L_2(x)-z_+[\lambda x+\eta L_6(x)]\}.$$

Apply the minimum **before** passing to the PNT limit. As $H$ is continuous, zero below $-.54$, and $O(1+z)$ on the right, Chebyshev controls the exponential tail as in the linked first-order bound. Then

$$ T_1-\eta C_3\ \ge\ \lambda\,8/9+\int H(z)e^{-z}\,dz+o_*(1).$$

[The checker](check-short-third-price.py) proves a lower bound $P>.57082929$ on the right-hand constant. For fixed $f_0=f(z)$ and $v=z_+$ the minimand has second derivative at most $4f_0+51\eta v$ since $-L_6''\le252/5$ on $[0,1]$. If a minimum is not an endpoint, compare the stationary point with the nearest node at spacing $1/512$. Subtract $(4f_0+51\eta v)/(8\cdot512^2)$ from the lower grid minimum. Integrate the chord of these lower bounds on each radial cell: The minimum of the affine functions of $z$ there is concave, and all ramp knots and zero are nodes. Beyond the last node $5$, use the endpoint lower bound plus $(z-5)$ times the lower minimum computed with the two slopes $\sum_l r_l e^{-y_l/2}$ and $1$. No restriction on the dependence of the phase on $z$ is used.

Under the shallow alternative at $t$, the normalized sine-vector polynomial and nonnegative Fejér mask of the [order-twelve argument](phase-shifted-cutoff.md) give the same inequality at degree eleven with $s_1=2\cos(\pi/13)$:

$$ S_{11}\le I/3-\frac{s_1}{\cosh c}(P+\eta C_3)+o_*(1). $$

At $C_3\ge-.72$ the limiting upper price is below $-.0002068$, strictly outside the screen. Separately, at height $3t$, $C_3$ differs from the smoothed unshifted order-one price by $o_*(1)$ (same short tent, bounded phase, negligible powers). If that window has no right depth $>1.40$, the [order-one trace](long-cutoff-moments.md#one-common-phase-on-the-divisor) gives $|C_3|\le\cosh(1.40)/3+o_*(1)<.72$ eventually: Reflection gives $|d|\le1.40$ there and $\log(3t)/R\to1/3$. No failure mean at $3t$ is needed.

**Decision at a candidate.** With the eleven signed orders available, compute $C_3$ on the short primes and use the joint price, not a price on $C_3$ inferred from one extremizer. In fact the [accepted order-eleven witness](translated-step-witness.md) has $-.90285<C_3<-.90283$ in its limiting model: Integrate $4a^3-3a$ against $z_+e^{-z}dz$ on its constant slabs, as in [its checker](check-translated-step.py). This excludes that particular witness at a much weaker lower bound than $-.72$; it does **not** exclude all shallow laws at that weaker bound. Both checkers run with SageMath's Python without `-O`. No short harmonic has been measured at a failing conductor. If $3t$ is unavailable and the joint price does not separate at $t$, retain the order-twelve test. Twelve remains the least maximum order for zero answers in the original fixed-translate model without the extra datum.
