# Long radial data can match, not just vanish

In the free prime-phase and shallow trace comparison at $t,3t$, long cutoffs test an arithmetic premise, not just more consequences of the short failure mean. A common first-layer law with a Fourier cap has a completion matching **all fixed radial orders and all fixed real translates** at both heights, when the long answers are not prescribed to vanish. The long prime answers are realized by phases on the *same primes* at both heights. The construction below is for this relaxation, not for phases $t\log p$ at a conductor, or for an actual zeta divisor.

Two consequences distinguish this statement from a zero-answer obstruction:

* The [two-height order-nine witness](two-height-translated-radial.md) has common cap $.62275$ and angular excess $>2.99\cdot10^{-6}$. Already at $c_*=\operatorname{arcosh}(3\cdot .62275)<1.23732$ it admits an all-order shallow completion. Thus adding arbitrarily many **fixed** translated radial identities with unconstrained long answers cannot force depth $>c_*$ from that mean alone in this model. For the decimal inequality, the Taylor sum for $\cosh(1.23732)$ through degree eight exceeds $3\cdot .62275$.
* At $c=39/20$ the [single-shift first law](single-shift-10-2.md) can keep every translated order $2,\ldots,10$ at $t$ exactly zero in the limit, **and** match every second translate at $3t$ with its Poisson-center value, generally nonzero. There is no contradiction with the [five-term separator](joint-refit-10-2.md), which prices a signed measurement. In particular the free phases are not restricted to the zero-answer path even after one restores the common prime law on all long cutoffs.

## From first moments to long prime profiles

Let $R=(9/5)\log q$, $V=R^2$, $D=\log V$, and use the [whole smoothed splines](long-cutoff-moments.md). At $z=D-\log p$ take a finite-slab finite-atom first law for $X=\cos\theta$, extending the last slab to infinity, with $X=0$ before the first slab. Write $Y_1=A=E X$, $Y_3=B=E(4X^3-3X)$, and $U=E\sqrt{(1+X)/2}$. Assume $Y_1,Y_3$ vanish below $a$ and $\|\widehat J_k\|_\infty\le C_1$ for $J_k(z)=e^{-z/2}Y_k(z)$, $C_j=\cosh(jc)/3$. Here $\widehat J(x)=\int e^{-ixz}J(z)\,dz$, $w=1/2+ix$, and $d\mu=dx/(2\pi|w|^2)$. Index $k=1,3$ denotes the height $kt$, not a radial order.

At each height take the trace $\mu$, symmetric depths $\pm c$, and conditional circle mean $m_k=-(\bar w/w)\overline{\widehat J_k}/C_1$. The Poisson law with parameter $m_k$ has all analytic moments $m_k^j$ (a point mass on equality in the cap). More generally take a fixed conjugation-symmetric unit-circle law of positive real mean $r_k\ge\|m_k\|_\infty$, and denote its moments by $\nu_{k,j}$. Multiply a sample by an independent unit-circle sample of Poisson parameter $m_k/r_k$. This gives moments $m_{k,j}=\alpha_{k,j}m_k^j$, where $\alpha_{k,j}=\nu_{k,j}/r_k^j$ is real and $\alpha_{k,1}=1$. The basic choice is $r_k=1$. For the second consequence use the twelve odd twelfth-grid angles $(2l+1)\pi/12$ rotated by $\pi$, with pre-rotation masses $(1-2r_1\cos((2l+1)\pi/12))/12$ and $r_1=1/(2\cos(\pi/12))$. The first cap for $A$ guarantees this radius suffices. The root sums give mean $r_1$ after rotation and $\nu_{1,j}=0$ for $2\le j\le10$. Use $r_3=1$ at $3t$.

For $j\ge1$ form the ordinary real convolutions

$$F_{k,j}(z)=(-1)^{j+1}\frac{C_j\alpha_{k,j}}{C_1^j}Y_k^{*j}(z).$$

In particular $F_{k,1}=Y_k$. A fixed $j\ge2$ profile is zero before $ja$, continuous, and bounded by a constant times $(z-ja)_+^{j-1}$: Integrate over the simplex left after translating each convolution variable by $a$. There is no assertion that $F_{k,j}$ itself is a cosine. Prescribe **$R^{1-j}F_{k,j}(jD-\log p)$** as the small cosine bias near endpoint $jD$.

## One assignment of phases

Keep the first law except on the disjoint layers $|\log p-jD|\le\sqrt D$, $2\le j\le\lfloor\sqrt D\rfloor$ (take $D$ large). These layers do not meet the short failure primes. On layer $j$, use the two prescribed biases together if the pair lies in the convex hull of $\pm(1,1)$ and $\pm(1/2,-1)$, and $(0,0)$; otherwise use $(0,0)$. All vertices come from $(X,4X^3-3X)$. The hull contains a neighborhood of the origin since the two generating directions are independent. For each fixed $j$, the polynomial growth just proved times $R^{1-j}$ ensures that eventually there is no clipping anywhere in its layer. The first law's entire finite alphabet is retained; the added vertices need represent only the small long biases.

This expectation construction also allows **deterministic** phases depending on $q$. In increasing order of primes add the probability vector at each prime to an accumulator, initially zero, and subtract one from its largest coordinate, using that atom at the prime. After every choice the sum of coordinates is zero, and each coordinate exceeds $-1$: Before subtraction the sum is one and the largest coordinate is positive. Thus every prefix discrepancy is bounded by the fixed alphabet size. Use $\theta_p=\arccos X_p$ and extend the unit values multiplicatively, with their cubes at $3t$. For each fixed observable one may replace the assigned atoms by their expectations at a cost $o(1)$. Indeed on $y=\log p\le(j+1/2)D$, the weight $y(k_\epsilon*B_j)(y-s)$ has supremum and total variation polynomial in $D$ for fixed shift $s$ and fixed $j,\epsilon$: The compact spline has polynomial supremum and piecewise derivative bounds, preserved up to $\|k_\epsilon\|_1$ by convolution. Partial summation against the bounded prefix discrepancies and division by $R^{j+1}$ prove the claim (sum over the finite alphabet). The identical argument with $y(D-y)_+$ on $[0,D]$ and normalization $R^{-2}$ covers the angular mean, which converges by PNT to $\int z_+e^{-z}U(z)\,dz$.

## What a fixed translated measurement sees

Keep the signed smoothing kernel $k_\epsilon$ on the **entire** translated spline, with $1/\epsilon>j+1$ for the test in question. The long-cutoff truncation bounds cited above are absolute, unchanged up to fixed factors by translation: Higher prime powers and $p>V^{j+1/2}$ cost $o(1)$, also for the deterministic phases. Higher layers are beyond this truncation for fixed $j$ eventually. The short layer contributes at most $O((1+D^j)R^{1-j})$ when $j>1$. Each fixed lower layer $2\le i<j$ costs at most

$$O_{i,j,s,\epsilon}\!\left((1+D^j)(1+D^{i}) R^{1-i}e^{iD+\sqrt D}/R^{j+1}\right)=o(1)$$

by Chebyshev, the bias bound, and $e^{iD}=R^{2i}$ (here $i$ is an integer index). This uses the actual log-prime mass, **without** an extra $p^{-1/2}$. No cancellation at intermediate spline knots is required.

For the intended layer put $z=jD-\log p$. The normalization $R^{-(j+1)}R^{1-j}=e^{-jD}$ makes the compact log-prime measure converge to $e^{-z}\,dz$ by PNT. For $j=1$ use the original first layer. On any compact $z$ interval, convolution of $B_j(y-s)$ at this endpoint tends uniformly to $\int k_\epsilon(v)h_j(z+s+v)\,dv$, since the remaining arguments of $h_j$ are shifted left by at least $D$ and the kernel has exponential tails. This convergence applies inside the prime integral: For all $z\ge ja$, the convolved finite difference is bounded in absolute value by $O_{j,s,\epsilon}((1+|z|)^j)$, since each truncated power's argument is at most $z+s+v$. After multiplying by $F_{k,j}$, the positive tail on each unit $z$ interval costs at most a polynomial in its location times $e^{-z}$ by Chebyshev, uniformly in $D$. There is no negative tail below $ja$. Thus for the Fourier-normalized shift, whose spline coefficient is $e^{-s/2}$, the exact model limit is

$$e^{-s/2}\int e^{-z}F_{k,j}(z)\int k_\epsilon(v)h_j(z+s+v)\,dv\,dz.$$

To identify it, the transform of $e^{-z/2}h_j(z)$ is $(1-w)^{j-1}/w^{j+1}=|w|^{-2}(\bar w/w)^j$ by integrating the truncated powers. Translation and convolution as displayed add the Fourier factor $e^{isx}g(w)$, $g(w)=\int k_\epsilon(v)e^{wv}\,dv$. Since $e^{-z/2}Y_k^{*j}=J_k^{*j}$, Plancherel multiplies by $(-1)^{j+1}C_j\alpha_{k,j}\overline{\widehat J_k}^{\,j}/C_1^j$. All the weighted profiles are in $L^1\cap L^2$ and the exponentially tilted kernel is integrable. The result is precisely

$$-C_j\Re\int e^{isx}g(w)m_{k,j}(x)\,d\mu(x).$$

This is the smoothed shallow boundary answer, with a minus sign at **every** order. Letting $\epsilon\downarrow0$ removes $g$ by dominated convergence ($|g(1/2+ix)|\le e$ for small $\epsilon$). The same assignment works for every fixed order and shift, with no uniform assertion for orders, translates, or masks growing with $q$. This proof does not assume a small error from unsmoothing the finite long prime sum.

## Price on the accepted five-shift mask

For the second example $F_{3,2}=-(C_2/C_1^2)(B*B)$. The [two-way price checker](check-five-shift-long-cutoff.py) integrates the piecewise affine convolution against each shifted $h_2$ including its tail and, independently, prices $m_3^2$ by the first-law jump kernel. After taking $\epsilon\downarrow0$, it gives $Q_t=0$ and $-.000886218<Q_3<-.000886216$. The per-shift contributions in support order $(-9,5,19,33,55)/25$, in millionths, are approximately $(-173.971,-301.953,-234.691,-219.539,+43.937)$. This uses the measured multiplier $-(C_1/C_2)h_l$, not $h_l$. In particular a lower bound of $-8\cdot10^{-6}$ on the signed sum, which would suffice for the five-shift screen, fails by more than a factor of 100 in magnitude on this common-phase model. A proof of that bound at actual failures must distinguish them from the model; more radial identities with no other control do not do so.

Replay the input caps with `sage .godel/bob/check-two-height-radial-witness.py` and `sage .godel/bob/check-single-shift-10-2.py`, and the new limiting price with `sage .godel/bob/check-five-shift-long-cutoff.py` at the repository root.
