# How far to extend a radial prime cutoff

At a real high-endpoint failure, how many of the [smoothed prime sums at the original height](long-cutoff-moments.md) would have to be small to force a deeper zeta zero? At scaled depth $c=1.90$, order **15** suffices in place of the general equal-coefficient construction's 54. Even knowing every order through 14 to be zero is insufficient **in the moment model**. At $c=1.75$ the earlier four-length certificate already has the least possible maximum order. In fact no two additional individual orders, however large, can replace the three used there on the zero-answer path.

Use the linked note's $R,V,D,t,J$ and $P_j$. An order $j$ uses endpoint $jD$ in log-prime coordinates, not a new height. At failure $P_1\ge p=47/81$ up to small errors. Under the additional hypothesis of no right zero at scaled depth $>c$ in $|\gamma-t|\le J$, equation (1) and harmonic extension there give the following limiting test:

$$m_0=1,\qquad m_j=-3P_j/\cosh(jc),\qquad m_1\le-a,\quad a=3p/\cosh c.$$

Every nonnegative even trigonometric polynomial must have nonnegative evaluation on these cosine moments. In all arithmetic applications use **strict margins**: For fixed $n,c$ the errors through order $n$ can be made arbitrarily small by fixing sufficiently small $\epsilon$ and then taking $q$ sufficiently large. The moment-model converse below is not a construction of zeros or primes.

## A signed test, and a matching law

If the measured values are not near zero, form the symmetric Toeplitz matrix $T=(m_{|i-j|})_{0\le i,j\le n}$ using the actual $P_1$ if available. Shallow data require $T\succeq0$: Apply the comparison to $|\sum_k v_k e^{ik\theta}|^2$ with real coefficients. A strictly negative quadratic form after accounting for errors rules out the shallow window; a small negative eigenvalue of a rounded matrix is not a certificate. For a fixed vector, errors $e_j$ on $m_j$ cost at most $2\sum_{j=1}^n e_j|\sum_{k=0}^{n-j}v_k v_{k+j}|$.

This checks the entire finite circle-moment condition, even at a singular boundary: If $T\succeq0$, take Gram vectors $u_0,\ldots,u_n$ in a finite complex Hilbert space. The map $u_k\mapsto u_{k+1}$ on the first $n$ vectors preserves their Gram matrix. It is thus a well-defined isometry between their span and the shifted span; extend it to a unitary $U$ on the whole space. The spectral measure of $U$ in $u_0$ has mass one and moments $\langle u_0,U^j u_0\rangle=m_j$ through order $n$. Symmetrize it in the angle if desired. Place this law on the strip boundary $|d|=c$ to match the model's cosine moments. Thus a *feasible* prefix is not evidence that another cutoff will separate it. Unknown entries are free subject to the constraints, not zero by default.

For zero longer measurements, $T$ with $m_1=-a$ is tridiagonal. Put $b_n=1/(2\cos(\pi/(n+2)))$ for $n\ge1$. **Separation from the shallow model is possible exactly when $a>b_n$.** Indeed the vector

$$v_k=\sqrt{2/(n+2)}\sin((k+1)\pi/(n+2)),\qquad 0\le k\le n,$$

has squared norm one and is positive. With zero boundary values at $k=-1,n+1$ it obeys $v_{k-1}+v_{k+1}=2\cos(\pi/(n+2))v_k$. The quadratic form at $m_1\le-a$ and $m_2=\dots=m_n=0$ is at most $1-2a\cos(\pi/(n+2))$. Conversely put mass $(1-2a\cos\theta)/(n+2)$ on each $\theta=(2l+1)\pi/(n+2)$, $0\le l<n+2$. The masses are nonnegative for $0\le a\le b_n$. The uniform grid kills all frequencies $1$ through $n+1$, so these tilted masses sum to one and give exactly $m_1=-a$, $m_2=\dots=m_n=0$. This includes equality and does not use a numerical PSD decision.

In use, set $s_j=2\sum_{k=0}^{n-j}v_k v_{k+j}>0$. At a shallow failure the limiting signed price is

$$\sum_{j=2}^n s_j\,P_j/\cosh(jc)\ \le\ 1/3-s_1p/\cosh c,\qquad s_1=2\cos(\pi/(n+2)).$$

At $c=1.90$, $n=15$ the right side is below $-.0004360$. For sufficiently small fixed $\epsilon$ and large $q$ the left side must therefore be **below $-.00043$**. Compare the measured combination, not separate absolute bounds. This is usable with signed nonzero measurements as well. It does not say that the required measurements are available.

| $c$ | Least maximum order $n$ for a strict zero-data separation | Least $n$ with the equal-coefficient test alone |
|---:|---:|---:|
| 1.54 | 2 | 3 |
| 1.67 | 3 | 4 |
| 1.75 | 4 | 6 |
| 1.80 | 5 | 9 |
| 1.81 | 6 | 10 |
| 1.90 | 15 | 54 |

The last column tests $2an/(n+1)>1$. It is **not** the cost of the earlier special certificates at $1.54$ or $1.75$; those already use the optimal orders. With $\delta=2a-1\downarrow0$, the least $n$ grows as $\pi/\sqrt{2\delta}$ instead of $1/\delta$. This compares fixed-parameter requirements as the target varies, not an explicit formula uniform in $n$ for the error in the prime sums.

## Can a few higher orders replace the prefix?

For $1\le n\le5$, among sets of $n-1$ distinct additional orders $\ge2$, the prefix $2,\ldots,n$ minimizes the largest compatible value of $-m_1$ when all the queried moments vanish. The minimum is $b_n$. This is about individual moment queries, not the number of linear combinations or the cost of evaluating them jointly.

To prove the other direction for a non-prefix set, let $h+1$ be its least missing order starting at 2. Use the tilted grid above through order $h$ with $a=b_h$; $h=1$ is allowed. Add an independent symmetric shift $\pm\pi/(2r)$ for each remaining queried order $r$. This multiplies each complex moment of index $j$ by $\cos(j\pi/(2r))$, retaining its existing zeros and killing order $r$. The new value of $-m_1$ is at least

$$b_h\prod_{r=h+2}^{n+1}\cos(\pi/(2r))\ >\ b_n\qquad(1\le h<n\le5).$$

Here the product uses the *smallest* possible distinct remaining orders; each cosine increases with $r$. The ten strict comparisons are [ball-checked](check-long-cutoff-moments.py). To match any smaller target $a$ exactly, mix with uniform measure. For $c=1.75$ one can see the two-query obstruction without the grid: Start at $\theta=\pi$ and use both shifts. For any pair $2\le r<s$, $-m_1\ge\cos(\pi/4)\cos(\pi/6)>3/5>a$. Thus even choosing the second order after a first zero answer cannot save a query in this model. For an adaptive test using $P_1$ too, fix $m_1=-a$ by the mixture. These countermodels are for the measurement path, not for a claimed actual conductor.

Consequently the first five rows have least **numbers** of additional zero measurements $1,2,3,4,5$, respectively: Compare with the obstruction at the previous order. At $1.90$ the proof gives a sharp *maximum order*, not a sharp sparse count. In fact the displayed product bound falls short of $b_6$ for $h=5$; this is not a sparse counterexample to optimality. Nothing improves the all-orders ceiling $\cosh c=6p$.

**Decision at a surviving candidate.** Start with the doubled cutoff as before. For a specified deeper target, test the prefix already measured, with error bounds, before extending it. If only the first lower price and a near-zero scenario are known, use the signed sine-vector price at the indicated length, not a long equal-coefficient sum. If data remain feasible, seek additional arithmetic information or retain the original signed census. Neither positivity of an estimated matrix nor reaching the tabulated length decides the actual failure without signed data. No uniform $Z$ exclusion or effective threshold for $q$ follows here.
