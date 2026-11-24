# A necessary gap window for two second translates

At depth $39/20$ in the $(10,2)$ comparison, the [152-slab prime law](single-shift-10-2.md) admits simultaneous zero second answers at any two $3t$ shifts whose distance $d$ satisfies

$$0\le d\le 3/16\qquad\text{or}\qquad d\ge4.$$

Consequently, only same-sign scalar masks with gap in $(3/16,4)$ can separate all common laws. The conclusion preserves all first translates, the zero orders two through ten at $t$, and the strict failure mean. It is not an assertion about actual prime or zero data.

Use the notation and certified bounds on $W,R,S,v,\mu$ from [the spacing certificate](separated-second-shifts.md). Write $V=R(0)>.50574$, $P=.476$, $K=.70$, and $\lambda=.48$. For two real coefficients the exact test is that capacity $\int|H|v\,d\mu$ covers center $|\Re\int Hm^2\,d\mu|$. Opposite signs and $d\ge7$ are already covered. It suffices to test same-sign coefficients; the compact convex separation argument in the spacing certificate then yields one completion per pair, not just one per mask.

## Small gaps

Normalize the positive coefficients to $a+b=1$. Then $|H|=|a+be^{idx}|\ge|\cos(dx/2)|$ since $4ab\le1$. Also $|H|\le1$. Subtracting $\int |H||m|^2\,d\mu\le1-V$ costs less than $.49426$, and the center costs at most $P$. Under the Cauchy probability,

$$\int |\cos(dx/2)|\,d\mu=\frac2\pi\left(1+2\sum_{k\ge1}\frac{(-1)^{k-1}q^k}{4k^2-1}\right),\qquad q=e^{-d/2}.$$

This is the cosine series of $|\cos(u/2)|$ integrated termwise. Its truncation after $k=16$ is a lower bound and increases with $q\in[0,1]$: In its derivative each odd term dominates the next even term since $k/(4k^2-1)$ decreases. At $q=e^{-3/32}$ this truncation exceeds $.9711$, paying both costs.

## Moderate to large gaps

For $4\le d\le7$ normalize the larger positive coefficient to $1$, the smaller to $r\in[0,1]$. Let $x,y$ be the magnitudes of $S$ at the respective shifts. The two exponential caps give $xy\le K^2 e^{-\lambda d}$ by the triangle inequality. Since both are at most $P$, $(P-x)(P-y)\ge0$ implies $x+y\le P+xy/P$. Thus $(1-r)x+r(x+y)\le P+r K^2 e^{-\lambda d}/P$, even when the larger coefficient is on the smaller center.

Write the cosine series of $|1+re^{iu}|$ as $c_0+\sum_{k\ge1}(-1)^{k-1}c_k\cos(ku)$ with $c_k\ge0$ as in the spacing certificate. With $b_j=\binom{1/2}{j}$, expanding the two square roots gives

$$c_0=\sum_{j\ge0} b_j^2r^{2j},\qquad c_1=r+2\sum_{j\ge1} b_j b_{j+1}r^{2j+1}.$$

The expansions converge absolutely even at $r=1$. Every product in the last sum is negative. At $r=1$ the explicit cosine series of $2|\cos(u/2)|$ gives $c_0=4/\pi$, $c_1=8/(3\pi)$. Therefore

$$1+r^2/4\le c_0\le1+.274r^2,\qquad c_1\ge r-.152r^3.$$

At $u=\pi$ all nonconstant terms subtract, so $\sum_{k\ge2}c_k=c_0-(1-r)-c_1\le .426r^2$. The existing envelope $|W(h)|\le(.38+10^{-6}h)e^{-h/2}$ gives $R(d)\ge .309q$ and $|R(kd)|\le .691q^2$ for $k\ge2$, by monotonicity of the upper envelope for $R$ at $2d\le14$. This retains the favorable sign of the first harmonic. Combining prices and using $r^3\le r^2$ gives the following lower bound on capacity minus center:

$$.50574-P + r\left(.309q- K^2e^{-\lambda d}/P\right)+r^2\left(.50574/4-.309\cdot .152q-.691\cdot .426q^2\right).$$

Both coefficients are increasing in $d$: For the linear one use $\lambda K^2/P>.309/2$ and $\lambda<1/2$. At $d=4$ denote them by $L,Q$. Here $Q>0$ and $.50574-P-L^2/(4Q)>.00379$, so the price works for every $r$. The endpoints of the remaining gap window are sufficient bounds, not claims of sharpness.

Replay `sage .godel/bob/check-two-gap-window.py` from the repository root (SageMath 10.9, assertions enabled); it rechecks the underlying 152-slab envelopes first.
