# Two separated real hits force an untwisted peak at twice their sum

At the two raw hits in [the cluster test](principal-cell-clusters.md#if-both-clusters-contain-actual-signed-hits), one need not estimate the product character to get a further test. Write $u=|y_2-y_1|$, $h=8/9$, $D=\log X$, and normalize the frozen ramp by its mass $M=S_X(0)$. Throughout, $Q\to\infty$ and the raw heights in a block have span $O(H_X)$, so the [difference formula (1)](principal-cell-clusters.md#the-ramp-at-differences-not-at-the-peak-ordinates) applies up to any fixed multiple of that span. Assume **both** real projections with their signs are $\ge h-o(1)$ after normalization. Freezing the raw cutoffs and filling zero signs costs $o(1)$ as there. Then, eventually,

$$\Re S_X(2(y_1+y_2))/M > \begin{cases} .75173 & u\to\infty,\\ .72411 & u\ge 6.\end{cases} \tag{1}$$

The second line does not require equidistribution at a fixed difference. Neither conclusion follows merely from membership in two buffered principal cells. The high frequency in (1) is **not** in the range of the difference formula.

**Keep the direction.** For each prime let $a_i=s_{i,p}p^{iy_i}=e^{i\alpha_i}$, $v=u\log p$, and $f(v)=\sqrt{(1+|\cos v|)/2}$. The half-difference factor in the cosine addition formula has magnitude $|\cos((\alpha_1-\alpha_2)/2)|\le f(v)$. Thus, writing $x=|\cos((\alpha_1+\alpha_2)/2)|$ and $\mathbb E$ for the frozen probability mean,

$$ h-o(1)\le \mathbb E\Re[(a_1+a_2)/2]\le \mathbb E(fx), \qquad 1-\mathbb Ex\le\sqrt2\,(\mathbb E f-h)+o(1). $$

Here $f\ge1/\sqrt2$; no lower bound on the *actual* chord length is needed. If $\mathbb E f\le F+o(1)$, put $c=1-\sqrt2(F-h)$. Twice applying the double-angle identity and Jensen, first to $x$ and then to $\cos(\alpha_1+\alpha_2)$, gives

$$\mathbb E\Re (a_1a_2)^2\ge b(F)-o(1),\qquad b(F)=2(2c^2-1)^2-1,$$

provided $c>0$ and $2c^2-1>0$. This is the [adjacent chord argument](adjacent-chord-deficit.md) applied across heights at **one prime**, with no shifts of weights or missing end edges. The square removes both signs, leaving exactly the real projection in (1).

For $u\to\infty$, the difference angles are equidistributed, so take $F=m=2\sqrt2/\pi$. For $u\ge6$, use the absolutely convergent expansion

$$ f(v)=m+\sum_{n\ge1}(-1)^{n+1}\frac{4\sqrt2}{\pi(16n^2-1)}\cos(2nv). $$

The coefficients follow by integrating $\cos(v/2)$ on the period $[-\pi/2,\pi/2]$; evaluation at $\pi/2$ gives absolute nonconstant coefficient sum $m-1/\sqrt2$. For each fixed $n$, the normalized ramp at $2nu$ has modulus $\le(1+4n^2u^2)^{-1}+o(1)$ uniformly. Truncate at fixed order, take the limsup, and then send the order to infinity using the absolute tail bound. Thus take $F=m+(m-1/\sqrt2)/145$. The resulting $b(F)$ in the two cases exceeds $.75173$ and $.72411$, respectively, with strict slack before the asymptotic errors.

**Restriction on two populated clusters.** Let $A,B$ be two nonempty finite sets of raw hits in this window at a common $h-o(1)$ level. If their minimum cross-distance tends to infinity, then eventually

$$ \operatorname{diam}(A)+\operatorname{diam}(B)<1.293 \quad\text{in raw }y\text{ units}. $$

If their minimum cross-distance is only known to be at least 6, the bound is $2.211$. Indeed every pair sum $s\in A+B$ gives a unit vector $z_s(p)=p^{2is}$ of mean real part $>b_0$, with $b_0$ the corresponding decimal in (1). Take the largest and smallest sums $s,t$; their difference $d$ is the sum of the diameters. Then $4b_0^2<\mathbb E|z_s+z_t|^2=2+2\Re S_X(2d)/M$ by Cauchy. The latter ramp is at a **difference** and its modulus is $\le(1+4d^2)^{-1}+o(1)$ uniformly. At $d=1.293$ or $2.211$, respectively, this is strictly less than $2b_0^2-1$ before the error. This rules out simultaneous raw occupancy of some configurations, not any individual buffered cell.

**Separation from the marginal and product tests.** In a free-phase control at $u\to\infty$, put $r=[2u\log p]_{2\pi}\in[-\pi,\pi)$ and write $u\log p=r/2+k\pi$. Start at angle $t-r/4$ with sign $+1$, and at offset $u$ take sign $(-1)^k$. Choose $0<t<\pi/4$ with $\cos(2t)=37/40$. The signed angles are $t\mp r/4$ modulo $2\pi$. The two doubled real means tend to $(37/40)2/\pi>.587$, and the product-sign difference cosine mean tends to $2/\pi>.60429$ (it is $|\cos(u\log p)|$). But the untwisted doubled sum of the two angles has cosine $\cos(4t)=2(37/40)^2-1=.71125$ identically. Thus (1) detects a loss those scalar tests miss. There is no paradox: The raw means tend to $m\cos t<8/9$. At $t=0$ the model instead passes even (1). Neither rotation realizes an actual prime-height pair or characters.

**Use.** On a supplied pair of raw candidate intervals with a checked separation of at least 6, intersect twice their sum with a *positive real* principal search at level $.72411$ (or $.75173$ in the diverging-separation regime). This is the $j=2$ frequency at the raw midpoint, not the $j=1$ frequency there. For an integer-only search, round the conductor $((y_1+y_2)/2)^{5/3}$ to a nearest in-block integer: The height error is $O(Q^{-2/5})$, the frozen derivative is at most $DM$, and the change back to the midpoint cutoff costs $o(1)$. The strict slack in the proof absorbs these and $M=1+o(1)$. Enlarge the searched range for rounding when applying the intersection. Absence can rule out a **pair** along the stated sequences. It is not a finite exclusion certificate without explicit errors. Whether an extra list is worth computing depends on the surviving pairs; start with Work's individual-representative comparison, not a second search on empty input. The [rational checks](check-two-hit-sum.py) verify the constant comparisons, not occupancy or RH.
