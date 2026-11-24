# A common ceiling for all dilations and harmonics

Changing a prime cutoff beats the old undilated ceiling, but how much more depth can such a change buy? In the [dilated ramp normalization](dilated-first-ramp.md), let $\theta$ be the doubled phase, $U=|\cos(\theta/2)|$, and let $P_z$ range over measurable conditional probability laws for $\theta$ at $z=\log(V/p)$. Impose only the continuum failure datum

$$\int_0^\infty z e^{-z}\mathbb E_{P_z}U\,dz\ge 8/9.$$

Write $C_j(l)=e^{-l/2}\int_{\mathbb R}(z+l)_+ e^{-z}\mathbb E_{P_z}\cos(j\theta)\,dz$. Then

$$.5895467121\ \le\ \inf_{(P_z)}\sup_{j\ge1,\ l\in\mathbb R}|C_j(l)|\ <\ .59084.$$

The lower bound uses just the two signed tests in the linked note; its pointwise dual inequality integrates against conditional laws. For the upper bound we exhibit **one law for every harmonic and every cutoff simultaneously**. Its sine moments are zero, so the same obstruction holds for complex moduli. The possible gain over the two-test lower certificate is less than $.001294$ in the normalized price. In particular, even all these tests cannot force a price $\cosh(1.175)/3$ from this datum alone. This is a limit on the positive-margin packet argument, not a limit on the actual depths of zeta zeros.

## The witness

For $z<-.30$ use uniform circle measure. For $z\ge-.30$, draw $u$ using the row for the slab containing $z$, choose either sign of $2\arccos u$ with equal probability, and add independent uniform noise on $[-h,h]$ with $h=.105$. Reduce modulo $2\pi$. Each row starts at the listed left endpoint and ends at the next; the last continues to infinity. The masses and nodes are exact decimals.

| Left endpoint | Nodes $u$ (masses in the same order) |
|---:|:---|
| $-.30$ | $.50$ (1) |
| $-.05$ | $.17,.18$ ($.32244,.67756$) |
| $0$ | $.53$ (1) |
| $.12$ | $.74$ (1) |
| $.45$ | $.84,.85$ ($.531,.469$) |
| $1.30$ | $.91,.92,1$ ($.49351,.31124,.19525$) |

Taking the unwrapped cosine before the absolute value gives $\mathbb E U\ge \operatorname{sinc}(h/2)\sum p u$ in a slab, where $p$ denotes its masses and $\operatorname{sinc}x=\sin(x)/x$. The cosine moment there is exactly $a_j=\operatorname{sinc}(jh)\sum p T_{2j}(u)$. Both statements follow by integrating over the noise; no angular grid bound is used. The [ball checker](check-dilated-harmonic-ceiling.py) verifies the mean inequality strictly with the original $ze^{-z}$ weight. A finite linear program suggested the rows, but is not part of the certificate.

## Extending the checks to the whole family

Set $s=-.30$. For any slab start $v$, its normalized ramp mass from $v$ to infinity equals

$$M_v(l)=e^{-l/2-b}(1+l+b),\qquad b=\max(v,-l).$$

Subtract consecutive tail masses to integrate a slab exactly. On $l\le-s$, $M_s(l)=e^{l/2}$. On $l\ge-s$ it is $e^{-l/2-s}(1+l+s)$, increasing to its peak at $l=1-s$, then decreasing. Write $M=2e^{-(1+s)/2}$ for the global maximum. All nonzero moments are supported on $z\ge s$. Thus $|C_j(l)|\le M_s(l)\min(1,1/(jh))$. This certifies the ceiling for all $j\ge24$, and, independently, on $l\le-1.2$ or $l\ge6$ at every $j$.

For the rest take $a(z)=\mathbb E_{P_z}\cos(j\theta)$, zero below $s$, with $|a|\le1$. The function $C=C_j$ has locally absolutely continuous first derivative. In fact $C'=-C/2+I$, where $I=e^{-l/2}\int_{-l}^\infty a(z)e^{-z}dz$; the moving endpoint term for the original ramp vanishes. Almost everywhere,

$$C''=C/4-I+e^{l/2}a(-l).$$

The last term has modulus at most $e^{-s/2}$ by support. Likewise $|I|\le e^{-l/2-\max(s,-l)}\le e^{-s/2}$. Thus $|C''|\le M/4+2e^{-s/2}<3$, including in the almost-everywhere sense across knots. On a length-$d$ interval the difference from the linear interpolant is bounded by $3d^2/8$: Compare the difference with the two parabolas $\pm(3/2)(l-l_0)(l_1-l)$ by convexity. Absolute continuity of the first derivative suffices for this comparison. Direct slab integration gives $|C_j(l)|<.59080$ at every hundredth between $-1.2$ and $6$ for $1\le j\le23$. Adding $3/(8\cdot100^2)$ closes the bound, with a uniform strict margin. The infinite tails, changes in the active slab, and the noise factor all enter before taking the supremum.

Replay with SageMath's Python: `sage -python .godel/bob/check-dilated-harmonic-ceiling.py` (here the interpreter is `/opt/sage-10.9/bin/python`). It checks the tail, interpolation, mean, and price comparisons as well as the grid, not the earlier lower certificate.

**Decision.** For a real high-endpoint failure the two-test implication at $c=1.17$ stands; at $c=1.175$ its limiting payment already exceeds the all-dilation, all-harmonic ceiling. Do not try to reach the latter depth just by adding cutoffs or harmonic indices to the mean comparison. A new arithmetic restriction on the radial phase law, a smaller shallow-zero payment, or a test with a different weight would be substantive. The witness is not a sequence of primes and does not give an upper bound on any actual prime harmonic, on the original signed $Z$, or on the exceptional signed packet. The [arithmetic mean and sign-band result](uncut-screen-mean.md) remains applicable with its original scope.
