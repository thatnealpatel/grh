# All pairs of second translates at distance at most one half

In the $(10,2)$ shallow comparison at $c=39/20$, for every $s\in\mathbb R$ and $0\le d\le 1/2$, there is a common law matching all first translates and giving zero answers through order ten at $t$ (starting at order two) and **both** second answers at $s,s+d$ at $3t$. The failure mean strictly exceeds $8/9$. The [previous gap window](two-gap-window.md) handles $d\le3/16$. On $[3/16,1/2]$ we use one new prime law throughout; its shallow second-moment completion can depend on the pair. Together with the previous large-gap and opposite-sign arguments, a two-term scalar mask separating every common law must have like signs and gap **strictly between $1/2$ and $4$**. The result is about abstract laws, not the signed-measurement premise at actual failures.

## First moments

On each slab, mix the [152-slab law](single-shift-10-2.md), the [416-slab hard-pair law](two-term-10-2.md), the [radial $(9,9)$ law](check-two-height-radial-witness.py), and the constant atom $X=0$ in proportions $(5710000,4195798,94000,202)/10^7$. This is a mixture of the underlying angular distributions, not a mixture of the final second moments. In particular the atom at zero contributes $1/\sqrt{2}$ to the failure mean. The strict mean surplus is $>9.48\cdot10^{-8}$. Adding the component cap bounds is **not** sufficient for the order-ten cap. Applying the jump-polynomial Taylor test directly to the combined $A=\mathbb EX$ on the union of the knots gives $\|G_A\|_\infty<.6186604<C_{10}$; the triangle bound for $B=\mathbb E(4X^3-3X)$ is $1.055479<C_1$. The [single-shift matching construction](single-shift-10-2.md) applies, with vanishing first profiles left of $-12$. In particular $m=-G_B/C_1$ at $3t$ is the mixed first representer *before squaring*.

## A quadratic allowance for unequal positive coefficients

Use $d\mu=dx/(2\pi(1/4+x^2))$, $v=1-|m|^2$, $V=\int v\,d\mu$, $R(d)=\int v\cos(dx)\,d\mu$, $S(s)=\Re\int e^{isx}m^2\,d\mu$, and $C(d)=\int |\cos(dx/2)|v\,d\mu$. For positive coefficients normalized to $a+b=1$, put $\eta=a-b$. Pointwise,

$$|a+be^{idx}|=\sqrt{\cos^2(dx/2)+\eta^2\sin^2(dx/2)}\ \ge\ |\cos(dx/2)|+\tfrac12\eta^2\sin^2(dx/2).$$

Indeed the sum of the two radical terms in the difference-of-squares identity is at most two (the case where both vanish is immediate). The integrated capacity is at least $C(d)+k(d)\eta^2$, where $k(d)=(V-R(d))/4$. For $p=S(s)$ and $q=S(s+d)$ the price is $|(p+q+\eta(p-q))/2|$. Thus a single lower bound on slack for *every* ratio, at a given node, is

$$C(d)-|p+q|/2-\min\{B_0,B_0^2/(4k(d))\},\qquad B_0=|p-q|/2.$$

The two losses follow from $|\eta|\le1$ and completing the square, respectively. Retaining the quadratic gain allows a joint test without a coefficient mesh. For opposite signs take the larger magnitude $a\ge1/2$. Real part gives capacity at least $aV-(1-a)R(d)$ whichever coefficient is larger. Subtract each signed center, affine in $a$, and test endpoints: At $a=1/2$ the lower bound is $2k(d)-B_0$; at $a=1$ it is $V-\max(|p|,|q|)$ for the worse orientation.

## Uniformity in the shifts

The [Sage checker](check-half-gap-mixture.py) uses the sum and difference kernels in the [two-term certificate](two-term-10-2.md). Write $E(d)=\int|m|^2\cos(dx)\,d\mu$, $T=\int x^2|m|^2\,d\mu$, so $|S''|,|E''|\le T$ and $R(d)=e^{-d/2}-E(d)$ for $d\ge0$. Truncate the cosine series for $C(d)$ at $N=600$:

$$C_N(d)=\frac2\pi V+\frac4\pi\sum_{j=1}^N\frac{(-1)^{j-1}R(jd)}{4j^2-1}.$$

For $u>D$, the difference kernel gives $|E(u)|\le L^2(2+u+D)e^{-(u-D)/2}$, with $L$ the sum of absolute normalized jump weights and $D$ the knot span. Beyond $u=(N+1)3/16$ the logarithmic derivative of this bound is at most $-1/3$. Two geometric tails give $|C-C_N|<1.37\cdot10^{-19}$ throughout. A curvature bound $M_C$ for $C_N$ is the sum of the absolute coefficients times $j^2(T+e^{-3j/32}/4)$.

For each fixed $\eta$ and price sign interpolate the **signed lower bound**, not the minimum over $\eta$. On an $s,d$ rectangle of widths $h_s,h_d$, its loss relative to the four corner lower bounds (using $C_N$) is at most

$$\big[T h_s^2+(M_C+T+(T+1/4)/2)h_d^2\big]/8.$$

This is successive one-variable linear interpolation using the pure second derivatives. The same loss covers the opposite-sign endpoint tests, including the coefficient $1/2$ on $R$ there. The checker certifies slack $>5\cdot10^{-6}$ on 1209 rectangles covering $[-17/2,8]\times[3/16,1/2]$. Outside the finite $s$ range, both $S$ values are bounded in magnitude by $.02$ using grid chords and their exponential-polynomial tails. Uniformly $C(d)>.4$ and $V-R(d)>.04$ by one-dimensional chord bounds. These pay for the same-sign capacity and both opposite-sign endpoints (also $V\ge C(d)$).

All real directions therefore pass the [compact convex separation test](separated-second-shifts.md), giving simultaneous matching for each pair. Replay from the repository root with `sage .godel/bob/check-half-gap-mixture.py` (SageMath 10.9, assertions enabled). No optimization output or sampled cap is an input.

**Update after Work:** The [six-profile exclusion and one-block repair](gap-51-hull.md) settle the balanced test at $(.05,.56)$. The original mixture fails there, but the new law covers the whole next strip, $1/2\le d\le13/25$, for all $s$. Do not refit the six constant weights at this pair. The next test uses more than one negative block at $(.07,.62)$, where the one-block law already fails.
