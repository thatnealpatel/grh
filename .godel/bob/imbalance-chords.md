# Two more gap intervals admit simultaneous zero answers

In the $(10,2)$ comparison at $c=39/20$, for every $s\in\mathbb R$ there is a common-law witness with zero second answers at the two $3t$ translates $s,s+d$ whenever

$$39/50\le d\le47/50\quad\text{or}\quad 37/20\le d\le 4.$$

All first translates at both heights, zero orders two through ten at $t$, and the strict failure mean are retained. The joint witness can depend on the pair. With the [negative-block strip](gap-51-hull.md) and [large-gap strip](two-gap-window.md), this reduces the necessary gap window for a two-term scalar separator to $(13/25,39/50)\cup(47/50,37/20)$, with like signs. These bounds do not assert a separator anywhere in the remaining intervals, or a measurement bound at an actual failure.

## Compare same-sign coefficients without resolving the balanced cusp

Use the [normalized kernels and scalar criterion](two-term-10-2.md). Let $m=-G_B/C_1$, $d\nu=(1-|m|^2)d\mu$, $S(s)=\Re\int e^{isx}m^2d\mu$, $E(t)=\int\cos(tx)|m|^2d\mu$, and $R(t)=e^{-|t|/2}-E(t)$. For same-sign coefficients normalized to sum one, set $h=|a-b|$ and denote the capacity by

$$K(h,d)=\int\sqrt{\cos^2(dx/2)+h^2\sin^2(dx/2)}\,d\nu.$$

It is increasing and **concave in $h^2$**, even at $h=0$. The maximum absolute center over the two orientations is $A+Bh$, where $A=|S(s)+S(s+d)|/2$ and $B=|S(s)-S(s+d)|/2$. At the nodes $h_j=j/16$, compute smooth lower bounds $L_j(d)$ for $K(h_j,d)$. Between nodes $l,u$ this gives the following lower bound for the slack:

$$L_l+\frac{L_u-L_l}{u^2-l^2}(h^2-l^2)-A-Bh.$$

Here subscripts denote the imbalance node. At each checked corner its quadratic coefficient is positive. Take any tangent near the clamped minimizer of the quadratic, and check the affine tangent at both endpoints. This needs no derivative of the true capacity in $h$ and no floating point optimizer.

The [checker](check-imbalance-chords.py) uses the absolute-cosine series through harmonic 200 for $h=0$. For $h>0$ it uses the squared truncated binomial series for $q=(1-h)/(1+h)$, divided by $1+q$. The tail estimates are as in the [two-term calculation](two-term-10-2.md): For the balanced series, if $y=kd>D=\max|z_j-z_i|$, then $|E(y)|\le V^2(2+y+D)e^{-(y-D)/2}$ with $V=\sum|\beta_j|$. Beyond $k=200$ this envelope falls by a factor at most $e^{-d_0/3}$ per harmonic for $d\ge d_0$, since $2+y+D>6$. For the unbalanced series take $3q^{n+1}/(1-q)<10^{-8}$. Each $L_j$ is the finite kernel combination minus $10^{-8}$.

For interpolation in $s,d$, fix **both** the coefficient vector and a signed branch of the center. The chord in $h^2$ now uses constant convex weights, so its second derivative in $d$ costs at most the largest node bound $M$. To compute $M$ apply the triangle inequality to the finite coefficients of $R(kd)$, using $|E''|\le T=\int x^2|m|^2d\mu$. When $y=kd_0>D$, differentiating the difference kernel gives the alternative bound $V^2(1/2+(y+D)/4)e^{-(y-D)/2}$ throughout $kd\ge y$ (the envelope decreases). The exponential in $R$ costs another $e^{-y/2}/4$ before multiplying by $k^2$. Each signed center costs at most $T$ in either coordinate. Thus a rectangle with side lengths $p,r$ loses at most $Tp^2/8+(M+T)r^2/8$ from its four corner lower bounds. We do not interpolate the absolute values, the minimizing $h$, or a chosen tangent across the rectangle.

For $s\notin[-8-d_1,8]$ both shifts have magnitude at least $8$. The check $|S|<.02$ there uses the chord bound on the finite part and the exact exponential-times-polynomial forms on the two tails. On both strips a 64-subinterval chord test gives $L_0(d)>.02+10^{-5}$, which suffices by monotonicity.

## Which laws give a joint witness?

The hard-pair law supplies the same-sign directions on $[.78,.94]$; on $[1.85,4]$ use the common prime law mixing hard-pair, regional, and single-shift laws with weights $2/5,2/5,1/5$. Means and first representers mix linearly, so the strict means and the caps follow from those of the individual laws. The capacity and centers must instead be recomputed from the mixed $B$ jumps. Replay from the repository root with assertions enabled:

```
sage .godel/bob/check-imbalance-chords.py
```

The 128-bit enclosure gives normalized same-sign slack $>10^{-5}$ on respectively 282 and 1,089 rectangles, besides the two outer ranges. Opposite-sign directions are covered by the [single-shift law](separated-second-shifts.md). This last step does **not** presume that the same-sign law passes them. Indeed, for a fixed pair let $K_1,K_2\subset\mathbb R^2$ be the compact convex second-answer images of the same-sign and opposite-sign laws. Every real functional has range containing zero on at least one of them. The compact convex hull of their union therefore contains zero. Each point in that hull is a constant mixture of a point of $K_1$ and a point of $K_2$. Mix the corresponding *entire* witnesses with those probabilities, including the prime law and both shallow laws. This preserves all linear matches and the strict failure mean, and attains both zeros with one law for the fixed pair. It does not produce one law for a continuum of pairs.
