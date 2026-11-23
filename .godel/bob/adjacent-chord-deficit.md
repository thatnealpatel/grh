# Adjacent chord deficit forces second-successor mass

The [two-successor box](rank-tapered-pair-mass.md) uses just a principal peak of size $47/81$. If testing an **endpoint failure** instead, the stronger one-prime datum $8/9$ is available *before* doubling. It yields a different disjunction involving just one scalar test on consecutive primes and a much larger positive-mass target on second successors. No equidistribution theorem is assumed.

Use the same clipped prime indices, $y=q^{3/5}$, $t=2y$, $X=((9/5)\log q)^2$, $D=\log X$, $z_j=\log(X/p_j)$, $Z=\sum_j z_j$, $e=9e^{-8}$, and $m=1-e$. Write $\langle f_j\rangle=Z^{-1}\sum_j z_j f_j$, omitting indices where a displayed edge does not exist (equivalently setting the integrand to zero). Define the **adjacent chord mean**

$$F=\left\langle \sqrt{(1+|\cos(y\log(p_j/p_{j-1}))|)/2}\right\rangle.$$

It measures how much real projection two neighboring unit phases can have on average after the best choice of signs and common rotation. It does not use character values, tail trimming by gap, or a count of labels. On a sequence of [raw signed endpoint hits](principal-list-sign-thinning.md) at level $8/9-o(1)$ one has the following alternative: **On the subsequence with $F\le 0.9005+o(1)$**, at $H=40D$,

$$\sum_{d<H} b_d(E_{2,d})_+\ \ge\ \sum_{d<H} b_d E_{2,d}\ >\ 0.002389 \qquad\text{eventually}. \tag{1}$$

Here $b_d=2(1-d/H)/H$ and $E_{2,d}=X^{-1}\sum_{p_j-p_{j-2}=d}z_j\log p_{j-2}\log p_j\cos(t\log(p_j/p_{j-2}))$. There is no rank taper in (1). A circle-uniform doubled adjacent difference would give $F=2\sqrt 2/\pi+o(1)<0.900317$, so the cutoff allows a fixed positive excess over that mean. The condition on $F$ cannot be imposed merely because it would hold for uniform differences.

**Proof.** Choose $a_j=\pm p_j^{iy}$ with nonnegative real part. All signed endpoint contributions, including zeros of characters, are majorized by these real projections. Below the clip the total one-prime mass is $e+o(1)$; on it $\log p_j=D+O(1)$ and $DZ/X=m+o(1)$ by PNT. Consequently $\langle\Re a_j\rangle\ge s_0-o(1)$, where $s_0=(8/9-e)/m$. Translating a bounded indexed observable by one or two indices changes its weighted mean by $O(1/Z)$, since $z_j$ decreases from at most 8 to zero up to endpoint truncation. In particular adjacent endpoint averages have the same lower bound.

Write $a_j=e^{i\alpha_j}$, $s_j=\alpha_j+\alpha_{j-1}$, $x_j=|\cos(s_j/2)|$, and let $f_j$ be the chord integrand in $F$. The half-difference cosine in the chord identity has absolute value at most $f_j$, regardless of signs. Hence

$$\tfrac12\Re(a_j+a_{j-1})\le f_j x_j,\qquad f_j\ge 1/\sqrt2.$$

This bounds the *loss* in the nearly saturated chord inequality: $\langle x_j\rangle\ge c-o(1)$, where $c=1-\sqrt2(0.9005-s_0)$. Twice applying $\cos(2u)=2\cos^2 u-1$ and Jensen gives $\langle\cos s_j\rangle\ge 2c^2-1-o(1)>0$ and $\langle\Re u_j\rangle\ge b-o(1)>0$ for $u_j=(a_j a_{j-1})^2$ and $b=2(2c^2-1)^2-1$. Dropping the undefined endpoints costs $o(1)$ at each step. By the shift estimate and Cauchy,

$$2+2\langle\Re(u_j\bar u_{j-1})\rangle\ \ge\ \langle |u_j+u_{j-1}|^2\rangle\ \ge\ 4b^2-o(1). \tag{2}$$

The middle prime cancels and squaring removes the chosen signs. Thus (2) bounds the *genuine* doubled second-successor cosine mean from below by $r-o(1)$, $r=2b^2-1>0.09793$.

To price the long gaps put $g_j=p_j-p_{j-2}$. Each elementary prime interval is covered at most twice by $[p_{j-2},p_j]$. Since $z$ is decreasing, $\sum_{j\ge3}z_jg_j\le 2\int_{e^{-8}X}^{X}\log(X/u)\,du=2mX$. Replacing 1 by $(1-g_j/H)_+$ therefore costs at most $2/40+o(1)$ in the normalized signed mean, including discarded gaps. Restoring both logarithms as $D+O(1)$ gives the lower bound $(2m/40)(r-2/40)-o(1)$, strictly larger than $0.002389$. This proves (1).

**Separation of the alternatives.** In the disjoint-clip multiplicative control of the [rank note](rank-tapered-pair-mass.md#why-not-just-consecutive-gaps-even-with-their-harmonics), the sign-corrected phase alternates between $e^{iU/2}$ and $e^{-iU/2}$ on each independent block. It attains the uniform chord mean but its doubled second-successor ratios are one internally. Conversely use the sign pattern $+,+,-,-$ repeated in each block's exponents $\pm iU/2$. The signed and doubled one-prime real means are unchanged. Now every internal second-successor difference has doubled phase $e^{\pm 2iU}$, of mean zero even at each fixed nonzero harmonic. The same block variance argument applies verbatim to rank two: At most two boundary edges per cut, $O(MD^2/X)$ absolute weight per block, and $O(D)$ over all blocks. The grouped rank-two positive budget tends to zero, while $F\to(1+2\sqrt2/\pi)/2$ since alternate adjacent edges have equal doubled phases (the weighted parity error per block is $O(1/Z)$). Both controls can meet the earlier one-prime thresholds; neither occurs here as an asserted untwisted height law. Thus even testing rank two alone is not a replacement for the disjunction.

**Fixture and decision.** The [interval checker](check-rank-box.py) at the named center $q=2^{127}-1$ gives $0.899035<F<0.899036$ and $0.0014475<\sum b_d(E_{2,d})_+<0.0014476$ for $C=40$. These are measurements of the new observables; (1) is asymptotic, not a finite exclusion rule. For the raw endpoint, test the upper tail of $F$ and the rank-two budget **jointly with the one-prime hit**. A generic principal peak does not supply the $8/9$ premise, and neither pointwise arithmetic estimate follows from this reduction.

For the subsequent interval test on the original projection, see [the triple endpoint cap](triple-endpoint-cap.md). It certifies a moving-height interval at the fixture, not control of the cells on the principal list.

[Overlapping three-prime allocations](finite-successor-cap.md) now calibrate the two thresholds finitely over the fixture cutoff interval and strengthen the asymptotic raw-hit alternative to $B>0.012825$ eventually. For a separate finite comparison on buffered cells see [the small block scan](selected-cell-comparison.md).
