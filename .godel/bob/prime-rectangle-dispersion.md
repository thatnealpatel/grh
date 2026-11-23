# Packing candidate peak intervals using rectangle dispersion

Let $L_1=X/D$, $L_2=X^2/D^3$, and use the [normalized rectangle statistic](prime-rectangle-persistence.md), including its fixed $m$, $H=8192mD^2$, and deletion of coincident primes. Fix $0<\delta<1$. In **every** interval of radius $X^{1-\delta}L_2$ around a sufficiently large $t$ with $X=X(t)$, there are only $O_\delta(1)$ disjoint pair-persistence neighborhoods of candidate peak centers. Here a candidate means a center $v$ having at least $\kappa\log X(v)$ shifts in the interior range with $A_{d,X(v)}\le M$ and $C_{d,X(v)}(v)>1/8$. The pair neighborhoods have radius $bX(v)/\log X(v)$, not a fixed fraction of $L_2$. This improves the [pair-only packing scale](prime-pair-dispersion.md), but still permits a candidate exactly at $t$.

## The local square has its own dispersion scale

For $1\le Q\le X^{1-\delta}$, $T=QL_2$, and shifts $cD\le d\le4D$, we have

$$\sum_d\int_{t-T}^{t+T}|R_{d,X(u)}(u)|^2\,du\ll_{c,m,\delta} DL_2. \tag{1}$$

First freeze $X$. Combine orientations by writing $R_{d,X}(u)=\Re\sum_{p,h} B_{p,h}e^{iu f(p,h)}$ for the four distinct primes, $1\le h<H$, $h\ne d$, and

$$f(p,h)=\log\left(1+\frac{dh}{p(p+d+h)}\right),\qquad B_{p,h}=\frac2X\int P_{p,p+h}(x)\,dx\le \frac{2a_p}X\le 16D^2/X.$$

The first inequality uses $P_{p,p+h}\le v_p$, independent of other primes in the windows. Use the squared modulus of the complex sum and the translated squared-sinc majorant as in the [pair calculation](prime-pair-dispersion.md). It suffices to bound by $O_\delta(D/Q)$ the sum of products $B_{p,h}B_{r,k}$ with $|f(p,h)-f(r,k)|\le1/T$, over all the shifts. Constants here may also depend on $c,m$. By symmetry restrict $h\le k$, at cost at most two. For each $p,h,k$, the allowed real $r$ in the band occupy an interval of length $O(Xw_k)$, $w_k=\min(1,H/(Qk))$. Indeed

$$|\partial_r f(r,k)|=\frac{dk(2r+d+k)}{r(r+d+k)[r(r+d+k)+dk]}\asymp dk/X^3.$$

We used $d\asymp D$, $k\le H$, and $r\asymp X$. Extend the interval to length comparable to $Xw_k$, at least $X/Q\ge X^\delta$. After an integer translation the four forms have the same determinant product as before (their offsets all shift by the same integer). Thus Ford's Theorem 2.5 as checked in the pair calculation bounds the number of eligible $r$ by $O_\delta(Xw_k U(d,k)/D^4)$, where $U(d,k)=[G(d)G(k)G(|d-k|)G(d+k)]^4$. For an inadmissible tuple the count in the original band is zero. The count of $p$ in the full band is $O(XU(d,h)/D^4)$. This argument also covers $h=k$, $p=r$; **no** independent-prime assumption for the two rectangles is made.

Group $k$ in $J/2<k\le J$ for dyadic $J\le 2H$. From the prefix-moment proof in the pair calculation, $\sum_d\sum_{h\le J}^{*}U(d,h)^2\ll DJ$ (here $d$ ranges over the entire shift range, and the star excludes $h=d$). Cauchy in $h$ gives $\sum_d(\sum_{h\le J}^{*}U(d,h))^2\ll DJ^2$. Thus the close-product mass is at most

$$\ll_\delta D^{-3}\sum_J J^2\min(1,H/(QJ))\ll_\delta D^{-3} H^2/Q\ll_m D/Q,$$

where the middle bound also follows just by summing $JH/Q$ geometrically. The dyadic variable is the **larger** separation; summing separate fixed-$h$ norm bounds would not give this calculation. Multiplication by $O(T)$ proves the frozen estimate.

In a fixed polynomial radius the cutoff moves by less than $X^{-A}$ for every fixed $A$. The [tensor stability proof](prime-rectangle-persistence.md) gives $R_{d,X(u)}(u)-R_{d,X}(u)=O(D^2/X)$ even for unselected $d$: The endpoint crossings have total $a_p$ cost $O(D^2)$, while the common normalized box-length variation and outer normalization cost $o(X^{-1})$ using just $A_d\le 8D^2$. The integrated squared error over all $d$ is $O(TD^5/X^2)=o(DL_2)$ throughout the claimed range. This proves (1); the same proof allows any fixed positive lower and upper multiples of $D$ for the shift range. It gives a common ordinate with $O_{c,m,\delta}(D/Q)$ shifts exceeding $1/(128m)$ in absolute value. This is $o(D)$ when $Q\to\infty$, **not** on the guaranteed interval of radius $b_2 L_2$.

## A limit on extending (1)

At $Q=X$ there is **no** bound of the form (1) uniform over all named centers. This is a diagonal-energy obstruction, not evidence of a peak. To see it, first freeze the cutoff at $X=X(t)$ for an arbitrary large $t$. Taking all phases one in the [pair extraction](short-prime-pair-bias.md) gives $\gg D$ shifts in its interior range with $1/8<A_d\le M$; drop any within 1 of the range boundaries. For these shifts the rectangle lower bound at zero gives $\sum_{d,p,h} B_{p,h}\gg_m D$. The full-band sieve and the prefix estimate with $h\le H$ count $O(XDH/D^4)=O_m(X/D)$ rectangles there. Thus $\sum_{d,p,h} B_{p,h}^2\gg_m D^3/X$ by Cauchy.

At a fixed $d$, all positive frequencies are distinct. In the reduced fraction $(p+d)(p+h)/[p(p+d+h)]$, the four primes are distinct, the smaller denominator prime determines $p$, and the other determines $h$. The fractions have denominators at most $X^2$ and are in $[1,2]$ eventually, so distinct logs differ by $\gg X^{-4}$. The same spacing holds for the union with their negatives, since $f(p,h)\gg X^{-2}$. Write each cosine as two exponentials with coefficients $B_{p,h}/2$. In the integrated squared norm on $[t-X^6,t+X^6]$ the diagonal multiplier is $2X^6$, while the off-diagonal absolute row sums are $O(X^4\log X)$ by the spacing and the harmonic sum (there are only polynomially many frequencies). By $2|ab|\le |a|^2+|b|^2$ this gives average frozen energy $\gg D^3/X$ summed over the retained shifts. Moving the cutoff preserves this lower bound by the $L^2$ triangle inequality and the uniform pointwise error above.

Partition this long interval into equal pieces of length comparable to $XL_2$ and at most $XL_2$. Some piece has at least the stated average. Its midpoint is within $o(1)$ of a named height $v$ by [odd-squarefree sampling](sampled-principal-peaks.md#rotate-first-then-sample), and all retained shifts lie in the range there. Since $X(v)-X=o(1)$, the window of radius $X(v)L_2(v)$ covers the whole piece. Its integral is $\gg XL_2 D^3/X$, larger than $DL_2$ by a factor $\gg D^2$. This rules out the lossless endpoint for **this norm**; it does not rule out packing bounds reached by other means.

## Use both statistics without interchanging them

For the packing statement use (1) with $\delta/2$ to allow interval enlargement by a constant, and enclose all moving shift ranges in $[cD/2,5D]$. Each candidate's rectangle neighborhood has radius $(1+o(1))b_2L_2$, and contributes $\gg_{b_2,\kappa,m}DL_2$ to the moving rectangle energy by persistence. A maximal disjoint collection of these neighborhoods has bounded size by (1); the centers of all candidates are within $O(b_2L_2)$ of a center in the collection. Inside each such region the **pair** energy (1) of the [pair calculation](prime-pair-dispersion.md) is $O(X)$, even allowing room for the full short neighborhoods. Each disjoint short neighborhood contributes $\gg_{b,\kappa}X$. This proves the stated two-scale packing bound. All comparisons $X(v)/X=1+o(1)$ are uniform over the outer interval. No relation between the identities of the selected shifts at different centers is needed.

A free multiplicative twist at a coupled peak obeys both energy bounds: Before the sinc estimate the complex coefficients acquire only constant unit factors with the reversed orientation conjugated. Thus neither the two energy budgets nor their intersection needs to be empty. They quantify how isolated a cluster must be, rather than supply signed cancellation on that cluster.
