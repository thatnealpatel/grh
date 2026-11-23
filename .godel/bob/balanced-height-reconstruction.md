# Reconstructing the completed one-copy excess from height data of degree at most three

For the original [net-pool test](net-pool-supply.md), write $S=u-v$, so that $I=S^2+o(B^2)$ at the positive detection scale $B=t^{-1+o(1)}$. The earlier [separation comparison](separated-signed-tuples.md) loses $\exp(o(n))$ on the height side. This need not preserve a fixed fractional margin. Here is a positive height test that **does** preserve such a margin, up to $o(B)$ at detection scale. It needs only the complex prime-pair sum and connected pairs and triples of its starts; at larger amplitudes only pairs are needed. No upper estimate for the value of the test at the named centers is proved.

Freeze $t=2q^{3/5}$, $X=(3\log(t/2))^2$, $D=\log X$, $0<\gamma<1/2$, $C=4+2\gamma$, $h=\lceil(2+\gamma)\log t/D\rceil$, $n=2h$. Work at $1\le d\le5D$, with $p,p+d$ prime in $[e^{-8}X,X]$, $w_p=X^{-1}\log(X/p)\log p\log(p+d)$, $A=\sum_p w_p>a_0>0$. Two distinct starts conflict at distance $\le r$, where $r=D^2$ or $X^\xi$, $\xi=\gamma/[16(2+\gamma)]$. In sums over ordered labels let $H_{ij}=1_{|i-j|\le r}$ **include equality**. At height $\tau$, set

$$ c_p=w_p e^{i\tau\log(1+d/p)},\quad Z=\sum_p c_p,\quad s=|Z|,\quad K_t(\tau)=t^{-1}\operatorname{sinc}^2(\pi(\tau/t-1)),\qquad \operatorname{sinc}(x)=\sin(x)/x. $$

All integrations below use $K_t(\tau)d\tau$, including at the outer heights. In particular nothing replaces the centered cosine by an unshifted triangular kernel. All $o(1)$ bounds are uniform in height and the indicated shifts for fixed $\gamma,a_0$.

**The two parts of the test.** Put $\alpha=(3/4+\gamma/8)/(C-1)$. Integrate the following positive functions on disjoint sets, and denote the two integrals by $M_2^{\rm ht}$ and $M_3^{\rm ht}$ (these are not pool masses).

* On $t^{7/10}\le |\tau|\le t^{13/8}$ and $s\ge X^{-1/10}$ use
  $$ W_2=s^n\exp\left(-\frac{n^2}{2s^2}\sum_{i,j} H_{ij}\Re(c_i\bar Z/s)\Re(c_j\bar Z/s)\right). $$
* On $t^{5/6}\le |\tau|\le t^{7/5}$ and $X^{-\alpha}\le s<X^{-1/10}$ use $W_3$ below. No auxiliary angular integration is required.

With $M=M_2^{\rm ht}+M_3^{\rm ht}$, the assertion is

$$ |S-M|\le o(1)M+t^{-1-\min(\gamma/8,1/100)+o(1)}. \tag{1} $$

Thus an upper bound $M\le(1-\epsilon)B$ gives $|S|\le(1-\epsilon+o(1))B$, and conversely a detection $|S|\ge B$ forces $M\ge(1-o(1))B$. This is not relative precision at arbitrarily small $S$. It is for separation **within** the one copy, not joint separation across the two copies in $I$.

**Balanced coefficient.** Form $P(y)=\sum_{J\ {\rm independent}}\prod_{j\in J}y_j$. The height sum $D_h(\tau)$ with $h$ ordered plus and $h$ ordered minus labels, all $2h$ separated, is exactly $(h!)^2[z^h w^h]P(zc+w\bar c)$. Conjugation interchanges the signs, so it is real. Its integral is the separated signed sum $J_r$ by the transform of $K_t$. The [completed-gate estimate](windowed-harmonic-witness.md) gives $S=J_r+O(t^{-1-\gamma/8+o(1)})$, keeping the low-private exclusion at $D^2$. This is the only gate replacement here.

For $s>0$ scale the activities to $y_p=h(a c_p/Z+b\bar c_p/\bar Z)$. Let $Q(a,b)$ be the first three homogeneous terms of $\log P(y)$, so its linear term is $h(a+b)$. Explicitly the quadratic and cubic terms are

$$ -\tfrac12\sum_{ij} H_{ij} y_i y_j,\qquad
\tfrac16\sum_{ijk}y_i y_j y_k(H_{ij}H_{ik}+H_{ij}H_{jk}+H_{ik}H_{jk}-H_{ij}H_{ik}H_{jk}). $$

Indeed the degree-$m$ term of $P$ is $1/m!$ times the ordered sum weighted by $\prod_{j<k}(1-H_{i_j i_k})$; expanding its formal logarithm through degree three gives these formulas. In particular no triples disconnected in the conflict graph have to be counted. Solve $a Q_a=h$, $b Q_b=h$ near $(1,1)$ with $b=\bar a$; the local solution is unique as shown below. Use

$$ W_3=\frac{(h!)^2}{2\pi h}\left(\frac{s}{h|a|}\right)^n e^{Q(a,\bar a)}. \tag{2} $$

**Precision of the saddle.** Put $s_0=t^{-(1+\gamma/8)/n}$, $w_*=\max w_p\le8D^2/X$, $B_0=C_0(1+2r)w_*$ for a sufficiently large absolute $C_0$. Write $\rho=0$ at $D^2$, $\rho=\xi$ at $X^\xi$. Then $B_0\le X^{-1+\rho+o(1)}$, $A=O(D^2)$, $s_0=X^{-1/4+3\xi+o(1)}$. The deletion estimate (2) in the [separation proof](separated-signed-tuples.md) uses only absolute values, so holds for complex activities: If $|y_p|\le Lw_p$, the $j$th homogeneous term of $\log P(y)$ is bounded by $4AL(LB_0)^{j-1}/j$, by scaling the auxiliary univariate indeterminate in $P(\lambda y)$. This is the analytic log branch from the origin when $LB_0<1$.

For $s\ge s_0$, use $L=3n/s$ on the radius-three polydisk. Define $\eta=nAB_0/s^2$, $\delta=AB_0^3(n/s)^4$. Uniformly,

$$ \eta\le X^{-6\xi+\rho+o(1)},\qquad nB_0/s\le X^{-1/4-3\xi+\rho+o(1)},\qquad \delta\le X^{-12\xi+3\rho+o(1)}. $$

In particular $\log P(y)=Q+O(\delta)$ there, and $E=Q-h(a+b)$ and its first three derivatives are $O(h\eta)$ on the radius-two polydisk (by its bounded degree, or Cauchy's estimate). The saddle equations are the fixed-point equations $(a,b)=(1-aE_a/h,1-bE_b/h)$. The map takes the closed polydisk of a sufficiently large constant times $\eta$ about $(1,1)$ into itself and has Lipschitz constant $O(\eta)$ there. Its unique fixed point is invariant under conjugate-swap, so $b=\bar a$, $Q(a,b)$ is real, and $|a-1|=O(\eta)$. No assertion about distant stationary points is needed.

In the coefficient integral use circles parametrized by $(ae^{i\phi},\bar a e^{i\psi})$. Subtract $Q(a,\bar a)$ and $ih(\phi+\psi)$ from the exponent, obtaining a phase $f$ with zero value and gradient at the origin. The difference from $h(e^{i\phi}+e^{i\psi}-2-i\phi-i\psi)$ has second derivatives $O(h\eta)$ on the whole angle square $[-\pi,\pi]^2$, and also vanishes to first order at zero. Since $1-\cos x\ge2x^2/\pi^2$ there, $\Re f\le-c h(\phi^2+\psi^2)$ globally. In particular the absolute contour mass after removing $e^{Q(a,\bar a)}$ is $O(1/h)$, so restoring the analytic log remainder costs $O(\delta/h)$, not $O(\delta)$, in the normalized integral.

For $v=(\phi,\psi)$, $f=-h|v|^2/2+O(h\eta|v|^2+h|v|^3)$. Interpolate the two exponentials on the straight segment of exponents: Both endpoints have real part $\le-c h|v|^2$. Integrating the error against this Gaussian on the square costs $O((\eta+h^{-1/2})/h)$. Including the $(2\pi)^{-2}$ angular normalization gives $(2\pi h)^{-1}(1+O(\eta+h^{-1/2}+\delta))$. The coefficient prefactor is $(h!)^2(s/h)^n|a|^{-n}$, proving $D_h=(1+o(1))W_3$ pointwise on $s\ge s_0$. This is why one can integrate a positive expression without assuming that every balanced coefficient is positive at small amplitude.

**When one quadratic evaluation suffices.** At $s\ge X^{-1/10}$ the shift of the stationary exponent from evaluating at $(1,1)$ costs $O(h\eta^2)$: In $Q(a,b)-h\log(ab)$ the linear part combined with the log is $2h+O(h\eta^2)$, and moving $E$ costs $O(h\eta^2)$. At $(1,1)$ the cubic is $O(AB_0^2(n/s)^3)$. The two errors are at most $X^{-1/10+2\rho+o(1)}$ and $X^{-1/5+2\rho+o(1)}$, respectively, both $o(1)$ even at the power radius. The quadratic at $(1,1)$ is precisely the exponent in $W_2$. Stirling's formula gives $(h!)^2 e^{2h}/(2\pi h\, h^{2h})=1+O(1/h)$. Hence $D_h=(1+o(1))W_2$ throughout this region. The quadratic exponent itself is **not** discarded; it need not be $o(1)$.

**Pricing the omitted heights.** The angular proof in the separation comparison gives the pointwise *absolute* bound $|D_h|\le e^{o(n)}s^n+t^{-1-\gamma/8+o(1)}$: On small real projections use its absolute recurrence estimate, and on the others use its upper bound before taking the angle average. The floor integrates just once against a probability measure. Also trivially $|D_h|\le A^n=t^{o(1)}$ by the ordered sum. This prices $|\tau|<t^{1/2}$ and $|\tau|>t^3$ at $t^{-3/2+o(1)}$ and $t^{-2+o(1)}$, respectively, using the double zero of the centered kernel at zero and its inverse-square tail.

On a shell $T\le |\tau|\le2T$, $T=t^y$, $1/2\le y\le3$, take $k=2\lfloor\log(T/4)/(2D)\rfloor\le n$. With the weights still frozen at $t$, the [permutation diagonal](dyadic-prime-pair-moments.md) gives $\int_{T\le |\tau|\le2T}s^k d\tau\ll T(k/2)!(Aw_*)^{k/2}\le T^{3/4+o(1)}$. Indeed the rational frequencies in this moment have numerator and denominator at most $X^k$, so a compact Fourier majorant of the two intervals of bandwidth $1/T$ sees only zero. At zero the plus and minus starts are permutations by the least differing start valuation. Here $\log(k/2)=D/2+o(D)$ uniformly. This argument needs no nonzero-frequency estimate at the growing order $n$.

Restrict first to $s\le X^{-\beta}$. Factor out $X^{-\beta(n-k)}$ from the upper bound for $s^n$. The kernel is $O(T^2/t^3)$ below $t$ and $O(t/T^2)$ above $t$ (a change of absolute constants covers shells meeting $t$). Apart from the uniform floor, the absolute contribution is $\le t^{f_\beta(y)+o(1)}$, where

$$ f_\beta(y)=\begin{cases}-3+11y/4-\beta(C-y), &y\le1,\\1-5y/4-\beta(C-y), &y\ge1.\end{cases} $$

For the unrestricted shell use $\beta=0$ with $A^{n-k}=t^{o(1)}$. For each $\beta$ used here the function increases to $y=1$ and decreases thereafter. Three applications suffice:

1. With $\beta=0$, the values at $7/10,13/8$ are $-43/40,-33/32$. Hence outside the wider height band even the unrestricted amplitude costs a power saving over $t^{-1}$.
2. With $\beta=1/10$, the values at $5/6,7/5$ are $-41/40-\gamma/5,-101/100-\gamma/5$. Thus outside the narrower band no cubic evaluation is needed.
3. For $\beta=\alpha$ the maximum is $-1/4-\alpha(C-1)=-1-\gamma/8$. This discards $s<X^{-\alpha}$ everywhere. The retained amplitudes exceed $s_0$ eventually since $(1+\gamma/8)/C-\alpha=3\gamma/[8C(C-1)]>0$.

Splitting shells at the stated endpoints or adjusting $y$ by $O(1/\log t)$ does not change the exponents. Summing $O(\log t)$ shells and using the two uniform relative estimates on their retained parts proves (1).

**Decision.** A fixed-margin comparison no longer requires resolving long separated tuple counts or controlling every real projection. There are two possible sources of a detection: Either the explicit quadratic-corrected high amplitudes pay at least $(1/2-o(1))B$, or the moderate amplitudes in the narrower height band pay that much through (2). The short diagonal estimate prices the complement but does not bound either source at this threshold. In particular the peak at height zero, an unsigned divisor count, or a test of only the real part of $Z$ cannot be substituted for this centered sum of positive contributions.

**Why not just use a higher interval moment?** The separated-frequency mean-value bound (Montgomery and Vaughan's Hilbert inequality, in the [higher-moment form in Weber, section 3](https://arxiv.org/abs/0907.4931)) applies: The $\lambda_p$ are rationally independent by the least-start valuation, and the grouped $k/2$-fold sums for even $k$ have minimum gap at least $X^{-k}$. For the actual coefficients this gives

$$ \int_T^{2T}s^k\ll (T+X^k)(k/2)!(A w_*)^{k/2}. $$

At $T=t$, using this gap and $s\le X^{-\beta}$ to price $s^n$, the exponent after division by $t$ is $-\beta(C-\kappa)-\kappa/4+(\kappa-1)_++o(1)$ for $k=(\kappa+o(1))L$, $0<\kappa\le C$, $L=\log t/D$. At $0\le\beta<1/4$ the best exponent occurs at $\kappa=1$. In particular at the upper edge of the moderate-amplitude range, $\beta=1/10$, even the best order gives $-1/4-(C-1)/10>-1$. The relative saddle factors do not alter this exponent: On retained heights $D_h\le e^{o(n)}s^n+t^{-1-\gamma/8+o(1)}$. This calculation tests the available spacing bound, not a conjecture that the minimum gap attains it.

There is a stronger obstruction on the high-amplitude part for the usual detector $B\asymp (X/D)(1/16)^n/t$. Even a sharp bound *uniform under translation* for the integral of $W_2\mathbf1_{s\ge X^{-1/10}}$ over a length-$t/4$ interval cannot price the interval $[t,5t/4]$ by $o(tB)$ or even $O(tB)$ using that uniform bound alone. Indeed the [consecutive-gap estimate](matched-prime-overlap.md) gives $A>1/4$ on $\gg D$ shifts. On $[0,1]$, $s\ge A(1-O(D/X))$ by the phase widths. The absolute quadratic exponent is $O(n^2 A B_0/s^2)=X^{\rho+o(1)}$ as an upper bound, which is $o(n)$. The interval integral at the translate $[0,t/4]$ is therefore at least $A^n e^{-o(n)}\gg tB$. This uses the *corrected* height weight with both separation radii, not just the bare moment. At the genuine translate $K_t\asymp 1/t$ on $[t,5t/4]$; it is not of that size on $[0,1]$. This rules out a translation-uniform mass estimate as the last step on this shell, not an estimate exploiting its actual height. For a first arithmetic test on the high-amplitude branch, retain the frozen untwisted phases and the translate, not just better spacing constants.

**Finite control: The rounded slot can change the sign.** At the [allocation fixture](distant-pool-allocation.md) $q=100000007$, $d=26$, $\gamma=1/4$, $r=D^2$, run `python3 .godel/bob/check-one-copy-supply.py`. At the genuine $t$ it gives, in the original unnormalized product weights,

$$ 0.8702416 < v/u < 0.8702420,\qquad 19007\cdot10^{-12}< S <19008\cdot10^{-12}. $$

On setting $B_{\rm unit}=(X/D)16^{-n}/t$ with coefficient exactly one, the same enclosures give $65000<S/B_{\rm unit}<66000$. Thus the percentage offset alone misses the size of the excess on the endpoint scale even in this small example. This is not a bound for the two-copy observable at this finite center, or a counterexample to any eventual inequality.

Keep the starts, signs, weights, separation, privacy requirement, exact $t\nu$ window, and kernel fixed. Omit **only** the nearest-slot recovery gate. The resulting sum $J_r$ is between $-7800\cdot10^{-12}$ and $-7799\cdot10^{-12}$. Thus even the sign of the ungated height integral is wrong for the finite completed excess. This does not contradict (1): The gate charge and saddle errors are asymptotic. The ratio above is one-copy supply, not the percentage of positive *net pool* mass offset in the earlier two-copy $H_r$ computation.

Here is the enumeration and enclosure. All private slots qualify since $R_*<2<r$. List all 80,331 separated quartets from the support, sorted by their exact rational product $\prod(p+d)/p$. For two quartets with product ratio $U/V>1$, exclude inter-quartet conflicts and take both choices of which is positive. Every admissible split occurs this way; equal ratios for distinct quartets are excluded by the least-start valuation. For each qualifying designated plus slot multiply by $3!4!$. For the control allow all four choices on each orientation, without changing any weight. The scan stops monotonically when $2\lfloor 10^6t\rfloor (U-V)/(10^6(U+V))>7$, strictly outside the window. For a retained bin this lower approximation to $|t\nu|$ errs by less than $10^{-8}$ by the series for $2t\operatorname{atanh}((U-V)/(U+V))$. The checker interpolates $G$ on a mesh of width $10^{-4}$ with outward enclosures, using $|G''|<2$ off the endpoint and the Lipschitz bound on the cell crossing it. Zeros of the cosine and the window endpoint need no sign decision: Both positive parts are bounded by monotonicity on the resulting interval of possible kernel values. The sign flip is certified for the complete one-copy family, not just the blocks that occur in a jointly separated pair of copies.

For a post-Work discrete version, see the [centered height mesh](centered-height-mesh.md): A bound on one chosen grid suffices, but a single locked prime phase can alias. The upper bound on the genuine weighted samples remains open.
