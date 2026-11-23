# A peak must pay on first and second prime successors

Can one drop pairs separated by many intervening primes from the [weighted positive shift test](short-prime-pair-bias.md)? Yes, without a prime-tuple conjecture. Enlarging the fixed gap constant buys a reduction all the way to the first **two** successors. Keeping just the first successor is different: Even restoring all its fixed harmonics and the high signed endpoint mean does not suffice in the multiplicative-phase control class.

## Charge the occupied support, including rank cuts

Write $t=2q^{3/5}$, $X=(3\log(t/2))^2$, $D=\log X$, $a=e^{-8}X$, $H=CD$ for fixed $C>0$. Number the clipped primes $a\le p_1<\cdots<p_n\le X$, put $z_i=\log(X/p_i)$, $l_i=\log p_i$, and $S=X^{-1}\sum_{p\le X}\log p\log(X/p)p^{it}$. Let $T$ be the positive ramp mass below $a$. For $1\le d<H$ and an integer $K\ge1$ define

$$P_{d,K}=X^{-1}\sum_{p_j-p_i=d}z_j l_i l_j(1-(j-i)/K)_+\cos(t\log(p_j/p_i)),\qquad b_d=2(1-d/H)/H.$$

The ramp here is at the **right** prime. Take $K=\infty$ to omit the rank taper. Put $J=(XH)^{-1}\sum_i l_i^2 z_i$ and

$$ A_0=X^{-1}\left(Hz_1+\sum_{i=2}^n\min(H,p_i-p_{i-1})z_i\right),\quad A_1=H X^{-1}\sum_i z_i,\quad A(K)=A_0+(A_1-A_0)/K.$$

For nonempty support the exact bound is

$$ |S|\le T+\sqrt{A(K)\left(J+\sum_{1\le d<H} b_d P_{d,K}\right)}. \tag{1} $$

In particular $B_K=\sum b_d(P_{d,K})_+$ gives a cap with no endpoint correction. All of this holds at every real phase height and cutoff $X$, so in particular at each fixed harmonic $2j q^{3/5}$, with its own cutoff or the base cutoff. It is a different positive budget for each $K$: Removing terms before taking positive parts is not monotone in general.

**Proof.** Choose a uniform residue modulo $K$ at which to cut the ordered prime indices into consecutive blocks of size $K$ (possibly shorter at either end). For each block $G$ use a separate copy of the $(s,R)$ plane with measure $ds\,dR/(XR)$, $a\le R\le X$. Integrate $H^{-1}\sum_{i\in G,\ p_i\le R,\ s<p_i\le s+H}l_i p_i^{it}$, only over its occupied support (at least one prime in the box). With counting measure over blocks and probability over cuts, the integral is exactly the clipped sum: Each prime has $s$-length $H$ and enters at $R=p_i$. For fixed $(s,R)$ the active indices form a consecutive string. If its length is $h>0$, the number of occupied blocks is one plus the number of cuts across its $h-1$ internal gaps, of expectation $1+(h-1)/K$. For $h=0$ it is zero. The integral of $h$ is $A_1$; the union area $\int 1_{h>0}$ is $A_0$ since adding $[p_i-H,p_i)$ extends the union by $\min(H,p_i-p_{i-1})$ after the first entry. This proves the support cost $A(K)$. The squared norm has diagonal $J$. A pair has probability $(1-(j-i)/K)_+$ of sharing a block, overlap length $(H-d)_+$, and enters at $R=p_j$. Cauchy on the whole measure gives (1). For $K=\infty$ take one block. No assertion about a typical unweighted prime gap was used.

## A necessary signed cost with bounded successor rank

Put $e=9e^{-8}$ and $m=1-e$. PNT and partial summation give $T=e+o(1)$, $X^{-1}\sum_i l_i z_i=m+o(1)$, $J=m/C+o(1)$, and $A_1=Cm+o(1)$, since $l_i=D+O(1)$ on the clip. At each $R$ the occupied union is inside $[a-H,R]$. Integrating its length upper bound gives $A_0\le m+8H/X$. Thus along a peak sequence $|S|\ge s-o(1)$, $s>e$, both the positive budget and the *signed* sum in (1) are at least

$$ L(C,K)-o(1),\qquad L(C,K)=\frac{(s-e)^2}{m(1+(C-1)/K)}-\frac mC. \tag{2} $$

At $s=47/81$, $L(4,9)>0.001405$: The original length $4D$ suffices using only the first eight successors. More strikingly, $L(400,3)>0.00000158$. Thus at length $400D$ no edges beyond the **second successor** are needed. The small constant matters. Explicitly let $E_{r,d}$ denote the same right-ramp sum without rank taper, restricted to $j-i=r$. A strict limiting upper bound below $0.00000158$ for

$$\tfrac23\sum b_d(E_{1,d})_++\tfrac13\sum b_d(E_{2,d})_+$$

at genuine named centers excludes such peaks there, by subadditivity of positive part. If the first sum without its $2/3$ factor is $o(1)$ along peaks, the second without its $1/3$ must exceed $0.00000474$ eventually. Each second-successor phase is the **product** of two consecutive edge phases, not the product of their gap averages. These implications use the full mass down to zero excursion; no list of overshoots or common dip enters.

**Finite check.** At $q=2^{127}-1$ itself with $C=4$, the [160-bit Sage interval checker](check-rank-box.py) prices the original left-ramp, untapered positive budget in $(0.01200240,0.01200241)$. Only $d=12,36$ have positive left-ramp real part above $1/16$. The shifts *below* $1/16$ contribute between $0.0069925$ and $0.0069926$ to this budget, more than half the total. This prices the smaller positive terms in the triangular statistic at one height, not their high powers integrated over the shell. With the exact right ramp and $K=7$, $B_7\in(0.0071606,0.0071607)$ and (1) with positive parts gives $|S|<0.572435<47/81$. Thus the first six successors suffice in this fixture. The same positive-part cap is in $(0.588638,0.588639)$ at $K=6$, so that particular certificate no longer clears the threshold; this is not a necessity result for the sixth successor. With every rank the cap is $<0.461901$. The $400D$, two-successor test has a different outcome here: $0.000045720<B_3<0.000045721$, although the signed sum is negative, between $-0.000000748$ and $-0.000000747$. A bound below $0.00000158$ on the positive budget cannot hold starting at this fixture. Equation (2) is asymptotic, and (1) is one-sided. This measures the aggregated observable at the center, not the [offset cell](real-run-length.md), and does not improve the [termwise component cap](short-edge-components.md) from stronger data. Replay with SageMath 10.9 Python and assertions enabled.

## Why not just consecutive gaps, even with their harmonics?

Here is a control with the actual prime support and quadratic signs. Take arbitrarily sparse prime conductors $q$ so their clips are disjoint; write $y=q^{3/5}$ and $\xi_q(p)=(p/q)$. There exists one fixed unit completely multiplicative twist $\omega$ with the following properties along them. Write $v_p=\omega(p)p^{iy}$, $w_p=X^{-1}\log p\log(X/p)$ for $p\le X$. Then

$$ \Re\sum_{p\le X}w_p\xi_q(p)v_p>8/9,\qquad \Re\sum_{p\le X}w_p v_p^2>47/81. \tag{3} $$

Yet for every fixed integer $k\ge1$ and fixed $C>0$, at $H=C D$,

$$ \sum_{1\le d<H} b_d \left|X^{-1}\sum_{p_{i+1}-p_i=d}z_{i+1}l_i l_{i+1}(v_{p_{i+1}}\overline v_{p_i})^{2k}\right|=o(1). \tag{4} $$

In particular this is small even with complex absolute values *after* aggregating by actual gap, for every fixed harmonic of the doubled phases. These are powers of one prescribed phase at the center, not claims about one Dirichlet series at many heights with its twist unpowered.

Split the clipped primes in order into blocks of $M=\lfloor X^{1/4}\rfloor$ indices, and choose independent $U_G$ uniform on $[-\pi/2,\pi/2]$. In block $G$ prescribe $v_{p_i}=\xi_q(p_i)\exp(i(-1)^i U_G/2)$. This determines $\omega$ on the clip. The two real parts per prime in (3) then have expectations $2\sqrt2/\pi$ and $2/\pi$ respectively. The first constant has a two-angle interpretation: If the doubled phase difference is uniform on the circle, the distance $u$ of the original difference to $\pi\mathbb Z$ is uniform on $[0,\pi/2]$. After arbitrary signs the average of the real projections of two unit phases is at most $\cos(u/2)$ by the chord formula. Its mean is $2\sqrt2/\pi$, attained by the symmetric pair above. Thus even uniform edge differences need not drive the signed one-prime mean below $8/9$. In (3) each block has ramp mass $O(MD/X)=o(1)$, so both clipped real sums have variance $o(1)$ by independence. Their full lower bounds in probability are $m\,2\sqrt2/\pi-e-o(1)>0.894$ and $m\,2/\pi-e-o(1)>0.631$, regardless of phases outside the clip.

On an internal edge the $2k$-th power ratio is $\exp(\pm 2ki U_G)$ of expectation zero. The sum of absolute weights $z_{i+1}l_i l_{i+1}/X$ over all consecutive edges is $O(D)$ by PNT; the corresponding sum in one block is $O(MD^2/X)$. Summing variances over $d$, independence across blocks bounds the expected sum of squared internal gap coefficients by $O((MD^2/X)D)$: Bound the square of each block-and-gap mass by its mass times the largest block mass. Since $b_d\le 2/H$, Cauchy over the $O(H)$ shifts gives expected left side from internal edges $O_C(\sqrt{MD^2/X})$. The boundary edges cost $O_C(1/M)$ even in absolute value before aggregation, because there are $O(X/(DM))$ of them. Hence each fixed test tends to zero in probability. It suffices to test integral $C\ge1$: For $C'\ge C$ the triangular weight for $C$ is bounded by $C'/C$ times that for $C'$. Choose the conductors successively large enough to satisfy a growing finite prefix of these countably many tests with errors tending to zero and (3) with fixed slack. Assign the phases on those disjoint clips and extend arbitrarily on other primes. This realizes all claims with one twist. In this same construction the doubled second-successor ratios are identically one within blocks: The statistic lost by restricting to rank one is precisely where coherence can reappear.

**Decision.** For genuine phases, aggregate first- and second-successor products with their actual gap and sign, or use the stronger constant at $4D$ if eight successors are tractable. Neither the untwisted uniform estimate nor endpoint exclusion follows here. The [dyadic diagonal estimate](dyadic-prime-pair-moments.md) is an exceptional-set bound even for unrestricted shifts, not the pointwise bound in (2); the prime-pair upper sieve in the [box test](short-prime-pair-bias.md) majorizes unsigned masses, which can be large with the same support. The control in (3)–(4) is not a counterexample at an untwisted height. It rules out replacing the second-successor test by cancellation of adjacent ratios alone, even if the quadratic signs are restored in the one-prime statistic.
