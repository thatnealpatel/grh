# Which sparse pairs still need a bound?

For the [fixed-gain moment test](critical-conductor-window.md#next-arithmetic-test-for-a-fixed-gain), it suffices to bound the pairs with **large gap after cancelling their gcd**. This removes part of the count at each prime, not merely on average over conductors.

Keep $L=\log q$, $B=\log L$, $X=(2.1L)^2$, $k=\lfloor(5/2)L/\log X\rfloor$, $N=X^k$, and $T=q^{6/5}$. Count ordered distinct values $n,m$ that are products of $k$ primes in $[X/B^4,X]$, repetitions allowed, with $q\mid n-m$ and $|n-m|\le 2N/T$. Put

$$
 H=2N/(qT)\le 2q^{3/10},\qquad g=(n,m),\qquad h=|n-m|/(qg).
$$

Here $h$ is a positive integer: $q>X$ for large $q$, so $q\nmid g$. In particular $gh\le H$. Write $C(J)$ for the count restricted to $h\le J$. Uniformly in prime $q$ and $1\le J\le H$,

$$ C(J)\le q^{5/4+o(1)}\sqrt J. $$

**Proof.** Let $P=\prod_{p\le X}(1-p^{-1/2})^{-1}$. Partial summation gives $\log P\ll \sqrt X/\log X=o(L)$. Rankin's bound for the number of $X$-smooth integers up to $z$ is $\sqrt z\,P$, by summing $(z/d)^{1/2}$ over them. Thus there are at most $\sqrt N\,P$ possible $n$. Fix one and one of its at most $2^k=q^{o(1)}$ divisors $g\le H$. Put $u=n/g$, $v=m/g$. Dropping coprimality is safe for an upper bound. We need $v\equiv u\pmod q$ and $|v-u|\le qJ$.

Every admissible $v$ exceeds $J$: Indeed $v\ge NB^{-4k}/H=(qT/2)B^{-4k}=q^{11/5-o(1)}$. It has a divisor $d$ in $(J/X,J]$: Take a product of successive prime factors up to just before the product first exceeds $J$. Each prime is at most $X$. For fixed $d$, the conditions $d\mid v$ and $v\equiv u\pmod q$ give one residue modulo $qd$. Thus the row interval has at most $1+2J/d\le 1+2X$ such integers. There are at most $\sqrt J\,P$ choices of $d$. Multiplying the bounds proves the display; it does not require uniform distribution of smooth numbers in progressions.

**Decision.** Taking $J=H$ gives only $q^{7/5+o(1)}$, above the sufficient exponent $13/10$. This is the limit of this calculation, not a lower bound on the count. Instead take $J=q^{9/100}$. The removed pairs cost at most $q^{259/200+o(1)}$, saving $1/200$ in the exponent. In the remaining pairs,

$$ q^{9/100}<h\le H/g,\qquad g<2q^{21/100}. $$

Only this range needs a bound $O(q^{13/10-\xi})$ for some fixed $\xi>0$ to complete the unweighted pair test. Equivalently, after fixing $g$, the reduced products are coprime and have difference $\pm qh$; the bound must still be **summed** over $g$. Neither that saving nor its necessity for the original Weil bound is established.

## Why change the handoff, not the program?

Work run `01a206de-1f1f-707b-aa60-c553c25ead5c` matches session `01a206de-20d3-708a-a2fb-2119f9996401` by input and output. The launch marker and embedded Work prompt match `f921053711121d025c32d2e7de21c07c2ce4188f`. Alice did well to keep the each-prime quantifier and change the height and the prime slice when the full fixed-gain estimate stalled. Reviewer `PKsEJTJ` checked the second-order theorem and the block transfer on `985f52d5c42a8045f6a10c9b3ccfb26cdde9f50f`; the proof text was unchanged at adoption (`fd044e18a8a55882ab30fade62491437ed71a30a`). That review was not a proof of the next pair estimate. Bob's [product-conductor argument](../bob/quadratic-product-window.md) uses distinct prime conductors; it does not supply the missing bound at one modulus.

At the handoff decision, two messages already identified the one-divisor barrier (Work events 70 and 113). In particular `vMKqpoe` supplied both the $13/10$ target and the $7/5$ row calculation before the note was written at event 136. The handoff kept the target and omitted the calculation. There is no evidence that a later live worker repeated it.

**Cold-reader replay.** Two fresh Sol readers in improvement session `01a206fa-0eac-7f3e-ac45-ec4cc2f9af81` received the same adopted note and bounded calculation task. Only `KMlOvSf` received the omitted row estimate; neither brief suggested splitting by gcd. Both found that split. `ItbbKuN` counted the reduced progression trivially and disposed of $g\ge q^{11/40}$ at cost $q^{51/40+o(1)}$. Its row cost at gap cutoff $J$ is $O(J)$ instead of $q^{o(1)}\sqrt J$: At $J=q^{9/100}$ it gives exponent $1.34$, not $1.295$. Thus the added evidence improved the *proved range*, not the choice of decomposition. Both readers took about one minute; there is no speed claim. Keep the graph, standing prompts, and independent proof check. Link this parameter-specific bound where the next worker reads the target. Recompute it if the product length or time cutoff changes; one replay does not justify a mandatory new review or establish live progress on the residual.

## Also discount repeated factors on both sides

There is a stronger normalized gap cutoff. For $n=gu,m=gv$ in the notation above put $e(t)=t/\operatorname{rad}(t)$, with $e(1)=1$. Uniformly for $S\ge1$, the count with

$$h\le S e(u)e(v)$$

is at most $q^{5/4+o(1)}\sqrt S$. In particular one may now discard all pairs with $h\le q^{9/100}e(u)e(v)$ for the same cost $q^{259/200+o(1)}$. This saves on pairs with repeat prime factors even if their gcd is one. It gives no further saving when both reduced products are squarefree.

First, among $X$-smooth $t\le z$ with at most $k$ prime factors counted with multiplicity and $e(t)\ge R$, there are at most $q^{o(1)}\sqrt{z/R}$ values. Indeed the radical is $X$-smooth and at most $z/R$; use the Rankin estimate above. For each radical with $j\ge1$ primes ordered by size, the possible positive exponent lists of sum at most $k$ number $\binom{k}{j}\le2^k$. The unit adds no difficulty. All losses here are uniform for the parameters in the count.

By symmetry put $e(u)\ge e(v)$. Use dyadic intervals $h\in(J/2,J]$, $e(u)\in[U,2U)$, $e(v)\in[V,2V)$, with $U\ge V\ge1$. For fixed $g$ the starting values $u$ cost $q^{o(1)}\sqrt{N/(gU)}$. To bound the row of $v$, put $W=\min(V,\sqrt J)$. Choose a divisor $b\mid e(v)$ in $[W/X,W]$: Multiply prime factors until just before exceeding $W$, or take the whole product if equal. Then $d_0=b\operatorname{rad}(b)$ divides $v$ and is at most $W^2\le J$. Complete it by multiplying remaining prime factors of $v$ up to just before exceeding $J$, giving $d\mid v$ in $(J/X,J]$ since $v>J$ for large $q$. Now $e(d)\ge e(d_0)=b\ge W/X$. The radical count bounds the number of possible $d$ by $q^{o(1)}\sqrt{J/W}$, absorbing $\sqrt X$. For each such $d$ the old CRT row costs $O(X)$: $v$ belongs to one class modulo $qd$ within distance $qJ$ of $u$. Summing over $g$ costs only $\sum_{g\ \text{$X$-smooth}}g^{-1/2}=P=q^{o(1)}$ after extracting the factor $\sqrt{N/U}$. Thus the dyadic block costs

$$q^{5/4+o(1)}\sqrt{J/(U\min(V,\sqrt J))}.$$

If $V\le\sqrt J$, the gap hypothesis gives $J<8SUV$. Otherwise $U\ge V>\sqrt J$ already bounds the square root by one. Summing the logarithmically many choices in each parameter and allowing both orientations proves the assertion. Here $J\le 2H$ and the lower bound $v\ge NB^{-4k}/H$ used earlier is still more than $J$.

**Remaining fixed-gain test.** It suffices to treat $h>q^{9/100}uv/\operatorname{rad}(uv)$ since $(u,v)=1$. In particular $g e(u)e(v)<2q^{21/100}$ there. The missing bound is still on the sum over $g$ and the large gaps, not a per-progression statement. In a dyadic range $h\asymp q^j$ with squarefree $u,v$, the row calculation gives $q^{5/4+j/2+o(1)}$ and needs a further $q^{j/2-1/20+\xi}$ saving when that exponent is positive. The separate [masked operator estimate](masked-conductor-window.md) improves the second-order window without furnishing this fixed-power saving.
