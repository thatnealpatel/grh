# Price ordinary labels with a bounded product outside prescribed primes

Fix one actual two-label list in the stratum of the [global double ratio](global-double-ratio.md). Work with ordinary triples only, in a bin $q^t\le J_0<2q^t$. Put $\mu=\min(t/2,.223)$, so the [ordinary multiplicity bound](cheap-filter-occupancy.md) is $q^{\mu+o(1)}$ triples per reduced label $L=N/M$. For an integer $u>0$, write $u_{\rm out}$ for the product with multiplicity of its prime factors outside a prescribed set $\mathcal P$.

**Claim.** Prescribe the primes of the six raw factors $k,h,Z,Z_0,Y,Y_0$ of at most $K=\lfloor(\log\log q)^2\rfloor$ actual witnesses, or any subset of these primes. Across *all* denominator pairs on this list, the ordinary triples with

$$ (NM)_{\rm out}\le q^{4.381-2\mu} $$

together cost at most $q^{1.1355+o(1)}$ in the bin. This is a price for one pool, uniform in its choice. Neither the inside nor the outside coordinates need to determine the label on their own.

**Proof.** Use the [signed divisor split](output-path-packets.md) on the global label rather than on a path at fixed endpoints. The eligible primes have ceiling $X\asymp(\log q)^2$ and floor $X/(\log\log q)^4$. Each polynomial-height product has $O(A)$ factors with multiplicity for $A=\log q/\log\log q$. Thus $|\mathcal P|=O(KA)$. The number of exponent vectors of total weight at most $O(A)$ on this set is at most $\exp(O(A\log(2+K)))=q^{o(1)}$ by stars and bars. Enumerate the two full supported parts of $N,M$ separately at this cost; write $m$ for their product.

Bin $N$ dyadically. The reduced labels are positive, $N/M\equiv1\pmod q$, and $N/M=1+O(q^{-1.110+o(1)})$ uniformly on the list. For two candidates in this bin the integer $\Delta=N_1M_2-N_2M_1$ satisfies

$$ |\Delta|/q=M_1M_2|L_1-L_2|/q\ll q^{-2.110+o(1)} N_1M_1. $$

Since the supported parts agree and are prime to $q$, $m\mid\Delta/q$. Choose a common upper bound $U=q^{4.381-2\mu-2.110+o(1)}$ for $|\Delta|/(qm)$ throughout the claimed class, including the uniform width constants. If $z=(NM)_{\rm out}\le U$, encode the two outside parts exactly. Otherwise take a divisor of $z$ strictly crossing $U$ in prime factor order, of size $U<f\le UX$, and encode its split between $N,M$. In this branch $mf\mid\Delta/q$ for two candidates with the same encoding, and $f>U$ forces $\Delta=0$. The reduced labels coincide. In both branches there are at most $q^{o(1)}\sqrt U$ encodings by the [smooth half-power estimate](shared-complement-count.md), first counting the product and then its divisor-many splits. Rankin's bound at $1/2$ costs $D^{1/2}\prod_{p\le X}(1-p^{-1/2})^{-1}$ for products up to $D$; the Euler factor has log $O(\sqrt X/\log X)=o(\log q)$ by partial summation. This absorbs the overshoot and the dyadic bins. The exponent for labels is $(4.381-2\mu-2.110)/2=1.1355-\mu$. Multiplying by the ordinary price proves the claim.

**A test on both actual rows.** For this bin, a contradiction to the existence of the following ordered sequence would suffice for the strict triple budget. If selection gets stuck before $K$ steps, the claim prices the whole bin: Start with the empty pool; at each step take one actual triple with $(NM)_{\rm out}>q^{4.381-2\mu}$, then add its six raw supports to the pool. Prior labels have outside product one, so each success supplies a new label. The estimate is applied to the current pool, not summed over the possible selection histories.

At each success both pairs of actual outputs satisfy

$$ (YY_0)_{\rm out},\ (ZZ_0)_{\rm out}\ \ge q^{.161+t-2\mu-o(1)}. $$

Indeed, with $n/w=Y/Y_0$ and $x/y=kZ/(hZ_0)$ in lowest terms, $NM=DB$ where $D=nw/J_0$ divides $YY_0$ and $B=xy/J_0$ divides $khZZ_0$. Here $D\le q^{2.890-t+o(1)}$, $B\le q^{4.220-t+o(1)}$, and $kh\le q^{1.330+o(1)}$. Bound $B$ in $D_{\rm out}B_{\rm out}$ to obtain the first inequality; bound $D$ and $kh$ to obtain the second. Use the union from *one chosen triple* per earlier label. These are product bounds, not radical bounds, and neither requires a fresh prime in each individual column. They need not use distinct primes on the two rows. No incompatibility between the two bounds has been proved.

The next question is whether the actual row equations permit these successive outside products on the same list. The common first input is shared by the two columns of each triple; it need not be fixed along the sequence. A bound on just one chosen valuation space, or sampling a few selections, would not rule them out. If these products can coexist in actual sequences, use the price above for the passing class only. Neither the number of triples with large outside product nor the unrestricted $q^{.998}$ incidence count is bounded here.
