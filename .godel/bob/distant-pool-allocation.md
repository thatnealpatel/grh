# Exclusive allocation across substantially different prime pools

Consider either the original $I$ or its jointly separated version $H_r$ in the [integrated arc test](jointly-separated-arc-test.md), **separately**. Work at one genuine center and one shift with $A>a_0>0$, with the parameters and unsigned pool sums of the [supply formula](net-pool-supply.md). Write $P,N$ for the sums of the positive net pool weights and of the magnitudes of the negative net pool weights of the chosen observable. Pool keys are multisets in $I$ and sets in $H_r$. The following is about the actual arithmetic coefficients with both gates, both cuts, the distance test, and all label multiplicities. It holds also for the log coefficients. It is not a comparison of $I$ with $H_r$.

**Allocation theorem.** Put $m=\lceil n/D\rceil$. For large $t$ the entire smaller of $P,N$ can be paid from the larger, using each pool at most to its net capacity. Every transfer can be required to be between pools for which, **in each direction**, fewer than $4m$ occurrences are within $r$ of the other pool. Since $m=o(n)$, all but a vanishing fraction of the $2n$ starts must change even allowing $r$-sized moves. In particular the minimal unfilled positive demand is exactly $(P-N)_+$, not a larger loss imposed by the support geometry. If one side is empty the statement asserts no positive amount of transport.

**Price a forbidden neighborhood.** Fix any eligible $2n$-occurrence pool $V$. Ignore its sign, weight, and realization. To bound the absolute mass of candidate pools having at least $m$ occurrences within $r$ of $V$, sum the absolute labeled weights, an upper bound even for net capacities. For a fixed mask of $m=m_1+m_2$ candidate labels, where $m_i$ are in copy $i$, each label hits with product probability at most $p_*=2n(2r+1)\max_p(w_p/A)\le X^{-1/2+\xi_r+o(1)}$. Here $\xi_r=0$ at $D^2$ and $\xi_r=\gamma/[16(2+\gamma)]$ at $R_*$. The candidate's two compact windows require $|t\nu_i|\le9$ eventually. Conditional on the marked values, the unmarked groups in each copy must hit translated windows of this radius. Dropping all remaining restrictions, their joint cost is $\le4 U_{n-m_1}U_{n-m_2}$ in the moment notation of the supply formula. These moment estimates hold for mixed signs. For each mask, after division by $U_n^2$, the cost including the marked hits is at most

$$4p_*^m (U_k/U_n)^{m/(n-k)}.$$

Both orders are at least $k$ eventually. By $k=L+O(1)$, $n=CL+O(1)$, $U_k\le t^{-1/4+o(1)}$, and $U_n\ge t^{-1+o(1)}$, the second factor costs at most $\exp((3/[4(C-1)]+o(1))mD)$. The masks cost $\binom{2n}{m}\le(2en/m)^m=\exp(o(mD))$, **not** a generic $\exp(O(n))$ here. The resulting saving exponent is at least $(1/2-\xi_r-3/[4(C-1)]-o(1))mD$, with a strictly positive bracket. Restoring $A^{2n}U_n^2\le e^{o(n)}M_2$ as in the [central comparison](joint-pool-isolation.md), the mass bound is $b=e^{-\Omega(n)}M_2$ because $mD\ge n$. This is uniform in the whole fixed pool.

If the reverse direction has $4m$ or more near occurrences, some $m$ candidate occurrences must be near $V$ as well. Indeed each interval of length $2r$ contains at most two occurrences from each of the two internally $>r$-separated copies realizing $V$. Hence at most four fixed occurrences can be served by one near candidate. The same bound $b$ thus controls **all** forbidden mass around any fixed vertex, whichever the sign and whichever side has the larger total.

**Why the larger side is not swallowed by the forbidden mass.** The jointly separated central pairs have weight $M_2$ and integrated kernel bounded below there by an absolute positive constant. By [same-pool isolation](joint-pool-isolation.md), all but a $t^{-\gamma/[2(3+2\gamma)]+o(1)}$ fraction of this mass lies in pools with no negative term even after repartition and resigning. A jointly separated unsigned pool has the very same coefficient in $I$ as in $H_r$: Every repartition of that pool is still jointly separated, and the other tests have not changed. Thus $P\gg M_2$ for each observable, with no conjecture on $N$. In particular $B_0=\max(P,N)\ge2b$ eventually. This use of isolation concerns central mass, not a lower bound on the signed difference.

**Fractional Hall check.** Join the two sign classes by the allowed edges. For a nonempty set $S$ on the smaller side of total weight at most $B_0-b$, the neighbors of even a single member have capacity at least $B_0-b$. If instead the weight of $S$ exceeds $B_0-b$, it exceeds $b$; every vertex on the larger side has a neighbor in $S$. In either case total neighbor capacity dominates the weight of $S$. The finite weighted Hall criterion follows by putting the smaller-side weights on source arcs, the larger-side weights on sink arcs, and infinite capacity on allowed internal edges, and applying max-flow/min-cut. This proves the allocation statement. It says no more about $P-N$ than the original signed formula: A large supply is not a consequence of being able to transport all of a small supply.

## Check on a complete finite shift

At $q=100000007$, $\gamma=1/4$, $r=D^2$, and $d=26$, use **all** of the [complete-shift arithmetic coefficients](complete-shift-balance.md) of $H_r$. Here use the finite distance criterion $|V\setminus W|\ge j$, counting replaced starts exactly, **not** the asymptotic $r$-near criterion. Each pool has 16 distinct starts. Let $F_j$ be the maximum negative mass simultaneously allocated to positive pools under this rule. One has $F_8=N$: All the negative net mass, about $47.21\%$ of $P$, can be spent on pools changing at least half their starts. With nine or more replacements, strictly less can be spent. Some enclosures for $100F_j/N$ are:

| Minimum replacements $j$ | Usable percent of $N$ |
|---:|---:|
| 8 | 100 |
| 9 | $(91.33,91.34)$ |
| 10 | $(51.12,51.13)$ |
| 11 | $(14.18,14.19)$ |
| 12 | $(5.90,5.91)$ |
| 13 | 0 |

Run `python3 .godel/bob/check-distant-allocation.py`. It uses the original outward arithmetic evaluator with all label splits, not a sign-reversed finite proxy. There are 11 negative pools and 21 positive ones. For each $j$ the unused negative mass is exactly

$$N-F_j=\max_{S\subseteq\text{negative pools}}\left(\sum_{V\in S}|s(V)|-\sum_{W\in\Gamma_j(S)}s(W)\right),$$

including the empty set. This is the same finite cut calculation, not a sum over partners that spends capacity more than once. The checker evaluates all subsets, using exact rationals for the interval endpoints. For an upper bound on unused supply it uses *upper negative magnitudes and lower positive capacities*, and reverses both for the lower bound. This checks distance feasibility and the actual signed residual at one finite shift: Even unrestricted spending of $N$ leaves $(1.3648871509394895,1.3648871509394896)\times10^{-21}$ positive in the stated enclosure. It is not a test of an eventual exception bound, and $H_r$ at this center is not the original $I$.
