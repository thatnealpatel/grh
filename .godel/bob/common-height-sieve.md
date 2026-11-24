# Buffered marks require the small primes to agree at one height

For the [dyadic principal search](principal-block-search.md) at amplitude $a=.587$, $Q=2^k$, $J=Q$, the following are the **only modes not excluded** for a marked cell meeting its target interval. A negative index means a negative real-part test at the positive frequency. No entry asserts existence.

| $k$ | Not excluded |
|---|---|
| 29–34 | $-3,-9,-14,-20$ |
| 35–36 | $-9,-14,-20$ |
| 37–38 | $-14,-20$ |
| 39 | $-20$ |
| 40–41 | None |

Together with the [verified-height certificate](verified-height-principal-band.md) this makes $40\le k\le59$ a consecutive empty band. This is about buffered nodes and either permitted frozen cutoff $V$, not just unbuffered hits or an average over conductors. There is no new zero verification or asymptotic claim.

**Individual and joint prices.** Write $S_V(t)=\sum_{p\le V}w_p e^{it\log p}$ with $w_p=(\log p)\log^+(V/p)/V$. The node estimate is within $\eta/8$ and must reach $a-\eta/2$ for a mark, so it suffices to exclude true values $\ge c=a-5\eta/8$, $\eta=1/\lfloor\sqrt{k+1}\rfloor$. For mode $j$ use $[2|j|Q^{3/5}-1,2|j|(2Q)^{3/5}+1]$: Even a left node outside the target but touching it by a closed cell lies here. Apply the preceding note's translated Weil inequality **before maximization**:

$$ \operatorname{sgn}(j)\Re S_V(t)\le G+\sum_p P_p(t\log p),\qquad P_p(\theta)=\sum_m (\operatorname{sgn}(j)\Delta_{p^m}-A_{p^m})\cos(m\theta). $$

All corrections are at $p\le\sqrt V$. Use the upper height in $G$ and enclose both cutoffs throughout. With certified upper prices $U_p\ge\max P_p$ and $T\ge G+\sum U_p$, a hit requires $T\ge c$ and

$$\sum_p (U_p-P_p(t\log p))\le T-c.$$

In particular no row can spend more than $T-c$, and **at most one** can spend more than $(T-c)/2$. The first test to run is just $T<c$ on each harmonic separately. For $k=40,41$ it leaves only $-20$, and for $k=39$ it leaves $-14,-20$. We used the common-height test on $(39,-14),(40,-20),(41,-20)$.

**Exhaustion, not sampling.** Run `sage -python .godel/bob/check-height-sieve.py` with assertions enabled (SageMath 10.9, NumPy). Each anchor $8n$ covers 64 consecutive closed eighths. For each charge limit $L\in\{T-c,(T-c)/2\}$, keep a phase bin if interval evaluation allows $P_p\ge U_p-L$ anywhere in it. Cosine symmetry reflects the first 512 closed bins onto the other half of the turn. Subtracting the *scalar* $U_p$ from the total does not subtract an unknown coefficient interval. Discard an eighth if any full-charge mask fails, or if two distinct half-charge masks fail. Both failures must hold throughout that same eighth; masks passing at different points need not yield any witness.

In more detail, put $r_p=\log p/(2\pi)$ and choose an integer $s_p$ within one unit of $8r_p2^{64}$. For $B=1024$, all anchors satisfy $Bn<2^{64}$. In bin units, $8nr_p B$ thus differs by less than one from $Bns_p/2^{64}$. Multiplying unsigned words modulo $2^{64}$ and extracting their top ten bits computes the latter's floored bin $b$ modulo $B$. On some lift the actual anchor phase lies between $b-1$ and $b+2$. Add $Br_p[h,h+1]/8$ for eighth $h$. The mask ORs all possibly reached bins, cyclically, with their indices rounded out; `roll(hot,-d)[b]` reads bin $b+d$. No trigonometric decisions use machine floating point. The first and last anchors may extend beyond the padded target. Only the intersection needs the Weil cap used to eliminate heights.

For every eighth not eliminated, bound the original negative real ramp at its exact midpoint by interval cosines, and add half its width times $\sum_p w_p\log p$. Bisect when this is not strictly below $c$; fail rather than silently skip a leaf. For the three joint tests above, respectively $19,979,336$, $43,261,443$, and $65,572,084$ anchors left **0, 7,710, and 53** eighths to check directly. All were excluded. As a control, using just the full-charge masks on the same $k=41$ interval left 1,005 eighths, not 1,005 marks.

**Next decision.** For a nonempty list with mass above $8/9$, screen only the listed modes in these blocks and certify a specific frozen lattice node with the mark's actual rounding rule before pricing successors. The small $k$ rows have a shorter physical interval and more unresolved modes than $k=39$; a search for a positive example need not exhaust negative certificates from the top down. The high-harmonic verified-height limit above the previous band is unchanged. No $d=6,8$ contribution has been measured here.
