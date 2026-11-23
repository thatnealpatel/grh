# A shared quadratic angle increases the dense hit count

On accepted base `0d94277be94007247cd3e3c0f5cf305a6eb01320`, use the frozen fixture of [the retained crest checker](check-retained-crest.py) and [the signed gap screen](signed-gap-cube-screen.md): $q=2^{127}-1$, $\gamma=1/4$, $t=2q^{3/5}$, $X=(3\log(t/2))^2$, $D=\log X$, $L=X/D$, $n=24$, $u=t+44L/\sqrt n$, and $K=61$.

| Common angle $\beta$ | Retained shifts with $B_d(\beta)>1/256$ | Count |
|:--|:--|--:|
| $0$ (untwisted) | $18,20,22,40$ | 4 |
| $21\pi/256$ | $18,22,28,32,38,40$ | 6 |

The inclusive integer trim is $11\le d\le40$. Retain $n^2C_d(D^2)\le61$, counting the diagonal and both orders in $C_d$. The pressure deletions are exactly $12,24,30,36$. Their sums were evaluated too: Of these four, only $12$ exceeds $1/256$ at zero, and none exceeds it at the witness. The 15 odd shifts have no prime starts and zero sums at both angles. Equality at the amplitude threshold would not count as a hit.

For each shift use the starts $p$ with both $p,p+d$ prime in $[e^{-8}X,X]$ (integer band $[9,25107]$). Put $z_p=w_p e^{iu\log(1+d/p)}$, with $w_p=\log(X/p)\log p\log(p+d)/X$. The checker sums $2z_p\overline{z_{p+g}}$ once per lower start in each positive gap $g>nD^2$, with no averaging. A group is dense if its number of lower starts exceeds $X/(nD^4)$, which lies strictly between zero and one here. Thus no nonempty far group is deleted. It evaluates $B_d(\beta)=\sum_g\Re(e^{-2i\beta dg}P_g)$ from these signed complex groups, without taking any group or sum modulus. At $d=18$, $g=22688$ has the single lower start $p=11$; the checker compares this complex contribution against the direct phase $u\log(1+dg/[p(p+g+d)])-2\beta dg$ at both angles. The witness multiplier there is $-i$, so the check distinguishes the rotation signs.

**Replay.** Run [`check-quadratic-overlap.py`](check-quadratic-overlap.py) with a SageMath Python interpreter and assertions enabled. The completed run used SageMath 10.9 and `/opt/sage-10.9/bin/python .godel/bob/check-quadratic-overlap.py` from the repository root. The checker uses Sage's exact prime list and rational arithmetic plus 192-bit real and complex interval enclosures; the witness is an exact rational multiple of $\pi$, not a grid-rounding convention. It enumerated 2,470,959 far pairs in 92,847 nonempty groups and classified all 30 shifts at both angles. Every pressure was more than $0.0002$ from $K$ and every signed sum was more than $0.0007$ from $1/256$, including on the deleted shifts. The closest sum was $B_{22}(21\pi/256)\in[0.0046211050976,0.0046211050995]$. A numerical probe only selected the witness; replay requires neither a search nor the shell-search algorithm.

Thus excluding six simultaneous hits uniformly in the auxiliary angle would be false on this fixture, even though there are only four at the genuine angle. The witness is a common rotation of genuine coefficients, not a second untwisted ordinate. No maximum over the period, real-projection conclusion, or asymptotic overlap bound is certified. To bound the untwisted overlap beyond this fixture, retain information that locates the superlevel sets relative to $\beta=0$.

**Persistence follow-up:** The [direct real check](conductor-interval-search.md#finite-checks-and-the-flagged-cell) finds a common subinterval below threshold for every trim shift inside the next genuine grid cell. A peak at the node does not persist on the entire cell; this does not exclude shorter overshoots.

**Short windows:** The [continuous run-length test](real-run-length.md) encloses the longest six-label real overlap inside this cell, resolves the signs, and prices the full positive box independently of retention.
