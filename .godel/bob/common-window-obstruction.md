# A positive jointly separated integral with no positive common-window arc

Use the [jointly separated family](jointly-separated-arc-test.md) at the prime $q=1532161$, $t=2q^{3/5}$, $d=24$, $\gamma=1/1000$, and $r=D^2$. Write $P=2\pi$, $W_u=[u-P,u)$, and $S=((X/D)16^{-n}/t)^2$. Define $D_r(u,w)$ and $Q_r(u,w;v)$ as in the [sharp-window test](sharp-period-windows.md), but with all $2n$ starts jointly separated. On the **whole shift**,

$$53 < H_r/S < 54,\qquad -22 < \mathbb E_u D_r(u,u)/S < -21,\qquad \max_{u\in[0,P],\ v\in[0,\pi/2]}Q_r(u,u;v)=0.$$

Two independent window locations give $H_r=\mathbb E_{u,w}D_r(u,w)$ by integrating the two window indicators separately. For a common location the joint inclusion probability of phases $a,c$ is instead $(1-\operatorname{diam}\{0,a,c\}/P)_+$. The loss exceeds $74S$. The sign of this mean alone does not exclude a positive arc at some location and width; the row check below does.

**Certificate.** Run `python3 .godel/bob/check-common-window.py` (standard library, assertions enabled). Here $h=3$, $n=6$, $A>2$, $42<r<43$, $R_*<2$, and $e^{-8}X<1<X<658$. Of 56 prime-pair starts, enumerate all 39,369 increasing 12-sets of minimum gap 43. Thus no endpoints coincide, all slots are private, and the old distance cut removes nothing. Orient the block containing the pool minimum so that the minimum is positive **for pruning only**. A lower bound $R$ on its ratio uses the two largest other starts upstairs and the three smallest remaining starts downstairs, since $(p+d)/p$ decreases. If $R>1$, even the reciprocal orientation has absolute defect at least $1-1/R$. The exact fifth-power window test on this lower bound leaves 66 pools. No sign or rounded label was used to choose them.

On each survivor split into complementary six-sets, and try each three-positive signing in each block. For its actual ratio $U/V$ check $32q^3|U-V|^5\le (8V)^5$; use $a=t(U/V-1)(1-(U/V-1)/2)$, not the log phase. For each positive slot $p$ the omitted ratio is $M/N=Up/(V(p+d))$. Count it only when $M<N$ and $dM/(N-M)$ rounds to $p$ (no ties); this also puts it in the required band. Each pair of signings with $g,j$ admissible labels contributes $2(2!3!)^2 gj\prod w_p$ before the phase factors. The 2 accounts for the two orders of the blocks, not for a reversal of either signing. Exact integer tests and outward intervals as in the [complete-shift checker](check-complete-shift.py) suffice.

Of the pairs passing both compact cuts and both gates, four signing pairs have nonzero tapers before exchanging the copies. All share the signing $+(199,419,523)$, $-(257,307,467)$, with phase about $-2.375337$ and valid label 199. The others have positives $(103,149,373)$ and negatives $(59,569,s)$, or the reverse:

| $s$ | forward phase | valid labels | reverse phase | valid labels |
|---:|---:|---|---:|---|
| 617 | $+3.946287$ | 103, 149 | $-3.946287$ | 59 |
| 619 | $+5.190605$ | 103 | $-5.190605$ | 59 |

Rounded phases in the table are for orientation only. For the forward rows the unwrapped difference exceeds $P$, so no $W_u$ contains both phases. For both reverse rows the absolute difference lies **strictly between** $\pi/2$ and $\pi$ (about $1.570950$ and $2.815268$). For every $u$ and $v\le\pi/2$ they can only be subtracted, never added. At $v=0$ neither arc counts either row. These strict tests cover the continuum, including the half-open window endpoints, without gridding it.

**Scope.** This rules out an exact finite passage from $H_r\ge S$ to any positive common-location arc, with the actual gates. It neither contests the common-window theorem for the original $I$ nor rules out an eventual result for $H_r$ or proves the common-dip failure hypothesis here. To reopen this particular shortcut, price the signed loss from requiring a common location on the required large-$q$ shifts. Do not invoke the unrestricted product variance to give that loss a sign.
