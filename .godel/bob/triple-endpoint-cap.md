# Test the signed endpoint on three consecutive primes

A raw hit in the [sign-thinning problem](principal-list-sign-thinning.md) needs a signed real projection of at least $8/9-o(1)$ at $y=q^{3/5}$, with $X=(3\log y)^2$. There is a test using only ratios inside disjoint triples of primes. It gives a moving-height rejection interval, not merely a count of survivors. There is also a linear necessary condition using just two harmonics, without a hypothesis on an adjacent chord mean.

Partition **all** primes $p<X$ in order, starting at 2, into triples $G$, allowing a short last group. Write $a_p=\log p$, $w_p=a_p\log(X/p)/X$, $M=\sum w_p$, and $m_G=\sum_{G}w_p$ (sum over primes in that group). For any real coefficients $|s_p|\le1$ the modulus of $\sum w_ps_p p^{iy}$ is at most

$$ U_X(y)=\sum_G\max_{\epsilon_p=\pm1}\left|\sum_{p\in G} w_p\epsilon_p e^{iy(a_p-a_G)}\right|, $$

where $a_G$ is the log of a middle prime. Indeed the maximum of the norm over a coefficient cube occurs at a vertex by convexity, and the triangle inequality allows a free rotation for each group. Four sign choices suffice per full triple after fixing its first sign. In particular the three pair signs in the squared norm must have product $+1$; taking a separate absolute value on each pair drops that constraint. The sum of radii is optimal when the only input is these within-group relative phases, with both signs and group rotations free. The arithmetic signs and rotations need not attain it.

**Price reuse in the original height variable.** At frozen cutoff the maximum and sum preserve the Lipschitz bound

$$ L_X=\sum_G\sum_{p\in G} w_p|a_p-a_G|. $$

This is $O(\log^3 X/X)$ without a prime-gap hypothesis: Each triple costs at most $3\max w_p$ times its log span, the spans are disjoint, and $\max w_p\le\log^2 X/(4X)$. Thus at fixed margin one evaluation can reject a whole interval of radius $cX/\log^3 X$ for sufficiently small $c>0$. For moving cutoff keep the old partition, adding new primes at their full absolute weight. More explicitly the raw projection at $y+h$ is bounded by $U_X(y)+|h|L_X+\sum_p|w_p(X(y+h))-w_p(X)|$, extending by zero. The last cost is $O(|\log(X(y+h)/X)|)$ by the [moving ramp estimate](principal-block-search.md), hence $o(1)$ on this radius. The coefficients may change arbitrarily at each point; there is no freezing of a character. This radius only applies **if** there is margin at the tested center.

**Two Fourier modes if linear sums are easier to estimate.** Put $D_0=\sum_G\sum_{p\in G}w_p^2/m_G$ and $P=M-D_0$. For each unordered pair $i<j$ in one group put $c_{ij}=2w_iw_j/m_G$, so $P=\sum c_{ij}$. Define $C_h=\sum c_{ij}\cos(2hy(a_j-a_i))$. Cauchy with weights $m_G$, followed by bounding each signed cross term by its absolute value, gives

$$ U_X(y)^2\le M\big(D_0+2P/3+(7C_1-C_2)/18\big). $$

Indeed $|\cos u|\le 2/3+(7\cos(2u)-\cos(4u))/18$: With $v=|\cos u|$ the difference multiplied by 18 factors as $(1-v)(2v-1)^2(2v+4)$. Thus the linear relaxation does not require independence between any edges.

Here $M=1+o(1)$ by PNT and $D_0=M/3+o(1)$. For a full triple the excess over $m_G/3$ is $\sum w_p(w_p-m_G/3)/m_G$, bounded by the range of its weights. The sum of ranges is at most the total variation of the unimodal ramp $a(\log X-a)/X$, at most $2\max_{0\le a\le\log X} a(\log X-a)/X$. The short last group costs $O(\log^2 X/X)$ too. Consequently a sequence of raw hits requires

$$ (7C_1-C_2)/P\ \ge\ 1/3-o(1),\qquad \max(C_1/P,-C_2/P)\ \ge\ 1/24-o(1). $$

The constant comes from $18((8/9)^2-7/9)/(2/3)=1/3$. These are specific weighted **within-triple** ratio sums on genuine primes. They mix first and second successors; they are not the gap-grouped positive parts of the [box test](rank-tapered-pair-mass.md). This trades the sign optimization for a linear arithmetic target and a loss in the cap.

**If only one ratio mode is accessible.** Let $S_2=\sum w_p p^{2iy}$. The same block Cauchy inequality, now applied to the *unsigned* doubled phases without dropping cross-term signs, gives $|S_2|^2\le M(D_0+C_1)$. A raw projection of modulus $R$ satisfies $R^2\le M(M+|S_2|)/2$: Rotate the signed sum onto the real axis, bound its projection by the sum of weighted absolute cosines, and apply Cauchy and the double-angle identity. Therefore either a raw hit or a principal peak $|S_2|\ge47/81-o(1)$ requires $C_1/P\ge 11/2187-o(1)$, since $2(8/9)^2-1=47/81$ and $((47/81)^2-1/3)/(2/3)=11/2187$. This smaller threshold needs just one signed linear ratio sum. At the fixture the resulting raw modulus cap $\sqrt{M(M+\sqrt{M(D_0+C_1)})/2}$ is in $(.872976,.872977)$. Neither mode estimate is asserted at every peak-search center.

**Genuine-height certificate.** At $y_0=(2^{127}-1)^{3/5}$ the [160-bit interval checker](check-triple-endpoint.py) brackets $U_X(y_0)$ between $.839117$ and $.839118$, with $L_X<.00437$. Throughout $|h|\le11$ the cutoff stays between 25107 and 25108 and the sum of absolute weight changes is less than $10^{-18}$. Hence throughout that interval the modulus is below $8/9$ even if every sign and every block rotation changes. A disjoint-pair calculation with the same weights gives a center cap in $(.883795,.883796)$ and certifies radius 1 by the same procedure. These radii are sufficient, not optimal. The two-mode triple cap at the center lies in $(.867177,.867178)$. Run `check-triple-endpoint.py` using SageMath 10.9 Python with assertions enabled.

**Use and limit.** One triple pass is linear in the number of primes, as is one direct projection; its benefit is a sign-independent interval that can be compared with an actual list of selected cells. This is a certificate against the raw $8/9$ level on that interval, not a finite evaluation of all error terms in the Weil endpoint implication. No selected cell is proved to lie there. Before inferring a search saving, test the triple cap and its radius at centers **from the principal list**, then measure how many other selected cells fall entirely inside a rejection interval. It is not known that the linear combination stays small on those centers, or that they cluster.
