---
evidence_revision: 6e777c9fccca8071842f8dbf9ac0940932090ab8
---

# Test robust prime-sample detection of edge attainment

**Hypotheses:** Fix a known integer $q\ge2$, a known real
polynomial $P$ of degree $D\ge1$ with positive leading
coefficient, and known $\kappa>0$. Use exactly $H$, the
weights, and the named primitive inducers in the shared
triangular landing. Let $\theta$ be the supremum of the
real parts of their nontrivial zeros, including zeta.
At each prime $p$ with $P(p)\ge2$, receive an indexed
real $y_p$ or an erasure. In each sufficiently late block
$[N,2N)$ there are $O(N^{1-\kappa})$ bad eligible indices,
counting erasures and arbitrary corruptions. On the good
tail, $y_p=H(P(p))+O(\sqrt{P(p)})$ uniformly, with unknown
bound and no convergence or mean condition. Use natural
logs.

**Proposition to test:**

1. For $N=2^j$ set $\delta=\min(\kappa/2,1/4)$. Let $U_N$
   be the $\lceil N^{1-\delta}\rceil$th largest $(-y_p)_+$
   among nonerased eligible primes in $[N,2N)$, or zero
   if there are too few entries. Then
   $$\theta=\max\left\{\tfrac12,\limsup_{j\to\infty}
   \frac{\log(1+U_{2^j})}{D\log(2^j)}\right\}.$$
2. For $\theta>1/2$, the edge is attained if and only if
   there are $c>0$, $C>1$, and $a>0$ such that in every
   sufficiently late real block $[N,CN]$, at least
   $aN/\log N$ nonerased eligible primes report
   $y_p<-cP(p)^\theta$. In the attained case such a block
   contains an interval of length at least $aN$ on which
   all good samples satisfy the same inequality. In the
   unattained case $|y_p|/P(p)^\theta\to0$ along the
   entire good tail.
3. For the same $\theta>1/2$, set $v_p=y_p/P(p)^\theta$
   at nonerased eligible primes and zero otherwise. Set
   $W_p=\max(-\log(2p),\min(\log(2p),v_p))$. For each
   real $t$, the ordinary limit
   $$\lim_{Z\to\infty}\frac1{\log Z}
     \sum_{\substack{p\le Z\\ P(p)\ge2}}
     \frac{\log p}{p}W_pP(p)^{-it}=c(\theta+it)$$
   reads the grouped coefficient from the shared pin,
   zero at absence. Its label inversion gives every
   named edge order, including at $t=0$.

**Source and payoff:** The shared landing's lines 109–157
supply the expansion, coefficient signs, and injection;
lines 159–197 use them for late subedge negative runs.
The propagation source is
`2a477e0bed19c2a3cfb88cf77d82a22104d69272`.
This is a proposed use, not a claim of that landing or
of `645200463f434bd285a45f71442650202427aa5b` (integer
sampling with aggregate labels) or
`7e7144a3b79704b7233c880832296e381f49a701` (median strips
and a specified small tolerance). The new consumer asks
for every-block attainment and direct prime averages from
real reports, not a raw-sign test, line recovery, strip
peeling, or effective or finite-data recovery.

**Discriminating test:** Compare dyadic peak counts and the
bad budget with the trimmed rank, including a crossing of
a power-of-two boundary. At the edge, use absolute
summability to test whether all left contributions vanish
without a gap. Test whether a nonzero real edge trace
with nonpositive mean must have a negative interval whose
translates recur relatively densely in real log time.
Include the real constant and the empty edge at $\theta=1$.
Pull back an entire recurring interval by $\log P$ and
verify prime mass uniformly in the block's starting point.
For the same data, bound the clipped corruption and
omitted clean mass on dyadic blocks, then calculate the
fixed-frequency twisted prime mean by partial summation.
Check $t=0$, absence, and the exact label inverse.
