---
evidence_revision: 6e777c9fccca8071842f8dbf9ac0940932090ab8
outcome: established
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

## Adjudication

**The three statistics work for the same reports.** All references to
line numbers below are to the shared landing at the evidence revision.
Use its expansion (109–131), writing the square term and smaller error
as $R(X)=O_q(\sqrt X)$. The coefficients are grouped by location,
conjugate in pairs, and nonzero at every zero (143–157). At a real
zero above $1/2$ the coefficient is strictly negative (133–142).
By reflection and nonemptiness, $1/2\le\theta\le1$.

**The rank measures the supremum, not its occupation.** Absolute
summability gives $H(X)=O_q(X^\theta)$. Thus late good entries have
$(-y_p)_+=O(N^{D\theta})$, including when $\theta=1/2$. Since
$\delta<\kappa$, fewer than the specified rank can exceed this bound.
This proves the upper bound, including the insufficient-entry case;
the floor in the formula suffices for the reverse bound at $1/2$.

For $1/2<b<\theta$ take $0<e<\min(\delta,1/10)$, and then take
$\max(b,\theta-e/(2D))<u<\theta$. Lines 159–174 give arbitrarily
late $Y$ with $H(Y)<-Y^u$, whether or not the edge is attained.
Indeed an eventually nonnegative $H(X)+X^u$ has a Mellin integral
whose continuation has every grouped pole to the right of $u$.
A real convergence abscissa there cannot be a pole (negative residue)
or regular (the nonnegative Taylor moments would give convergence to
its left); an abscissa at or left of $u$ contradicts a visible pole.
This uses continuation for the continuous peak lemma, not on the data.

Take $P(T)=Y$ on the increasing tail. For $T\le x\le T+T^{1-e}$,
$t=\log(P(x)/Y)=O(T^{-e})$. The half-moment and
$|e^{tz}-1|\ll(t|z|)^{1/2}$ for $0\le t\le1$ bound the variation
of the zero sum by $O(Y^{\theta-e/(2D)})$. Bounding both remainder
values and the good error costs $O(\sqrt Y)$ since $P(x)/Y\to1$
uniformly. Both costs are $o(Y^u)$, so good reports throughout are
below $-P(p)^b$. The all-interval corollary of
[Guth and Maynard](https://arxiv.org/abs/2405.20552) applies to
$y=x^{9/10}$ since $17/30+1/10<9/10<0.99$; its error is $o(y/\log x)$.
Pack adjacent intervals of this length, using their respective left
endpoints $x$. The unused tail is $O(T^{9/10})=o(T^{1-e})$. Thus
there are $\gg T^{1-e}/\log T$ primes. At most two dyadic blocks meet
the excursion; keep the one with at least half the count, $N\asymp T$.
After removing $O(N^{1-\kappa})$ indices the count still exceeds
$\lceil N^{1-\delta}\rceil$, since $e<\delta<\kappa$. Hence
$U_N\gg N^{Db}$ arbitrarily late. Taking $b\uparrow\theta$ proves (1).

**Every block, not just a subsequence.** Now $\theta>1/2$. Write
$f(s)=\sum_\gamma a_\gamma e^{i\gamma s}$ with
$a_\gamma=c(\theta+i\gamma)$ on the edge, zero at absence. Then
$X^{-\theta}H(X)=f(\log X)+o(1)$: Each strictly left term vanishes,
dominated by its summable coefficient modulus, and the remainder is
$o(X^\theta)$. The good normalized error also vanishes along the whole
good tail. If the edge is empty this gives the stated uniform decay.
Only bad entries can then cross any fixed negative threshold late;
any fixed $[N,CN]$ meets $O_C(1)$ dyadic blocks of scale comparable
to $N$, costing $O_C(N^{1-\kappa})=o(N/\log N)$ even on a subsequence.

For an occupied edge, put $M=\sum|a_\gamma|$ and
$S=\sum|a_\gamma|^2>0$. Conjugation makes $f$ real. Here is a direct
check of negative-interval recurrence in **real log time**. Write
$A_{s,L}$ for the average over $[s,s+L]$. At frequency $v\ne0$ the
exponential average has modulus at most $\min(1,2/(L|v|))$,
independently of $s\in\mathbb R$; at zero it is one. Consequently
$$
 A_{s,L} f\longrightarrow a_0\le0,\qquad
 A_{s,L}|f|^2\longrightarrow S
$$
uniformly in $s$. For the second limit expand the absolutely summable
double series ($\sum_{\gamma,\nu}|a_\gamma a_\nu|=M^2$); precisely
the diagonal survives, with no spacing assumption. Since $|f|\le M$,
$$
 (-f)_+=(|f|-f)/2\ \ge\ (|f|^2/M-f)/2.
$$
Fix $L$ large enough that $A_{s,L}(-f)_+>S/(4M)$ for **every** $s$.
With $c=S/(16M)$, each such block contains a point with $f<-4c$.
Uniform continuity (uniform trigonometric approximation) gives a
fixed $h>0$ with $f<-3c$ within distance $h$ of any such point.
Apply the point bound on the middle length-$L$ part of each block
of length $L+2h$. This yields a whole length-$2h$ negative interval
inside each block, including for a negative constant trace. A
nonnegative trace, or unbounded gaps between these excursions, is
therefore impossible.

Eventually $D/2\le xP'(x)/P(x)\le2D$. Fix $C$ so that
$(D/2)\log C>L+2h$. Under $x\mapsto\log P(x)$ each late $[N,CN]$
covers such a block; the negative interval pulls back to $[A,B]$ of
length at least $hN/D$, since the derivative is at most $2D/N$.
All good reports there satisfy $y_p<-cP(p)^\theta$ by the uniform
tail bound. Ordinary PNT gives $\vartheta(B)-\vartheta(A)=B-A+o(N)$
uniformly for these endpoints, so there are $\gg N/\log N$ primes.
Removing the full bad budget still leaves $\gg N/\log N$. Take $a>0$
small enough for both the length and the count. This proves (2).

**Clipped selector.** Late good normalized reports are bounded, hence
unclipped. Compare $W_p$ to the bounded clean trace $f(\log P(p))$
at eligible primes. Their difference is $o(1)$ along the good tail.
At all bad indices of dyadic block $j$ together, the absolute cost
to the twisted sum is $O((1+j)^2 2^{-j\kappa})$, including erasures:
Use the cap plus $M$, the maximum prime weight, and the whole budget.
These costs sum to $O(1)$, also for partial blocks.

For fixed $v$, replacing $P(p)^{iv}$ by
$\operatorname{lc}(P)^{iv}p^{iDv}$ costs $O_{P,v}(1)$ in the
unnormalized prime sum since $\log P(p)=D\log p+\log\operatorname{lc}(P)
+O_P(1/p)$ eventually. Put $\lambda=Dv$ and $E(x)=\vartheta(x)-x=o(x)$.
Partial summation against $x^{-1+i\lambda}$ gives the main integral
$\int_2^Z x^{-1+i\lambda}\,dx$ and error bounded by
$$
 O_\lambda\!\left(1+|E(Z)|/Z+\int_2^Z |E(x)|x^{-2}\,dx\right)
 =o_\lambda(\log Z).
$$
The integral is bounded for fixed nonzero $\lambda$, and is
$\log Z+O(1)$ at zero. Thus the normalized prime kernel tends to
$\mathbf1_{v=0}$, and its modulus is bounded uniformly in $v$ by
the normalized untwisted mass, which tends to one. This mass also
makes the normalized good-tail error $o(1)$, by cutting off any fixed
prefix. Finitely many ineligible primes do not change the limits.

Apply the kernel with $v=\gamma-t$ termwise by absolute summability.
Only $a_t$ survives, including at $t=0$; the square term has vanished
above $1/2$. An empty edge, including $\theta=1$, returns only zeros.
At an occupied point $z$, lines 143–157 recover $F_j$ as $-8d/r$
times the $\alpha^{j+1}$ coordinate of $dc(z)/K(z)$ over
$\mathbb Q(\zeta_d)$, and then the named orders as
$d^{-1}\sum_j\psi(g_j)F_j$. Injectivity makes absence unambiguous.
This proves (3) pointwise for every real $t$ without input ordinates.
None of the statistics decides the actual location of this family's
edge from finite data or decodes the critical line under this noise.
