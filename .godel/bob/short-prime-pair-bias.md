# A principal peak forces signed correlations at many prime gaps

Isolating $\log n=\log X+O(1)$ on the Euler line is [a linear reweighting](prime-band-phase-controls.md). There is a different test on the **same band**: Square a short additive box sum *before* averaging its location. At the named height a putative peak forces a positive bias for a positive proportion of shifts of order $\log X$. The bias persists on a height interval of length comparable to $X/\log X$. This concerns ratios of distinct primes, not higher harmonics of one prime. It is a necessary condition, not an upper bound for the peak.

Write $t=2q^{3/5}$, $X=X(t)=(3\log(t/2))^2$, $D=\log X$, $I=[e^{-8}X,X]$, and $z(x)=\log(X/x)$. Define

$$ S_X(t)=X^{-1}\sum_{p<X}\log p\,z(p)p^{it},\qquad C_{d,X}(u)=X^{-1}\!\sum_{p,p+d\,\in I\ {\rm prime}}z(p)\log p\log(p+d)\cos\!\left(u\log(1+d/p)\right). $$

**Claim.** Along any sequence $t\to\infty$ with $|S_X(t)|\ge 47/81-o(1)$ there are absolute constants $c,b,\kappa>0$ and $M<\infty$ such that eventually at least $\kappa D$ distinct even shifts $cD\le d\le(4-c)D$ satisfy

$$ C_{d,X}(0)\le M,\qquad C_{d,X}(t)>1/8,\qquad C_{d,X(u)}(u)>1/16\quad (|u-t|\le bX/D). \tag{1} $$

The shifts can depend on the peak but are the **same shifts throughout its interval**. In particular a concentration on just a few shifts with large singular series cannot explain the peak. The implication also holds at continuous center heights with this same $X(t)$; it uses no strip hypothesis. A bound on $C$ averaged over all heights need not exclude the stated intervals.

## Subtract the diagonal at mean-prime-gap scale

Put $H=CD$ for fixed $C>0$, $s=47/81$, $e_0=9e^{-8}$, and $m=1-e_0$. Use the measure $d\mu=1_I(x)z(x)\,dx/X$ of mass $m$, and put

$$ F(x)=H^{-1}\sum_{p\in I\cap(x,x+H]}\log p\,p^{it}. $$

PNT and partial summation give full positive ramp mass $1+o(1)$ and clipped mass $m+o(1)$ (the limiting integrals are $\int_0^1\log(1/v)dv$ and its restriction to $[e^{-8},1]$). Thus the clipped sum has modulus at least $s-e_0-o(1)$. It differs from $\int F\,d\mu$ by $o(1)$ uniformly in the phases. Indeed the overlap for prime $p$ is $I\cap[p-H,p)$; away from the clipped endpoint $z(x)=z(p)+O(H/X)$ there. The $O(H+1)$ possible integers at the lower endpoint cost $O(HD/X)$. Cauchy gives $\int|F|^2d\mu\ge(s-e_0)^2/m-o(1)$.

For $p\le p'=p+d$ the exact overlap integral in the square is $(XH^2)^{-1}\int_{I\cap[p'-H,p)}z(x)dx$ for $d<H$, and zero otherwise. Replace its numerator integral by $(H-d)z(p)$. Off the lower boundary the error per integral is $O(H^2/X)$ and there are $O(XH)$ integer pairs. At the boundary at most $O(H^2)$ pairs cost $O(H)$ per integral. After multiplication by at most $D^2/(XH^2)$ the total error is $O(HD^2/X)=o(1)$, even with absolute values. In particular no approximation to the phase by a Taylor polynomial at height $t$ is involved. The diagonal is $(XH)^{-1}\sum_{p\in I}z(p)\log^2p=m/C+o(1)$ since $\log p=D+O(1)$ there. Hence

$$ B_X(t):=\frac2H\sum_{1\le d<H}(1-d/H)C_{d,X}(t)\ \ge\ \frac{(s-e_0)^2}{m}-\frac mC-o(1). \tag{2} $$

Even $C=3$ makes the right side positive (limiting constant $>0.0018$); take $C=4$ for a constant $>0.0849$. For rational checks one may enclose $e^8$ between $\sum_{j=0}^{34}8^j/j!$ and this sum plus $(8^{35}/35!)/(1-8/36)$. At the *frozen* cutoff, taking all phases one in the same Cauchy argument gives $B_X(0)\ge m(1-1/C)-o(1)$. Thus even exact unsigned prime-pair counts used termwise to bound (2) cannot establish the requisite cancellation.

## Extract the shifts and keep the height interval

Set $A_d=C_{d,X}(0)$. We need only $\sum_{d<H}A_d^2\ll H$, not a Hardy–Littlewood asymptotic or an explicit sieve constant. For even $d$ the upper-bound sieve for two primes gives $A_d\ll\mathfrak S_d$, uniformly for $d<H$: The two log weights cost at most $D^2$, $z(p)\le8$, and both primes exceed $X^\delta$ for any fixed small $\delta>0$. See the uniform **pair** bound (4.2), not just the successor-gap count (4.1), in Friedlander, [*When Euler met Brun*](https://arxiv.org/abs/2305.11530). For odd $d$ there are no such pairs. For even $d$, the Euler product (3.1) there gives $\mathfrak S_d\ll\prod_{\ell\mid d,\,\ell>2}(1+1/(\ell-2))$ over primes $\ell$. To average its square expand the product with factors $1+v_\ell=(1+1/(\ell-2))^2$. An average over multiples of each squarefree divisor bounds the mean by $\prod_{\ell>2}(1+v_\ell/\ell)<\infty$.

Let $w_d=2(1-d/H)/H$ for $1\le d<H$. The **even** shifts have $\sum_{2\mid d}w_d=1/2+o(1)$. Those with $C_{d,X}(t)\le1/8$ therefore contribute at most $1/16+o(1)$ in total (odd terms vanish). Since $|C_{d,X}(t)|\le A_d$, the absolute cost of $A_d>M$ is $O(1/M)$ by the second moment; that of the two end strips of length $cD$ is $O(\sqrt c)+o(1)$ by Cauchy. Choose $M$ large and $c>0$ small to spend less than half of $0.0849-1/16$. Each remaining shift costs at most $2M/H$ in (2), so at least $\kappa D$ meet the first two tests in (1).

For each selected $d$, the frozen sum has $|\partial_u C_{d,X}(u)|\le A_d e^8d/X\le 4Me^8 D/X$. Thus for $b\le1/(256Me^8)$ it stays above $1/8-1/64$ throughout the interval. To unfreeze the cutoff, $X'(v)=18\log(v/2)/v$ gives $\sup_{|u-t|\le bX/D}|X(u)-X|=o(1)$. Moving the endpoints of $I$ crosses $O(1)$ integers; for fixed $d$ each affects at most two pairs, costing $O(D^2/X)$. Common pairs have a change $O(|X(u)-X|/X^2)$ in $z(p)/X$, times at most $O(XD^2)$ in absolute log weights. These errors are $o(1)$ uniformly in $d$ and $u$, which gives (1). This stability is for the **pair statistic**. It does not imply that nearby $u$ are themselves ramp peaks or that any conductor fails an endpoint test.

**Decision.** It suffices to find, in *each* such neighborhood of a sufficiently large named height, one $u$ with only $o(D)$ even shifts in the specified range above $1/16$ at $X(u)$. A sequence approaching the threshold would contradict (1). The cited sieve theorem has the right shift range but controls only the unsigned masses. The [free multiplicative and frozen-cutoff controls](prime-band-phase-controls.md) already have a ramp peak, so the box argument also forces signed pairs in those controls, using their own phases. What is missing is cancellation of the actual ratio phases at the coupled height. A proof need not give cancellation for every shift, and a bound outside an exceptional set of center heights alone is not enough.

**Follow-on after Work.** Before testing the common ordinate, read the [handoff check](prime-pair-handoff-review.md): Every center-selected pair already clears the threshold on that entire short interval by the derivative estimate above. A [normalized four-prime test](prime-rectangle-persistence.md) instead persists on a longer interval of radius $b_2X^2/D^3$. Its signed upper bound at the coupled heights remains open; smoothing over the guaranteed interval alone cannot give appreciable phase cancellation.
