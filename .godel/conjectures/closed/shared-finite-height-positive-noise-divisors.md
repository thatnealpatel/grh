---
evidence_revision: 6e777c9fccca8071842f8dbf9ac0940932090ab8
outcome: established
---

# Test positive-noise finite-height decoding for the shared stream

**Proposition:** Fix known integer $q\ge2$ and real $T\ge1$.
Use exactly the shared operator, labels, triangular kernel $K$,
and natural logs at the evidence revision. In particular,
$d=\varphi(q)$, $\ell$ is the least prime greater than $d$,
$\alpha=2^{1/\ell}$, and $R=10^6\lceil\log(2q)\rceil$.
For units $g_j$ in least-positive order starting at $g_0=1$,
$w(g_j)=1-R^{-1}(\tfrac12\mathbf1_{j=0}+\alpha^{j+1}/(8d))$
and $b_\chi=d^{-1}\sum_g w(g)\overline{\chi(g)}$. Set
$$
M=\lceil100\log(4q(T+2))\rceil,\quad A_0=8d^2R,\quad
n_F=\ell\varphi(d),\quad B_0=2A_0dM,
$$
$$
k_T=\frac{(\sqrt2-1)^2}{1/4+T^2},\quad
\mathrm{gap}=\frac{k_T}{A_0B_0^{n_F-1}},\quad
\eta=\min(1/100,\mathrm{gap}/4)>0,
$$
with $\varphi(1)=1$. Let $P$ be a known real polynomial of
degree $D\ge1$ and positive leading coefficient, and let
$\kappa>0$ be known. At eligible prime indices $p$ with
$P(p)\ge2$, the data give indexed real $y_p$ or an erasure,
with at most $O(N^{1-\kappa})$ erased or arbitrarily bad
entries in each late block $[N,2N)$. Along the good tail,
$$\limsup_{p\to\infty}\frac{|y_p-H(P(p))|}{\sqrt{P(p)}}\le\eta.$$
The bad set is unknown. The same data determine all exact
nontrivial off-line locations and named orders at all
heights, and the exact line locations and named orders at
$|\Im z|\le T$, including the center. Joint GRH remains
equivalent to $O(N^{1-k})$ raw reported negatives per
block, omitting erasures, for some $k>0$.

**Source and payoff:** The shared card at the evidence pin
uses $o(\sqrt X)$ good errors for its line selector. The
robust and triangular predecessor cards at
`6169a926323525cf7f02428e73cee7d63e68d694` and
`6596fa6e00f481978d7f2792eec2b3dde99a8a29` provide,
respectively, median strip peeling and the contour input.
The proposed stronger consumer replaces the convergent
selector by finite-codebook identification with a known
positive tolerance, without a supplied list of ordinates,
zero tables, separation, or a rightmost zero. No GRH,
simplicity, convergent noise average, finite work, or
positive all-height line radius is assumed or asserted.

**Discriminating test:** Calculate the exact Hadamard
difference at $2+it$ and $-1+it$, then use the functional
equation, an explicit digamma sum, and the absolutely
convergent Euler bound to test $m_\chi(1/2+it)\le M$,
including the pole-cancelling terms of $\xi$ and $q=2$.
In $\mathbb Q(\zeta_d,\alpha)$ test integrality, nonvanishing,
and the conjugate bounds for $A_0\sum_\chi b_\chi h_\chi$
for nonzero codeword differences. Check the resulting
uniform distance against $2\eta$, including absence.
Recompute medians after samplewise subtraction from the
original values and verify the coefficient of $\eta$ does
not accumulate. Test Mellin holomorphy in every next open
strip and label-preserving reflection. At each arbitrary
$t$ in the closed band, test whether a potentially
nonconvergent twisted logarithmic mean selects a unique
codeword by limsup distance, including $t=0$ after
subtracting the known square bias. Recheck the raw sign
counts against the same good-error bound and bad budget.

## Adjudication

The tolerance suffices. The changed proof decision is at lines
224–229 of `shared-triangular-sign-and-labelled-divisors.md` at
6e777c9fccca8071842f8dbf9ac0940932090ab8. Do not take the noisy
mean as the coefficient. Select a word whose distance from the
mean has limsup at most $\eta$. Here is why that word exists, is
unique, and includes the right answer even at an unlisted ordinate.

**How many orders must the selector allow?** For one primitive
inducer let $D_\chi$ denote the log derivative of its entire
completion, using $\xi$ for zeta. The functional equation and
conjugation give $D_\chi(s)=-\overline{D_\chi(1-\bar s)}$.
Difference the order-one Hadamard log derivatives at $2+it$ and
$-1+it$. Neither point is a zero of the completion. The constant
and the genus-one corrections cancel; the difference series
converges absolutely (its tail is $O_t(\sum_z |z|^{-2})$).
Taking real parts gives, for $z=\beta+i\gamma$ counted with order,
$$
2\Re D_\chi(2+it)=\sum_z\left(
\frac{2-\beta}{(2-\beta)^2+(t-\gamma)^2}+
\frac{1+\beta}{(1+\beta)^2+(t-\gamma)^2}\right).
$$
Each term is positive, and a line zero at $t$ contributes $4/3$
per order. At $2+it$ the left side is $\log(f/\pi)+\Re\psi(x+iy)
+2\Re(L'/L)(2+it)$, where $f\mid q$ is the conductor,
$x=(2+a)/2$ for parity $a$, and $y=t/2$. For zeta take $f=1$,
$a=0$, and add $2\Re(1/(2+it)+1/(1+it))\le3$ from $s(s-1)$.
In both cases $|L'/L|\le\sum_{n\ge2}(\log n)/n^2<2$ by the
$n=2$ term plus the integral from two to infinity.

In the digamma series, bound $-\gamma$ by zero and the first
$J=\lceil2+|y|\rceil$ terms by $\sum_{j<J}1/(j+1)\le1+\log J$.
For $j\ge J$ use
$$
\frac1{j+1}-\frac{j+x}{(j+x)^2+y^2}
\le \frac{x-1}{(j+1)^2}+\frac{y^2}{(j+1)^3}.
$$
Their sum is at most $(x-1)/J+y^2/(2J^2)<1$. Hence the line
order satisfies $(4/3)m_\chi\le 2\Re D_\chi(2+it)
<9+\log(4q(T+2))$ since $1\le x\le3/2$ and $J\le2(T+2)$.
This is more than sufficient for $m_\chi\le M$, including at
$t=0$, the two endpoints, and for the sole inducer at $q=2$.

**Separation for the shared weight.** Put $F=\mathbb Q(\zeta_d)$
and $E=F(\alpha)$. By Eisenstein, $\ell\mid[E:\mathbb Q]$;
as $[F:\mathbb Q]=\varphi(d)<\ell$, we get $\ell\mid[E:F]$.
The polynomial upper bound gives equality, so $[E:\mathbb Q]=n_F$.
For the difference $h$ of distinct words in the order box, put
$F_j=\sum_\chi \overline{\chi(g_j)}h_\chi$. The scaled difference
before multiplication by $K$ is the algebraic integer
$$
u=A_0\sum_\chi b_\chi h_\chi
=\sum_{j=0}^{d-1}(8dR-4d\mathbf1_{j=0}-\alpha^{j+1})F_j.
$$
If $u=0$, the independence of $1,\alpha,\ldots,\alpha^d$ over
$F$ forces all $F_j=0$, hence $h=0$ by Fourier inversion. For
any embedding $\sigma$, the character values still have modulus
one and $|\sigma(\alpha^{j+1})|<2$, so $|\sigma(w_j)|<2$ and
$|\sigma(b_\chi)|<2$. Since $|h_\chi|\le M$, all conjugates of
$u$ are bounded by $B_0$. The nonzero integer norm therefore
gives $|u|\ge B_0^{-(n_F-1)}$. This includes $F=\mathbb Q$,
$d=1$. For $z=1/2+it$ in the band, the reverse triangle inequality
gives $|K(z)|=|2^z-1|^2/|z|^2\ge k_T$. Thus two distinct order
vectors at the *same* $t$ give coefficients separated by at least
$\mathrm{gap}\ge4\eta$. No spacing between ordinates is used.

**What a median preserves.** Use the shared expansion at lines
109–131 of the evidence pin, including its known square term
$C\sqrt X$, grouped coefficients $c(z)=K(z)\sum b_\chi m_\chi(z)$,
and $\sum|c(z)|(1+|z|)^{1/2}<\infty$. Set $e=\min(\kappa/2,1/20)$,
$h_0=e/(2D)$. On the increasing branch with $P\ge2$, partition
each late dyadic block $[N,2N)$ into $\lfloor N^e\rfloor$ equal
cells. Packing the pinned short intervals of length $x^{9/10}$
(lines 185–194) loses at most $O(N^{9/10})$ length per cell and
at most one prime at its excluded endpoint. This gives uniformly
$\gg N^{1-e}/\log N$ primes, more than twice the whole bad budget.
A strict majority of nonerasures is good.

At $a=1$ start with the original data. At each cut $a$ subtract
all already recovered modes with $\Re z>a$ from the original
nonerasures at their own arguments. The sum is absolutely
convergent and real by conjugation. Take the lower residual
median $m_a$ on each image cell, zero if empty. For $U,X$ in
that cell, $|\log(U/X)|=O(N^{-e})=O(X^{-e/D})$ by $P'/P=O(1/N)$.
Write $S_a(X)=\sum_{\Re z\le a}c(z)X^z$. For nonnegative log
width $v\le1$, $|e^{vz}-1|\ll\min(1,v|z|)\le(v|z|)^{1/2}$;
ordering $U,X$ and using the half-moment bounds the variation of
$S_a$ by $O(X^{a-h_0})$. The square term varies by $o(\sqrt X)$.
The expansion remainder is $o(\sqrt X)$ and the good measurement
error is at most $(\eta+o(1))\sqrt X$, since $\sqrt{U/X}=1+o(1)$
uniformly. The majority places the median in the same interval:
$$
|m_a(X)-S_a(X)-C\sqrt X|
\le O(X^{a-h_0})+(\eta+o(1))\sqrt X.
$$
No noise radius is added from a previous median.

For $a>1/2$ this makes the Mellin transform of $m_a-S_a$
holomorphic on $\Re s>b=\max(1/2,a-h_0)$. A finite initial
segment contributes an entire term. Starting at an image endpoint
$A\ge2$, the data germ of $m_a$ on $\Re s>a$ equals that
discrepancy transform plus $\sum_{\Re z\le a} c(z)A^{z-s}/(s-z)$.
The sum converges normally off its locally finite poles by
absolute summability. Thus uniqueness of continuation fixes all
poles and residues in $b<\Re z\le a$; the discrepancy is not an
input. The same power-coordinate argument as above is injective
on *all* integer vectors, so every zero appears, and its exact
residue determines the labels without an off-line order cap.
Reset $a=b$, including intermediate lower edges in the next
strip. At most $\lceil D/e\rceil$ stages suffice. The same-label
reflection $z\mapsto1-\bar z$ supplies every strictly left order.

**Select, do not take a limit.** At $a=1/2$, strict left terms
after division by $\sqrt X$ tend to zero by domination by
$|c(z)|$. Thus $m_{1/2}/\sqrt X-C$ equals the absolutely
summable series $\sum_\gamma c(1/2+i\gamma)X^{i\gamma}$ plus a
remainder with limsup absolute value at most $\eta$. For *every*
real $|t|\le T$, average this observable times $X^{-it}$ on
$[A,V]$ with measure $dX/(X\log(V/A))$, obtaining $A_t(V)$.
On the series alone each unmatched frequency has mean tending
to zero by integration; the matched one has mean one. All such
means have modulus at most one, so the limit passes through the
series. For the remainder a fixed initial segment costs $o(1)$,
and the unit-modulus twist does not enlarge the tail bound. Hence
$$
\limsup_{V\to\infty}|A_t(V)-c(1/2+it)|\le\eta,
$$
using $c=0$ at absence. The true order vector is in the box, and
any other word has liminf distance at least $\mathrm{gap}-\eta>\eta$.
Choosing the unique vector passing the limsup test therefore
defines the divisor on the entire band by its nonzero entries.
This is pointwise identification for all $t$, not uniform
convergence or a search restricted to supplied ordinates. Removing
$C$ handles $t=0$.

For example, take no bad indices and add $(-1)^j\eta\sqrt{P(p)}$
on $2^{n_j}\le p<2^{n_{j+1}}$, with $n_j=2^{2^j}$. On each such
range every median cell has the same noise sign. The comparison
at the final cut holds there with square coefficient
$C+(-1)^j\eta$ and error $o(\sqrt X)$. At the image endpoints
$V=P(2^{n_{j+1}})$ the last range occupies a fraction tending to
one of the logarithmic integration length, since $n_j/n_{j+1}\to0$.
Thus the center means have subsequential limits $c(1/2)\pm\eta$.
Even this admissible noise cannot change the selected word.

**Raw signs need no new selector.** Under joint GRH the margin
$H(X)>\sqrt X/25$ exceeds the eventual good error. Off joint GRH,
lines 159–194 of the shared pin apply to $H$, not the reports:
For each proposed $k>0$ they give arbitrarily late excursions
below $-P(x)^b$ for fixed $b>1/2$, with $\gg N^{1-e'}/\log N$
prime indices in one block for some $0<e'<\min(k,\kappa,1/20)$.
The good error is negligible there. Subtracting even the whole
bad budget leaves a count whose ratio to $N^{1-k}$ is unbounded.
This preserves both directions for raw reported negatives.

The gain is a specified positive deterministic noise floor for
each fixed band. It is not an optimal radius, a positive radius
uniform in height, or a finite-data or stable continuation result.
