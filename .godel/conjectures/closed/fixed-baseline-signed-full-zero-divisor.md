---
evidence_revision: 645200463f434bd285a45f71442650202427aa5b
outcome: established
---

# Recover the noncentral zero divisor from signed samples

**Proposition to test:** For every fixed choice of integers $q\ge2$,
$m\ge8$, and $B\ge1$, the constants $q,m,B$ and the exact sequence
$H(n^B)$ for integers $n\ge1$ determine all distinct nontrivial zeros
$\rho\ne1/2$ of the primitive inducers of characters modulo $q$,
including zeta. Recover $m_\zeta(\rho)$ and the total multiplicity
$S(\rho)=\sum_{\chi\bmod q}m_{\chi^*}(\rho)$, not individual
characters or nonprincipal central multiplicities. Use at most
$\lceil B/2\rceil$ successive meromorphic strip continuations and
one critical-line logarithmic averaging step, without a line,
spacing, or rightmost-zero attainment hypothesis. This is exact
analytic determination, not a finite-data or stable algorithm.

**Source and payoff:** Put $M=10^{15}$, $h_m=\mathbf1_{[0,\log 2]}^{*m}$,
$k_m=4h_m^{(4)}-5h_m''+h_m$, and $v_p=\log(p/X)$. Use
$$H(X)=MX-\sum_{p\nmid q}(\log p)
  [Mh_m(v_p)+\mathbf1_{p\equiv1\bmod q}k_m(v_p)].$$
The [edge card](../closed/fixed-baseline-signed-edge-ordinates.md)
at the evidence revision supplies the full signed expansion, square
bias, visibility of grouped coefficients, and edge harmonic selector.
The [window card](../closed/fixed-baseline-variable-order-prime-density.md)
at `f5fbeb09e9b972565848e25ac295f3341a537afd` supplies the windows
and the continuous-deficit residues. The extension would recover
interior divisors even when no zero lies at the supremum, which
neither the unsigned envelope nor the edge selector alone does.

**Discriminating test:** With $a=1$ initially, let $r_n$ be the
samples minus all terms $c(\rho)n^{B\rho}$ already recovered to
the right of $a$. For $b=\max(1/2,a-1/B)$, form
$$D_a(s)=B\sum_{n\ge1}r_n n^{-1-Bs},\qquad \Re s>a.$$
Test that it continues to $\Re s>b$ with precisely the remaining
zero poles in $b<\Re s\le a$, and residue $c(\rho)$ at each.
Use the unit-cell sum-minus-integral for each power: Check its
holomorphic extension and uniform height bound on compacts, the
first absolute coefficient moment at $m=8$, and normal convergence
of the pole sum off its locally finite pole set. Check visibility
and separation of the two multiplicities even on $\Im Q=0$ and
at real zeros, with $Q(s)=(4s^2-1)(s^2-1)$. Check that uniqueness
of the continuation and absolute convergence of the next
subtraction avoid any input of zero locations. Iterate with
$a=b$, including upper boundaries and deferring the lower ones;
check $B=1$ and odd $B$. At $a=1/2$, test domination for the
strictly left terms without a gap, and harmonic selection on
$n^B$ with the correct square bias. Check that reflection
preserves the two multiplicities. Only the residual in each
round is asserted to continue across that round's strip.

## Adjudication

**The samples determine the stated divisor.** The induction is on
fixed strip boundaries, not on the real parts of individual zeros.
In particular it never needs to select a rightmost remaining zero.

At the edge pin, lines 63–105 and 107–122 give, with $d=\varphi(q)$,
$\Phi(z)=(2^z-1)/z$, and $C=(M/2)\Phi(1/2)^m$,
$$H(n^B)=\sum_\rho c(\rho)n^{B\rho}+R_n,\qquad
 c(\rho)=\Phi(\rho)^m[Mm_\zeta(\rho)+Q(\rho)S(\rho)/d],\qquad
 R_n=Cn^{B/2}+o(n^{B/2}).$$
The sum is over distinct points; the unit-height counts include
multiplicity. Indeed $m_\zeta\le S$, $Q$ is quartic, and
$\Phi(\rho)\ll(1+|\Im\rho|)^{-1}$ in the critical strip. Thus on
$j\le|\Im\rho|<j+1$ the sum of $(1+|\rho|)|c(\rho)|$ is
$O_{q,m}((1+j)^{5-m}\log(2+j))$, summable even at $m=8$.

### One residual strip

Initially all nontrivial zeros have $\beta=\Re\rho\le1$. Suppose
only terms with $\beta\le a$ remain along with $R_n$. For
$\Re s>a$ absolute convergence allows exchange of the two sums:
The absolute zero contribution is bounded by
$B\sum|c(\rho)|\sum_n n^{-1-B(\Re s-a)}$. The $R_n$ series is
holomorphic for $\Re s>1/2$ by normal convergence.

Put $w=1+B(s-\rho)$. On each cell the fundamental theorem of
calculus gives the exact identity
$$n^{-w}-\int_n^{n+1}x^{-w}\,dx
  =w\int_n^{n+1}(n+1-x)x^{-w-1}\,dx.$$
Write $E_\rho$ for $B$ times the sum of these differences. The
absolute tail from cell $L\ge1$ on is bounded by
$B|w|L^{-\Re w}/\Re w$ when $\Re w>0$. On a compact $K$ of
$\Re s>b=\max(1/2,a-1/B)$, one has
$\Re w\ge1+B(\min_K\Re s-a)>0$ and $|w|\ll_{B,K}1+|\rho|$.
The cells are entire in $s$. The tail bound proves holomorphy of
$E_\rho$ and, with $L=1$, normal convergence of
$\sum c(\rho)E_\rho$ by the first moment. On the initial half-plane
$B\int_1^\infty x^{-w}dx=B/(w-1)=1/(s-\rho)$. Therefore the
continuation of $D_a$ is the $R_n$ series plus
$$\sum_{\beta\le a} c(\rho)E_\rho(s)
   +\sum_{\beta\le a}\frac{c(\rho)}{s-\rho}.$$
The latter sum converges normally off the zero set: On a compact
only finitely many denominators can have modulus less than one
anywhere, by local finiteness. At an isolated point only its own
summand can be singular. Thus there are no extra poles, and the
residue at each visible point is $c(\rho)$, without a factor $1/B$.

### No invisible strip zeros

The decoding at edge-pin lines 141–156 depends on the real part
$x\in[1/2,1)$, not on its being extremal. For $z=x+it$ divide the
coefficient by $\Phi(z)^m\ne0$ and call the result $U$. If
$\Im Q(z)\ne0$, then $S=d\Im U/\Im Q(z)$ and
$m_\zeta=(U-Q(z)S/d)/M$. Otherwise, at $t\ne0$ the identity
$\Im Q(z)=2xt[8(x^2-t^2)-5]$ gives $t^2=x^2-5/8$. Here
$|z-1|^2=2x(x-1)+3/8\le3/8$ and $|z|/x<\sqrt2$. Euler summation
bounds $|\zeta(z)-1/(z-1)-1/2|\le|z|/(2x)$, so
$|(z-1)\zeta(z)-1|\le\sqrt{3/8}(1+\sqrt2)/2<1$. Hence
$m_\zeta=0$ and $S=dU/Q(z)$, since $Q$ has only real roots.
For $1/2<x<1$, the positive paired eta series excludes real zeta
zeros and $Q(x)<0$, giving the same division. There are no zeros
on the line at one. In each exposed strip $S>0$ at a family zero,
so the decoding excludes a vanishing residue even at a shared zero.

### Update from data and finish

The samples fix the initial germ. Uniqueness of meromorphic
continuation on the connected half-plane fixes the poles and
residues of the current germ. The zero expansion proves that these
are the required data; it is not a list needed to form the germ.
Subtract the terms read from the poles in $b<\beta\le a$. For each
$n$ their absolute sum is at most $n^{Ba}\sum|c(\rho)|$. This leaves
exactly the next residual, with the same $R_n$. After $j$ strips the
boundary is $\max(1/2,1-j/B)$, reaching $1/2$ at $j=\lceil B/2\rceil$.
An intermediate cut is included as the next upper boundary; for
$B=1$ the single cut reaches the line, and for odd $B$ the last
strip has width $1/(2B)$.

Now divide the residual by $n^{B/2}$. Strictly left terms tend to
zero in sum by domination by $|c(\rho)|$, without a uniform gap.
For every real $t$, twist by $n^{-iBt}$ and take the harmonic sum
to $N$ divided by $\log N$. A line term contributes the selector
for $u=B(\Im\rho-t)$: The sum of $n^{-1+iu}$ differs from its
integral by $O(1+|u|)$ by the unit-cell bound, and the integral is
bounded for fixed $u\ne0$. At $u=0$ the normalized limit is one.
The normalized sums are bounded independently of $u$ by the
normalized harmonic sum, permitting passage through the line
series. The normalized mean of the twisted $o(1)$ tends to zero.
Thus for $t\ne0$ the result is $c(1/2+it)$ at a family zero and
zero otherwise. The same decoding recovers both multiplicities.
At $t=0$
only $C$ survives by eta nonvanishing and $Q(1/2)=0$.

In the open critical strip the completed functional equation sends
a zero of a primitive character at $z$ to one of its conjugate at
$1-z$ with the same order. Complex conjugation takes this back to
the original character at $1-\overline z$; the completion factors
are regular and nonvanishing there. This preserves each order,
including zeta's, and hence the aggregate. Reflection supplies
the remaining left half. The finite strip count uses infinite exact
data and can involve infinite subtractions. It gives no finite-work
or stability conclusion, no individual character labels, and no
central nonprincipal multiplicity. The grids proved here are $n^B$.
