---
evidence_revision: c321e4c860a2734028529d53aaa3d0c9625ce6a1
outcome: established
---

# Recover each character divisor from one triangular prime sum

**Proposition to test:** Fix integers $q\ge2$ and $B\ge1$.
Order $G=(\mathbb Z/q\mathbb Z)^*$ as $g_0,\ldots,g_{d-1}$
by least positive residue, with $d=\varphi(q)$. Let $\ell$
be the least prime greater than $d$, $\alpha=2^{1/\ell}$,
and $w(g_j)=\alpha^j$. Put $A=\log 2$, let
$h=\mathbf1_{[0,A]}*\mathbf1_{[0,A]}$ be ordinary convolution,
and write $\bar w=d^{-1}\sum_g w(g)$. Define the one scalar
$$H(X)=\bar w X-\sum_{p\nmid q}(\log p)w(p\bmod q)
 h(\log(p/X)).$$
The integers $q,B$ and the exact signed samples $H(n^B)$,
$n\ge1$, determine the locations and orders of every
nontrivial zero of each named character's primitive inducer,
including all orders at $1/2$. Use at most $\lceil B/2\rceil$
successive meromorphic strip continuations and one harmonic
averaging stage for the whole critical line. No GRH,
simplicity, zero independence, or attainment is assumed.

**Source and payoff:** The [full-divisor card](../closed/fixed-baseline-signed-full-zero-divisor.md)
at the evidence revision peels residual strips for a
higher-order window but sees only two aggregate orders,
and not nonprincipal central orders. The [edge card](../closed/fixed-baseline-signed-edge-ordinates.md)
at `645200463f434bd285a45f71442650202427aa5b` supplies the
higher-order full contour shift and harmonic selector. This
is a new use with one bounded positive class weight and the
same order-two triangular window in every class. It seeks
exact determination, not sign, stability, or finite work.

**Discriminating test:** Expand in Dirichlet characters with
$b_\chi=d^{-1}\sum_g w(g)\overline{\chi(g)}$. Restore powers
with $w(p^k)$ and pass to primitive inducers. At order two,
check inversion at the knots and shift to $\Re s=-1/2$,
including selected-height bounds, residue signs, and
absolute moments of every order $v<1$. With
$\Phi(s)=(2^s-1)/s$, test the square bias
$C=\Phi(1/2)^2\sum_g w(g^2)/(2d)$ by fixed-class PNT.

For a residual with real parts bounded by $a$, test that
$B\sum_n r_n n^{-1-Bs}$ continues to
$\Re s>b=\max(1/2,a-1/B)$ with exactly the intended poles.
For each $z$, split sum-minus-integral cells at
$L=\lceil1+|1+B(s-z)|\rceil$ and check a locally uniform
sublinear bound in $|z|$, not a first-moment assumption.
Check normal convergence and subtraction from known residues,
including infinite strips and zeros on an intermediate cut.
On the line, test harmonic selection with the known $C$
subtracted at zero frequency, and label-preserving reflection.

Finally divide each grouped coefficient by $\Phi(z)^2$.
Test whether $1,\alpha,\ldots,\alpha^{d-1}$ are independent
over $\mathbb Q(\zeta_d)$ by the degree calculation and
whether character inversion then recovers every order,
including at shared points and at the center. Check the
case $d=1$ and the absence of a kernel at every zero.

## Adjudication

**One scalar suffices.** The first absolute moment at lines 65–91 of
`fixed-baseline-signed-full-zero-divisor.md` at the evidence pin is not
an input here. The triangle gives all moments strictly below one, and
on each compact of a residual strip one such moment suffices.

### What the triangular prime sum measures

Write $K(s)=\int h(v)e^{sv}dv=\Phi(s)^2$ by convolution, with
$\Phi(0)=\log 2$. The triangle is continuous, including at $0,A,2A$,
so Fourier inversion of $e^{2v}h(v)$ with its integrable transform
returns the actual value at every knot. In fact $K(1)=1$, and on the
closed strip from $-1/2$ to $2$, $K(\sigma+it)\ll(1+|t|)^{-2}$.

Complete the prime sum using $(\log p)w(p^k\bmod q)$ at each $p^k$,
$p\nmid q$. Character inversion gives a sum of von Mangoldt sums
with coefficients $b_\chi$ as above. Replacing $\chi$ by $\chi^*$
changes the total by $O_q(1)$: For each omitted prime dividing $q$,
at most $1+\log(4)/\log p$ exponents have $X\le p^k\le4X$. The
primitive sum is the inverse integral of $X^sK(s)(-L'/L)(s,\chi^*)$
on $\Re s=2$, by absolute convergence of the Euler series there.

Here is why the shift at edge-pin lines 79–105 still works. The
order-one Hadamard product for the entire completed function (use
$\xi$ for zeta), evaluated via its real logarithmic derivative at
$2+iT$, gives $\sum_z(1+(T-\Im z)^2)^{-1}\ll_q\log(2+|T|)$ with
orders counted. Indeed $\Re(2+iT-z)^{-1}$ dominates a fixed multiple
of the summand, the real parts of the genus-one corrections $1/z$
are absolutely summable since $0<\Re z<1$, and the Euler series and
Stirling bound the derivative. This gives a unit-height count. In
positive and negative unit intervals tending to infinity, exclude
neighborhoods of radius $c_q/\log(2+|T|)$ of the nearby family
ordinates. Their total length is less than one for small $c_q$.
At a remaining height, compare the completed derivative across the
horizontal segment with its value at $2+iT$. For $|T-\Im z|>1$ the
difference per zero is $O((T-\Im z)^{-2})$; the other
$O_q(\log(2+|T|))$ terms cost $O_q(\log(2+|T|))$ each. Removing the
completion leaves $L'/L=O_q(\log^2(2+|T|))$. The horizontals thus
vanish even with only quadratic decay, for fixed $X$. On $\Re s=-1/2$
the functional equation, Stirling, and the Euler series at $1-s$
give $L'/L\ll_q\log(2+|t|)$; there is no gamma pole on this line.
The left integral is $O_q(X^{-1/2})$ for $X\ge1$.

Only the principal inducer has the pole at one, giving
$b_{\rm princ}K(1)X=\bar w X$. A nontrivial zero gives minus its
order times $K(z)X^z$ before the character weighting. A trivial zero
at zero contributes $O_q(1)$. Subtracting the full sum in $H$ cancels
the pole, reverses the zero sign, and requires adding the powers back.
For squares, put $T=\sqrt X$. Partial summation with the fixed-class
prime number theorem for $\sum\log p$ gives in class $g$ the unweighted
square sum $T d^{-1}\int_1^2 h(2\log u)du+o(T)$, since the test
function has bounded variation. With $v=2\log u$ the integral is
$K(1/2)/2$, and the multiplier in this class is $w(g^2)$. Higher
powers cost $O_q(X^{1/3}\log^2(2X))$ since $p\le(4X)^{1/3}$ and
$k\ll\log(2X)$. Consequently, with $m_\chi(z)$ the order for $\chi^*$,
$$H(X)=\sum_z c(z)X^z+C\sqrt X+o_q(\sqrt X),\qquad
c(z)=K(z)\sum_\chi b_\chi m_\chi(z),\quad
C=\frac{K(1/2)}{2d}\sum_g w(g^2).$$
The sum groups distinct points. On $j\le|\Im z|<j+1$, the contribution
to $\sum |c(z)|(1+|z|)^v$ is $O_{q,v}((1+j)^{v-2}\log(2+j))$
by the unit count. This proves absolute summability for every $v<1$.

### No label collision or hidden pole

Put $F=\mathbb Q(\zeta_d)$, containing every character value. Since
$Y^\ell-2$ is Eisenstein at two, $\ell$ divides $[F(\alpha):\mathbb Q]$.
It does not divide $[F:\mathbb Q]=\varphi(d)\le d<\ell$, also for
$d=1$. Hence $[F(\alpha):F]=\ell$, using the polynomial upper bound.
Since $K(z)\ne0$ for $0<\Re z<1$, the unique coefficients of
$1,\alpha,\ldots,\alpha^{d-1}$ over $F$ in $d c(z)/K(z)$ are
$$F_j=\sum_\chi\overline{\chi(g_j)}m_\chi(z),\qquad
m_\psi(z)=\frac1d\sum_j\psi(g_j)F_j.$$
The last equality is character orthogonality. Thus vanishing means
all orders vanish, and one exact scalar distinguishes even two vectors
of shared orders. This decoding is uniqueness in a number field,
not rounding in the complex plane. All weights are in $[1,2)$.

### Why peeling works without the first moment

Start with $a=1$. Let $r_n$ be the samples minus the terms recovered
with $\Re z>a$; the untouched remainder is $R_n=Cn^{B/2}+o(n^{B/2})$.
For $\Re s>a$ the germ $D_a=B\sum_n r_n n^{-1-Bs}$ permits exchange
of the sample and zero sums by $\sum|c(z)|<\infty$. The $R_n$ series
is holomorphic for $\Re s>1/2$. Put $b=\max(1/2,a-1/B)$ and
$u=1+B(s-z)$. On a compact of $\Re s>b$, $\sigma=\Re u\ge\delta>0$
uniformly in the remaining zeros. Let $E_z$ be $B$ times the sum of
the differences between $n^{-u}$ and $\int_n^{n+1}x^{-u}dx$. Each
difference equals $u\int_n^{n+1}(n+1-x)x^{-u-1}dx$. The tail from
$L$ is bounded by $B|u|L^{-\sigma}/\sigma$, proving locally uniform
convergence for each fixed $z$, hence holomorphy.

For a bound summable in $z$, choose $L=\lceil1+|u|\rceil$ and
$e=\min(\delta/2,1/2)$. For $n<L$, the absolute sum of the terms and
integrals separately is $O_B(\sum_{n<L}n^{-e})=O_B(L^{1-e})$.
The tail is at most $(B/\delta)L^{1-e}$. Since $L\ll1+|z|$ on the
compact, the moment with $v=1-e$ now gives normal convergence of
$\sum c(z)E_z$. On the initial half-plane the integral from one to
infinity times $B$ is $B/(u-1)=1/(s-z)$. Thus the continuation is
the remainder series plus $\sum_{\Re z\le a} c(z)(E_z+1/(s-z))$.
The pole sum is normal off its locally finite set, since only finitely
many points are within distance one of a compact. Each exposed zero
has residue exactly $c(z)\ne0$.

The germ from the data uniquely fixes these poles and residues. For
each $n$, subtracting them as powers in $b<\Re z\le a$ costs at most
$n^{Ba}\sum|c(z)|$ in absolute mass. This defines the next residual
even for infinitely many poles, without supplying any zero list.
After $j$ strips the upper bound is $\max(1/2,1-j/B)$, so at most
$\lceil B/2\rceil$ are needed. Intermediate cuts belong to the next
strip; the final cut itself is reserved for averaging. This continues
a new germ each round, not the original series through every strip.

### Reading the center rather than discarding it

Divide the last residual by $n^{B/2}$. The strictly left terms tend
to zero in sum by domination by $|c(z)|$. For each real $t$, twist
by $n^{-iBt}$ and take $\sum_{n\le N}(\cdot)/n$ divided by $\log N$.
For fixed $v=B(\Im z-t)$ the sum of $n^{-1+iv}$ differs from its
integral from one to $N$ by $O(1+|v|)$ by the cell derivative bound.
The integral is bounded for $v\ne0$ and is $\log N$ at zero. All
normalized sums are bounded by the normalized harmonic sum for
$N\ge2$, so their limits pass through the absolutely summable line
series. The twisted $o(1)$ has vanishing mean. The result is
$c(1/2+it)+C\mathbf1_{t=0}$, taking $c=0$ at nonzeros. Subtract the
known $C$ at zero, and apply the same label inversion. These are
pointwise limits for all frequencies in one stage. At $t\ne0$ the
twist can return a complex coefficient from real samples. Finally the
primitive functional equation sends $z$ to $1-z$ for the conjugate
label, and conjugation sends it to $1-\bar z$ for the original label
with the same order. This fills the strictly left half. Neither a gap
nor attainment of a greatest real part was used. The result is exact
infinite-data determination, not a stable or finite-work algorithm.
