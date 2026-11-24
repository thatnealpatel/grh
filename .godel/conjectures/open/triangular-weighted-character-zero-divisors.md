---
evidence_revision: c321e4c860a2734028529d53aaa3d0c9625ce6a1
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
