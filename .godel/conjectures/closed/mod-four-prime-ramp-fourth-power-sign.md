---
evidence_revision: dca062832345d6f827769b6a1af9b923d21e3b0e
outcome: established
---

# Fourth-power samples of the mod-four prime ramp

Let $\chi_4$ be the primitive real character modulo $4$, and
for real $X\ge1$ let

$$P(X)=\sum_{p<X}\chi_4(p)\log p\,\log(X/p).$$

**Proposition to test:** There exists an integer $N\ge1$ such
that $P(n^4)\le0$ for every integer $n\ge N$ if and only if
every nontrivial zero of $L(s,\chi_4)$ has real part $1/2$.
The ramp is unnormalized, unmodulated, and over primes only,
with natural logarithms. No sign between samples is assumed.

**Source and payoff:** This is a proposed weakening of the
sampling premise of the [all-cutoff sign criterion](../closed/mod-four-prime-ramp-eventual-sign.md).
The ramp comes from Bob's [equation (1) and signed-pair use](../../bob/fixed-strip-endpoints.md#the-product-mean-at-the-original-endpoint-weight)
at `bbca37033019090f6f40e6223b5054d382c9d789`, taking
$(d_i,d_j)=(1,-4)$ at an odd base conductor and $v=0$. Neither
source asserts the sampled proposition. A transfer at this
mesh would separate the cost of chaining local intervals from
the arithmetic needed to establish the sampled signs.

**Discriminating test:** In $t=\log X$, subtract the chord of
the actual signed hinge sum on each adjacent sample cell.
Check which hinges remain, including equality at the cell
ends, and bound the one-sided deficit by counting integers,
without prime cancellation. Test whether the resulting
upper envelope is $O(\sqrt X\log^A(2X))$ for a fixed $A$.
If so, add a dominating envelope to $-P$ and test Landau on
that nonnegative tail, not on $-P$ itself. Check on
$\Re s>1/2$ the envelope transform, the prime-power
correction, real-axis regularity, zero-pole noncancellation,
and reflection. For the reverse direction check whether the
all-cutoff result applies with identical weights and cutoffs.

## Adjudication

**The equivalence holds.** The sampled signs give an upper envelope with a logarithmic loss at square-root scale. They need not give a sign inside a cell by interpolation. It is the difference between the envelope and the ramp that has a nonnegative Mellin tail.

### The cell calculation

Fix $n\ge1$, $A=n^4$, $B=(n+1)^4$, $a=\log A$, and $h=\log(B/A)$. Put $x=\log(X/A)/h$ for $A\le X\le B$, and $C=(1-x)P(A)+xP(B)$. Each prime contributes $\chi_4(p)\log p$ times the hinge $(\log X-\log p)_+$. For $p\le A$ the hinge is affine on the closed cell, and for $p\ge B$ it is identically zero there. Thus both endpoint equalities are covered; $p=X$ contributes zero under the strict cutoff as well.

For $A<p<B$ put $y=\log(p/A)/h$. The unsigned hinge's chord minus its value is $hK(x,y)$, where

$$K(x,y)=x(1-y)-(x-y)_+=\begin{cases}x(1-y),&x\le y,\\y(1-x),&y\le x.\end{cases}$$

In either branch $0\le K\le x(1-x)\le1/4$. Hence $P(X)-C=-h\sum_{A<p<B}\chi_4(p)(\log p)K(x,y)$. Only primes with $\chi_4(p)=-1$ can lift the ramp above its chord. Even counting **all integers** in the open cell gives the absolute error bound

$$|P(X)-C|\le \tfrac14 h(B-A)\log B\le 15n^2\log B\le E(X),\qquad E(X)=15\sqrt X\log(16X).$$

Indeed $h=4\log(1+1/n)\le4/n$, $B-A=4n^3+6n^2+4n+1\le15n^3$, and $B\le16X$. A bound on the raw slope would charge primes before the cell; here their cost is exactly zero. The cells cover the tail, and each chord uses the actual endpoint values, so the errors do not add from cell to cell. If the sample signs hold from $N$ on, then $C\le0$ and $P(X)\le E(X)$ for every $X\ge X_0=N^4$. This gives neither an absolute bound on $P$ nor its interior sign by the cell estimate alone.

### From the envelope to zeros

Set $F=E-P$ and $L=L(s,\chi_4)$. For $\Re s>1$ the Euler product and the single-hinge transform $p^{-s}/s^2$ give the absolutely convergent identity (write $z=s-1/2$)

$$\int_{X_0}^{\infty}F(X)X^{-s-1}\,dX
=15X_0^{-z}\left(\frac{\log(16X_0)}{z}+\frac{1}{z^2}\right)
+\frac{(L'/L)(s)+H(s)}{s^2}+\int_1^{X_0}P(X)X^{-s-1}\,dX,$$

where $H(s)=\sum_p\sum_{k\ge2}\chi_4(p)^k(\log p)p^{-ks}$. The envelope term follows by integrating $(w+\log16)e^{-zw}$ from $w=\log X_0$ to infinity. Its only possible pole is on the boundary, and the compact integral is entire. For $\sigma=\Re s\ge1/2+\delta$, the prime-power correction converges normally by comparison with $\sum_{m\ge2}(\log m)m^{-1-2\delta}/(1-2^{-1/2-\delta})$. Thus the right side continues meromorphically to $\Re s>1/2$. It is regular at every real $u>1/2$, since the alternating odd series gives $L(u)\ge1-3^{-u}>0$.

Suppose the convergence abscissa $\alpha$ of the nonnegative tail $F$ exceeded $1/2$. It is at most $1$. The continuation agrees with the integral to the right of $\alpha$ by meromorphic uniqueness, and is analytic in a disk about $\alpha$. Its Taylor series at a sufficiently close real $b>\alpha$ therefore reaches a real $s<\alpha$. In powers of $b-s$ its coefficients are the integrals of $F(X)X^{-b-1}(\log X)^j/j!$ (differentiate using convergence at a point in $(\alpha,b)$). They are nonnegative since $X_0\ge1$. Summing by monotone convergence gives a finite defining integral at $s$, a contradiction. The integral is consequently holomorphic on $\Re s>1/2$. There a zero $\rho$ of multiplicity $m$ would leave residue $m/\rho^2\ne0$, with every other term regular. The functional equation of the primitive real character reflects any nontrivial zero left of the line to the excluded half-plane.

### Reverse implication and scope

The [all-cutoff proof, lines 59–80](mod-four-prime-ramp-eventual-sign.md#from-zeros-to-sign), at the evidence revision, uses the identical ramp. Under the zero-line hypothesis its prime-power ramp has total absolute zero contribution at most $C_0\sqrt X$, with $C_0=\sum_\rho|\rho|^{-2}<4/3$. Removing odd prime squares subtracts $(2+o(1))\sqrt X$: The coefficient is $\log p$ and the weight is $2\log(\sqrt X/p)$. Higher powers and the remaining contour terms cost $o(\sqrt X)$. Hence $P(X)\le(C_0-2+o(1))\sqrt X<0$ eventually, in particular at fourth powers. Via the equivalence, eventual strict all-cutoff negativity also follows indirectly from the sampled signs.

The new step is the mesh-to-envelope transfer, not an arithmetic proof of the endpoint signs. Bob's (1), lines 17–35, supplies magnitude information used at lines 45–51, not these signs. Neither sign independence nor a finite sign check enters the proof. No optimal mesh or unconditional zero-line conclusion follows.
