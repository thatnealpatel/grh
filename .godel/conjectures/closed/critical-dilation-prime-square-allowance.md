---
evidence_revision: 25e564b06ce948bd41fbc69aa73f1df306a7f043
outcome: established
---

# A prime-square allowance at the critical dilation

Fix any primitive nonprincipal Dirichlet character $\chi$
of conductor $q$, real or nonreal. For an integer $m\ge2$
let $h_m=\mathbf{1}_{[0,\log 2]}^{*m}$ under ordinary real
convolution. For $X>0$ define

$$W_m(X)=\sum_p\Re\chi(p)\log p\,h_m(\log(p/X)),\qquad
S_m(X)=\sum_{p\nmid q}\log p\,h_m(\log(p^2/X)).$$

**Proposition to test:** All nontrivial zeros of $L(s,\chi)$
lie on $\Re s=1/2$ if and only if there exist one integer
$m\ge2$ and one $X_0\ge1$ such that

$$\sqrt2\,W_m(X)-W_m(2X)\le S_m(X)\qquad (X\ge X_0).$$

The order and threshold may depend on $\chi$. The order is
fixed over all real $X\ge X_0$. There is no chosen phase,
real-axis nonvanishing premise, or conductor uniformity.
The allowance counts genuine prime squares with $\log p$,
not $\log(p^2)$.

**Source and payoff:** The operator proposes this as a
single-comparison replacement for the real-character
[family of comparisons](../closed/real-character-prime-spline-dilation-comparison.md)
at the evidence revision, built on the
[fixed-character sign criterion](../closed/real-character-prime-spline-eventual-sign.md)
at `d3675071daa1e1afbff4107024f1a9943855a43b`. Bob's
[fixed-strip estimate (1)](../../bob/fixed-strip-endpoints.md#the-product-mean-at-the-original-endpoint-weight)
at `bbca37033019090f6f40e6223b5054d382c9d789` is a magnitude
bound with a different weight and premise. None of these
sources asserts the proposed critical-dilation criterion.
The payoff would be a characterization for complex as well
as real characters, not an independent proof of the
comparison or an equivalence with a prime-only comparison.

**Discriminating test:** Use the holomorphic average of the
logarithmic derivatives for $\chi$ and $\overline\chi$.
Derive the fixed-order explicit formula, keeping
multiplicity at shared and real zeros. Audit the square
mean of $\Re(\chi(p)^2)$ by fixed-modulus prime arithmetic
and the separate positive mean of $S_m$. Test whether the
critical factor removes all constant $\sqrt X$ terms and
whether summable kernel contraction beats that allowance
for a fixed order, even at small nonzero ordinates.
Conversely, carry $S_m$ and the finite endpoint corrections
through the Mellin transform of the nonnegative tail.
Locate its singularities, test the residue sign at a real
abscissa above $1/2$, and check all possible multiplier
cancellations and the reflection for a nonreal character.

## Adjudication

**One comparison suffices.** At the critical dilation the prime sum has no remaining constant term in units of $\sqrt X$. The margin comes from the unsigned count on the right, even when the signed squares on the left have mean zero. In the converse this same count is regular strictly to the right of the critical line.

Put $d=\log 2$, $K(s)=\int_0^d e^{st}dt=(2^s-1)/s$ (with $K(0)=d$), $k=K(1/2)=2(\sqrt2-1)$, and $D(s)=\sqrt2-2^s$. Use the meromorphic function

$$Y(s)=\tfrac12\left(\frac{L'}L(s,\chi)+\frac{L'}L(s,\bar\chi)\right).$$

In the Euler series of $-Y$ the coefficient at $p^\ell$ is $\Re(\chi(p)^\ell)\log p$. At each distinct nontrivial zero $\rho$ in the union for the two characters the residue of $Y$ is $w_\rho=(\operatorname{ord}_\rho L(\cdot,\chi)+\operatorname{ord}_\rho L(\cdot,\bar\chi))/2>0$. Absent zeros have order zero. Shared zeros add, and at a real zero conjugation gives the full multiplicity, not half.

### From zeros on the line to the counted inequality

Conjugation puts the zeros of both characters on the line under the hypothesis for $\chi$. Invert $K(s)^m$, the transform of $h_m$ by convolution, on $\Re s=2$ and sum against $\Lambda(n)\Re\chi(n)$. This gives the integral of $-Y(s)X^sK(s)^m\,ds/(2\pi i)$. The Euler series there is absolute, and $K(s)^m$ is integrable along the line for $m\ge2$. The spline is continuous, including at the knots, and is zero at the ends of its support; inversion gives its value for every translate.

It suffices here to shift to $\Re s=1/4$: No trivial zero of either parity is crossed. For clarity, for each completed primitive $L$-function $B$ the real part of its order-one product logarithmic derivative at $2+it$ gives $\sum_\rho(1+(t-\Im\rho)^2)^{-1}\ll_\chi\log(3+|t|)$ with multiplicities. Indeed $\Re(2+it-\rho)^{-1}$ majorizes a constant times the summand, the terms $\Re(1/\rho)$ are summable, and the Euler series and gamma derivative bound $B'/B$ there. Subtract $B'/B(2+it)$ from the product derivative at $\sigma+it$, $1/4\le\sigma\le2$. Terms with $|t-\Im\rho|>1$ have differences bounded by a constant times the same summands. There are $O_\chi(\log(3+|t|))$ nearer zeros. On the new vertical each is at distance at least $1/4$; on horizontal edges in successive unit intervals in both directions choose heights separated from all nearby ordinates of both characters by $\gg_\chi 1/\log(3+|t|)$. Subtracting the gamma derivatives then bounds $Y$ by $O_\chi(\log(3+|t|))$ on the vertical and $O_\chi(\log^2(3+|t|))$ on the edges. Since $K(\sigma+it)^m\ll_m(1+|t|)^{-m}$, the edges vanish at each fixed $X$, and the vertical integral is $O_{\chi,m}(X^{1/4})$. Thus

$$\sum_n\Lambda(n)\Re\chi(n)h_m(\log(n/X))
=-\sum_\rho w_\rho X^\rho K(\rho)^m+O_{\chi,m}(X^{1/4}).$$

The zero sum is absolute by the inverse-square bound. To isolate primes, subtract powers of exponent at least three at a cost $O_m(X^{1/3}\log^2(2X))$ for $X\ge1$ (base at most $(2^m X)^{1/3}$ and $O_m(\log(2X))$ exponents). For the squares put $T=\sqrt X$ and $f(v)=h_m(2\log v)$. By the prime number theorem in each reduced class modulo fixed $q$, partial summation gives $\sum_{p\equiv a\bmod q}\log p\, f(p/T)=T\int f(v)dv/\varphi(q)+o_{q,m}(T)$: The PNT remainder at $Tv$ is uniformly $o(T)$ on the fixed support $[1,2^{m/2}]$, and $f$ has bounded variation. Substitution $t=2\log v$ yields $\int f(v)dv=k^m/2$, not $k^m$. The reduced-class mean of $\Re(\chi^2)$ is $\delta=1$ for order two and $0$ otherwise by orthogonality, regardless of parity or primitivity of $\chi^2$. It is not the mean of $(\Re\chi)^2$. The signed squares being subtracted therefore contribute $\delta T k^m/2+o_{\chi,m}(T)$ before subtraction. The allowance uses coefficient one in every reduced class, so $S_m(X)/(T k^m)\to1/2$.

Write $r=\operatorname{ord}_{1/2} L(\cdot,\chi)$, interpreting this as zero at a nonzero value. The constant in $W_m(X)/(T k^m)$ is $-r-\delta/2$. Critical dilation kills both parts. In fact, with $V=\sqrt2 W_m(X)-W_m(2X)$ and $z_\rho=K(\rho)/k$,

$$\frac{V}{T k^m}=-\sum_{\rho=1/2+i\gamma,\ \gamma\ne0}w_\rho D(\rho)X^{i\gamma}z_\rho^m+o_{\chi,m}(1).$$

For $\gamma\ne0$, $|z_\rho|<1$ by strict triangle inequality for the nonconstant phase $e^{i\gamma t}$ against $e^{t/2}dt/k$ on $[0,d]$. The summands in the absolute budget are dominated for all $m\ge2$ by $2\sqrt2\,w_\rho |z_\rho|^2$, a summable sequence. Dominated convergence first gives one order with absolute budget $<1/8$, independently of every phase $X^{i\gamma}$. A very small nonzero ordinate need not contract rapidly. Only after fixing that order take $X$ sufficiently large for the remainder to have modulus $<1/8$ and the normalized allowance to exceed $3/8$. This proves the desired inequality for every such real $X$.

### From one comparison to zeros on the line

Fix $m,A\ge1$ from the comparison, with $m\ge2$, and put $G(X)=S_m(X)-\sqrt2 W_m(X)+W_m(2X)$. Write

$$P_q(u)=\sum_{p\nmid q}(\log p)p^{-u},\qquad R(s)=\sum_p\sum_{\ell\ge2}\Re(\chi(p)^\ell)(\log p)p^{-\ell s}.$$

Transforming a single $p^\ell$ spline against $X^{-s-1}dX$ over $(0,\infty)$ gives $p^{-\ell s}K(s)^m$; replacing $X$ by $2X$ multiplies the transform by $2^s$. The prime-only series is $-Y-R$. Hence by absolute summation for $\Re s>1$ the nonnegative tail has transform

$$F_A(s)=\int_A^\infty G(X)X^{-s-1}dX
=K(s)^m\big[P_q(2s)+D(s)(Y(s)+R(s))\big]-\int_0^A G(X)X^{-s-1}dX.$$

The correction is entire because all sums are locally finite and $G$ vanishes below $2^{-m}$. On $\Re s\ge\sigma>1/2$ the allowance series and $R$ converge normally by comparison with $\sum_p(\log p)p^{-2\sigma}/(1-2^{-\sigma})$. Neither $K$ nor $D$ vanishes in this open half-plane, since $|2^s|>\sqrt2$. Thus every zero there forces a simple pole of residue $w_\rho D(\rho)K(\rho)^m$. For real $\rho>1/2$ this is strictly negative.

Let $b\le1$ be the real convergence abscissa of the tail, allowing $-\infty$. The integral is holomorphic to the right of $b$ by absolute domination, and equals the continuation on $\Re s>\max(b,1/2)$ by uniqueness. If $b>1/2$ is regular, take $u=b+\epsilon$ so close that its Taylor series reaches $b-\epsilon$ in a disk of regularity. In powers of $u-s$ the coefficients are $\int_A^\infty G(X)X^{-u-1}(\log X)^n dX/n!\ge0$; differentiation uses convergence at $u-\epsilon/2$. Monotone convergence at $s=b-\epsilon$ then gives a finite integral there, contradicting the abscissa. If $b>1/2$ is a pole instead, its negative residue forces $F_A(u)\to-\infty$ as $u\downarrow b$, impossible inside convergence for a nonnegative tail. Hence $b\le1/2$ and every zero pole in $\Re s>1/2$ is excluded. No rightmost zero or real-axis hypothesis is needed.

At the boundary, $D$ vanishes at $1/2+2\pi i n/\log 2$ for every integer $n$, so a pole of $Y$ there need not survive. At the real boundary $P_q(2s)$ itself has residue $1/2$ by the principal Euler logarithmic derivative (subtract the normally convergent higher powers near $2s=1$). The square part of $R$ has at most a simple pole there by the same calculation for $\chi^2$ and its conjugate; powers $\ell\ge3$ are regular. Thus $D$ removes possible real boundary poles of $Y+R$, leaving the positive allowance residue $k^m/2$. The argument needs no boundary regularity. The functional equation and conjugation send a nontrivial zero $\rho$ for $\chi$ to $1-\rho$ for $\bar\chi$ and then to $1-\bar\rho$ for $\chi$. This excludes the left side as well.

The real-character landing uses its family at lines 60–82 and its strictly positive dilation gap at lines 84–94. Neither is an inference about the critical comparison. Here the counted squares replace that gap, and the open half-plane obtained from the single order suffices. This is an equivalence for each fixed character, not an independent proof of its inequality or a removal of the allowance.
