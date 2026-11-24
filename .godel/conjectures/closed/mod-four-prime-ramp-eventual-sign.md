---
evidence_revision: bbca37033019090f6f40e6223b5054d382c9d789
outcome: established
---

# Eventual sign of the genuine mod-four prime ramp

Let $\chi$ be the primitive real character modulo $4$. For
real $X\ge1$ set

$$P(X)=\sum_{p<X}\chi(p)\log p\,\log(X/p).$$

**Proposition to test:** There exists a real $X_0$ such that
$P(X)\le0$ for every real $X\ge X_0$ if and only if every
nontrivial zero of $L(s,\chi)$ has real part $1/2$. The sum
uses only genuine primes, natural logarithms, and the
unnormalized ramp, with no modulation. Neither side assumes
any rate, sampling, ordinate independence, or family average.

**Source and payoff:** Bob's [endpoint comparison, (1) and
its signed-pair use](../../bob/fixed-strip-endpoints.md#the-product-mean-at-the-original-endpoint-weight)
uses the prime ramp after division by the cutoff. Taking
$(d_i,d_j)=(1,-4)$ at an odd base conductor and $v=0$ gives
this fixed character. The [unsigned-edge Mellin argument](../../bob/unsigned-edge-rh.md#an-endpoint-lower-bound-and-its-mellin-obstruction)
at `5f22f5a60aef2da44527fee5b442065015202396` suggests the
one-sided transfer. This equivalence is operator-proposed,
not a premise or result of either landing. If it holds, an
independently proved eventual sign would locate the zeros
for this character alone. The prior reweighting cards are
not hypotheses here.

**Discriminating test:** In the sign-to-zero direction,
form the Mellin transform of the nonnegative tail of $-P$.
Price all higher powers on the open right half-plane of
interest, check real-axis analyticity and whether any zero
pole can cancel there, and test Landau and reflection. In
the reverse direction derive the smoothed prime-power
formula with multiplicities and control its lower-order
terms. Compute the leading square correction in the same
ramp normalization, and compare it to a certified absolute
bound on the entire critical-line residue sum. Test the
completed beta log derivative at $1$ and an elementary
bound on $L'/L(1,\chi)$, without sampling zeros. An
insufficient absolute bound would not refute the sign.

## Adjudication

**Both implications hold.** The forward implication needs no bound on the size of the nonpositive tail. For the reverse implication, in the original normalization the squares contribute $(2+o(1))\sqrt X$, whereas the absolute zero contributions together cost less than $(4/3)\sqrt X$.

### From sign to zeros

Write $L=L(s,\chi)$, $Y=L'/L$, and $H(s)=\sum_{p\ {\rm prime}}\sum_{k\ge2}\chi(p)^k(\log p)p^{-ks}$. For $\sigma=\Re s\ge1/2+\delta$, the sum over exponents in absolute value is at most $(\log p)p^{-2\sigma}/(1-2^{-\sigma})$. Thus $H$ is holomorphic on $\Re s>1/2$, not just near the real axis. The prime $2$ contributes nothing. For $\Re s>1$ the transform of a single ramp is $p^{-s}/s^2$; hence, taking $X_0\ge1$ beyond the last possible positive value under the sign hypothesis, the transform is

$$ G(s)=\int_{X_0}^\infty [-P(X)]X^{-s-1}\,dX
=\frac{Y(s)+H(s)}{s^2}+\int_1^{X_0}P(X)X^{-s-1}\,dX. $$

The last integral is entire. The continuation on the right is regular at every real $u>1/2$: The alternating series gives $L(u)\ge 1-3^{-u}>0$, including at $1$. If the nonnegative tail had convergence abscissa $a>1/2$, Landau's theorem would force a singularity at $a$. Indeed, analyticity near $a$ would let the Taylor series at a real $b>a$ sufficiently close to $a$ reach a real point left of $a$. Its coefficients in $b-s$ are the nonnegative logarithmic moments divided by factorials, so monotone convergence would give a finite defining integral there. Thus the integral is holomorphic throughout $\Re s>1/2$. At a zero $\rho$ of multiplicity $m$ there, the right side would instead have residue $m/\rho^2\ne0$. Reflection by the functional equation excludes left-of-line nontrivial zeros too.

### From zeros to sign

Use the primitive odd completion $B(s)=(4/\pi)^{(s+1)/2}\Gamma((s+1)/2)L(s)$. Its reflection is $B(s)=B(1-s)$: The Gauss sum is $2i$, giving root number $2i/(i\sqrt4)=1$. For the growth input, $B(s)$ is half the Mellin integral of $\sum_{n\in\mathbb Z}n\chi(n)e^{-\pi n^2t/4}$ against $t^{(s+1)/2}dt/t$. Poisson summation gives the transformation factor $t^{-3/2}$ under $t\mapsto1/t$. Splitting at $1$ and using exponential decay at infinity gives entireness and $\log\max_{|s|\le R}|B(s)|=O(R\log(2+R))$. Thus Jensen gives $O(T\log(2+T))$ zeros in a disk of radius $T$ with multiplicity. The zeros of $B$ are precisely the nontrivial zeros: At the negative odd gamma poles use reflection to $s>1$; at $0$ use reflection to $1$.

Now assume the zero-line hypothesis. The center is nonzero by the alternating series. Hadamard factorization about the center pairs the factors for $\pm i\gamma$ into $1+z^2/\gamma^2$ for $z=s-1/2$, repeated by multiplicity. The zero count gives normal convergence and evenness kills the residual linear exponential. A pair contributes $2z/(z^2+\gamma^2)$ to $B'/B$, so at $z=1/2$ the contribution is $1/(1/4+\gamma^2)$. Consequently, counting both signs in the sum and using $\psi(1)=-\gamma_E$ for the digamma function,

$$ C=\sum_\rho |\rho|^{-2}=2B'(1)/B(1)
=\log(4/\pi)-\gamma_E+2L'(1)/L(1). $$

Here is an elementary strict bound independent of any ordinates. Differentiate the alternating odd Dirichlet series (locally uniform by partial summation). At $1$ the derivative starts with $+(\log 3)/3$ and alternates with decreasing magnitudes since $(\log t)/t$ decreases for $t\ge3$. Thus $0<L'(1)<(\log 3)/3<3/8$: Indeed $\sum_{j=0}^4(9/8)^j/j!-3=2027/32768>0$. Also $L(1)=\arctan(1)=\pi/4>3/4$, $\log(4/\pi)<\log(4/3)<1/3$, and $\gamma_E\ge0$. Hence $C<1/3+2(3/8)/(3/4)=4/3$.

For the prime-power ramp $Q(X)=\sum_{n<X}\Lambda(n)\chi(n)\log(X/n)$, invert $-Y(s)X^s/s^2$ on $\Re s=2$. Shift to $-1/2$, before the first trivial zero at $-1$. On the new vertical, the functional equation, the Euler product at $3/2-it$, and Stirling's digamma bound give $Y(-1/2+it)=O(\log(2+|t|))$. For the horizontal edges choose heights $h\in[T,2T]$ at distance at least $c/\log T$ from all positive ordinates, possible by the zero count with $c$ small. By conjugacy use $-h$ as well. In the paired logarithmic derivative the zeros with $|\gamma|\le3T$ cost $O(T\log^2 T)$ there; the rest cost $O(T\sum_{|\gamma|>3T}\gamma^{-2})=O(\log T)$. Subtracting the gamma and conductor terms preserves the horizontal bound. The inverse-square kernel therefore makes the horizontal integrals vanish for fixed $X$. The zero residues and the double kernel pole at $0$ (where $L(0)\ne0$) give

$$ Q(X)=-\sum_\rho X^\rho/\rho^2-Y(0)\log X-Y'(0)+O(X^{-1/2}). $$

The error bound is uniform for $X>1$ by absolute integration on the new line. The zero sum costs at most $C\sqrt X$ absolutely. The ramp vanishes at equality, so the inversion includes prime-power cutoffs without an endpoint correction.

For squares $\Lambda(p^2)=\log p$ and $\chi(p)^2=1$ at every odd prime. Writing $\vartheta_{\rm odd}(t)=\sum_{2<p\le t}\log p$, their contribution is exactly

$$ S_2(X)=2\int_1^{\sqrt X}\vartheta_{\rm odd}(t)\,dt/t=(2+o(1))\sqrt X $$

by the ordinary prime number theorem. The $2$ comes from $\log(X/p^2)$, not the coefficient. Exponents $k\ge3$ cost $O(X^{1/3}\log^2 X)$ altogether by $\vartheta(t)\ll t$, ramp size $\le\log X$, and $O(\log X)$ exponents. Subtracting the powers gives $P(X)\le(C-2+o(1))\sqrt X$, strictly negative for every sufficiently large real $X$.

This establishes the equivalence, not either side unconditionally. Bob uses (1) at `fixed-strip-endpoints.md:45–51`, not this sign criterion. His estimate of absolute size does not prove the sign. An independent unconditional eventual sign would give a new zero-location input for this character; finite sign checks would not. Positivity at provably unbounded cutoffs would contradict the zero-line hypothesis.
