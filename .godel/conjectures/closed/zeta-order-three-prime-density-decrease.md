---
evidence_revision: a08d9dfe9adc87383319f9e970b60bd443cfcca2
outcome: established
---

# Arbitrarily late decreases of the cubic prime density

Put $a=\log 2$, $h_3=\mathbf{1}_{[0,a]}^{*3}$, and
$U_3(X)=X^{-1}\sum_p(\log p)h_3(\log(p/X))$ for real
$X>0$, with rational primes only. The spline is globally
$C^1$ and the prime sum is locally finite.

**Proposition to test:** Unconditionally, for every real
$A>0$ there exists a real $X>A$ with $U_3'(X)<0$.

**Source and payoff:** This operator proposition tests the
cubic version of the signed derivative argument in the
[order-four continuous criterion](../closed/zeta-prime-only-continuous-density.md),
not a result of that landing. On RH it would separate cubic
continuous nondecrease from both cubic eventual doubling
and quartic continuous increase. The
[order-three doubling criterion](../closed/zeta-prime-only-doubling-density.md)
at `d5301e8af8a5b4a76db76248f3264d9c9b5a394c` supplies
the converse needed off RH. The
[signed phase precedent](../open/zeta-order-two-prime-comparison.md)
at `9328b646effbe6e2cc0559c62e40521bab600b48` supplies
a recurrence method for a different fixed-step comparison.
The proposition is not a biconditional with RH.

**Discriminating test:** Put $g=-h_3'-h_3$,
$\Phi(s)=(2^s-1)/s$, $G(s)=(s-1)\Phi(s)^3$, and
$k=\Phi(1/2)$. Independently derive the full smoothed
explicit formula for $x>1$, checking all residues and
the receding left edge. Under RH use it to test the signed
zero phase at $x=3/2$ against $-1/4$. Evaluate the finite
Mangoldt sum, with actual prime-power weights, and a finite
trivial-zero sum using rigorous enclosures and a proved
one-sided remainder. Verify the square contribution to the
large-$X$ prime-only derivative, control higher powers,
and use absolute convergence and simultaneous recurrence
if the seed is strict. Off RH, check that nonnegative
derivative on a tail would imply eventual doubling for
every real starting point, contradicting its converse.

## Adjudication

**Yes.** On RH a signed phase beats the square margin and recurs
arbitrarily late. If RH fails, a tail without decreases would
imply the known doubling criterion at every large real translate.

### An exact identity at the seed

Convolving the interval three times gives
$$h_3(t)=\tfrac12\sum_{j=0}^3(-1)^j\binom3j(t-ja)_+^2.$$
Both $h_3$ and its first derivative vanish at the support ends.
Termwise differentiation of the locally finite sum thus gives
$X^2U_3'(X)=\sum_p(\log p)g(\log(p/X))$ even at knots. Integrating
by parts gives $\int e^{st}g(t)dt=G(s)$ as above, since the
transform of the convolution is $\Phi(s)^3$.

For fixed $x>1$ write $S(x)=\sum_n\Lambda(n)g(\log(n/x))$.
Fourier inversion on $\Re s=2$ and the Euler series give the upward
integral of $-(\zeta'/\zeta)(s)x^sG(s)\,ds/(2\pi i)$. The series
and inversion integral converge absolutely: $G$ decays quadratically
in height and $g$ is continuous, so no half weights occur.
Shift to $\Re s=-R$ for a fixed positive odd integer $R$. To check
the horizontal edges, taking real parts in the product logarithmic
derivative of $\xi$ at $2+it$ gives
$$\sum_\rho (1+(t-\Im\rho)^2)^{-1}\ll\log(3+|t|).$$
Indeed $1\le 2-\Re\rho\le2$, the real parts of $1/\rho$ in the
genus-one product are summable, and Stirling and the Euler series
bound the completed logarithmic derivative there. The local count
leaves heights $T$ in successive unit intervals at distance at least
$c/\log T$ from all ordinates for a fixed small $c>0$. Subtract
the product derivative at $2+iT$ from that at $\sigma+iT$: Zeros
with ordinate distance greater than one cost $O_R(\log T)$ by the
weighted count, and those within one cost $O_R(\log^2 T)$ in total.
Removing the completion factors and using conjugation gives the
same latter bound for $\zeta'/\zeta$ on both horizontals. Hence
$G=O_R(T^{-2})$ kills these edges. The count also gives absolute
convergence of the nontrivial-zero residues, with multiplicities.

On the odd left line the functional equation expresses $\zeta'/\zeta$
as $\log(2\pi)+(\pi/2)\cot(\pi s/2)-\psi(1-s)-(\zeta'/\zeta)(1-s)$.
Here the cotangent and reflected Euler series are bounded and the
digamma term costs $O(\log(2+R+|t|))$. Since $|2^s-1|\le2$,
$|G(s)|\ll(R^2+t^2)^{-1}$. The left integral is therefore
$O(x^{-R}\log(2+R)/R)$ and tends to zero. The pole at one is
canceled by $G(1)=0$, and zero is regular since $\zeta(0)=-1/2$
and $\Phi$ is entire. At a zero the residue of $-\zeta'/\zeta$ is
minus the multiplicity. Thus
$$S(x)=-\sum_\rho x^\rho G(\rho)-\sum_{j\ge1}x^{-2j}G(-2j).$$
On RH put $F(t)=-k^{-3}\sum_\rho G(\rho)e^{it\Im\rho}$, a real
series by conjugation. The identity, not a large-$X$ asymptotic,
evaluates $F(\log x)$ as $(S(x)+\sum_j x^{-2j}G(-2j))/(\sqrt{x}k^3)$.

### Independent finite check

Set $x=3/2$ and $D=\sqrt{x}k^3$. The prime powers $n$ in $[x,8x]$
are $2,3,4,5,7,8,9,11$, with weights respectively the logarithms
of $2,3,2,5,7,2,3,11$. Evaluating $g$ piecewise avoids numerical
branch decisions at knots. Use these expressions:

* For $n<3$, use $-t-t^2/2$ with $t=\log(2n/3)$.
* For $3\le n<6$, use $2v-a-a^2/2-av+v^2$ with $v=\log(n/3)$.
* For $6\le n\le12$, use $w-w^2/2$ with $w=\log(12/n)$.

The $j$th trivial term is
$-(4/9)^j(2j+1)((1-4^{-j})/(2j))^3$, strictly negative. The first
term alone, $-9/128$, suffices. Independent rational enclosures gave
$$-0.1299219760\le S(3/2)\le-0.1299219759,\qquad
0.6963195048\le D\le0.6963195049.$$
To reproduce, reduce each rational log argument to $y\in[1,2]$
by divisions by two, adding back the corresponding multiples of $a$.
For $z=(y-1)/(y+1)$ sum $2z^j/j$ for odd $1\le j\le31$ and add
$[0,2z^{33}/(33(1-z^2))]$ for the positive series tail. Use the
same formula at $y=2$ for $a$. Bound each square root of a rational
$q$ by $[b,b+1]/10^{12}$, with $b$ the integer square root of
$\lfloor 10^{24}q\rfloor$. Use rational interval sums and the extrema
of the endpoint products. The resulting first-term ratio satisfies
$$F(\log(3/2))\le (S(3/2)-9/128)/D<-0.28756<-1/4.$$
With eight terms the *finite upper bound* lies between
$-0.3110856161$ and $-0.3110856160$; this interval is not an
enclosure of the full phase.

### Returning to the actual prime-only derivative

The square contribution to $S(X)$ integrates $g(2\log v)$ against
$d\vartheta(\sqrt X v)$ on $[1,\sqrt8]$. There the PNT error is
uniformly $o(\sqrt X)$, and $g$ has fixed bounded variation. Partial
summation gives $\sqrt X G(1/2)/2+o(\sqrt X)=-\sqrt X k^3/4+o(\sqrt X)$
by $t=2\log v$. Higher powers cost $O(X^{1/3}\log^2(2X))$ in total,
since $p\le(8X)^{1/3}$ and the exponent is $O(\log(2X))$.
The trivial sum is $O(X^{-2})$. Subtracting the powers yields on RH
$$\frac{X^2U_3'(X)}{\sqrt X k^3}=\tfrac14+F(\log X)+o(1).$$
The zero count and quadratic decay make the series for $F$ uniformly
absolutely convergent. For a finite truncation, simultaneous Dirichlet
approximation gives unbounded integer shifts making every phase
multiplier arbitrarily close to one (if the approximants stay bounded
as tolerance shrinks, an exact period repeats and its multiples work).
Choose successively smaller uniform tails and recur on the retained
terms. Thus there are $X\to\infty$ with $F(\log X)\to F(\log(3/2))$.
The derivative is strictly negative along this sequence eventually.
No independence or bound on the first return is needed.

If RH fails, an everywhere nonnegative derivative beyond some $A$
would, by the mean value theorem, give $U_3(2X)\ge U_3(X)$ at every
real $X\ge\max(A+1,1)$. Lines 135–168 of the pinned doubling card
imply RH from precisely that premise. This contradiction completes
the unconditional proof.

The quartic card at the evidence revision uses its derivative formula
(lines 49–96) in an absolute sign bound (lines 98–119). Its proof
and cubic eventual doubling on RH both survive: A local decrease
need not last a doubling step. Least order is a separate corollary
for the positive-integer powers of this same interval indicator:
$$U_{m+1}(X)=\int_0^a e^v U_m(Xe^v)\,dv.$$
This follows by expanding one convolution inside the prime sum. The
positive average passes eventual nondecrease up one order, even if
$U_m$ is not differentiable. Orders one and two are thus excluded
by the order-three result. On RH four is the least such order for
eventual continuous nondecrease in this family, not among arbitrary
smoothing kernels.
