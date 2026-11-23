# A growing Weil window for most characters of each prime conductor

**Decision.** Can character cancellation pay for a larger window than one can certify by charging the unsigned prime translations to the conductor? Yes, provided the archimedean frequency cost is retained. In fact the norm of the prime compression *alone* does not see the character phases at all in the range below.

Use the centered conductor normalization of the [right-hand Pick and Weil window note](../adhoc/pick-block-weil-window.md). Let $q$ tend to infinity through primes, $A>0$ be fixed, $b=\log(A\log q)$, $L=2b$, and $X=e^L$. Write $\lambda_\chi(b)$ for the infimum of the Weil quotient over all nonzero complex $C_c^\infty(-b,b)$ tests, with neither parity nor moment restrictions. For each fixed $0<\alpha<1$, apart from a fraction at most $q^{-(1-\alpha)/2+o(1)}$ of the nonprincipal characters modulo $q$,

$$
 \lambda_\chi(b)\ \ge\ \big[\min(1,1+\alpha-A)-o(1)\big]\log q. \tag{1}
$$

All error terms here may depend on the fixed $A,\alpha$, not on a test or a good character. In particular, for $1<A<2$ and any $0<c<2-A$, all but $o(q)$ primitive characters of **each** prime conductor have floor at least $c\log q$. A test in any fixed interval shorter than $\log 2$ gives the companion upper bound $\log q+O(1)$ for all characters, since it has no prime terms. Thus for $A<1$ the leading floor for almost all characters is actually $\log q$ (take $\alpha>A$). These are asymptotic paper bounds, not numerical certificates or GRH for any character.

## The cost of dropping all phases

Translate the input to $[0,L]$ and extend by zero. Use $U_t h(x)=h(x+t)$ on the line and $a_n=\Lambda(n)/\sqrt n$. The finite self-adjoint operator

$$
 B_\chi=\sum_{2\le n\le X}a_n\big(\chi(n)U_{\log n}+\overline{\chi(n)}U_{-\log n}\big)
$$

is the term to **subtract** from the form. With $\widehat h(y)=\int h(x)e^{-iyx}\,dx$ the other term is the Fourier multiplier $\log q+g_a(y)$, where $g_a(y)=\Re\psi(1/4+a/2+iy/2)-\log\pi$ and $a=0,1$ is the parity. This is the compact-test Dirichlet explicit formula for the completion $(q/\pi)^{(s+a)/2}\Gamma((s+a)/2)L(s,\chi)$: The logarithmic derivative of the conductor and Gamma factors is paired with its conjugate, and the Euler term is paired with its adjoint. There are no poles for a primitive nonprincipal character. Switching Fourier sign exchanges the two shifts without changing the estimates. Uniformly in parity, $g_a(y)\ge -O(1)$ everywhere and $g_a(y)\ge\log |y|-O(1)$ for $|y|\ge1$, by continuity and Stirling. In particular it is not legitimate to drop the conductor power from the completion.

We use two bounds with different domains. On the full line $\|B_\chi\|\le2\sum_{n\le X}a_n=O(\sqrt X)$ by partial summation. On an interval of length $D\ge L$, the unsigned compression including all shifts up to $e^D$ bounds the signed Rayleigh quotient from above by $(1+o(1))e^{D/2}$ as $D\to\infty$. The [sharp prime-translation estimate, sections 1 and 2](../adhoc/prime-translation-norm.md) proves this by weighted Schur with $w(x)=e^{-x/2}+e^{-(D-x)/2}$ on $[0,D]$. The main terms of the weighted row add to $e^{D/2}w$, not $2e^{D/2}w$. At $D=L$ and $q>X$, the signed upper spectral edge agrees exactly with the unsigned one: Modulating the input by $e^{itx}$ makes the finitely many $\chi(p)p^{it}$ approach 1 simultaneously by Kronecker's theorem. Thus the coefficient $A$ in the worst prime cost $e^b=A\log q$ cannot be reduced without accounting for frequency. Below, the full-line bound controls only leakage; using it for the main high-frequency estimate would lose the result.

## Cancellation below a frequency cutoff

Put $Y=q^\alpha$ and

$$
 P_\chi(t)=\sum_{p\le X}\frac{\log p}{\sqrt p}\chi(p)p^{it},\qquad V=\frac{\log q}{\log\log q}.
$$

We show that outside the exceptional set in (1), $|P_\chi(t)|\le V$ **for all** $|t|\le 2Y$. Write $k=\lfloor\log(qY)/\log X\rfloor$, $N=\lfloor X^k\rfloor\le qY$, and expand $P_\chi^k=\sum_{n\le N}d_n\chi(n)n^{it}$. Unique factorization and the multinomial formula give $\sum d_n^2\le k! (\sum_{p\le X}(\log p)^2/p)^k$ (each multinomial coefficient is at most $k!$). The inner variance is $O((\log X)^2)$ by partial summation. Averaging over all $q-1$ characters, including the principal character only for this bound, gives

$$
 \mathbb E_\chi\int_{-3Y}^{3Y}|P_\chi(t)|^{2k}\,dt
 \ll (Y+N\log(2N)/q)\sum_n d_n^2.
$$

In fact the diagonal costs $6Y\sum d_n^2$. The other surviving pairs have $m\equiv n\pmod q$, $m\ne n$, and the time integral costs at most $2/|\log(m/n)|\le 2N/|m-n|$. Using $2d_md_n\le d_m^2+d_n^2$ and summing reciprocal multiples of $q$ proves the estimate. Time averaging is important here: It allows length $qY$, not just $q$.

By partial summation $|P_\chi'|\ll\sqrt X\log X$. A value above $V$ in $[-2Y,2Y]$ therefore costs an integral at least $(V/2)^{2k}\min(1,c_0V/(\sqrt X\log X))$ in the enlarged range for some absolute $c_0>0$. The reciprocal of this length is $q^{o(1)}$. Since $\log X=2\log\log q+O_A(1)$ and $k\sim(1+\alpha)\log q/(2\log\log q)$, the log of the moment ratio satisfies

$$
 \log\frac{k!\big(O((\log X)^2)\big)^k}{(V/2)^{2k}}
 \le k\,[ -\log\log q + O(\log\log\log q)]
 =[-(1+\alpha)/2+o(1)]\log q.
$$

Multiplying by $Yq^{o(1)}$ gives the claimed exceptional fraction. Dropping the principal character changes the denominator only by $1+o(1)$. The squares in the Euler sum cost $O(\log X)$ by partial summation, and exponents at least three cost $O(1)$ by absolute convergence. Hence the **full truncated** prime multiplier has modulus $o(\log q)$ throughout $[-2Y,2Y]$ for each good character.

## Recombining the two frequency ranges without losing the support bound

Fix real smooth multipliers $l(t),r(t)$ with $l^2+r^2=1$, $r=0$ for $|t|\le1$, and $r=1$, $l=0$ for $|t|\ge2$ (take a cosine and sine of a smooth transition angle). Split a unit test into $h_l,h_r$ by multiplying its transform by $l(y/Y),r(y/Y)$ respectively. Squared norms add, as do the quadratic forms of both full-line multipliers, including $B_\chi$. This is an exact splitting of the **finite** prime operator already selected by the original support. We do not reapply an untruncated explicit formula to the two filtered functions.

The low piece costs at most $o(\log q)\|h_l\|^2$ in the prime term. For the high piece, the global multiplier bound alone costs too much. Instead put $d=Y^{-1/2}$, $I=[-d,L+d]$, and $f=1_Ih_r$. Since $r-1$ is compactly supported and smooth, $h_r=h+Y K(Y\cdot)*h$ for a fixed Schwartz kernel $K$. Young's inequality with the kernel restricted to distances at least $d$ gives $\|h_r-f\|_2\le\int_{|s|\ge Yd}|K(s)|ds=o(1)$ uniformly in the original unit test. Replacing $h_r$ by $f$ **only in the prime term** costs $o(\log q)$ by the full-line norm bound. On $I$, absolute values and the Schur estimate for $D=L+2d$ now give

$$
 \langle B_\chi h_r,h_r\rangle\le (A+o(1))\log q\,\|h_r\|^2+o(\log q),
$$

since adding the unsigned translations up to $e^D$ only enlarges the positive kernel. The archimedean estimate is applied to $h_r$, **not** to the abruptly cut $f$. Its gain is at least $\log Y-O(1)$ per unit squared norm there. Combining the two bounds leaves coefficients $1-o(1)$ on $\|h_l\|^2$ and $1+\alpha-A-o(1)$ on $\|h_r\|^2$, in units of $\log q$, as asserted.

## The same estimate for whole right-hand blocks

For the same $A,\alpha$ and the same exceptional-fraction bound, (1) also bounds $P_\chi$ below, relative to the Cauchy Gram matrix $C$, **uniformly over all** finite sets of distinct real nodes $m\ge (\log\log q)^3$ with $\sum 1/m\le b$. Here $C_{mn}=1/(m+n)$ and $(P_\chi)_{mn}=(F_\chi(m)+\overline{F_\chi(n)})/(m+n)$ for the centered completed logarithmic derivative. This is not a diagonal application of a fixed-window limit.

Indeed take $B=\log\log q$, $\eta=B^2$, $D=L+B^{-1/2}$, and a Cauchy-normalized exponential polynomial $h$ on the positive half-line, extended by zero. The matrix form is the same Gamma form minus the *untruncated* prime correlation sum by the Laplace representation in the Pick note (conjugating the coefficient vector if needed). Its weighted Fourier integral is finite even at a jump of the zero extension, since each generator's transform is $1/(m+iy)$. Section 4 of the [prime-translation estimate](../adhoc/prime-translation-norm.md) gives $\|1_{[t,\infty)}h\|\le\exp(H-\eta t)$, with $H/\eta\le2b+O(B^{-1})$; the proof uses $\sum m^{-3}\le B^{-6}b$ and does not require $A<1$. The omitted prime correlations for $n>e^D$ cost $O(e^{H-(\eta-2)D}\sum_n\Lambda(n)n^{-5/2})=o(1)$, and $v=1_{[0,D]}h$ satisfies $\|h-v\|=o(1)$.

Apply the moment estimate with $X'=e^D=(A\log q)^2 e^{o(1)}$, which leaves the exponents and the derivative estimate unchanged up to constants. Now split the original $h$ using the same two Fourier multipliers, with $B_\chi$ cut off at $X'$. For the high-frequency prime estimate one has $\|h_r-v_r\|=o(1)$ by contraction, and the preceding kernel tail bound applies to $v_r$ outside $[-d,D+d]$. Hence the enlarged-window Schur cost is again $(A+o(1))\log q$ per high squared norm, plus $o(\log q)$ per original unit test. Neither the Gamma term nor the low-frequency estimate uses this spatial truncation. Combining both frequency pieces proves the matrix assertion. Taking the union of the exceptional sets at $X$ and $X'$ preserves the exceptional-fraction bound.

**Boundary of the method.** For example $A=3/2$, $\alpha=3/4$ gives a floor $(1/4-o(1))\log q$ with exceptional fraction $q^{-1/8+o(1)}$, where the unsigned conductor-only bound is negative. Nothing here tests every support for a single fixed character. The barrier at $A=2$ in this calculation is the simultaneous need for $\alpha>A-1$ to pay the high-frequency cost and $\alpha<1$ to get a vanishing exceptional fraction. To reach, for example, $A=2.1$ at most characters of *each* prime conductor, test a large-values bound for $P_\chi$ up to $q^{1.2}$ that is stronger than the spacing-and-diagonal moment above, or reduce the high-frequency prime cost with a bound that charges the frequency of near alignment. Another estimate of the norm of the signed prime compression without that frequency cost cannot suffice.
