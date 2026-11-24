---
evidence_revision: 6a7a69610f307bbc5427e262d04cebe3c69a408b
outcome: established
---

# Prescribe a polynomial onset at the fixed baseline

**Proposition to test:** There are absolute $C,D\ge1$
such that, for every integer $q\ge2$, joint GRH for the
primitive inducers modulo $q$, including zeta, is
equivalent to nondecrease of $W_{q,m}(X)/X$ on the
entire real interval $[(2q)^D,\infty)$, where
$m=\max(8,\lceil C\log(2q)\rceil)$. Under joint GRH its
derivative is strictly positive at every point of that
interval. Use the same fixed $M=10^{15}$ and the same
windows: $a=\log 2$, $h_m=\mathbf1_{[0,a]}^{*m}$,
$k_m=4h_m^{(4)}-5h_m''+h_m$, and
$$W_{q,m}(X)=\sum_{p\nmid q}(\log p)
 [Mh_m(\log(p/X))+\mathbf1_{p\equiv1\bmod q}k_m(\log(p/X))].$$
No numerical $C,D$ or unconditional finite certification
of monotonicity is sought.

**Source and payoff:** This is an operator strengthening
of the logarithmic-order landing at the evidence pin:
that landing bounds the critical-zero budget uniformly
but only claims a fixed-modulus tail. The exact kernel
and converse are at
`f5fbeb09e9b972565848e25ac295f3341a537afd`; the quartic
all-prime margin is at
`a08d9dfe9adc87383319f9e970b60bd443cfcca2`.
A uniform remainder would prescribe the onset without
changing the weights or assuming GRH for other moduli.

**Discriminating test:** In $X^2$ derivative units test
whether the perturbation error after the critical zeros
is $O(A^m X^{3/8}\operatorname{polylog}(2qX))$ with
absolute constants. Bound the full imprimitive log
derivative on $\Re s=1/4$ by a primitive Hadamard
difference using absolute local zero counts. For signed
squares test the full $\chi^2$ prime-power sums at scale
$\sqrt X$ with transform $G_m(s/2)/2$ and shift only to
$\Re s=3/4$. Check the principal pole cancellation,
normalized orthogonality, and crude subtraction of
higher powers using convolution from order eight. Then
test absorption after division by $\Phi(1/2)^m\sqrt X$
for every $X\ge(2q)^D$, rational-prime exclusions, and
derivative regularity at all knots. Check the converse
on the same interval and with the same prescribed order.

## Adjudication

**Yes.** The logarithmic-order landing (lines 55–61 and 135–157)
controls the zeros. Its use at lines 159–170 takes a tail *after*
fixing the modulus. To prescribe the onset, replace that last step,
not the zero budget. In particular, fixed-class PNT with an
unspecified error in the square term does not suffice.

### Two contours with absolute vertical bounds

Assume joint GRH only for the inducers modulo this $q$. Put
$L=\log(2q)$, $d=\varphi(q)$, $\Phi(s)=\int_0^a e^{sv}dv$,
$\kappa=\Phi(1/2)$, and $Q(s)=(4s^2-1)(s^2-1)$. Let $V$ be the
identity-class term of $W_{q,m}/X$. The truncated-power formula for
$h_m$ uses translates of $v_+^{m-1}$, so it is globally $C^{m-2}$.
In particular $k_m$ is $C^2$ even at order eight. Differentiating
the locally finite sum, including at knots, gives
$$X^2 V'(X)=\sum_{p\equiv1\bmod q}(\log p)g_m(\log(p/X)),
\qquad g_m=-k_m'-k_m.$$
Integration by parts with compact support gives the transform
$G_m(s)=\int g_m(v)e^{sv}dv=(s-1)Q(s)\Phi(s)^m$. On $1/4\le\Re s\le2$,
$\Phi(s)=(2^s-1)/s$ gives $|\Phi(s)|,|\Phi(s/2)|\le K/(1+|\Im s|)$
with absolute $K$. Eight factors pay for the degree-five polynomial
and cubic decay. Both $G_m(s)$ and $G_m(s/2)/2$ are therefore
$O(K_1^m(1+|\Im s|)^{-3})$ with absolute $K_1>1$.

For an inducer of conductor $c\mid q$, let $\Xi$ be its order-one
completion, multiplying by $s(s-1)$ for zeta. At $2+it$ its
logarithmic derivative is $O(\log(2c(2+|t|)))$ by the absolute
Euler series and Stirling's formula for either parity. Subtract the
Hadamard derivative at $-1+it$ from that at $2+it$. The product
constants cancel, and the functional equation identifies the former
with the negative conjugate of the latter. For $\rho=1/2+i\gamma$ the
difference of reciprocal terms is $3/((3/2)^2+(t-\gamma)^2)$. Thus
$$\sum_\rho(1+(t-\gamma)^2)^{-1}\ll\log(2c(2+|t|))$$
with absolute constant and multiplicities, also bounding the local
count. Next subtract at $2+it$ from $\sigma+it$ for $\sigma=1/4,3/4$.
Each zero costs at most an absolute multiple of the summand above:
The two denominators have real parts at least $1/4$ in absolute
value. Removing completion terms costs the same logarithmic bound,
since both lines avoid gamma poles and the zeta pole. Missing Euler
factors cost at most $\sum_{p\mid q}\log p/(p^{1/4}-1)\ll\log q$.
Hence the full imprimitive $L'/L$ on either line is absolutely
bounded by a constant times $\log(2q(2+|t|))$.

Define $F_\chi=\sum_n\Lambda(n)\chi(n)g_m(\log(n/X))$. Invert on
$\Re s=2$ against $X^s(-L'/L)(s,\chi)$ and move to $1/4$. For the
horizontal edges it suffices to fix $q,m,X$: In each distant unit
interval choose a height separated from nearby ordinates by
$\gg_q1/\log(3+|t|)$ using the local count. The derivative difference
then costs $O_q(\log^2(3+|t|))$ there (use the displayed sum at
ordinate distance greater than one). Cubic decay kills the edges.
No trivial or removed-factor zeros are crossed. The pole term at one
vanishes by $G_m(1)=0$. Integrating the absolute vertical bound gives
$$F_\chi=-\sum_{\rho_{\chi^*}} X^\rho G_m(\rho)
           +O(K_1^m L X^{1/4}).$$
The minus is the zero residue of $-L'/L$; the sum is absolute by
the local count. Constants in the surviving error are absolute.

### Subtract squares with their signs and multiplicities

At $T=\sqrt X$ use $J_{\chi^2}=\sum_n\Lambda(n)\chi^2(n)
g_m(2\log(n/T))$. The change of variable $v\mapsto2v$ gives the
transform $G_m(s/2)/2$. This time shift only to $3/4$. The inducer
of $\chi^2\bmod q$ is in the hypothesized family, so no zero is
crossed. Every principal square character has pole coefficient
$G_m(1/2)/2=0$ by $Q(1/2)=0$. The same integration gives
$J_{\chi^2}=O(K_1^m L T^{3/4})=O(K_1^m L X^{3/8})$.

Average with weight $1/d$ over the **original** characters, without
deduplicating their squares. At $n=p^j$ the auxiliary coefficient is
$\chi^2(p)^j=\chi(p)^{2j}$, zero also for nonunits. Its average is
$\mathbf1_{p^{2j}\equiv1\bmod q}$; its weight is $(\log p)
g_m(\log(p^{2j}/X))$, not $2\log p$ times the kernel. Thus the
auxiliary terms cancel exactly the even exponents of the original
full sum. Equivalently, writing $H$ for the original averaged terms
with $j\ge3$ and $E$ for the auxiliary averaged terms with $j\ge2$,
$$X^2V'=\langle F_\chi\rangle-\langle J_{\chi^2}\rangle+E-H.$$
For an exact coefficient check, take $q=15,m=8,X=16$. Enumerating
$p^j\in[16,4096]$ gives counts $67,7,2,1,1$ at exponents
$1,2,4,8,12$ after orthogonality. Enumerating $p^j\in[4,64]$ in the
auxiliary sum and indexing by $2j$ reproduces the last four counts
and prime bases. The identity above holds without any finite cutoff
assumption beyond the kernel support.

Convolution gives $\|g_m\|_\infty\le\|g_8\|_\infty a^{m-8}$, and
the support is $[0,ma]$. For $X\ge1$, the original higher powers
have $p\le(2^m X)^{1/3}$; the auxiliary higher powers have
$p\le(2^m X)^{1/4}$. Counting even all integer bases up to each
bound costs at most two additional factors $O(m+\log(2X))$ for the
number of exponents and $\log p$. Increasing the exponential base
absorbs the polynomial dependence on $m$. Combining the estimates,
for absolute $A>1$ and an absolute implied constant,
$$X^2 V'=-d^{-1}\sum_\chi\sum_{\rho_{\chi^*}} X^\rho G_m(\rho)+R,
\qquad |R|\ll A^m X^{3/8}\log^2(2qX).$$

### Absorb the error on the entire interval

Choose the absolute $C$ of the logarithmic-order pin. For its
prescribed $m$, the zero sum including $1/d$ costs strictly less
than $M/400$ in units $\kappa^m\sqrt X$, since the central terms
vanish. Write $B=\max(2,A/\kappa)$. For every $X\ge(2q)^D$, $D\ge1$,
$\log(2qX)\le2\log X$ and $\log^2 X\ll X^{1/16}$. Consequently
$$\frac{|R|}{\kappa^m\sqrt X}\ll B^m X^{-1/16}
\le B^8(2q)^{C\log B-D/16}.$$
As $2q\ge4$, one absolute $D$ makes this strictly less than $M/400$
throughout the interval, not just at its left endpoint.

On zeta RH the quartic pin gives a single threshold $X_4$ for
$X^{3/2}U_4'(X)>\kappa^4/100$, with $U_l=X^{-1}\sum_p(\log p)h_l(\log(p/X))$.
The convolution derivative integrates $e^{2v}U_l'(Xe^v)$ over
$0\le v\le a$. Its arguments are at least $X$, and its normalized
margin gains $\int_0^a e^{v/2}dv=\kappa$. Induction gives the same
threshold for every order. Enlarge $D$ so $4^D\ge X_4$. This choice
requires no GRH at other moduli: If zeta RH fails, there are no true
forward antecedents and the converse below still applies. Since
$X>q$, each $p\mid q$ has $\log(p/X)<0$ and is outside the support.
Combining the baseline margin and both error budgets gives
$$(W_{q,m}(X)/X)'>(M/200)\kappa^m X^{-3/2}>0
\qquad (X\ge(2q)^D).$$
Conversely, nondecrease there supplies exactly a full-tail witness
with this integer $m\ge8$, to which lines 144–197 of the variable-order
pin apply. This proves the equivalence without deciding joint GRH or
providing a finite monotonicity test.

The operator question was “Can the tail onset as well as the smoothing
order be controlled by a single prescription in q?” The open card
was adopted at `be4a426e2d1c6a4a2b817c6e4141148e519f0391` on
`d62a81b9e59287ea612f5c6a6ee2db4e41a1cb2b`. The evidence revision
above and both supporting pins are unchanged.
