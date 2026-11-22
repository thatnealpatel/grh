# Uncut trace class for Gaussian angular weight four

**Result (ordinary mathematics, not Lean).** Let $F=\mathbb Q(i)$,
$G=C_F$, and $K=\prod_{w<\infty}\mathcal O_w^\times$. In the class
model $(\mathbb C^\times\times K)/\mathbb Z[i]^\times$, take
$\eta([z,u])=(z/|z|)^4$ and
$\varphi(g)=b(\log|g|_F)\eta(g)$ with $b\in C_c^\infty((0,\log 2))$.
At $a=1/2$, $I=\{0\}$, and $s=4$, the actual uncut operator
$P_a^{\mathrm{spec}}A(\varphi)$ in Masullo's Theorem 10.4.2.1 and
(10.4.2.5), PDF p. 459, is trace class on $W^{4,2}(G)$. In fact
$A(\varphi)P_a^{\mathrm{spec}}$ is trace class too. This is a proof
using local Sobolev restrictions and a zero count, not the printed
lift-bound or kernel-series argument.

## Source and closure inputs

The local PDF matches the [pinned edition](../sources/masullo/README.md).
The worker read Chapter 10 Markdown and compared the numbered layout
of p. 459, then inspected Poppler pixels at (10.4.2.5): The left
side has the projection after convolution, and the right side is
$S_a\circ A_a^{\mathrm{spec}}(\varphi)\circ Q_a$. The [accepted angular
operator check](trace-spectral-angular-qi.md#test-and-source-interface)
provides the independent rendered reading of this order and the
applicable source conventions. Its proof shows that this $\varphi$ is
a Bruhat test, $A=A(\varphi)$ is the integrated left action from
(9.3.1.2), p. 419, and $A$ is supported on input and output in the
$G^1$ **left-action** $\bar\eta$-isotype. The orthogonal projection
$P=P_a^{\mathrm{spec}}$ onto $M_a^\perp$ preserves that block and its
orthogonal complement. Here $M_a$ is the closed twisted theta space
(10.1.1.3), p. 434. The singleton quotient (10.2.1.1), p. 439, has
ambient squared norm with weight $(1+x^2)^2$, $x=\log|g|_F$, from
(9.1.2.3), p. 399. These latter definitions and the class model are
inherited readings for the same field and parameters, not new visual
checks.

Use the [accepted Gaussian closure check](trace-theta-density-qi.md)
at `aceedd47ecbce262ef762eb415ee425b35c47399`. It identifies the
completed $L(w,\bar\eta)$ of (3.2.1.2)–(5), p. 123, with one quarter
of the radial lattice Mellin integral below. It also puts
$L(a+it,\bar\eta)v(t)$ in the positive log Fourier image of the
indicated theta block for every $v\in C_c^\infty(\mathbb R)$. The
admissibility of the lift, character, and completed-factor readings
are inherited from that independently rendered source check. The
[rational singleton proof](trace-spectral-q.md#translation-and-local-finite-rank)
supplies the row construction, not the Gaussian zero count.

## Gaussian tails and Jensen's bound

Write $h(z)=z^4e^{-2\pi |z|^2}$ and
$$
 B(x)=\sum_{0\ne \alpha\in\mathbb Z[i]}h(e^{x/2}\alpha),\qquad
 D(w)=\int_{\mathbb R}B(x)e^{wx}\,dx=4L(w,\bar\eta).
$$
The Euclidean Fourier transform with phase $e^{-2\pi i z\cdot\xi}$
sends $e^{-2\pi |z|^2}$ to $\frac12 e^{-\pi |\xi|^2/2}$.
Multiplication by $z$ applies $\frac{i}{2\pi}(\partial_{\xi_1}+
 i\partial_{\xi_2})$ to the transform. Since this differential
operator without its scalar annihilates $\xi_1+i\xi_2$, iterating
on the Gaussian gives
$$
 \widehat h(\xi)=\frac1{32}(\xi_1+i\xi_2)^4 e^{-\pi |\xi|^2/2}.
$$
Use Euclidean Poisson summation on the covolume-one self-dual
lattice, with $h(0)=\widehat h(0)=0$. The two expansions give
$$
\begin{aligned}
 |B(x)| &\le e^{2x}\sum_{\alpha\ne0}|\alpha|^4
                          e^{-2\pi e^x|\alpha|^2} &&(x\ge0),\\
 |B(x)| &\le \tfrac1{32}e^{-3x}\sum_{\alpha\ne0}|\alpha|^4
                          e^{-(\pi/2)e^{-x}|\alpha|^2} &&(x\le0).
\end{aligned}
$$
In each sum, split the Gaussian exponent in half, bound one half
using $|\alpha|\ge1$, and sum the other half using $e^{|x|}\ge1$.
Thus for positive constants $C,c$,
$$
 |B(x)|\le C\exp(3|x|-c e^{|x|}).
$$
In particular $D$ is entire by locally dominated integration,
including after differentiation in $w$. Its value at $2$ is
nonzero: By the accepted above-one unfolding it is four times the
Gamma factor times an absolutely convergent Euler product with
nonzero factors, whose logarithms converge absolutely there. For
$|w-2|\le R$, $|\Re w|\le R+2$, so substitution $y=e^{|x|}$ gives
$$
 \max_{|w-2|\le R}|D(w)|
 \le 2C\int_1^\infty y^{R+4}e^{-cy}\,dy
 \le 2C c^{-R-5}\Gamma(R+5).
$$
Stirling's estimate bounds the logarithm of the maximum by
$O((R+1)\log(R+2))$. The segment $w=1/2+it$, $|t|\le T$, lies in
the disk centered at $2$ of radius $r=T+2$. Choose an outer circle
of radius $R\in[2r,3r]$ avoiding the isolated zeros. By Jensen's
formula every zero in the inner disk contributes at least $\log 2$
to the sum bounded above by
$\log\max_{|w-2|\le R}|D(w)|-\log|D(2)|$. Consequently the number
$N(T)$ of line zeros with $|t|\le T$, counted with multiplicity, is
$$
 N(T)=O\bigl((T+1)\log(T+2)\bigr).
$$
The same proof counts zeros on any fixed line $\Re w=a$ with an
inner radius $T+|a-2|+1$. No zero-free range on that line, lower gap
bound, or assertion on the location of zeros is required.

## Summable restrictions and the operator order

In the selected block write a function as $\eta(g)f(x)$, and split
$G$ using the positive radial section $[e^{x/2},1]$. Write
$d\bar\mu=dm_{G^1}\,dx$ and $C_H=m_{G^1}(G^1)>0$. The angular factors
in $\varphi(g)U_g$ cancel on this block. In positive log Fourier
coordinates $A$ is multiplication by the Schwartz function
$$
 m(t)=C_H\int_{\mathbb R}b(x)e^{itx}\,dx.
$$
Plancherel identifies the weighted norm with the Sobolev squared norm
$\|u\|_2^2+2\|u'\|_2^2+\|u''\|_2^2$, up to a fixed overall factor.
Below $P$ also denotes the transported orthogonal projection.

Write $Z(t)=L(1/2+it,\bar\eta)$ and let $J$ range over the components
of $\mathbb R\setminus Z^{-1}(0)$. Dividing any $C_c^\infty(J)$ test
by $Z$ gives a compact smooth multiplier extended by zero outside
$J$. Thus these tests lie in the transformed theta closure.
Orthogonality for $u=Pf$ gives $(1-\partial_t^2)^2u=0$ on $J$ in
distributions. The space of such solutions has dimension four:
The factors $(\partial_t-1)^2$ and $(\partial_t+1)^2$ are coprime,
and after conjugation by $e^{\pm t}$ the respective kernels are
polynomials of degree at most one. Membership in $H^2(J)$ can only
reduce that dimension, also for unbounded intervals.

On each $H^2(J)$ use the same derivative coefficients $(1,2,1)$.
The restriction $E:H^2(\mathbb R)\to\bigoplus_J H^2(J)$ is an
isometry, because the isolated zeros have measure zero and the
weak derivatives restrict to those on $J$. Surjectivity is not
asserted. For its $J$th row $E_J$ the operator $E_J mP$ has rank
at most four. The product rule through order two gives, for all
$v\in H^2(J)$,
$$
 \|mv\|_{H^2(J)}\le C_2
 \max_{0\le k\le2}\sup_J|m^{(k)}|\,\|v\|_{H^2(J)}.
$$
This estimate only multiplies and adds the local $L^2$ norms of
$v,v',v''$. In particular $C_2$ is independent of the interval length
and the estimate does not use a Sobolev embedding or extension on
$J$. Restriction and projection are contractions, so the trace
norm of the row, as an operator between Hilbert spaces, satisfies
$$
 \|E_J mP\|_1\le 4 C_2\max_{0\le k\le2}\sup_J|m^{(k)}|.
$$

For $d(J)=\inf_{t\in J}|t|$, at most one interval contains $0$;
for every other interval $d(J)$ is attained at a finite endpoint
in the zero set, each endpoint serving at most twice. Hence at
most $1+2N(T)$ rows have $d(J)\le T$. The Schwartz bounds give a
row estimate $O_M((1+d(J))^{-M})$ for each $M$. Grouping $d(J)<1$
and $2^j\le d(J)<2^{j+1}$, $j\ge0$, proves summability, e.g. with
$M=3$ by the bound on $N(T)$. Embed each row in the direct sum by
its coordinate inclusion. Their sum converges absolutely in trace
norm and equals $E mP$ by equality in every coordinate. Applying
$E^*$ on the left proves $mP\in\mathcal S_1$, and the zero extension
on the other isotypes proves the full $AP\in\mathcal S_1$.

Finally $A M_a\subset M_a$. Indeed left translations take generating
twisted theta functions to generating ones by translating the lift
and multiplying by the twist scalar, with the two zero modes
preserved under dilation. The closed space is preserved by the
bounded integrated action: On compact log supports the translation
norms are bounded by $2(1+x^2)$ at $s=4$, and norm integration
preserves a closed linear subspace. Thus $PA(1-P)=0$ and
$$
 PA=PAP=P(AP)\in\mathcal S_1.
$$
This establishes the convolution-first assertion without any
claim that $A$ commutes with $P$.

## Scope and next check

The same argument works on this full $\bar\eta$ block for any fixed
real twist $a$, singleton $I=\{0\}$, even index $s=2r$ for integers
$r\ge1$, and $b\in C_c^\infty(\mathbb R)$. Use the matching
single-lift closure inclusion, the order-$2r$ equation
$(1-\partial_t^2)^r u=0$, and the local product rule through order
$r$ in the binomial Sobolev norm. Neither the generality nor the
selected case claims a positive-width result. The argument does
not evaluate or show nonvanishing of the scalar trace, or justify
the printed kernel series or any local-to-global diagonal comparison.
It supplies the trace-class hypothesis for the
[actual operator's circle compression](trace-spectral-angular-qi.md#what-the-boxes-omit-and-what-remains),
not its kernel identification.

**Review evidence.** Independent read-only reviewer `qi-trace-review`
(agent `OZyyRtr`, Yah transcript `01a20285-0635-7163-be3c-6a5aea3f731d`)
recomputed the Fourier transform and both tail estimates, checked
nonvanishing at the Jensen center and the count with multiplicity,
and checked the length-independent row sum, full-space extension,
operator order, and fixed-parameter generality. The reviewer checked
the applicability of the accepted angular and Gaussian source readings,
not new rendered pages. The worker's p. 459 crop agrees with that
inherited independent reading. Selector Yah:
`01a20283-d6c0-70fa-80f5-245defc5ec35`.

**Next bounded check:** Test jet annihilation for arbitrary admissible
lifts in this same Gaussian isotype by averaging over finite units
and taking the weight-four Archimedean angular component. Reduce the
resulting finite-place profiles to a finite linear combination of
fractional ideal ball indicators and test whether each projected
Mellin transform factors by the completed $L(w,\bar\eta)$ with a
factor holomorphic near $\Re w=1/2$. This would advance the opposite
inclusion in the Sobolev-capped jet kernel (value and, at multiple
zeros, first derivative), rather than extrapolating from one lift.
Jet totality, scalar trace nonvanishing, convergence and identification
of any proposed kernel series, and the local-to-global diagonal
comparison remain separate.

**Deferred comparison:** The primitive $p$-adic conductor amplitude in
(3.3.2.24), PDF p. 141, would give a reusable modulus but leave the
local zeta-integral interface. The Gaussian check takes precedence
because it proves trace class for the actual operator now.
