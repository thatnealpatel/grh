# The actual Gaussian singleton trace is the capped jet sum

**Result (reviewed ordinary mathematics, not Lean).** Let
$F=\mathbb Q(i)$, $G=C_F$, $G^1=\ker|\cdot|_F$, and
$K=\prod_{v<\infty}\mathcal O_v^\times$. In the class model
$(\mathbb C^\times\times K)/\mathbb Z[i]^\times$, put
$\eta([z,u])=(z/|z|)^4$. For $a=1/2$, $I=\{0\}$, $s=4$, and
$\varphi(g)=\eta(g)b(\log|g|_F)$ with $b\in C_c^\infty((0,\log 2))$,
the actual convolution-first operator in (10.4.2.5), PDF p. 459,
satisfies

$$
\operatorname{Tr}\big(P_a^{\mathrm{spec}}A(\varphi)\big)
   =\sum_{t:Z(t)=0}\min(d_t,2)\,m(t),\qquad
Z(t)=L(1/2+it,\bar\eta),\qquad
m(t)=\mu_1(G^1)\int_{\mathbb R}b(x)e^{itx}\,dx .
$$

Here the sum is over distinct real $t$, $L$ is completed, $d_t$ is the
zero order, and the sum is absolutely convergent. This verifies the
**character-corrected** singleton sum of (10.3.1.3)–(5), PDF pp. 448–449,
for this operator. It is not a proof with the literal homogeneous
character labels or the printed kernel.

## Inherited source and operator inputs

Use the [accepted rendered jet conventions](trace-theta-jets-qi.md#source-and-character-convention)
and the [accepted angular operator interface](trace-spectral-angular-qi.md#test-and-source-interface)
for the same [pinned Masullo edition](../sources/masullo/README.md).
These are inherited visual readings, not fresh page checks. The test
is Bruhat: The fourth power is trivial on diagonal Gaussian units,
$\eta$ is trivial on $K$, and the norm-radial test factors through the
Lie quotient by the compact image of $K$. Norm-one fibers are compact,
so the prescribed compact log support gives compact support on $G$ and
$\varphi(1)=0$. See the angular note for the test-space cross-references.

In (9.3.1.2), p. 419, the integrated action uses
$U_h f(g)=f(h^{-1}g)$ and no conjugation on $\varphi$. Compact angular
averaging puts the input and the output in the full left-action
$\bar\eta|_{G^1}$ block $B$. The singleton quotient (10.2.1.1)–(2),
p. 439, divides the ambient $W^{s,2}(G)$ by the closed twisted theta
space $M_a$ of (10.1.1.1)–(3), p. 434. Its orthogonal lift in
(10.4.2.5), p. 459, identifies $P=P_a^{\mathrm{spec}}$ with the
projection onto $M_a^\perp$. The block reduces $P$ because norm-one
translations are unitary and preserve $M_a$.

On $B$ write $f(g)=\eta(g)q(x)$ with $x=\log|g|_F$. The norm
$|[z,u]|_F=|z|^2$ is split by $x\mapsto[e^{x/2},1]$, on which $\eta=1$,
and quotient Haar splits as $d\mu_1\,dx$. The angular factor in
$U_hf$ cancels $\eta(h)$ in $\varphi(h)$, leaving convolution of $q$
by $\mu_1(G^1)b$. The positive log Fourier transform sends this to
multiplication $M_m$ by the displayed $m$, with no twist or further
scalar. By the weight $(1+x^2)^2$ in (9.1.2.3), p. 399, the transform
identifies the block with $H^2(\mathbb R)$ in the $(1,2,1)$ derivative
norm, up to a fixed scalar which does not affect projections or traces.

The bilinear jet convention (10.2.1.5), p. 440, and (10.2.1.9), p. 442,
uses $\chi=\bar\eta$: The compact factors cancel on $\eta q$, and the
positive sign gives the $j$th derivative of $\mathcal F_+q$ times the
nonzero scalar $\mu_1(G^1)i^{-j}$. The cap (10.2.1.6), p. 440, uses
$2j+1<s$ from (9.1.2.16), p. 402, so the orders are $0,1$ subject to
$j<d_t$. The completed product is that of (3.2.1.2)–(5), p. 123, with
the complex Gamma factor, as checked in the [Gaussian Mellin source
interface](trace-theta-density-qi.md#source-interface).

The [character-label audit](trace-spectral-angular-qi.md#character-labels-in-the-two-printed-trace-routes)
checks the printed route separately. With $\omega=\eta|_{G^1}$ the
test has action weight $\bar\omega$, so it fits that homogeneous
premise. But the printed $\chi|_{G^1}=\omega$ label in the plus-Mellin
sum gives zero angular average: The compact factor on translation is
$\eta(h)\chi(h)$, nontrivial for this restriction. The correction used
here is to select $\chi|_{G^1}=\bar\omega$, agreeing with the actual
output block and with the jets. This character check does not decide
whether the corrected scalar is nonzero.

The [trace-class proof](trace-spectral-singleton-qi.md) gives
$PA=PAP\in\mathcal S_1$ for the uncut operator, and the completed
zero count with multiplicity $O((R+1)\log(R+2))$ for $|t|\le R$.
The [totality proof](trace-theta-totality-qi.md#projection-and-scope)
identifies $P$ on $B$ as the projection onto the closed span of the
Riesz representers of the capped jets. Neither input evaluated the
scalar trace. The following uses the finite compression idea of the
[rational singleton calculation](trace-spectral-q.md#trace-and-cutoff-limit).

## Finite jet matrices and trace-norm limit

Work on the transported block and denote its restricted projection
again by $P$. The complement of $B$ contributes zero to the full trace.
Put $n_t=\min(d_t,2)$, let $S_N=\{t:Z(t)=0,\ |t|\le N\}$, and define
$J_Nu=(u^{(j)}(t))_{t\in S_N,\ 0\le j<n_t}$. Let $V_N$ be the span of
these jet representers and $P_N$ its orthogonal projection. Each $S_N$
is finite. For each $t\in S_N$ choose a smooth cutoff $\rho_t$ equal
to one near $t$, compactly supported in disjoint neighborhoods. The
functions $\rho_t(v)(v-t)^j/j!$ have one unit coordinate and all other
coordinates zero. Thus $J_N$ is onto. Since the kernel of $J_N$ is
$V_N^\perp$, $J_N P_N=J_N$, and the restriction of $J_N$ to $V_N$ is
an isomorphism. This uses no lower bound on zero spacing or on the
conditioning of the coordinates as $N$ grows.

Since $V_N\subseteq\operatorname{ran}P$, the compression
$P_N T P_N=P_N M_m P_N$ acts on $V_N$ by the following formula in
those coordinates:

$$
\big(J_N P_N M_m u\big)_{t,j}
  =(mu)^{(j)}(t)
  =\sum_{k=0}^{j}\binom{j}{k}m^{(j-k)}(t)u^{(k)}(t),
  \qquad u\in V_N.
$$

The pointwise product rule applies to the continuous jet representatives
of the Sobolev derivatives of orders below the cap. At each $t$ the
matrix is lower triangular with $n_t$ diagonal entries $m(t)$, with no
terms from the other zeros. Trace in these coordinates equals the
Hilbert-space trace of the compression, since outside $V_N$ the
compression is zero and the trace on $V_N$ is invariant under a change
of basis. Hence $\operatorname{Tr}(P_NTP_N)=\sum_{t\in S_N}n_t m(t)$,
including the empty-span case.

The increasing $V_N$ exhaust a dense subspace of $\operatorname{ran}P$,
so $P_N\to P$ strongly on $B$. As $T=PTP$, the identity
$$
T-P_NTP_N=(P-P_N)T+P_N T(P-P_N)
$$
reduces trace-norm convergence to strong convergence against a
trace-class factor on either side. For rank-one factors this follows
from the trace norm being the product of the two vector norms and
$P-P_N$ being self-adjoint. Finite-rank approximation in trace norm
and the uniform bounds on the projections extend it to $T$. Thus
$\|T-P_NTP_N\|_1\to0$, and trace continuity yields the asserted limit.
This argument does not exchange a sum of nonorthogonal rank-one
operators with a trace, and does not commute $P$ with $M_m$.

For absolute convergence, $b$ compact smooth makes $m$ Schwartz.
In a shell $2^k\le |t|<2^{k+1}$ the sum of $n_t$ is
$O(2^k(k+1))$, and the supremum of $|m|$ is $O(2^{-3k})$.
The shell bounds are summable and the remaining bounded interval
contains only finitely many zeros. This also covers a zero at $0$,
without assigning it twice.

**Independent review:** `gaussian-trace-review` (agent `LYVhqiz`,
transcript in worker Yah session `01a20437-26d9-7b64-81ea-d55e0c71139b`)
checked the applicability of the inherited rendered source, including
the Bruhat test, quotient lift, Haar and Fourier factors, completed
product, and cap. The reviewer checked the finite interpolation,
coordinate preservation, Leibniz diagonal, trace-norm limit, absolute
summability, and fixed-parameter extension. Separately, the review
confirmed the angular cancellation in the inherited printed route and
that it is a label mismatch, not a nonzero-trace counterexample. No
consequential reading remains provisional for this verdict; no pages
were newly rendered. The reviewed base was
`8b3c6d68f958a27fd401b8d1e0adeb677b0406ed`; the intervening general-field
Gaussian inversion inputs did not change these premises or the
spectral navigation hunk. Selector Yah `01a20435-e456-71b3-974e-4a380fc7ea99`.

## Reuse and remaining checks

The same proof gives the operator identity on this Gaussian isotype
for any fixed real $a$, singleton $I=\{0\}$, even $s=2r\ge2$, and
any compact smooth log profile. Indeed the accepted totality and
trace-class inputs cover those parameters; the ambient binomial
$H^r$ norm admits orders $j<r$, and the count applies to each fixed
line. Replace $Z(t)$ by $L(a+it,\bar\eta)$ and $n_t$ by $\min(d_t,r)$.
The larger bump class is a scope of the ambient operator identity,
not a relaxation of the manuscript's support hypotheses in its other
trace comparisons. There is no positive-width claim.

**Next bounded check:** Turn the Gaussian–Poisson/Jensen count in the
[trace-class proof](trace-spectral-singleton-qi.md#gaussian-tails-and-jensens-bound)
into a numerical tail bound for the real-zero sum for one specified
positive-log bump. For example, use $L_0=\log 2$ and
$b_0(x)=\exp(-1/(1-u^2))$ for $|u|<1$, zero elsewhere, with
$u=4x/L_0-2$. Combine an explicit upper bound for the Gaussian tail
and lower bound at the Jensen center with an integration-by-parts
bound for $\mathcal F_+ b_0$. This would supply an error budget for a
finite zero calculation, not a nonvanishing proof by itself.

**Separate open premises:** A certified nonzero scalar for a test on
the prescribed support, convergence and identification of the printed
kernel, the local-to-global diagonal comparison, and positive-width
density. The [circle cancellation](trace-spectral-angular-qi.md#what-the-boxes-omit-and-what-remains)
is still a statement about averaging the actual operator's kernel;
the present result supplies its omitted scalar, not its nonvanishing
or an identification with the named printed kernel.
