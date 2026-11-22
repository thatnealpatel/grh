# Capped jet totality in the Gaussian singleton isotype

**Result (ordinary mathematics, not Lean).** Take $F=\mathbb Q(i)$,
$G=C_F$, $G^1=\ker|\cdot|_F$, and $K=\prod_{v<\infty}\mathcal O_v^\times$.
In the class model $(\mathbb C^\times\times K)/\mathbb Z[i]^\times$,
let $\eta([z,u])=(z/|z|)^4$. For Masullo's Theorem 10.2.1.1,
PDF pp. 440–442, at $a=1/2$, $I=\{0\}$, and $s=4$, put
$Z(t)=L(1/2+it,\bar\eta)$, with the completed $L$-function, and write
$d_t$ for the order of a real zero. Let $M_{1/2}$ be the closed twisted
theta space and $B$ the full left-action $\bar\eta|_{G^1}$ isotype.
On this block write functions as $\eta(g)q(\log|g|_F)$ and transform
$q$ by the positive log Fourier transform $\mathcal F_+$, with phase
$e^{itx}$. Then

$$
\mathcal F_+(M_{1/2}\cap B)=
\{u\in H^2(\mathbb R): u^{(j)}(t)=0\text{ whenever }Z(t)=0,
\ 0\le j<\min(d_t,2)\}.
$$

Here the transform of a subspace of the block means the transform of
its radial profiles. The actual singleton spectral projection restricted
to $B$ is, in these coordinates, the orthogonal projection onto the
closed span of the continuous jet Riesz representers. For this assertion
use the norm transported from the manuscript, proportional to
$\|u\|_2^2+2\|u'\|_2^2+\|u''\|_2^2$ in squared norm.

## Inherited source and reduction

Use the [accepted rendered source and character readings](trace-theta-jets-qi.md#source-and-character-convention)
for the same [pinned PDF](../sources/masullo/README.md), together with
the linked [single-Gaussian source interface](trace-theta-density-qi.md#source-interface)
and [angular operator interface](trace-spectral-angular-qi.md#test-and-source-interface).
These are inherited rendered readings, not new visual checks. In
(10.1.1.1)–(3), p. 434, the generating theta profiles are twisted once
by $|g|_F^a$ before closure. In (10.2.1.1)–(2), p. 439, the singleton
uses the $W^{s,2}(G)$ quotient by this closure. In the class model,
$|[z,u]|_F=|z|^2$ and $x\mapsto[e^{x/2},1]$ splits the norm with
$\eta=1$ on the section. The ambient weight (9.1.2.3), p. 399, is
$(1+x^2)^{s/2}$, with no $a$ in it. Haar splits as $d\mu_1\,dx$;
Plancherel therefore gives the indicated $H^2$ inner product up to
$\mu_1(G^1)/(2\pi)$.

For $U_h f(g)=f(h^{-1}g)$ the pointwise factor $\eta$ gives left-action
character $\bar\eta|_{G^1}$. Thus the bilinear pairing
(10.2.1.5), p. 440, and (10.2.1.9), p. 442, with $\chi=\bar\eta$
and positive $it$ has its compact factors cancel. Its $j$-th log moment
is $\mu_1(G^1)i^{-j}u^{(j)}(t)$ for $u=\mathcal F_+q$. The cap in
(10.2.1.6), p. 440, uses the strict threshold (9.1.2.16), p. 402:
$2j+1<s$, so $j=0,1$ are the admissible orders at $s=4$ before imposing
$j<d_t$. For the projection, (10.4.2.5), p. 459, and the orthogonal-lift
interface in the angular note identify $P_a^{\mathrm{spec}}$ as the
projection onto $M_a^\perp$. Translation invariance of $M_a$ under the
compact norm-one group makes $B$ a reducing block for this projection.

The [arbitrary-lift result](trace-theta-jets-qi.md#continuation-and-descent)
puts the transformed closed theta block inside the common jet kernel.
The [single Gaussian](trace-theta-density-qi.md#averaging-in-the-defining-weighted-norm)
puts $Zv$ in the transformed block for every $v\in C_c^\infty(\mathbb R)$.
The [Gaussian Mellin identity](trace-theta-density-qi.md#the-zero-modes-and-the-completed-mellin-factor)
uses the completed product of (3.2.1.2)–(5), p. 123, with its complex
Gamma factor. It identifies $L(w,\bar\eta)$ with a nonzero entire
function: Its value above one is nonzero by absolute convergence of
the Euler product and the nonzero Gamma factor there. The map
$t\mapsto 1/2+it$ preserves orders and restricts this function to a
line, so the real zeros of $Z$ are locally finite and of finite order.
No zero count is needed for the reverse inclusion.

## Local division, Sobolev cap, and exhaustion

More generally, let $r\ge1$ be an integer and $Z:\mathbb R\to\mathbb C$
be smooth with locally finite zeros, each of finite order $d_t$. Then

$$
\overline{Z C_c^\infty(\mathbb R)}^{\,H^r}
=\bigcap_{Z(t)=0}\ \bigcap_{0\le j<\min(d_t,r)}\ker[u\mapsto u^{(j)}(t)].
$$

These jets are continuous: Each $u^{(j)}$ for $j<r$ is in $H^1(\mathbb R)$
and has a continuous representative with its sup norm controlled by
its $H^1$ norm. Each $Zv$ has the indicated vanishing, which gives the
forward inclusion. For the converse take any continuous complex-linear
functional $U$ on $H^r$ annihilating these products. Its restriction to
compact smooth functions is a distribution, since on a fixed compact
the $H^r$ norm is bounded by a constant times the sup norms of the
first $r$ derivatives and the function. The relation $ZU=0$ here means
$U(Zv)=0$ on compact smooth tests; it does not assume $Z$ is a bounded
multiplier on the whole $H^r$ space. Off the zeros any test divides
smoothly by $Z$, so $U$ vanishes there.

At a zero $t_0$ of order $d$, work in an open interval containing no
other zero, shrunk so $Z(t)=(t-t_0)^d g(t)$ with $g$ smooth and nowhere
zero, by Taylor's formula. For a compact smooth test $\phi$ in this
interval, subtract its Taylor polynomial of degree $d-1$ at $t_0$
multiplied by a fixed compact smooth bump $\psi=1$ near $t_0$. The
remainder has its derivatives of orders $0,\ldots,d-1$ zero at $t_0$.
Taylor's integral remainder gives smooth division by $(t-t_0)^d$ there;
elsewhere division is ordinary. The remainder divided by $Z$ still has
compact support in the interval and extends by zero to a smooth test
on the line. Hence locally

$$
U(\phi)=\sum_{j=0}^{d-1} c_j\phi^{(j)}(t_0),\qquad
c_j=U\bigl(\psi(t)(t-t_0)^j/j!\bigr).
$$

In delta-derivative notation the coefficients are $(-1)^j c_j$. To
check the cap without assuming Sobolev admissibility of a point
supported distribution, take $\rho\in C_c^\infty((-1,1))$ equal to one
near zero and test with $\phi_{j,\epsilon}(t)=\epsilon^j
h_j((t-t_0)/\epsilon)$, where $h_j(y)=\rho(y)y^j/j!$. For sufficiently
small $\epsilon>0$ this is supported in the chosen interval. Its jet of
order $j$ at $t_0$ equals one, and all other derivatives there vanish.
For $0\le k\le r$,

$$
\|\phi_{j,\epsilon}^{(k)}\|_2
=\epsilon^{j-k+1/2}\|h_j^{(k)}\|_2.
$$

If $r\le j<d$, its $H^r$ norm tends to zero with $\epsilon$, so
$c_j=U(\phi_{j,\epsilon})=0$. At $r=2$ a simple zero leaves only a delta;
a double zero allows delta and first delta derivative, and higher
multiplicity adds nothing. The allowed jets really are continuous and
independent locally, by the $H^1$ bound and the same bump interpolation.

On any bounded open interval with compact closure, only finitely many
zeros occur. Choose disjoint localizing bumps equal to one near each
zero inside the interval, with support in its own zero neighborhood.
For tests compactly supported in the interval, subtract the localized
tests. The leftover test is supported off the zeros, where $U=0$;
each localized test contributes exactly the above jets with the
original derivative values. This finite identity also holds on
$H^r$ profiles compactly supported in the interval: Mollify the profiles
with support in a fixed compact neighborhood inside that interval;
$U$ and each of the finitely many jets are continuous in $H^r$.

Finally put $\chi_R(t)=\chi(t/R)$, with $\chi\in C_c^\infty(\mathbb R)$
equal to one on $[-1,1]$. Multiplying a common-kernel profile $u$ by
$\chi_R$ preserves its jets by Leibniz, so $U(\chi_R u)=0$ by the finite
identity. For $0\le k\le r$, the term $(\chi_R-1)u^{(k)}$ tends to zero
in $L^2$ by the $L^2$ tail bound, while every term differentiating
$\chi_R$ a positive number $l$ of times has norm bounded by a constant
times $R^{-l}\|u^{(k-l)}\|_2$. Thus $\chi_R u\to u$ strongly in $H^r$,
so $U(u)=0$. Closed subspace separation proves the reverse inclusion.
No uniform separation, summability of local coefficients, or convergence
of an unlocalized series of delta derivatives was used. This is a
local-division version of the annihilator argument used in the
[rational singleton](trace-spectral-q.md#trace-and-cutoff-limit).

## Projection and scope

Applying the lemma and the two inherited theta inclusions gives the
claimed equality. The orthogonal complement of the common kernel is
the closed span of the jet Riesz representers in the transported norm,
hence it is the actual projected range on $B$. The proof also applies
on this same block at any fixed real twist $a$ and even singleton
index $s=2r\ge2$: The two theta inclusions cover those parameters,
Plancherel transports the binomial norm, and an integer $j$ satisfies
$2j+1<2r$ exactly when $j<r$.

**Independent review:** `capped-jet-review` (agent `SEmCIHk`, transcript
in Yah session `01a2042e-4adf-7569-bc48-e2ee1955c560`) checked that the
inherited rendered readings apply to the singleton twist, quotient,
ambient weight, left-action block, bilinear sign, cap, and completed
$L$-function. No consequential source cross-reference was unresolved;
the reviewer did not reinspect the rendered pages. The review checked
both theta inclusions and the nonzero-entire input, local smooth division,
the shrinking-bump cap at simple and multiple zeros, the fixed-compact
approximation and strong cutoff exhaustion, the actual projection,
and the integer-index generality independently. A Lean transfer still
needs a normed closure and localization argument: The pinned Mathlib's
`MemSobolev` is a membership predicate on tempered distributions.

Selector Yah `01a2042c-b3df-7fe7-977a-0dbf29434b14`; worker Yah
`01a2042e-4adf-7569-bc48-e2ee1955c560`.

**Next bounded check:** For the [actual trace-class operator](trace-spectral-singleton-qi.md)
with $b\in C_c^\infty((0,\log 2))$, test the compression to jets with
$|t|\le N$. Use finite bump interpolation and the Leibniz matrix for
multiplication by $m(t)=\mu_1(G^1)\mathcal F_+b(t)$, then check the
trace-norm limit using strong convergence of the finite jet projections.
This would decide whether the actual singleton trace is the absolutely
convergent sum of $\min(d_t,2)m(t)$, without a basis of canonical lifts.

**Separate open premises:** Nonvanishing on a specified support, the
printed kernel and its convergence, the local-to-global diagonal
comparison, and positive-width density. None is inferred from jet
totality.
