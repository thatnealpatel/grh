---
evidence_revision: 27a1adef92eeedd8260b7d54b2210277b74707fb
outcome: established
---

# Do four boundary probes control every Gaussian prefix?

Use the [all-prefix card][prefix] and the [selected-cutoff
landing][selected] with their exact weight-four singleton,
fixed $b_0$ and multiplier $m(t)=c\int b_0(x)e^{itx}\,dx$,
$c=\mu_1(G^1)$, signed real ordinates of the completed
$Z(t)=L(1/2+it,\bar\eta)$, and cap
$n_t=\min(\operatorname{ord}_t Z,2)$. Keep the original
convolution-first $PA$ and coordinate truncations $T_N$.
Each ordinate contributes all its allowed jets. Allow
all nondecreasing absolute-height orderings and ties,
including a prefix retaining only one sign at a height.
Let $r$ be the absolute height of the last retained
ordinate. Use the positive log Fourier $H^2$ input, the
transported $(1,2,1)$ derivative norm, the common-jet
kernel quotient, and the usual quotient and lift factors.
In the transported norm one may include the common
Plancherel scalar $c/(2\pi)$ in the squared norm.

Fix $\beta\in C_c^\infty((-1/2,1/2))$ equal to one near
zero. Use $b_{a,k}(t)=(t-a)^k\beta(t-a)$ for $a=+r,-r$
and $k=0,1$. For each probe form raw data $d_{t,l}$ on
all signed ordinates with $||t|-r|\le2$ and $0\le l<n_t$:
Use $(m b_{a,k})^{(l)}(t)$ at omitted ordinates and zero
at retained ones. Let $G$ be the Riesz Gram of these raw
jet evaluations in the indicated $H^2$ norm. Set $e_N$
to the maximum of the four finite Hermite minimum norms
$(d^*G^{-1}d)^{1/2}$, with an empty minimum norm zero.

**New implication:** Under the common-jet kernel,
multiplicity-counted Jensen bound, angular lift, and
accepted rapid selected-cutoff tail in [selected], test
whether there are $c_*,C_*>0$ independent of the prefix,
tie order, and gaps such that for every $M>0$ and all
sufficiently large last heights $r$,

$$
c_*e_N\le\|PA-T_N\|_{\rm op}\le\|PA-T_N\|_{\rm HS}
\le\|PA-T_N\|_1\le C_*e_N+O_M(r^{-M}).
$$

**Source and payoff:** The selected landing concerns one
unsplit sequence only. The new use is its rapid trace
tail above a prescribed prefix, with the [jet totality],
[zero count], [angular lift], and [Haar kernel] interfaces.
If true, the three norm limits for the original prefixes
are equivalent to $e_N\to0$. This would not establish
that $e_N$ tends to zero, or prove the all-prefix card.

**Discriminating test:** Retract the ambient value and
slope traces at both boundaries onto the four probes.
On the resulting common kernel of the traces, test the
zero extension of $m u$ from the strict exterior in
$H^2$, and compare all retained and omitted jets,
including a split tie. Test the finite difference with
the first specified selected cutoff at
$j=\lfloor r\rfloor+1$ by rank times operator norm, not
by a codimension argument; use the selected trace tail
for the rest. For the four probe outputs, compare global
quotient minima with the finite Gram minima by fixed
localization preserving every zero jet. Verify complex
Riesz and product-jet conventions, $Q=S^*$, and the
mixed output-first Haar kernel conversion. Use exact
model controls for split and unsplit close pairs, a
capped double jet, and failure of zero extension with
only the value trace zero. These are analytic controls,
not spacing evidence for the actual Gaussian ordinates.

[prefix]: ../open/gaussian-singleton-corrected-kernel-series.md
[selected]: gaussian-singleton-selected-cutoff-trace-norm.md
[jet totality]: ../../obligations/trace-theta-totality-qi.md
[zero count]: ../../obligations/trace-spectral-singleton-qi.md
[angular lift]: ../../obligations/trace-spectral-angular-qi.md
[Haar kernel]: ../../obligations/trace-spectral-singleton-kernel-qi.md

## Proof of the implication

**Identify the error before estimating it.** Let $H$ be the ambient
positive log Fourier space with squared norm
$\alpha(\|u\|_2^2+2\|u'\|_2^2+\|u''\|_2^2)$, $\alpha=c/(2\pi)$.
Let $D$ be the common kernel of the capped jets, $Q:H\to H/D$ the
quotient, and $S=Q^*$ its isometric lift. For the original prefix,
$E_N=S(I-B_N)\bar A Q$, where $B_N$ is the biorthogonal coordinate
sum, not an orthogonal projection onto the retained jet representers.
By biorthogonality it keeps precisely the selected coordinates of
$\bar A Q u=Q(mu)$. Hence $\|E_Nu\|$ is the minimum $H$ norm among
functions with zero jets at retained points and the jets of $mu$ at
omitted points: Equality of these raw jets determines the class by
[jet totality]. The coordinate factors $c i^{-l}$ are nonzero.

**The trace-norm remainder.** On $H$, let $L$ take the values and
first derivatives at both interfaces and let $J$ synthesize the four
probes in that order. Sobolev evaluation and translation invariance
bound $L$ and $J$ uniformly; disjoint supports and flatness near the
centers give $LJ=I$. Put $K=I-JL$. Both traces of $v=mKu$ vanish at
both interfaces, so $f=\mathbf 1_{\{|t|>r\}}v$ has weak derivatives
of orders one and two given by the corresponding exterior derivatives
extended by zero. Indeed, the boundary terms from integration by
parts are multiples of the value and slope traces. The product rule
and the Schwartz bounds through order two for $m$ give
$\|f\|_H\ll_M r^{-M}\|u\|_H$. Below the last height $f$ has zero jets,
above it $f$ has the jets of $v$, and at either boundary both jets
are zero, also the prescribed data if that sign is omitted. Thus $f$
represents the error class on $Ku$, even at a split tie. In particular
$\|E_N K\|_{\rm op}\ll_M r^{-M}$, without evaluating a quotient
representative at an unconstrained point.

For $j=\lfloor r\rfloor+1$ the pinned landing gives $r<R_j<r+2$ and
$\|E_{R_j}K\|_1\ll_M r^{-M}$ by the ideal inequality. The difference
$F=E_N K-E_{R_j}K=(T_{R_j}-T_N)K$ therefore has rapid operator norm.
Its range lies in the span of the added coordinate vectors, including
a missing sign at $r$ if present. Its rank is at most the signed
multiplicity count through $r+2$, hence $O((r+1)\log(r+2))$. Applying
$\|F\|_1\le\operatorname{rank}(F)\|F\|_{\rm op}$ with two extra powers
of decay, and adding back $E_{R_j}K$, gives
$\|E_N K\|_1\ll_M r^{-M}$. The rank estimate was used only on $F$.

**Four finite minima.** With the inner product linear in its first
slot, the representer of the raw jet $(s,l)$ is
$h_{s,l}(t)=\alpha^{-1}\partial_s^l g(t-s)$, where
$g(x)=(1+|x|)e^{-|x|}/4$. Indeed $(1-\partial_x^2)^2g=\delta_0$:
The homogeneous equation holds on either side, the first two
derivatives match, and the third has jump one. Integration against a
test function gives the value representer; differentiation in the
source gives the slope representer (both belong to $H$). The Gram
entry in row $(t,k)$ and column $(s,l)$ is
$\alpha^{-1}\partial_t^k\partial_s^l g(t-s)$, with the minus sign
for each source derivative. Any finite set of allowed jets is onto
as evaluation data, by polynomials times disjoint local bumps flat
at the nodes. Thus its Gram is positive definite. In the span of the
representers the interpolation equations are $Gz=d$; the orthogonal
complement contributes no data. The exact minimum squared is
$d^*G^{-1}d$ (zero for no constraints). For an omitted capped double,
$d_{t,1}=m'b+mb'$ at $t$. Replacing raw jets by normalized ones sends
$d,G$ to $\Sigma d,\Sigma G\Sigma^*$ with diagonal $\Sigma_{t,l}=c i^{-l}$
and preserves the quadratic form.

For a single probe $b$, write $p_b$ for the finite minimum norm.
Dropping constraints gives $p_b\le\|E_N b\|$. Conversely multiply
the finite minimizer by the sum of translates to $\pm r$ of a fixed
smooth cutoff equal to one on $[-3/4,3/4]$ and supported in
$(-3/2,3/2)$. This multiplier has uniformly bounded $H$ operator
norm by Leibniz. Wherever a probe can give nonzero jet data the
cutoff is identically one nearby. Elsewhere in the windows, zero
value is preserved, and zero slope when required stays zero because
the value there is zero too. Outside the windows the product is
locally zero. This is a global competitor, so $\|E_N b\|\le C p_b$.
The comparison constant does not involve the inverse Gram norm.

Now $e_N=\max_b p_b\le (\max_b\|b\|_H)\|E_N\|_{\rm op}$. In the other
direction $E_NJL$ is the sum of the four rank-one maps with outputs
$E_N b$ and coefficient functionals the corresponding rows of $L$.
Their trace norms sum to at most $C_* e_N$. Adding the rapid
trace-norm remainder $E_N K$ gives the upper bound. The intermediate
inequalities are the singular-value norm inequalities. The leading
constants are fixed independently of $M$, gaps, prefixes, and orders.

The lift identifies $E_N$ with the quotient error plus a zero block,
since $Q=S^*$ and $QS=I$; the other angular blocks also contribute
zero. For $\nu=w\mu$ the output-first Haar kernel is
$K_\mu(x,y)=w(y)K_\nu(x,y)$. Its squared mixed norm against
$w(x)w(y)^{-1}d\mu(x)d\mu(y)$ is exactly the squared HS error against
$\nu\otimes\nu$. Integration against Haar adds no reciprocal weight.
This is the convolution-first error for $PA$, not $AP$.

**Controls and decision.** At two simple model nodes distance $h>0$
apart and $\alpha=1$, the value Gram has diagonal $1/4$ and off-diagonal
$\rho/4$, $\rho=(1+h)e^{-h}$. Its inverse gives split energy
$4/(1-\rho^2)$ for $(0,1)$, versus $8/(1+\rho)$ for $(1,1)$.
Since $1-\rho^2=h^2-2h^3/3+O(h^4)$, the norms scale as $2/h$ and
$2$, respectively. At a single capped double the Gram is $I_2/4$.
For model $m=1+2i$, $m'=3-i$ at the omitted center, the flat and
slope probes give energies $60$ and $20$, respectively. Finally a
profile equal to $t$ near zero has zero value there, but its positive
side extended by zero has a unit delta in its second derivative.
This is why both traces are removed before gluing. None of these
controls is evidence about the actual spacings or multiplier values.

Along prefixes with last height tending to infinity, each of the
three error norms tends to zero if and only if $e_N\to0$. The proof
does not bound the latter on the Gaussian data, give a stable
numerical inversion, or establish the original all-prefix claim.
