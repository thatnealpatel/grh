---
evidence_revision: 27a1adef92eeedd8260b7d54b2210277b74707fb
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

[prefix]: gaussian-singleton-corrected-kernel-series.md
[selected]: ../closed/gaussian-singleton-selected-cutoff-trace-norm.md
[jet totality]: ../../obligations/trace-theta-totality-qi.md
[zero count]: ../../obligations/trace-spectral-singleton-qi.md
[angular lift]: ../../obligations/trace-spectral-angular-qi.md
[Haar kernel]: ../../obligations/trace-spectral-singleton-kernel-qi.md
