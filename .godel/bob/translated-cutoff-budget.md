# How much can another translated mask save?

At scaled depth $c=1.90$, **seven is the least possible maximum radial order** on the zero-answer path in the translated-mask moment comparison. The [five-shift price](masked-cutoff.md) suffices at order seven. For the converse, there is one limiting model in which the original angular mean exceeds $8/9$, every first-order translated ramp has its correct signed price for that prime-phase assignment, and **every** translated measurement of orders two through six is zero. The shallow side uses the same ordinate, depth, and angle law for all those comparisons. The result concerns maximum order, not number of measurements, and is not a construction of zeta zeros.

## Match all first prices, not just a norm bound for one price

Use the notation of the [long-cutoff identity](long-cutoff-moments.md): $z=D-\log p$, $w_0=1/2+ix$, $k=|w_0|^{-2}$, and $\mu(dx)=k(x)\,dx/(2\pi)$, a probability. At any fixed order $j$ allow a fixed finite real combination of shifts $s$, with prime coefficients $A_s$ and multiplier $H(x)=\sum_s A_s e^{s w_0}$. The real symmetric masks are included, but no positivity is needed here. In the limiting shallow comparison, boundary depths $d=\pm c$ with equal probabilities give the signed value

$$ -\frac{\cosh(jc)}3\int \Re\{H(x)\,m_j(x)\}\,d\mu(x),\qquad m_j(x)=\mathbb E[e^{ij\phi}\mid x]. $$

Indeed, before taking real parts the rational carrier in the residue is $k(x)e^{-2ij\arg w_0}$, with $e^{ijDx}$ supplying the rest of $e^{ij\phi}$. The multiplier of each shift on the shallow window is $e^{sw_0}+O_{s,c}(1/D)$. These are the fixed-test, small-smoothing limits, not uniform estimates for a growing collection of shifts. The relaxation retains the trace marginal $\mu$ and uses conditional circle laws for the limiting fast phase. It does not impose a microscopic zero count or assert this freedom on the actual divisor.

Take the explicit step law $a(z)$ of [the one-height Fourier witness](common-filter-depth.md#why-not-optimize-the-cutoffs-to-reach-1226). In the abstract prime assignment set $\cos(t\log p)=a(D-\log p)$; the half-angle absolute cosine is then $\sqrt{(1+a)/2}$. The phase-free PNT on the fixed slabs gives the certified angular mean $>8/9$ in the limit. Write $J(z)=e^{-z/2}a(z)$ and use $\widehat{F}(x)=\int F(z)e^{-ixz}\,dz$. For a first-order weight $f(z)=\sum_s A_s(z+s)_+$, put $F=e^{-z/2}f$. Its transform is $H(x)/w_0^2$. By Plancherel (both $F,J\in L^2$), its signed first prime price is

$$ \int f(z)a(z)e^{-z}\,dz = \int \Re\{H(x)G(x)\}\,d\mu(x),\qquad G(x)=\frac{\bar w_0}{w_0}\,\overline{\widehat J(x)}. $$

The first-order tent-to-ramp and smoothing errors vanish in the iterated limit as in the five-shift proof, by linearity for each fixed list. Thus it suffices to set $m_1(x)=-3G(x)/\cosh c$. Keeping this **complex value** rather than its norm matches all first prices simultaneously. The modulus is bounded using the same jump polynomial as before, now checked against $C=.61655$ instead of $.6167$. The polynomial has periodic modulus; folding to $|x|\le8\pi$ only decreases the denominator $|w_0|$. The [checker](check-common-filter.py) encloses the squared modulus on the full interval, not a grid of ordinates. The smaller constant matters: At order six and $c=1.90$, the allowable cap is $\cosh(1.90)/(6\cos(\pi/8))= .6165543\ldots$.

## One conditional circle law for the remaining orders

Let $n\ge2$ be fixed and $b_n=1/(2\cos(\pi/(n+2)))$. If $3C/\cosh c\le b_n$, then $|m_1(x)|\le b_n$ everywhere. At each $x$ use the [tilted grid](finite-cutoff-budget.md) of $n+2$ angles $(2l+1)\pi/(n+2)$ with masses $(1-2|m_1(x)|\cos\theta)/(n+2)$. It has first complex moment $-|m_1(x)|$ and moments two through $n$ zero by the roots-of-unity sum. Rotate by $\arg(-m_1(x))$ (zero rotation at $m_1=0$). The first moment is now the required $m_1(x)$; all the zeros persist **conditionally on $x$**. Integrating any of the translated multipliers gives zero through those higher orders, even if different masks are used at each order. If $3C/\cosh c\le1/2$, the density $(1+2\Re(m_1(x)e^{-i\theta}))/(2\pi)$ instead kills all orders $j\ge2$ in a single law.

These zero answers also match the prime assignment, not just the circle matrices. The same $a$ vanishes for $z<-12/8$. Only primes up to $e^{12/8}V$ contribute. For each fixed $j\ge2$ and fixed translates, the **whole smoothed** spline is $O_{j,\epsilon,H}(1+D^j)$ in supremum norm by its unsmoothed bound and the smoothing kernel's bounded $L^1$ norm. Chebyshev therefore prices those primes at $O_{j,\epsilon,H}((1+D^j)R^{1-j})=o(1)$ after division by $R^{j+1}$. Prime powers cost $o_\epsilon(1)$ by the long-cutoff truncation for sufficiently small fixed $\epsilon$. No replacement of the long prime sum by an unsmoothed ramp at its growing endpoint is involved.

## When changing the first mask does save an order

For a sufficient test at $1.95$, form the **difference** shifts of the [nine-point filter](common-filter-depth.md): Let $h_i=i/10$ for $-5\le i\le3$ and let $p_i$ in that order be $(1,4,8,12,15,16,17,17,10)/100$. At each order call the resulting signed sum $T_j$. Use shift $s=h_i-h_l$ with coefficient $p_i p_l e^{h_l}$, grouping equal shifts and smoothing the whole weight. Then $H(x)=|\sum_i p_i e^{h_i w_0}|^2\ge0$ and $I_H=\int H\,d\mu=\sum_{i,l}p_i p_l e^{\min(h_i,h_l)}$. The latter identity uses the characteristic function $e^{-|s|/2}$ of $\mu$. The older **sum** shifts would not give this real multiplier. The [prime floor calculation](masked-cutoff.md#five-shifts-and-their-first-price) applies to these positive ramp coefficients without modification: With $f(z)=\sum_{i,l}p_i p_l e^{h_l}(z+h_i-h_l)_+$ use $P=2(8/9)^2/(\int_0^\infty z^2e^{-z}/f(z)\,dz)-\sum_{i,l}p_i p_l e^{h_i}$. The [piecewise ball calculation](check-masked-cutoff.py) gives $P>.55279649$ and $I_H<.90445972$.

Apply the matched-mask comparison, not the unmasked second-moment formula. At $c=1.6065$ the shallow limiting upper price on $T_2$ is $I_H\cosh(2c)(1-2(3P/(I_H\cosh c))^2)/3<-.00028$, so **$T_2\ge-.00027$ forces depth $>1.6065$** under the same failure and error hypotheses. For $c=1.95$, take the positive sine vector at $n=13$ and its coefficients $s_j$ as in the finite-cutoff proof. Under shallowness the limiting upper price on $\sum_{j=2}^{13}s_j T_j/\cosh(jc)$ is

$$ I_H/3 - 2\cos(\pi/15)P/\cosh c < -.00012, $$

with strict room to absorb errors. Thus thirteen orders suffice instead of fifteen; the price is seventeen shifts rather than five. This is a smaller maximum endpoint, not a measured runtime saving. Both implications concern a zero with $|\gamma-t|\le(2/\epsilon)\log D$, including the center, for sufficiently small fixed $\epsilon$ and sufficiently large failures.

| Depth | Compatible zero answers for all translated masks | Consequence on that path |
|---|---|---|
| $1.616$ | Order 2 | The doubled cutoff alone cannot force this target in the relaxation; the difference-shift test works at $1.6065$. |
| $1.90$ | Orders 2 through 6 | Use the signed order-7 price; do not search for a different order-6 mask. |
| $1.95$ | Orders 2 through 10 | The necessary maximum order is at least 11 and at most 13; this comparison leaves a gap. |
| $1.983$ | All higher orders | No fixed finite translated-mask prefix separates on this path. |

The upper-order sufficiencies use the same height and original angular datum, with their indicated masked **signed** measurements and their strict margins. The obstructions are feasibility statements about limiting information, not converse zero theorems, effective conductor thresholds, or bounds at a surviving sample. Reopen the decision if measurements are nonzero, if additional arithmetic data restrict the phase assignment, or if the test uses more than these fixed-translate limiting comparisons. In particular, a signed order-six test can still decide particular nonzero data.
