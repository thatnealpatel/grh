# A signed packet in a doubly logarithmic window

The [global buffered obstruction](buffered-mark-obstruction.md) gives an explicit finite-radius necessary zeta zero at *every* high-mass mark. Here is a different, asymptotic test. It uses **no fixed zero-free strip**. It applies both to the marked sign and, at a failing high endpoint, to the first harmonic without searching the other seven.

Write $V=R^2$, $D=\log V$, $t\asymp e^{R/3}$, and let $s=\pm1$. The assertion holds for real cutoffs as well as frozen integers. Define $b=f+s g$, $h=B(z)\overline{B(\bar z)}$, as in the global proof. Fix a sufficiently small absolute $\epsilon>0$ and put

$$ g_\epsilon(z)=\exp(1-\cosh(\epsilon z)),\qquad J=(2/\epsilon)\log D. $$

At $x=\gamma-t$, $u=1/2-\beta$, put $\mathcal B_J=\{\rho: |x|\le J,\ |u|>0.1/D\}$. Use multiplicities. Define the signed charge for the tested sign by

$$ Z_s(t)=-\frac1{2R}\sum_{\mathcal B_J}\Re[h(x+iu)g_\epsilon(x+iu)]. $$

For all sufficiently large buffered marks, $Z_s(t)>0.24$. Moreover, for the [failure of a real twist at the named high endpoint](sampled-principal-peaks.md#if-the-first-harmonic-barely-passes-price-the-third), take $V=X(q)$ and **always** take $t=2q^{3/5}$, $s=+1$. At every sufficiently large such failure, $Z_+(t)>0.233$. These are implications, not examples. The window and the large-cutoff threshold may have large constants. This is not a finite-height exclusion based on an unspecified smoothing constant.

## Price the smoothing on the original prime side

Apply the translated zeta formula to $F(z)=(h g_\epsilon)(z-t)$, with both factors translated. In the strip $|\Im z|\le1$, $|g_\epsilon(z)|=\exp(1-\cos(\epsilon\Im z)\cosh(\epsilon\Re z))$; the test is entire and has the required decay for $\epsilon<1/4$. The inverse transform is $e^{-itv}(K*k_\epsilon)(v)$, where $K$ is the autocorrelation of $b$ and $k_\epsilon(w)=\epsilon^{-1}k(w/\epsilon)$, $\int k=1$. As in the [filtered ramp](localized-principal-packet.md#a-filter-with-a-priced-prime-side-error), shifting the inverse transform of $\exp(1-\cosh x)$ by $\pm i$ bounds $|k(w)|\ll e^{-|w|}$. This signed kernel is not used as a probability measure.

The autocorrelation vanishes outside $[-D,D]$ and is Lipschitz with constant $\le\|b\|_\infty\operatorname{TV}(b)\le4$ by the $L^1$ translation bound for functions of bounded variation. At a fixed shift $w$, $|K(\log n-w)-K(\log n)|\le4|w|$, and for $n>Ve^{|w|}$ both vanish. Chebyshev and partial summation give $\sum_{n\le Y}\Lambda(n)/\sqrt n\ll\sqrt Y$. Hence replacing $K$ by $K*k_\epsilon$ in the prime sum after division by $2R$ costs

$$ \ll \int |k_\epsilon(w)|\,|w| e^{|w|/2}dw\ll \epsilon $$

uniformly in the tested height, cutoff, sign, and small $\epsilon$. This bound also justifies absolute convergence and interchange with the convolution. It uses the original arithmetic weights including prime powers, not a phase variation estimate on the zero sum. The same-half and prime-power corrections on the unsmoothed prime side are $o(1)$ by the analytic tail in the global proof.

On the real axis $0\le hg_\epsilon\le h$. Bound the archimedean excess over $\log(t/(2\pi))$ using the **nonnegative pointwise upper bounds** in the [translated formula](verified-height-principal-band.md#translated-formula-with-a-finite-error). Thus the excess is $O((1+\log t)/t)$ before division, and the main term uses a mass divided by $2\pi$ of at most $2(1-1/R)$. The pole evaluations are $o(1)$ after normalization. The prime sum enters the explicit formula with a minus sign; it follows that

$$ s\Re S_V(t)\le \tfrac13+O(\epsilon)+o(1)-\frac1{2R}\sum_\rho\Re[(hg_\epsilon)(x+iu)]. $$

## Price the complement of the packet

Throughout $|u|\le1/2$ the test satisfies $|h(x+iu)|\le16 e^{D|u|}\min(1,x^{-2})$ by the centered support and integration by parts. The completed zeta identity of the global proof at $2+it$ gives the sharper asymptotic $W_2=\frac12\log(t/(2\pi))+O(1)=R/6+O(1)$ (absolute Euler convergence). In particular $\sum_\rho\min(1,x^{-2})\le 2.5W_2$. Outside $J$, $|g_\epsilon(x+iu)|\le\exp(1-D^2/4)$ and $e^{D|u|}\le R$. The entire normalized outer charge is $O(R\exp(1-D^2/4))=o(1)$, without dropping any off-line pairs.

Inside $J$, if $|u|\le0.1/D$, the global proof gives $-\Re h(x+iu)\le0.064\min(1,x^{-2})$. Uniformly in real $x$, $g_\epsilon(x+iu)=g_\epsilon(x)+O(\epsilon/D)$ there: Differentiate the analytic multiplier and use its double-exponential decay throughout $|\Im z|\le1$. Since $0<g_\epsilon(x)\le1$ and $e^{D|u|}\le e^{0.1}$, the normalized negative cost on this near-line set is at most

$$ 0.064\,\frac{2.5W_2}{2R}+o(1)=\frac1{75}+o(1). $$

Consequently $Z_s(t)\ge s\Re S_V(t)-1/3-1/75-O(\epsilon)-o(1)$. At a mark the signed value is at least $0.587-o(1)$, leaving $0.240333\ldots$ before smoothing. At a high endpoint failure use the moving cutoff: Reality forces $\mathbb E|\cos(q^{3/5}\log p)|\ge8/9-o(1)$ under the normalized weights. The double angle identity and Cauchy–Schwarz force $\Re S_V(2q^{3/5})\ge47/81-o(1)$, leaving $0.233580\ldots$. Choose $\epsilon$ small **before** taking the large-cutoff limit, retaining both strict constants. No GRH for the twist or external $7/8$ strip was used.

For example at the mark, reflection at the same ordinate gives the weaker absolute necessity

$$ \sum_{|\gamma-t|\le J,\ \beta>1/2+0.1/D}\frac{V^{\beta-1}}{1+(\gamma-t)^2}>\frac{0.24}{32\exp(1-\cos(\epsilon/2))}. $$

Indeed $|g_\epsilon|\le\exp(1-\cos(\epsilon/2))$ on the zero strip, $\min(1,x^{-2})\le2/(1+x^2)$, and $e^{D|u|}/R=V^{\beta_{\rm right}-1}$ on each pair. At the named failure replace $0.24$ by $0.233$. If one also invokes the [external $7/8$ strip](fixed-strip-endpoints.md#what-supplies-the-hypothesis), each factor $V^{\beta-1}$ is $\le V^{-1/8}$ and the lower bound becomes $\gg V^{1/8}$ on inverse-square weighted counts. That last translation needs the strip; the signed requirement does not. Compared with the earlier short packet, this trades horizontal reach for a signed price and removes the strip from the primary implication.

## Decision for a high endpoint

Use the **single** smoothed signed charge at $2q^{3/5}$ rather than a uniform bound on eight unsigned counts if testing the named failure. Do not infer that the same failure requires equally large packets at two or more harmonic centers. For instance take an abstract wrapped Gaussian angle $\Theta$ obtained by reducing $N(0,2\log(3/2))$ modulo $2\pi$ and put $U=|\cos(\Theta/2)|$. Its mean is at least $(2/3)^{1/4}>8/9$ by taking the unwrapped cosine first. Its moments $\mathbb E T_{2j}(U)=\mathbb E\cos(j\Theta)=(2/3)^{j^2}$ are below $1/3$ at **every** $j\ge2$. Thus the angular-mean datum alone cannot force a second harmonic above even the archimedean baseline. This is a phase law, not a prime sequence. In the more restrictive branch $\Re S_V(2q^{3/5})\le7/12+o(1)$, the cited two-mode lemma does force a second, negative peak at $6q^{3/5}$ and the same packet subtraction applies there.

Here is one phase restriction that does not require an ordinate count. At the named failure $s=+1$, the centered $b$ is even and nonnegative, so $h(z)=B(z)^2$. For $|x|D\le1.5$ and $|u|\le1/2$,

$$ \Re B(x+iu)=\int b(v)\cos(xv)\cosh(uv)\,dv>0,\qquad |\Im B(x+iu)|\le\tan(0.75)\Re B(x+iu). $$

This uses $|v|\le D/2$ and $|\sinh(uv)|\le\cosh(uv)$. Consequently $|\arg B|\le0.75$, and the multiplier has a choice of argument $-\sinh(\epsilon x)\sin(\epsilon u)=O(1/D)$ there. Since $1.5<\pi/2$, $\Re(hg_\epsilon)\ge0$ on this central interval eventually. Thus a packet *centered exactly on the witness*, however far off the critical line or numerous, cannot by itself pay the charge. The full $0.233$ is still required from $1.5/D<|\gamma-t|\le J$ in the positive test (and from the negative-real-part terms there if one drops the others). This particular hole is not asserted for the negative sign.

A unit zero count or an averaged zero-density bound does not price the signed sum at a prescribed exception. The explicit Poisson majorant alone allows order $R$ in the local inverse-square count, versus the required order $V^{1/8}$ even with the external strip. For the remaining annulus, test the phases of the **right-hand reflected pairs** using the actual transform $B$: Determine whether enough negative charge must come from alternating bands in $(\gamma-t)D$ rather than the full annulus. Keep the complex phase of $g_\epsilon$, and price the complement in the same normalization before discarding it. The existence of any such packet, or a uniform upper bound incompatible with it, remains open.

**After Work:** For the prescribed positive first harmonic the [even-tent Mellin test](opposite-phase-bands.md) now gives explicit opposite phase bands and prices their signed imbalance on right zeros alone, without a fixed strip. Test that imbalance rather than decomposing $B$ as a prerequisite. The two tests have different weights; retain the present test for the marked sign and its own signed charge.
