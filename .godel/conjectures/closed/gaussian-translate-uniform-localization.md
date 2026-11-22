---
evidence_revision: 022676f32fb32118354a025cb57b7c48d5dac9cf
outcome: refuted
---

# Local centers do not uniformly localize Gaussian superpositions

Fix $I=[-0.8,0.8]$, a nonempty open interval $J\subset I$, and $\sigma>0$. The claim tested was that some $c<1$ satisfies $\|1_{I^c}f\|_2\le c\|f\|_2$ for **every finite linear combination** of $g_t(x)=\exp(-(x-t)^2/(2\sigma^2))$ with $t\in J$.

**Refuted:** These translates span a dense subspace of $L^2(\mathbb R)$. If $h$ is orthogonal to the span, its convolution with the Gaussian extends to an entire function by Cauchy–Schwarz and locally uniform Gaussian domination. It vanishes on $J$, hence everywhere. The Gaussian Fourier multiplier never vanishes, so $h=0$. Approximating a unit bump supported outside $I$ now makes the exterior-to-total norm ratio tend to one.

Numerical illustration, not the proof: At $\sigma=0.2$ put $h=0.01/32$. The test combination was proportional to $e^{-x^2/(2\sigma^2)}\sinh(hx/\sigma^2)^{32}$; the binomial expansion uses 33 centers from $-0.01$ to $0.01$. Midpoint integration on $[0,4]$ by symmetry, at steps $0.0002$ and $0.0001$, gave an exterior **squared** mass fraction of $0.999809435$ to nine decimal places, versus about $1.54\times10^{-8}$ for the centered Gaussian alone. These are not certified quadratures. The density argument is on paper, not in Lean. It rules out uniform small-tail truncation of Gaussian combinations, not positivity of the [Weil cross term](weil-two-packet-all-separations.md).
