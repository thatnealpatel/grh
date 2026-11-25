---
evidence_revision: fd9b420ec415046d03028c1929d0b349ac0f7426
outcome: established
---

# An effective capped-tail bound for the singleton Gaussian spectral trace

Let $\mathcal T\subset\mathbb R$ be the distinct real zeros of the completed $Z(t)=L(1/2+it,\bar\eta)$ over $\mathbb Q(i)$, let $d_t$ be the order at $t$, and set $w(t)=\min(d_t,2)$. This is the cap for the [character-corrected Gaussian singleton trace](../../obligations/trace-spectral-sum-qi.md) at $a=1/2$, $I=\{0\}$, $s=4$. With $\mu=\mu_1(G^1)>0$ the mass of the compact norm-one group in the split quotient Haar, put

$$
m(t)=\mu\int_{\mathbb R}b_0(x)e^{itx}\,dx,\qquad
M(R)=\sum_{t\in\mathcal T,\,|t|\le R}w(t),\qquad
S_T=\sum_{t\in\mathcal T,\,|t|\le T}w(t)m(t).
$$

Here $b_0(x)=e^{-1/(1-u^2)}$ for $|u|<1$, zero elsewhere, with $u=4x/\log 2-2$. The head includes a zero at $0$ if present and both cutoff endpoints; the tail is on $|t|>T$.

## Conditional analytic bound

Assume an explicit $C\ge0$ satisfies $M(R)\le C(1+R^2)$ for every $R\ge0$. For every integer $k\ge3$ and every $T>0$,

$$
\left|\sum_{t\in\mathcal T}w(t)m(t)-S_T\right|
\le |\mu|\,\|b_0^{(k)}\|_1
\left(\frac{C(1+T^2)-M(T)}{T^k}+\frac{2C}{k-2}T^{2-k}\right).
$$

Indeed, integration by parts gives $|m(t)|\le |\mu|\|b_0^{(k)}\|_1|t|^{-k}$ for $t\ne0$. On the strict tail, Stieltjes summation gives
$\int_{(T,\infty)}r^{-k}\,dM(r)=-T^{-k}M(T)+k\int_T^\infty M(r)r^{-k-1}\,dr$.
The boundary term at infinity vanishes since $k>2$. Inserting the majorant gives $(C-M(T))/T^k+kC T^{2-k}/(k-2)$, equal to the displayed expression. With its first term kept as $[C(1+T^2)-M(T)]/T^k$, the exact remaining coefficient is $2C/(k-2)$, not $kC/(k-2)$.

## Certified signed head and nonvanishing

For this bump the [checked quartic Gaussian tail](../../../Proofs/Lemmas/QuarticGaussianTail.lean), `Masullo.quarticGaussianTail_bound`, supplies an independent absolute tail budget on $|t|>8192$, in place of choosing $C$ above. It bounds the sum with both signs and the cap at two by $425984/10^{12}$ **without** the Haar factor. Its concrete $2\pi$-scale quartic Mellin transform is $4L(s,\bar\eta)$ in ordinary mathematics, so the zeros and orders agree. The error in trace units is $E_{8192}=\mu\,425984/10^{12}$.

The [reproducible signed-head certificate](../../adhoc/gaussian-singleton-head/certificate.md) establishes

$$
-0.160 < S_{8192}/\mu < -0.078,\qquad
|S_{8192}/\mu+0.118965|<0.040751.
$$

It brackets 298 positive zeros, selects one copy of each and of its reflection, and excludes a central zero. The signed midpoint quadrature sum is in $(-0.118966,-0.118964)$; the normalized location and quadrature errors are less than $0.01659$ and $0.00132$. Positivity of a resolvent weight over the whole zero strip bounds the remaining real capped contribution in absolute value by $0.02284$, including any other real ordinates, additional capped copies at chosen zeros, and zeros at $|t|=8192$. Off-line zeros consume weight in that bound but are not terms of the trace. No complete zero list, simplicity assumption or GRH input is used.

With $c=-0.118965\,\mu$ and $\varepsilon=0.040751\,\mu$, the strict separation is $|c|-\varepsilon-E_{8192}>0.078\,\mu>0$. Thus the full capped sum and the actual convolution-first singleton trace on this test are real and negative. The same omission bound also encloses the full normalized capped sum directly in $(-0.160,-0.078)$.

**Scope:** The absolute tail bound for the concrete transform is in Lean. The divisor and multiplier normalization, signed head (analytic bounds and `python-flint` interval computation), and identification and nonvanishing of the actual trace are ordinary mathematics, not a Lean endpoint. The result does not identify the printed kernel or establish a positive-width or local-to-global trace comparison.
