---
evidence_revision: a684299f2b54e602be826969b35b7c1f30742700
outcome: established
---

# Exact upper-cut band ranges after projected convolution

On the rational zero line let $E_Y$ consist of theta profiles of even real-place Schwartz inputs $b$ with $b(0)=\widehat b(0)=0$ and additive Fourier support in $[-Y,Y]$, $Y>0$. For a prime $p$, put $D u(x)=u(x)-u(x+\log p)$. Let $T=M_\rho P A_f Q_Y$ in the polynomially weighted space of degree $s\ge0$, where $Q_Y,P$ are the band and full even-image projections, $f$ is continuous and compactly supported in $[a,\infty)$ in log coordinates, and $\rho$ is bounded measurable and supported on $x\le R$. Then $T E_Y=T D E_{Y/p}$ as sets, without closure.

**Established in Lean:** [`Masullo.rationalTheta_projected_cutBand_image_eq`](../../../Proofs/Theorems/RationalThetaCutConvolution.lean) gives the equality; `rationalTheta_primeMasked_cutBand_image_eq` in the same file identifies the underlying pointwise masked range on the standard finite lift.

Choose $p^N>Y e^{R-a}$ and set $c=-\sum_{j=1}^N b(\cdot/p^j)$. Its band is at most $Y/p$. The difference telescopes, and Poisson summation kills the remainder throughout the input window sampled by the convolution. Both level inputs are fixed by $Q_Y$, and convolution preserves the full closed even image. The band is not a log-frequency bound. Unlike the [lower-cut result](rational-one-prime-post-cut-strictness.md), this is exact on generators, but it neither provides a uniform lift nor identifies the indented source kernel. See the [two telescope arguments](../../obligations/trace-cut-range-q.md).
