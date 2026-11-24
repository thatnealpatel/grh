# A high-endpoint failure needs an imbalance between opposite phase bands

At the [real high-endpoint failure](sampled-principal-peaks.md#if-the-first-harmonic-barely-passes-price-the-third), put $R=(9/5)\log q$, $V=R^2$, $D=\log V$, and $t=2q^{3/5}=2e^{R/3}$. Its arithmetic consequence is $\Re S_V(t)\ge47/81-o(1)$, where $S_V(t)=V^{-1}\sum_{p<V}(\log p)\log(V/p)p^{-it}$. Conjugating the phase does not change this real part. Use that sum directly. In particular, no hypothesis on zeros of zeta beyond the classical critical strip and its symmetries is needed.

For fixed sufficiently small $\epsilon>0$, put $g(s)=\exp(1-\cos(\epsilon s))$, $J=(2/\epsilon)\log D$. For each nontrivial zeta zero $\rho=\beta+i\gamma$, put $x=\gamma-t$ and define

$$ w_\rho=\frac{V^{\beta-1}|g(\beta+ix)|}{\beta^2+x^2},\qquad
\phi_\rho=xD+\sin(\epsilon\beta)\sinh(\epsilon x)-2\arctan(x/\beta)\pmod{2\pi}. $$

Let $E$ consist **only of right zeros** with $\beta>1/2+0.1/D$ and $1.5/D<|x|\le J$. All sums use multiplicity. At every sufficiently large failure,

$$ \sum_{E} w_\rho(-\cos\phi_\rho)>0.24. \tag{1} $$

In particular **for some** $0.02/R\le h<1$ the weight in $E$ with $\cos\phi_\rho<-h$ exceeds that with $\cos\phi_\rho>h$ by more than $0.24$. These are alternating phase bands of the *same width*, centered at $\pi$ and $0$ modulo $2\pi$. The radius $\arccos h$ need not be the same at different failures. This is not the charge of the [two-half test](short-buffered-packet.md): There is no additional division by $2R$ in (1).

## Use the unused half of the log axis

Extend the prime ramp to the even tent $F(v)=(D-|v|)_+$. On $v=\log n$ for every integer $n\ge1$ it is exactly the original ramp. Its bilateral transform $\int F(v)e^{sv}\,dv=(V^s+V^{-s}-2)/s^2$ is entire, including at zero. With

$$ K(s)=\frac{V^s+V^{-s}-2}{V s^2}g(s), $$

integrate $-(\zeta'/\zeta)(s+it)K(s)$ on the upward line $\Re s=2$, with factor $1/(2\pi i)$. The Euler series and inversion give $V^{-1}\sum_n\Lambda(n)n^{-it}(F*k_\epsilon)(\log n)$: As in the [signed smoothing proof](localized-principal-packet.md#a-filter-with-a-priced-prime-side-error), $k_\epsilon(w)=\epsilon^{-1}k(w/\epsilon)$ has transform $g$, integral one, and $|k(w)|\ll e^{-|w|}$. This follows by shifting the inverse Fourier contour of $\exp(1-\cosh u)$ by $\pm i$; continuation gives the bilateral transform in $|\Re s|<1/\epsilon$. The sign convention is immaterial for the two even transforms. Since $F$ is 1-Lipschitz, the unsmoothed and translated weights differ by at most $|w|$ and are both zero for $n>Ve^{|w|}$. Chebyshev gives a smoothing cost $\ll\int |k_\epsilon(w)|\,|w|e^{|w|}\,dw\ll\epsilon$, uniformly for $0<\epsilon<1/4$. This absolute estimate allows the signed convolution; the phase is not translated. The unsmoothed prime powers with exponent at least two cost $O(D^2/\sqrt V)$ by Chebyshev, summing $O(D)$ exponents at prime cutoff $\le\sqrt V$.

Shift to $\Re s=-1/4$. For clarity write $K_a(\beta,x)=(a-\beta)/((a-\beta)^2+x^2)$ and $W_a(t)=\sum_\rho K_a(\beta,\gamma-t)$ for $a>1$. The [completed Hadamard identity](endpoint-zero-packets.md#price-the-part-near-the-critical-line) gives $W_2(U)=\tfrac12\log(2+|U|)+O(1)$ and hence $O(\log(2+|U|))$ zeros in $|\gamma-U|\le1$. On the slab $[-1/4,2]$, subtraction of the logarithmic derivatives at $z$ and $2+i\Im z$ as in the [horizontal contour proof](strip-edge-height.md) leaves the nearby zero terms in $\zeta'/\zeta(z)$ with error $O(\log(2+|\Im z|))$ at large $|\Im z|$. The distant differences are $O((\Im z-\gamma)^{-2})$ per zero. Take horizontal sides with $t+\Im s$ at distance $\gg1/\log(2+|t+\Im s|)$ from ordinates, available by the unit count. At fixed $t,V$ these sides vanish by the resulting squared-log bound, the $s^{-2}$ factor, and $|g|\le e$ on the slab. This does not move $t$. On the new vertical the functional equation and absolute Euler convergence at $5/4$ give $|\zeta'/\zeta(-1/4+iU)|\ll\log(2+|U|)$, including bounded $U$ since the Gamma factors have no singularity there. The integral costs $O(V^{-3/4}\log(2+t))=o(1)$ by $\log(2+|t+y|)\ll\log(2+t)+\log(2+|y|)$ and inverse-square integration.

The pole gives $+K(1-it)=O(t^{-2})$; there is no kernel pole and no trivial zero crossed. Each nontrivial zero contributes $-K(\rho-it)$. For $0\le\beta<1/4$, write the tent factor as $V^{s-1}[(1-e^{-Ds})/s]^2$. The quotient has modulus $\le D$ by its integral over $[0,D]$ and $\le2/|x|$ for $x\ne0$. These zeros cost $O(D^2V^{-3/4}W_2(t))=o(1)$ since $(1+x^2)^{-1}\le2K_2(\beta,x)$. For $\beta\ge1/4$ the two unwanted numerator terms $V^{-s}-2$ have modulus $\le3$ in total, and $|s|^{-2}\le16/(1+x^2)$. Dropping them costs $O(W_2(t)/V)=o(1)$. These comparisons also give absolute convergence at fixed $V,t$. Taking real parts now gives

$$ \Re S_V(t)=\sum_{\beta\ge1/4}w_\rho(-\cos\phi_\rho)+O(\epsilon)+o(1). \tag{2} $$

In particular the plus sign on the $\sinh$ term is required by $\Im(1-\cos(\epsilon s))$. The implicit constant on $\epsilon$ is independent of small $\epsilon$.

## Spend one Poisson budget, not two

Write $c=0.1$, $G=\exp(1-\cos\epsilon)$, $\sigma=1+1/D$. Then $|g(\beta+ix)|\le G$ and $W_\sigma(t)\le R/6+O(D^2+1)$ by the same completed identity, Stirling, and absolute Euler convergence ($\sum (\log n)n^{-\sigma}\ll D^2$). Also $W_2(t)=R/6+O(1)$. Use $W_\sigma$ on the following **disjoint** sets, without an ordinate restriction.

* On $N=\{|\beta-1/2|\le c/D\}$ reflect at the same ordinate. Uniformly in $x$, $K_\sigma=(1+O(1/D))/(2(1/4+x^2))$ and $(\beta^2+x^2)^{-1}=(1+O(1/D))/(1/4+x^2)$. The average of $V^{\beta-1}$ over a reflected pair is at most $\cosh(c)/R$; a line zero has $1/R$. Thus $\sum_N w_\rho\le(2G/R)(\cosh c+O(1/D))\sum_N K_\sigma$.
* On $L=\{1/4\le\beta<1/2-c/D\}$ charge each zero to **itself**, not its right companion. For $b=1/2-\beta$ and $d=\sigma-\beta\ge\beta$, the ratio $(d^2+x^2)/(d(\beta^2+x^2))$ is at most $d/\beta^2$. Thus $Rw_\rho/(G K_\sigma)\le e^{-Db}(1/2+b+1/D)/(1/2-b)^2$. The log derivative of the last expression in $b$ is at most $-D+2+8<0$ eventually, so the ratio is at most $2e^{-c}(1+O(1/D))$ by evaluation at $c/D$.

As $e^{-c}<\cosh c$, the combined payment is $\sum_{N\cup L} w_\rho\le G\cosh(c)/3+o(1)$. This pays all left companions that occur in (2), even those of right zeros we keep. On $\beta\ge1/4$ we also have $w_\rho/K_2\le |g|\,V^{\beta-1}(2-\beta)/\beta^2\le |g|$ eventually: The log derivative of the last $\beta$-factor is $D-1/(2-\beta)-2/\beta\ge D-9$ and the factor is one at $\beta=1$. Hence the $|x|>J$ tail costs at most $\exp(1-D^2/4)W_2=o(1)$. For right zeros at $|x|D\le1.5$ the real representative of $\phi$ in the definition has $|\phi|\le1.5+O(1/D)<\pi/2$, so deleting them can only increase the signed charge. Equation (2) gives

$$ \sum_E w_\rho(-\cos\phi_\rho)\ge47/81-G\cosh(0.1)/3-O(\epsilon)-o(1). $$

For the band assertion let $H(h)=\sum_E w_\rho(\mathbf1_{\cos\phi_\rho<-h}-\mathbf1_{\cos\phi_\rho>h})$. Its integral from zero to one is exactly the left side. The integral on $[0,0.02/R]$ is at most $(0.02/R)G W_2$ by the same $K_2$ comparison. The remaining lower bound tends, as the smoothing error vanishes, to $47/81-\cosh(0.1)/3-0.02/6>0.2419$ (for instance bound the cosh series after its quadratic term by a geometric tail). Fix $\epsilon$ small enough **before** taking $R\to\infty$ to retain a strict $0.24$ margin on that integral. Its length is at most one. This proves (1) and the stated existence of $h$; it does not give a fixed positive gap in cosine independent of $R$.

**Next test.** Price the *difference* $H(h)$, or its integral, at the one prescribed height. A large unsigned count in the negative-cosine bands could be matched in their opposite bands and would not decide (1). Conversely a uniform bound $H(h)\le0.24$ on $[0.02/R,1)$ at all large candidate failures would exclude them. The discarded near-line and far-left terms require no further conjectured cancellation. No bound of the required size on this right-hand imbalance, effective height threshold, or actual failing twist is proved here.
