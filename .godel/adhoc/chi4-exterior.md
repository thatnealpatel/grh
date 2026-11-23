# What a positive supported Weil floor buys on the whole frequency line

Let $m$ be the frozen conductor-four symbol from [the window certificate](chi4-circle-window.md) at diameter $11/5$: It contains the signed atoms at $\log 3,\log 5,\log 7,\log 9$, the last with amplitude $-2\log 3/3$. The same symbol applies at $9/4$. There exists a finite, zero-mean cosine polynomial $E$ with **rational coefficients and rational shifts in $[2.24,10^6)$** such that $m(y)+E(y)>10^{-9}$ on the entire real line. Its shifts annihilate every autocorrelation from an interval of length $11/5$, or even $2.24$. They need not annihilate those at $9/4$.

This is a construction by formula, not a tabulation of the coefficients. Its input is the whole-space lower certificate at $9/4$, not the finite trial upper bound. It expresses positivity already proved, rather than increasing the certified support. Below we give the general mechanism, the constants for this instance, and two much smaller correction classes that provably cannot work.

## Strict exterior duality at one fixed window

Write $\widehat f(y)=\int f(t)e^{-iyt}dt$ and normalize the line form by $dy/(2\pi)$. Suppose $m$ is real, even, $C^2$, has bounded second derivative, and satisfies

$$A\log(2+|y|)-B\le m(y)\le B+C\log(2+|y|),\qquad A>0.$$

Let $\lambda_D(m)$ be the infimum of its form over unit complex functions of finite logarithmic energy supported in an interval of length $D>0$. Then

$$\lambda_D(m)=\sup_E\inf_{y\in\mathbb R}(m(y)+E(y)),$$

where $E=\sum d_k\cos(t_k y)$ ranges over finite sums with $d_k,t_k$ rational and $t_k>D$. For the easy direction, a cosine adds the real part of a translate inner product, zero on these tests. For the other direction fix $c<\gamma<\lambda_D(m)$.

**Support slack.** With the symbol held fixed, $\lambda_L(m)\to\lambda_D(m)$ as $L\downarrow D$. Indeed, centered near-minimizers at shrinking lengths have uniformly bounded log energy and hence uniformly small Fourier tails. Bounded spatial support and Fourier tightness imply strong $L^2$ precompactness (Fourier truncation bounds translation differences uniformly). The limit of a convergent subsequence is unit and supported in the limiting interval. Lower semicontinuity, by Fatou after shifting $m$ to be nonnegative, and the lower logarithmic bound put this limit in the form domain with no increase in energy. Monotonicity gives the opposite inequality. The same compactness gives an actual minimizer at fixed $D$. No fixed finite $E$ attains the displayed supremum: $m+E$ grows at infinity and the Fourier transform of the nonzero compactly supported minimizer, being entire, cannot vanish on a real interval.

Choose $L>D$ with $\lambda_L(m)>\gamma$. To make the construction below qualitative, one can use $\phi(y)=\operatorname{sinc}^2(ay)$, where $\operatorname{sinc} z=\sin(z)/z$ with value one at zero. Its inverse Fourier transform has support length $4a$. First choose $a$ so this length is less than $(L-D)/2$ and $(1-\phi^2)(\gamma-m)_+$ is uniformly small. This is possible since the sublevel set is bounded and $\phi\to1$ locally uniformly as $a\downarrow0$. With $h>0$ rational, $P=2\pi/h$, form the even periodic function

$$b(y)=\gamma+\sum_{j\in\mathbb Z}\phi(y+jP)^2(m(y+jP)-\gamma).$$

For fixed $a$, the summands decay as $O((1+\log|y|)/|y|^4)$. As $P\to\infty$ the noncentral sum tends uniformly to zero on $[-P/2,P/2]$, by $|y+jP|\ge (|j|-1/2)P$. The central term plus $\gamma$ is bounded above independently of $P$, and outside the cell $m$ uniformly exceeds this bound plus one for large enough $P$. Hence $b\le m+\epsilon$ **globally**, with $\epsilon>0$ as small as desired by these successive choices. Take $h$ small enough also to choose $n$ with $D<nh$ and $(n-1)h+4a<L$.

**Positive completion.** Let $c_k=P^{-1}\int_{-P/2}^{P/2}(b-\gamma)e^{-ikhy}dy$. Unfolding the integral shows that the real Toeplitz matrix $(c_{i-j})_{0\le i,j<n}$ is strictly positive definite. Indeed, its quadratic form is $P^{-1}\int_{\mathbb R}(m-\gamma)|\phi(y)\sum_{j<n}z_je^{ijhy}|^2dy$. The expression inside the absolute value is the Fourier transform of a test supported in an interval of length at most $(n-1)h+4a$, nonzero if $z\ne0$. Its logarithmic energy is finite by the decay of $\phi$. Apply the supported floor on length $L$.

Give $e_0,\ldots,e_{n-1}$ this Gram matrix. The shift $e_j\mapsto e_{j+1}$ on the first $n-1$ vectors is an isometry by Toeplitz symmetry. Make it a real orthogonal operator $U$ by mapping the normalized projection of $e_{n-1}$ onto the orthogonal complement of its predecessors to the normalized projection of $e_0$ onto the orthogonal complement of its successors. Strict positivity ensures both projections are nonzero. The spectral measure $\mu$ of $U$ at $e_0$, on the circle parameterized by $e^{ihy}$, is positive and even; its moments $\mu_k=\langle U^ke_0,e_0\rangle$ agree with $c_k$ for $|k|<n$. Its mass is $c_0$, **not** one.

**One smoothing kernel on both sides.** Take $v(t)=\sqrt{2/T}\cos(\pi t/T)$ on $[-T/2,T/2]$, zero elsewhere, and $K(y)=|\widehat v(y)|^2/(2\pi)$. It is an even probability density. Its Fourier transform $\kappa$ is the autocorrelation of $v$, zero at and beyond $|t|=T$. By the zero endpoint values and Plancherel its second moment is $\|v'\|_2^2=\pi^2/T^2$. Define

$$E=\gamma-K*b+P\int\sum_{j\in\mathbb Z}K(\,\cdot-z+jP)\,d\mu(z),$$

where $K*b$ is ordinary line convolution with the periodic function. The last term is nonnegative and has Fourier coefficients $\kappa(kh)\mu_k$. Thus the constant and every mode with $|k|<n$ cancel; the kernel need not preserve any individual nonzero moment. Equivalently the exact real polynomial is

$$E(y)=2\sum_{n\le k<T/h}\kappa(kh)(\mu_k-c_k)\cos(khy).$$

Since $b\le m+\epsilon$ globally, evenness of $K$ and Taylor's inequality give

$$m+E\ge\gamma-\epsilon-\|m''\|_\infty\pi^2/(2T^2).$$

Choose $\epsilon$ small and $T$ large, then round the finitely many real cosine coefficients to rationals within the remaining slack above $c$. This proves the supremum identity without spectral factorization on the line. It does **not** prove strict positivity of its left side. The arithmetic symbol can be frozen separately at each requested window; the argument supplies no control on the lower bounds as the window grows.

## Instantiation with a flatter pulse

Take $L=9/4$, $\gamma=1.1\cdot10^{-9}$, $a=10^{-4}$, $h=10^{-11}$, $n=224000000000$, and $T=10^6$. Use $\phi=1-(1-\operatorname{sinc}^2(ay))^8$ in exactly the same construction. The polynomial in $\operatorname{sinc}^2$ has no constant term, so the inverse transform is supported on $[-16a,16a]$ (convolutions of at most sixteen intervals $[-a,a]$). The test width is now $(n-1)h+32a=2.24319999999<9/4$. The [circle certificate](chi4-circle-window.md) gives the required strict floor. Also $0\le\phi\le\min(1,8/(ay)^2)$.

Here are scalar details; [chi4-pulse-scalars.py](chi4-pulse-scalars.py) checks the numerical inequalities in SageMath ball or exact arithmetic. Write $p_j,t_j$ for the four cosine amplitudes and shifts. In the archimedean series $u=3/4+j$, $s=y/2$, the increment is the sum of $s^2/[u(u^2+s^2)]$. Comparing the decreasing summand with its integral gives bounds $I(y)$ and $I(y)+4/3$, where $I(y)=\tfrac12\log(1+4y^2/9)$. The value at zero before adding the atoms is $\pi/2-\gamma_{\rm Euler}-\log(2\pi)$. Thus

$$\log\max(1,2|y|/3)-5.85\le m(y)\le6+\log(1+|y|).$$

Twice differentiating the summand gives $4(2u)^{-3}(1-3r^2)/(1+r^2)^3$, $r=y/(2u)$. The resulting majorant is summable. First term plus integral yields $\|m''\|_\infty\le44/27+\sum|p_j|t_j^2<17$.

On the fundamental cell, if $m(y)<\gamma$ then $|y|<1000$ and $\gamma-m<6$. There $1-\phi^2\le2(ay)^{16}$ since $1-\operatorname{sinc}^2 z\le z^2$ for $|z|\le0.1$ (use $\sin z/z\ge1-z^2/6$). The central excess over $m$ is therefore below $12(0.1)^{16}$. For remote terms $z=y+jP$, use $m(z)-\gamma\le2|z|$ at $|z|\ge\pi/h$ and $|z|\ge(2|j|-1)\pi/h$. Their total is at most $256a^{-4}(h/\pi)^3\sum_{j\ge1}(2j-1)^{-3}<2\cdot10^{-16}$, by $\sum j^{-3}\le3/2$. On the cell $b<18$: For $|y|\le10^5$ use $6+\log(100001)$; beyond that use $64(6+\log(1+|y|))/(a|y|)^4$, decreasing and already smaller at the split. Allow $\gamma$ and the alias bound in both cases. Outside the cell $m>19$. Thus $\epsilon=2\cdot10^{-14}$ suffices everywhere.

There are fewer than $10^{17}$ cosine coefficients. Rounding each to the nearest multiple of $10^{-30}$ (either nearest at a tie) costs at most $5\cdot10^{-14}$ uniformly. The lower bound **after** rounding exceeds $1.0160\cdot10^{-9}$. The construction specifies the coefficients but has not evaluated the huge Gram matrix or the coefficient vector. The scalar checker is not a test on sampled values of a computed polynomial.

## Two restricted classes that cannot work

Run [chi4-exterior-cert.py](chi4-exterior-cert.py) with SageMath 10.9 Python and assertions enabled. It reads nonnegative integer weights, normalizes them exactly, and uses no optimization at verification time.

* **Arbitrary real shifts above $11/5$, total absolute coefficient mass at most $54$.** Take the mixture of centers in [chi4-exterior-spline.txt](chi4-exterior-spline.txt), convolved with four uniform variables on $[-1/12,1/12]$. Its mean symbol is below $-0.01208658$. The cosine moment is the weighted cosine sum times $\operatorname{sinc}^4(t/12)$. A mesh through $110$ with the second-moment interpolation remainder controls its absolute value; beyond $110$ the sinc tail suffices. The checker gives a uniform moment bound below $0.000219936$ and, using the unrounded bounds, $\inf(m+E)<-0.00021004827$.
* **Lattice $t=j/30$, $67\le j\le480$, arbitrary coefficient mass.** For the discrete measure in [chi4-exterior-lattice.txt](chi4-exterior-lattice.txt) let $r_j$ be its cosine moments and $H=2\sum r_j\cos(jy/30)$. On $[-30\pi,30\pi]$ normalized Lebesgue measure gives $H$ exactly the chosen moments. Add density $U-H\ge0$ there to the discrete measure, with $U\ge\sup H$ certified by mesh and curvature; divide by $1+U$. The new probability measure annihilates all the proposed cosines. If the original symbol mean is $q$, its new mean is bounded by $(q+U\langle m\rangle+\|m\|_\infty\|H\|_2)/(1+U)$, with the last norms on this cell. The checker gives $\inf(m+E)<-0.08023015$.

Neither obstruction bounds the unrestricted exterior supremum or disproves positivity of the supported form. They show why a successful small certificate requires more than rescaling the coefficients of the tested lattice or refining a mesh under the same mass cap.
