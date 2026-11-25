# Signed Gaussian singleton head: proof and interval certificate

For the weight-four singleton over $F=\mathbb Q(i)$ at spectral parameters $a=1/2$, $I=\{0\}$, $s=4$, use the [Gaussian trace evaluation](../../obligations/trace-spectral-sum-qi.md). Its completed function is $L(s,\bar\eta)$, with $\eta([z,u])=(z/|z|)^4$. Write $\mathcal T$ for the distinct real ordinates of its zeros on $\Re s=1/2$, $d_t$ for their orders, and $w(t)=\min(d_t,2)$. Write $\mu=\mu_1(G^1)>0$ for the finite, positive volume of the compact norm-one group in the split quotient Haar $d\mu_1\,dx$, $x=\log|g|_F$. The bump is

$$
a_b=\frac{\log 2}{4},\qquad u=\frac{x}{a_b}-2,\qquad
b_0(x)=\begin{cases}e^{-1/(1-u^2)}& |u|<1,\\0& |u|\ge1.\end{cases}
$$

Use the unnormalized positive transform $\widehat b(t)=\int b_0(x)e^{itx}\,dx$. The operator test is $\varphi(g)=\eta(g)b_0(\log|g|_F)$. The spectral multiplier is $m(t)=\mu\widehat b(t)$, with no other factor. In the [raw counting-quotient Haar convention of (A.3.2.5)](../../obligations/trace-theta-density-qi.md#the-zero-modes-and-the-completed-mellin-factor), the complex polar density is $dx\,d\theta$, the product of finite unit masses is $1/2$, and the four diagonal units divide the norm-one mass by four, giving $\mu=\pi/4$. The result below keeps $\mu$ explicit and only uses its positivity.

**Result.** For $S_T=\sum_{t\in\mathcal T,\,|t|\le T}w(t)m(t)$, the real number $S_{8192}/\mu$ lies in $(-0.160,-0.078)$. More precisely it is within $0.040751$ of $-0.118965$, whereas the checked normalized tail is at most $425984/10^{12}$. This separates the full capped sum, and hence the actual character-corrected singleton trace, from zero. The interval argument also bounds the full normalized capped sum directly in $(-0.160,-0.078)$. This is computer-assisted ordinary mathematics: The tail estimate is in Lean, but the comparisons of normalizations, signed head and operator nonvanishing are not.

## Reproduction

Run both scripts in order on fresh copies, with ordinary Python (assertions enabled). `loc.py` uses 800-bit Arb/Acb balls and writes the `idx` bracket list alongside the script; `budget.py` uses 100-bit Arb balls. The bounds below are checked by whole-ball comparisons, not rounded display values. From the repository root, for example:

```sh
set -eu
run=$(mktemp -d)
cp .godel/adhoc/gaussian-singleton-head/loc.py \
   .godel/adhoc/gaussian-singleton-head/budget.py "$run/"
cd "$run"
python3 -m venv env
./env/bin/python -m pip install 'python-flint==0.9.0'
./env/bin/python -c 'import flint; assert flint.__version__ == "0.9.0"'
./env/bin/python loc.py
./env/bin/python budget.py
```

## The zero divisor and its normalization

For the numerical calculation use the $\pi$-scale profile (here $s$ is the complex Mellin variable, not the Sobolev index)

$$
q(x)=e^{5x/2}\sum_{\alpha\in\mathbb Z[i]}\alpha^4e^{-\pi|\alpha|^2 e^x},\qquad
\Lambda(s)=\int_{\mathbb R}q(x)e^{(s-1/2)x}\,dx.
$$

Lattice conjugation makes $q$ real on the real axis. In the Euclidean Fourier convention with phase $e^{-2\pi i\langle x,\xi\rangle}$, the transform of the homogeneous harmonic quartic times $e^{-\pi y|x|^2}$ is the same quartic times $i^{-4}y^{-5}e^{-\pi|\xi|^2/y}$. This follows by differentiating the Gaussian transform; harmonicity kills the lower-degree terms. Since $i^{-4}=1$ and $\mathbb Z[i]$ is self-dual in this Euclidean convention, Poisson summation gives $q(-x)=q(x)$. The lattice series is holomorphic in $|\Im x|<\pi/2$ by local uniform absolute convergence there, so the evenness holds on that strip too.

For $\Re s>1$, substitute $y=|\alpha|^2 e^x$ in each nonzero lattice term. Absolute convergence follows from $\sum_{\alpha\ne0}|\alpha|^{-2\Re s}<\infty$. Its integral is $(\alpha/|\alpha|)^4|\alpha|^{-2s}\pi^{-s-2}\Gamma(s+2)$. There are four generators per nonzero ideal and no phase variation among them. At a prime ideal $(\alpha)$ the positive finite uniformizer class has complex coordinate $\alpha^{-1}$ after division by the principal idele; thus its $\bar\eta$ value is $(\alpha/|\alpha|)^4$. All finite places are unramified. Consequently

$$
\Lambda(s)=4\pi^{-s-2}\Gamma(s+2)L_f(s,\bar\eta)=4\,2^{s+2}L(s,\bar\eta),
$$

where $L_f$ is the finite product and the $2\pi$-scale completed Gamma factor is that of the [Gaussian Mellin source interface](../../obligations/trace-theta-density-qi.md#source-interface). The $2\pi$-scale lattice integral `QuarticGaussianD` in the [Lean zero count](../../../Proofs/Lemmas/QuarticGaussianZeroCount.lean) equals $2^{-s-2}\Lambda(s)=4L(s,\bar\eta)$: Its profile is $2^{-2}$ times the $\pi$-scale untwisted profile at $x+\log 2$. Thus all three functions have the same zeros and orders, also after the affine change $s=1/2+it$. Neither the four generators nor the change of Gaussian scale multiplies the spectral multiplier or the cap.

The lattice bound below and evenness give double exponential decay on the real axis. In particular $\Lambda$ is entire, and for $|s|\le R$ the absolute Mellin integral is bounded by a constant times an integral of the form $\int_1^\infty y^{R+c}e^{-y}\,dy$ with fixed $c$. This gives $\log\max_{|s|\le R}|\Lambda(s)|=O((R+1)\log(R+2))$ and order at most one. Evenness gives $\Lambda(1-s)=\Lambda(s)$ and hence symmetry of the line ordinates with orders. The nonvanishing absolute Euler product and Gamma factor on $\Re s>1$, and reflection, confine the zeros to $0\le\Re s\le1$. No assertion that this divisor is all on the line is used.

## Locating a selected signed submultiset

Let $Q(t)=\Lambda(1/2+it)=\int q(x)e^{itx}\,dx$, real and even on the real line. With $y=e^{\Re x}\ge1$ and $|\Im x|\le1$, at most $(2\lfloor\sqrt n\rfloor+1)^2\le9n$ lattice points have squared norm $n\ge1$. Using $\pi\cos(1)>3/2$,

$$
|q(x)|\le9 y^{5/2}\sum_{n\ge1}n^3e^{-3ny/2}
\le 9 y^{5/2}e^{-y}\sum_{n\ge1}n^3e^{-n/2}.
$$

Here $3ny/2\ge n/2+y$ for $n,y\ge1$, the sum is less than $200$, and $\int_1^\infty y^{3/2}e^{-y}dy\le\int_0^\infty y^2e^{-y}dy=2<3$. Reflection gives the bound on the other half-line. The absolute integrals on the shifted contours $\Im x=\pm1$ are therefore less than $11000$. The same bound on vertical edges justifies shifting by $+i$ for $t\ge0$ and $-i$ for $t<0$, giving $|Q(t)|\le11000e^{-|t|}$. The displayed strip bound and Cauchy estimates give Schwartz decay of $q$ and its derivatives on the real axis. Poisson summation for the infinite trapezoid of $q(x)e^{itx}$ identifies its difference from $Q(t)$ with the aliases at $t+2\pi k/h$, $k\ne0$. At $h=1/256$ and $|t|<271$, their total absolute value is at most

$$
\frac{22000\,e^{271-2\pi/h}}{1-e^{-2\pi/h}}.
$$

Two further analytic errors enter the finite DFT:

- **Lattice shells.** For $0\le x\le6$, omitting $n>240$ in $q(x)$ costs at most $9e^{15}\sum_{n\ge241}n^3e^{-\pi n}$ per sample. Use even reflection before truncating for $x<0$. The weighted sum has $h(2\cdot1536+1)=12+h$ as its length factor; the shell series is bounded by its first term divided by $1-(242/241)^3e^{-\pi}$. The resulting error is less than $10^{-300}$.
- **Log samples.** On $x\ge6$, factor out $e^{-\pi e^x}$ in the shell bound and use $9\sum_{n\ge1}n^3e^{-(n-1)}<1000$. Then $|q(x)|\le1000e^{5x/2-\pi e^x}\le1000e^{-2e^x}$, since $5x/2<e^x$ there and $\pi>3$. For $x=6+kh$, $k\ge1$, use $e^x\ge e^6(1+kh)$ and sum a geometric series with ratio $e^{-2e^6h}$, including both signs and the factor $h$. This error is less than $10^{-300}$.

`loc.py` checks the two shell-series constants using $\sum n^3r^n=r(1+4r+r^2)/(1-r)^4$, and checks that the alias, shell and sample bounds together are less than $10^{-205}$. It sums the exact real lattice coefficients through $n=240$ (both coordinates are at most 15 in absolute value), evaluates the polynomial at $e^{-\pi e^{jh}}$, and zero-pads the even samples $h q(jh)$ of this truncation modulo 65536. The unnormalized finite DFT therefore encloses the finitely sampled transform at $t_j=j\delta$, $\delta=2\pi/(65536h)=\pi/128$. The sign of its Fourier phase is immaterial for the even samples. The DFT rounding error is already in the balls. Comparing the entire real-part balls to $\pm10^{-205}$ gives signs of the true transform, after all three analytic errors.

The test covers $j=1,\ldots,11001$ with $11001\delta<271$. It gives 298 disjoint open intervals $(t_{j-1},t_j)$ with opposite endpoint signs, starting at right index 308 and ending at right index 10996. Each encloses a real zero by continuity; select one there and one at its negative reflection, each once. No simplicity, uniqueness in a bracket, or completeness of this list is required. The same error test gives $Q(0)\in(0.15808,0.15809)$, so there is no central zero for this function.

## Bounding every omitted real term

For any zero $\rho$ of $\Lambda$, set $z=(\rho-1/2)/i$, so $|\Im z|\le1/2$. Define

$$
W(z)=\frac{1}{(1+z^2/900)(1+z^2/1600)}.
$$

For $z=t+iy$ and $A=30,40$, $\Re(A^2+z^2)=A^2+t^2-y^2>0$. The ratio $|\Im/\Re|=2|ty|/(A^2+t^2-y^2)$ is at most $|y|/\sqrt{A^2-y^2}<1$, by maximizing over $|t|$. The two denominators have arguments in $(-\pi/4,\pi/4)$, so $\Re W(z)>0$ even off the line. On the real axis $W$ is positive, even and decreases with $|t|$.

For the centered function $\Xi(v)=\Lambda(1/2+v)$, subtract its genus-one Hadamard logarithmic derivatives at $v=A$ and $v=-A$. These points are zero-free and neither the constant term in the derivative nor the genus-one counterterms survive. The order bound implies $\sum_\rho |\rho-1/2|^{-2}<\infty$ (also by Jensen at the nonzero center). Reflection gives $\Xi'(-A)/\Xi(-A)=-\Xi'(A)/\Xi(A)$, and each zero contributes $1/(A-iz)-1/(-A-iz)=2A/(A^2+z^2)$. Thus, with full orders,

$$
U_A=\sum_\rho\frac1{A^2+z^2}=\frac{(\Lambda'/\Lambda)(1/2+A)}{A},\qquad
\sum_\rho W(z)=\frac{1440000}{700}(U_{30}-U_{40}).
$$

This sum is real because the logarithmic derivatives on the right are real. At $s=1/2+A$ the derivative is $\psi(s+2)-\log\pi+L_f'/L_f(s)$; using $-\log(2\pi)$ here would use the wrong function for the centered reflection. A coefficient at $p^k$ of the finite logarithmic derivative has modulus at most $2\log p$, since the sum of the residue degrees over $p$ is at most two and all the phases are unitary. Thus the Euler term is real and has modulus bounded by

$$
2\sum_{n\ge2}n^{1-s}\le 2\left(2^{1-s}+\frac{2^{2-s}}{s-2}\right)<10^{-8}
$$

at both evaluation points. `budget.py` includes this uncertainty in the Arb evaluations.

Write $h(t)=1$ on the 596 selected ordinates and $h(t)=0$ otherwise. Then $0\le h(t)\le w(t)\le d_t$. For **any** subset $E$ of the real ordinates, the omitted weight satisfies

$$
\sum_{t\in E}(w(t)-h(t))W(t)
\le \sum_\rho \Re W(z)-\sum_{t\in\mathcal T}h(t)W(t)
\le \sum_\rho W(z)-2\sum_{j\in\texttt{idx}}W(t_j)<0.08577.
$$

The middle subtraction uses the *outer* bracket endpoints, giving lower weights than the chosen zeros. Off-line zeros only increase the upper bound; they do not occur in the target trace. This upper bound includes every unselected real zero and possible extra capped multiplicity at every selected one, also any zero exactly at $|t|=8192$. It requires no census up to that cutoff.

For real $t$, Fourier differentiation gives $|\widehat b(t)|\le W(t)M$, where

$$
M=\|b_0\|_1+(1/900+1/1600)\|b_0''\|_1+\|b_0^{(4)}\|_1/1440000.
$$

The script bounds these norms and $\|b_0'\|_1$ in the rescaled variable $u$. For $v=(1-u^2)^{-1}$, the derivatives of $e^{-v}$ are $P_k(u,v)e^{-v}$ with $P_0=1$ and $P_{k+1}=\partial_uP_k+2uv^2(\partial_vP_k-P_k)$. On $0\le u\le 1-1/256$ it sums the upper absolute ball ranges over cells of width $1/16384$. On the last strip $1-1/256\le u<1$, $v>128$ and $v^j e^{-v}$ decreases for $v\ge128$ and all monomial exponents $j\le8$ used here. Bounding each monomial by its absolute coefficient times $128^j e^{-128}$ covers that strip. The rescaling and parity multiply the half-line integrals by $2a_b^{1-k}$. The certified upper bounds at orders $0,1,2,4$ are $0.076943$, $0.736100$, $18.481922$, $226358.366$. The resulting $M<0.26623$ and the residual weight comparison give an absolute omitted Fourier budget less than $0.02284$ for any such subset $E$.

## Signed summation and tail comparison

A reflected pair contributes $2\int b_0(x)\cos(tx)\,dx$. At each bracket midpoint, `budget.py` uses the composite trapezoid on $[a_b,3a_b]$ with 4096 equal subintervals of length $\Delta x=2a_b/4096$; the two endpoint terms vanish. On a cell $[p,q]$ the integrated error is bounded by $\int_p^q (x-p)(q-x)|f''(x)|/2\,dx\le (\Delta x)^2\int_p^q |f''(x)|\,dx/8$. With $f(x)=b_0(x)\cos(tx)$ this gives the per-sign bound $(\Delta x)^2(\|b_0''\|_1+2t\|b_0'\|_1+t^2\|b_0\|_1)/8$ for $t>0$. It is doubled for the reflected pair.

To move from the midpoint to the chosen ordinate, differentiate in $t$ and use the Fourier transform of $xb_0$. Integration by parts twice gives

$$
|\widehat b'(t)|\le \min\!\left(3a_b\|b_0\|_1,
\frac{2\|b_0'\|_1+3a_b\|b_0''\|_1}{t^2}\right).
$$

Use the positive left endpoint in the denominator for a bound uniform over the entire bracket. Multiply by the half width $\delta/2$ and by two for the pair. The checked bounds, before the Haar factor, are:

| Quantity | Certified interval or strict upper bound |
| --- | ---: |
| Signed midpoint trapezoidal sum (both signs) | $(-0.118966,-0.118964)$ |
| Total location error | $0.01659$ |
| Total quadrature error | $0.00132$ |
| All omissions, including extra capped orders | $0.02284$ |

Both the head and full sum retain the selected terms, and the omitted-term bound can be applied in either domain. The three errors sum to less than $0.04075$; adding the midpoint-to-center difference gives $|S_{8192}/\mu+0.118965|<0.040751$. The same calculation directly gives the stated real interval for each sum; reality follows from reflection, equal caps, and conjugate Fourier values.

Independently of the global omitted-weight argument for the full sum, [`Masullo.quarticGaussianTail_bound`](../../../Proofs/Lemmas/QuarticGaussianTail.lean) gives the normalized absolute tail at $|t|>8192$, with both signs and the same cap and [bump](../../../Proofs/Lemmas/PositiveLogBumpDecay.lean). By the divisor identification above, this gives a budget $\mu\,425984/10^{12}$ in trace units. At $c=-0.118965\,\mu$ and $\varepsilon=0.040751\,\mu$ the separation margin is $|c|-\varepsilon-\mu\,425984/10^{12}=0.078213574016\,\mu>0$. This proves the separation required by the [tail card](../../conjectures/closed/effective-capped-tail-bound-singleton-gaussian.md). It does not establish the printed kernel, convergence of every coordinate prefix, a local-to-global diagonal comparison, or any positive-width trace identity.
