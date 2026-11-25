# Theta outputs: Zero samples versus norm closure

**Claim.** Vanishing at every open-strip zeta zero does not make a theta output zero. It
can obstruct density only in a topology where the samples are continuous. Keep the range
of the *input derivative profile* separate from the closure of the *convolved outputs*.

**Checked foundation.** Use even $f\in C_c^\infty(\mathbb R)$ supported away from zero
with $\int f=0$, and put
$$
H_f(v)=e^{-v/2}\sum_{n\ge1} f(ne^{-v}),\quad
h_f(t)=e^{-3t/2}f'(e^{-t}),\quad K(v)=e^{-v/2}\{e^v\}.
$$
Lean proves $H_f=K*h_f$ (positive sign, no reflection). At the origin, the theorem
requires $f(0)=0$, not support away from it. Lean also proves absolute
integrability and the value $-\zeta(s)/s$ of $\int_0^\infty \{x\}x^{-s-1}\,dx$ for
$0<\Re s<1$, and constructs a countable complex-linearly independent family of
actual two-ray outputs with all open-strip zeta-zero samples zero. On $1<u<2$, for seeds
supported in $1<|x|<2$, the two-ray sum reduces to $2f(u)$, so disjoint balanced bumps
give diagonal evaluations. In our convention,
$$
T_g(s)=\int_{\mathbb R}g(v)e^{(1/2-s)v}\,dv,\qquad
T_{H_f}(s)=\tfrac12\int_{\mathbb R}\mathrm{rationalTheta}(f,e^x)e^{sx}\,dx.
$$
The latter normalization uses $x=-v$. Lean states the independence and samples for the
unnormalized sum; the change of coordinate and nowhere-zero multiplier preserve
independence.

**Calculation on paper: Input versus output.** Write $X_a=L^1(e^{a|v|}dv)$ and
$M_b h=\int e^{bt}h(t)\,dt$. Substitution gives
$M_bh_f=\int_0^\infty x^{1/2-b}f'(x)\,dx$. The exact input range on compact tests is
$M_{1/2}h=M_{-1/2}h=0$: The inverse is $f(x)=\int_{-\log x}^\infty e^{t/2}h(t)\,dt$ for
$x>0$, extended evenly. The first moment gives compact support, and the second gives
balance. The only possible continuous input annihilators restrict on tests to linear
combinations of the two independent exponential densities. Both are bounded relative to
the weight exactly at and above $a=1/2$; below it neither tail allows a nonzero
combination. Thus the input closure is all of $X_a$ for $0\le a<1/2$, and the two moment
kernels for $a\ge1/2$. In unweighted $L^2$ neither exponential combination belongs to
the dual, so the input range is dense there too.

For outputs, $T_K(s)=-\zeta(s)/s$ in the open strip, and
$T_{h_f}(s)=-s\int_0^\infty f(x)x^{s-1}\,dx$. Since $|K(v)|\le e^{-|v|/2}$, weighted
Fubini applies for each strip sample with $a=|\Re s-1/2|$. Density of the inputs there
shows that exactly the strip zeros give evaluations that vanish on every output. In
unweighted $L^1$, only the line samples are continuous among these evaluations, and the
known line zeros make the output closure proper. In $L^2$, Fourier evaluation is not
continuous: The convolution multiplier is analytic near the real axis and is nonzero
almost everywhere (it is positive at frequency zero). Plancherel and the dense input
range give dense outputs in $L^2$.

**Endpoint restart on paper.** Write $f=g'$ on the positive axis with
$g(x)=x^{1/2}\phi(-\log x)$ for arbitrary compact smooth $\phi$. Then
$h_f=(\partial_v^2-1/4)\phi$. Although $K\notin X_{1/2}$, $H_f$ has bounded left support
and decays faster than every exponential on the right by even Poisson summation with
$f(0)=\widehat f(0)=0$. Unfolding for $\Re s>1$, integrating by parts, and continuing
gives the entire identity $T_{H_f}(s)=(1-s)\zeta(s)T_\phi(s)$. In $X_{1/2}$, the
interior jets $T^{(j)}(\rho)$ for $j<\operatorname{ord}_\rho\zeta$ annihilate the
closure: Their densities divided by the weight are bounded by
$|v|^j e^{-\min(\Re\rho,1-\Re\rho)|v|}$. These span
**all finite exponential-polynomial annihilators** in the bilinear integral pairing. For
densities $\sum_s P_s(v)e^{(1/2-s)v}$ the weight allows only strip exponents, including
the boundary, and constant polynomials on the boundary (a nonzero leading trigonometric
polynomial cannot tend to zero). At finitely many distinct points, the jets of $T_\phi$
are independently free by independence of exponential monomials. Multiplying by
$(1-s)\zeta(s)$ therefore kills just the low jets at its zeros. The multiplier has no
zeros on the strip boundary, including $s=0,1$, where its values are $-1/2,-1$ after
pole cancellation.

**What it does not show.** The endpoint closure is contained in the joint jet kernel,
not identified with it. Next, prove that every continuous annihilator in
$e^{|v|/2}L^\infty$ is in the weak-$*$ closed jet span, or find one outside it.
Holomorphic division of the sample transform by the multiplier does not give norm
approximation.

**Source.** Checked in
[`FractionalPartZetaMellin.lean`](../../Proofs/Lemmas/FractionalPartZetaMellin.lean),
`Masullo.integrableOn_fract_mul_cpow` and `Masullo.integral_fract_mul_cpow`;
[`RationalThetaFractionalPart.lean`](../../Proofs/Theorems/RationalThetaFractionalPart.lean),
`Masullo.rationalThetaNormalized_exp_neg_eq_integral_logKernel`; and
[`RationalThetaIndependentNull.lean`](../../Proofs/Theorems/RationalThetaIndependentNull.lean),
`Masullo.exists_rationalTheta_linearlyIndependent_mellin_null`. The norm-closure and
finite-jet calculations above are paper arguments for this compact-input model.
