# Weighted prime carvings do not identify the local level

**Scope:** Rational trivial compact isotype, $S=\{\infty\}$, half twist
$a=1/2$, $0<\alpha<1/2$, and degree $s=2r\ge4$. The algebra and norm
estimates below are project mathematics, not Lean declarations. The
operator test only needs one interior zeta zero, not the converse of
jet annihilation or the full-measure hypothesis of the global trace repair.

## What the cited carving actually supplies

**Provisional source reading:** `pdftotext -layout` of the
[digest-matched PDF](../sources/masullo/README.md), pp. 480, 483–485, and
488–496. Theorem 11.1.2.1, (11.1.2.3–7), takes closures and their
intersection **after** multiplication by a fixed position cutoff on the
**zero line**. The expression on p. 483 passes to an $S$-local theta
profile under the lower position truncation $|g|>1/\Lambda$. Equations
(11.2.0.2–5) use the difference $g(x)-g(\pi_v^{-1}x)$ and place the
orbital functionals in the zero-line polynomial topology. The underlying
local difference is (5.3.1.1), p. 240; its closed range in the local Schwartz
topology does not settle the range in either Hilbert completion. The
[closed-range repair](trace-orbital-q.md#which-quotient-is-closed)
distinguishes the exact range from its Hilbert closure. The passage
from the quotient (11.3.1.3) to (11.3.1.4), pp. 493–494, introduces the
half twist and mentions an additional Paley–Wiener condition. The proof
of (11.3.2.1), pp. 495–496, uses a right stratum cutoff at fixed left
position cutoff and then invokes the orbital quotient and global inversion.
It does not prove uncut weighted norm convergence of the carvings. The
[literal same-chain right cutoff](trace-orbital-q.md#the-right-cutoff-erases-a-fixed-shell-in-the-literal-chain)
has a separate problem even before any change of topology. Theorem 12.4.1.1,
pp. 514–518, takes a joint limit for a local kernel; it does not supply
these missing weighted operator identifications.

## Uncut completion erases every finite carving

Put $x=\log|g|$, $w(x)=e^{2\alpha|x|}(1+x^2)^r$, and
$H=L^2(w(x)\,dx)$. For an even real-place Schwartz test $b$ with
$b(0)=\widehat b(0)=0$, write

$$
 u_b(x)=2e^{x/2}b(e^x),\qquad
 v_b(x)=2e^{x/2}\sum_{n\ge1}b(ne^x).
$$

The first is its half-twisted local periodization over $\{\pm1\}$, and
the second its half-twisted global theta profile. These global generators
suffice for the full geometric closure in this isotype by finite unit and
sign averaging: A compactly supported, locally constant radial finite
factor is a finite linear combination of indicators of rational balls.
Each ball sum is a real lattice sum after rescaling the real test. For
an adelic sum, the combined real factor inherits vanishing at zero from
the original sum's value there and vanishing integral from the product
of the real integrals and the finite volumes of the balls. See the
[rational generator reduction](trace-orbital-q.md#genuine-global-theta-lifts).
Let $G$ be the resulting closed span and $P$ its orthogonal projector. With
$S_d h(x)=h(x+d)$, both $S_d$ and $S_{-d}$ preserve $G$ by dilating the
real test. The operator norm satisfies
$\|S_d\|\le C_r e^{\alpha|d|}(1+|d|)^r$ by change of variables and
$1+(x-d)^2\le 2(1+x^2)(1+d^2)$.

For the inserted $p$-uniformizer, the difference in (11.2.0.2) becomes
$D_p=1-p^{-1/2}S_{\log p}$ on the **once-twisted** profiles. This is just
conjugation of $1-S_{\log p}$ by $e^{x/2}$ on theta inputs, and it removes
the terms with $p\mid n$ in $v_b$. The inverse is
$\sum_{j\ge0}p^{-j/2}S_{j\log p}$: The norms are summable by the
translation estimate and $\alpha<1/2$, and multiplication by $D_p$
telescopes on either side. Each partial sum preserves $G$, so the inverse
preserves $G$ as well. Thus for any finite prime set $F$, the range of
$D_F=\prod_{p\in F}D_p$ on $G$ is exactly $G$, and the closure of its
image on the unbanded theta inputs is $G$. Their cofinal intersection
is still $G$. If $W_Y$ is the closed global real band level, then
$D_FW_Y$ is closed, lies in $G$, and exhausts $G$ as $Y$ increases at
fixed $F$. This does **not** say $D_F W_Y=W_Y$ at a finite band.

Consequently the zero-line Euler quotient is not a nontrivial quotient
of these *uncut*, once-twisted, weighted carved closures. In the
positive-sign Mellin coordinate $z$, the weighted difference multiplier
is $1-p^{-1/2-z}$, with its Euler zeros on $\Re z=-1/2$, outside the
closed relative strip. This explains the distinction without replacing
the zero-line orbital construction with a zero trace. If this particular
uncut Hilbert filtration is used to define the shells, their projections
are all equal after the band limits, at every fixed position cutoff.
That tautological vanishing is **not** vanishing of the input-indicator
pieces of the indented diagonal in (11.3.1.4).

## What a fixed window hides

For finite $F$ containing every prime $<Q$, one has the pointwise identity

$$
 v_F(x):=D_Fv_b(x)=2e^{x/2}
 \sum_{\substack{n\ge1\\ p\nmid n\ (p\in F)}} b(ne^x).
$$

The terms other than $n=1$ have $n\ge Q$. The resulting Schwartz tail
bound gives $v_F\to u_b$ locally uniformly. It even gives weighted
**Mellin** convergence over some growing position windows. Choose a
shifted interior zero $z_0=\rho_0-1/2\ne0$, and put
$\beta=\Re z_0$. The jet $J(h)=\int e^{z_0x}h(x)\,dx$ is continuous on
$H$ and zero on $G$; see the checked
[`rationalThetaWeightedLog_closure_subset_ker`](../../Proofs/Theorems/RationalThetaJetClosure.lean)
with $m=0$, after multiplying by the square root of the weight to enter
the Lean $L^2(dx)$ chart. For $R=\kappa\log Q$, $0<\kappa<1$, and $N$
sufficiently large,

$$
 \int_{-R}^\infty e^{\beta x}|v_F(x)-u_b(x)|\,dx
 \ll_{b,N,z_0} Q^{1-N+\kappa(N-1/2-\beta)}=o(1).
$$

Indeed the error in the profile is at most a constant times
$e^{(1/2-N)x}\sum_{n\ge Q}n^{-N}$, and the integral at $+\infty$
converges for $N>1/2+\beta$. If $J(u_b)\ne0$, the integral of the jet
of $v_F$ over $x<-R$ tends to $-J(u_b)$, since its total jet is zero.
But the dual norm of the jet on that tail is at most
$C e^{-(\alpha+\beta)R}(1+R)^{-r}$, by integrating
$e^{2\beta x}/w(x)$ there. Hence for large $Q$,

$$
 \|\mathbf 1_{x<-R}v_F\|_H\ \gtrsim_{b,z_0}\
 Q^{\kappa(\alpha+\beta)}(1+\log Q)^r.
$$

In particular, local convergence in the carving proof cannot be upgraded
to boundedness in the uncut weighted Hilbert topology. The divergence
is on the far **negative** log tail; a fixed annular position cutoff
removes it. To choose a witness, take an even bump $h$ off zero whose
local Mellin integral at $1/2+z_0$ is nonzero (use a narrow bump near
$+1$ and its reflection). Use $b(t)=h(t)-c h(ct)$ for any $c>1$. This
preserves vanishing at zero, makes $\int b=0$, and multiplies the
nonzero Mellin integral by $1-c^{1/2-z_0}\ne0$. One can impose any
prescribed real band $[-Y,Y]$, $Y>0$: First use the [two-mode Fourier band
approximation](trace-orbital-q.md#checked-density-of-real-band-weighted-theta-levels)
in Schwartz topology to keep a nonzero local Mellin value, then dilate
by a sufficiently small positive factor. This dilation rescales the
Mellin value by a nonzero scalar. For a witness at any positive width
one may use a nonzero-ordinate critical-line zero, by Hardy's classical
theorem; no assertion that all zeros are on the line is needed.

## The above-one control in the corrected order

Take $A_f$ to be log convolution, $(A_f h)(x)=\int f(y)h(x-y)\,dy$.
For $f=\psi'$ with a sufficiently narrow nonnegative nonzero
$\psi\in C_c^\infty((0,\log 2))$, one has $\int f=0$ and
$\widehat f_{\rm M}(z)=-z\int e^{zy}\psi(y)\,dy\ne0$ at both $z_0$
and $+1/2$. Narrow support keeps the phases inside an open half-plane
for the first value. Convolution takes each of $u_b$, $v_b$, and $v_F$
to the same respective construction on

$$
 b_f(t)=\int f(y)e^{-y/2}b(e^{-y}t)\,dy.
$$

This preserves the two moments and the additive band: On the support of
$f$, $e^{-y}<1$, so each dilated test has no frequencies beyond the
original band. Fubini gives $J(u_{b_f})=\widehat f_{\rm M}(z_0)J(u_b)\ne0$.
Thus even **after** the causal convolution the pointwise carving has
the same lower-tail escape, while the actual local level of (11.2.1.6)
in the rational real model contains $u_b$.

There is also a test at a **single fixed position cutoff** that does not
use a choice of lifts. Let $L_Y$ be the orthogonal projector onto the
local level in the project strip norm, and let $Q_*$ be any orthogonal
projector in $H$ whose range is in $G$, including the projectors onto
$D_FW_{Y'}$.
Apply the operators to the same $u_b$ in the local band $Y$. Then
$L_Yu_b=u_b$, whereas $A_f Q_*u_b\in G$ because convolution preserves
$G$. In particular $PA_fQ_*=A_fQ_*$, with the terminal $Q_*$ retained.
All these global outputs have norm at most $M=\|A_f\|\,\|u_b\|$. Choose
$R_0$ so $M\|J\mathbf 1_{|x|>R_0}\|$ and
$|J(\mathbf 1_{|x|>R_0}A_fu_b)|$ are each less than
$|J(A_fu_b)|/4$. For any smooth annular norm cutoff $\rho$ equal to one
on $|x|\le R_0$, the truncated jet gives

$$
 \left|J\left(\mathbf 1_{|x|\le R_0}M_\rho
              (A_fL_Y-PA_fQ_*)u_b\right)\right|
 \ \ge\ \tfrac12|J(A_fu_b)|>0.
$$

The bound is uniform over the finite global carving sets and levels,
and over position cutoffs equal to one on this window. In particular
these global localized operators do not converge to the specified local
one on their common weighted log chart, despite convergence of the
carved **vectors** on compact windows. This also handles a left local level projector before position cutoff:
Causality gives $A_f u_b=u_{b_f}$ in the same local level. The estimate
concerns ambient operators on one input, not the equality or inequality
of their scalar traces. It neither evaluates the missing
$-\widehat f_{\rm M}(1/2)$ nor
identifies the shell operators of (11.3.1.4) with our projected ranges.
A trace comparison by some other transport is not excluded.

## Next comparison and checks

For the next scalar comparison, start with the explicit
[clopen finite-unit fundamental window](trace-orbital-q.md#the-right-cutoff-erases-a-fixed-shell-in-the-literal-chain)
and point-mass indentation. It puts the entire corrected Haar diagonal
in $S$ by construction. This is a **specified replacement lift**, not
the literal (11.3.2.2) or a proof that other indented lifts have zero
orbital trace. At a common good width, the
[corrected level-first, position-second trace](trace-hardy-diagonal-q.md#removing-the-order-defect-in-the-weighted-rational-isotype)
in this lift is $-Z_\alpha(f)$, with $Z_\alpha$ the weighted strip zero
sum. The [specified joint local level limit](trace-joint-local-q.md#above-norm-one-the-defect-is-a-single-mellin-moment)
is $J_f-\widehat f_{\rm M}(-1/2)$. The exact remaining residual to
compute, including the sign of the desired correction, is

$$-Z_\alpha(f)-J_f+\widehat f_{\rm M}(-1/2)+\widehat f_{\rm M}(1/2).$$

Use the classical full rational explicit formula with the same Haar
normalization as an independent diagnostic for this lift: The
[full-versus-strip comparison](trace-to-zeros.md#full-versus-positive-width-sums-on-the-same-tests)
identifies the residual as $Z_{\rm full}(f)-Z_\alpha(f)$, since there are
no finite prime powers in the support. Ask whether this omitted-zero
distribution is detectable on mass-zero tests supported in $(0,\log 2)$;
do not infer that short-window agreement implies global agreement.
This diagnostic is not an independent geometric derivation of zero
residual. The actual source lift, its orbital trace, and the derivation
of $-\widehat f_{\rm M}(1/2)$ with compatible cutoffs remain open.
Neither local level exhaustion nor a projected weighted prime carving
justifies changing the cutoff order in this calculation.

**Review:** Independent Yah review (`carving-review`) verified the
pp. 480, 483–485, and 493–496 extraction locators, norm-summable inverse,
quantitative escape (including the sign and exponent), and the uniform
fixed-window operator test. These comparisons use a common positive-width
ambient model; the review did not verify a rendered page or identify
these operators with the manuscript's indented shell traces.

**Lean interface:** In the pinned Mathlib, `isUnit_one_sub_of_norm_lt_one`
and `summable_geometric_of_norm_lt_one` apply after a suitable power of
$p^{-1/2}S_{\log p}$ has norm $<1$. In the unweighted `Lp` chart of
`rationalThetaWeightedLog`, the required continuous linear translation
is $h(x)\mapsto [\sqrt{w(x)}/\sqrt{w(x+d)}]h(x+d)$; using unweighted
translation alone would give the wrong carving. The jet above is
already checked in that chart. The project results in this handoff have
not been elaborated in Lean.
