# Ordered inertia: translation balance does not bound the surviving charge

**Status.** The metric-translation identity below and its exhaustion estimate are for the whole rational positive-width **replacement** trace. The negative three-plane is for a proper restriction of its theta inputs, not for the unrestricted rational projector. The requested bound remains open. These are paper arguments, not Lean statements or an evaluation of a manuscript shell.

## Setup and test of the mechanism

Use the half twist and degree four of the [floor/Gram handoff](handoff.md). Write $a$ for the strip **half-width**, $0<a<1/2$, and use

$$H=L^2(w\,dx),\qquad w(x)=e^{2a|x|}(1+x^2)^2.$$

Take $a$ in the common full-measure set of [two-sided good widths](../../obligations/trace-theta-density-q.md#bounds-for-division-by-zeta), so we can ask for a bound along widths tending to zero without making a claim at zero. Let $V_B$ be the closure in this **full** metric of the profiles $v_d(x)=e^{x/2}\Theta(d,e^x)$ with $d$ even Schwartz, $d(0)=\widehat d(0)=0$, and $\operatorname{supp}\widehat d\subset[-B,B]$. Write $P_B$ for its orthogonal projector and $P$ for the projector onto the unrestricted closure $V$. The [cofinal band theorem](../../../Proofs/Theorems/RationalThetaBandClosure.lean) gives $P_B\to P$ strongly. Write $J=1-P$.

Fix any nonempty open interval $I$ with $\overline I\subset(0,(\log 2)/2)$. Tests $u,v\in C_c^\infty(I;\mathbb R)$ have mass zero. Put $f=u*v$ (ordinary convolution, **not** convolution with a reflection), $A_f b=f*b$, and $M_b(z)=\int e^{zx}b(x)\,dx$ for the exponential moment. For multipliers in physical position use the notation $m_\eta b=\eta b$. Then $f$ is supported in $(0,\log 2)$, has mass zero and $f(0)=0$. No finite prime-power or identity samples intervene. Use real, uniformly bounded compactly supported position cutoffs $\rho_R\to1$ a.e.; for a rate take $\rho_R(x)=\chi(x/R)$ with $\chi$ smooth, compactly supported and one near zero. The form in question is $G_a(u*v)$, where

$$G_a(f)=\lim_{R\to\infty}\ \lim_{B\to\infty}\operatorname{Tr}(m_{\rho_R} A_f P_B).$$

The right projection is retained. In the order with a left geometric projector as well, $P A_f P_B=A_f P_B$ by invariance of $V$, not by commutation. See the [order repair](../../obligations/trace-hardy-diagonal-q.md#removing-the-order-defect-in-the-weighted-rational-isotype). We use the existing result $A_fJ\in S_1$ in the original norm to control exhaustion, **not** its spectral value to infer a sign. In this normalization the [fixed-pulse note](../rational-strip-fixed-pulse.md) explains why index at most two for the **uncorrected** form is enough, and why that is not a bound at arbitrary fixed cutoffs. Relative to the positive-log joint local model the remaining full-formula pole is $-M_f(1/2)$, not $-M_f(-1/2)$; it is not added back here.

**Mechanism under test.** Since translating the weight moves only a cutoff difference into the trace, can exhaustion kill the interior metric shear and leave at most two negative coordinates, one for each end? The first part is true; the rank inference is false from this balance and the structural hypotheses used to prove it. To discriminate, impose a fixed finite number of linear conditions **inside the genuine two-moment band cores**. Test whether the balance still holds and whether the added quotient is invisible to the *ordered trace itself*, rather than merely invisible to its changes under translation. This differs from the [even separator](../../obligations/trace-even-separator-q.md): Neither metric clipping nor the joint local projection enters the test.

## The aggregate identity, band first

Let $S_h b(x)=b(x-h)$. The log weight is Lipschitz, so the translations are bounded on $H$, locally uniformly in $h$. They are strongly continuous by density of compact smooth functions. Rescaling $d$ to $d_h(y)=e^{-h/2}d(e^{-h}y)$ gives $v_{d_h}=S_h v_d$ and $\widehat d_h(\xi)=e^{h/2}\widehat d(e^h\xi)$; the two zero modes are preserved. Thus $S_h V_B=V_{Be^{-h}}$ and $S_h V=V$. Closed invariance under all $S_h$ implies invariance under $A_f$ by the vector-valued integral $A_fb=\int f(y)S_y b\,dy$.

For bounded compactly supported $\eta$, $T_\eta=m_\eta A_f$ is trace class with trace $f(0)\int\eta=0$. One direct check: Restrict the convolution input to a compact interval containing both the output support and its enlargement by $-\operatorname{supp} f$. Fourier inversion on the kernel $f(x-y)$ gives an absolutely trace-norm integrable sum of rank-one operators: Their two vectors before the scalar Fourier coefficient are $\eta(x)e^{itx}$ and $\mathbf 1_{\rm input}(y)e^{ity}/w(y)$ in $H$. Their norm product is bounded independently of $t$, and their traces are $\int\eta$. Strong convergence of the orthogonal $P_B$, and finite-rank approximation of $T_\eta$, now give $T_\eta P_B\to T_\eta P$ in trace norm. Only after this limit can we write

$$\operatorname{Tr}(m_\eta A_f P)=-\operatorname{Tr}(m_\eta A_f J).$$

This also proves existence of the position limit using $A_f J\in S_1$ and $m_{\rho_R}\to 1$ strongly. It is not a trace of the uncut $A_fP$.

Let $Q_{B,h}=S_hP_BS_{-h}$, the orthogonal projector onto $V_{Be^{-h}}$ **in the translated metric** $w_h(x)=w(x-h)$, and $Q_h=S_h P S_{-h}$, onto $V$ in that metric. At fixed $\rho$ each cutoff trace is defined, $A_f$ commutes with $S_h$, and conjugation by the bounded invertible $S_h$ gives

$$\operatorname{Tr}(m_\rho A_f Q_{B,h})=\operatorname{Tr}(m_{\rho(\cdot+h)} A_f P_B).$$

Now take the band limit at fixed $\rho,h$, using the unshifted trace-norm convergence on the right. Subtract the $h=0$ trace. The resulting identity, including the transition term, is

$$
\boxed{\quad
\operatorname{Tr}(m_\rho A_f(Q_h-P))
=\operatorname{Tr}(m_{\rho(\cdot+h)-\rho}A_fP)
=-\operatorname{Tr}(m_{\rho(\cdot+h)-\rho}A_fJ).
\quad}                                                     \tag{1}
$$

For scaled cutoffs the absolute value is bounded by $|h|\|\chi'\|_\infty\|A_fJ\|_1/R$. For any bounded exhaustion as above and fixed $h$, the multiplier on the right tends strongly to zero, and multiplication of $A_fJ$ on the left then tends to zero in trace norm. This proves cancellation of the *aggregate translated-metric difference* after exhaustion; neither end is discarded locally. Constants here need not be uniform as $a\to0$.

There is also an infinitesimal version directly in position. With $r_h=w_h/w$ and $C_h=P m_{r_h}|_V$, the normal equation gives

$$Q_h-P=C_h^{-1} P m_{r_h} J.$$

Here $C_h$ is bounded positive and bounded below on $V$. Every such displacement maps $JH$ into $V$ and kills $V$, so products of two displacements vanish. That is a block identity, not a rank bound. The derivative $\ell=(\log w)'=2a\operatorname{sgn}x+4x/(1+x^2)$ is bounded a.e. The difference quotients of $r_h$ converge a.e. to $-\ell$ with a uniform bound for small $h$, and $C_h^{-1}\to 1_V$ in norm. Hence $(Q_h-P)/h$ converges strongly, with uniformly bounded norms, to $-P m_\ell J$. Differentiate (1) at **fixed smooth compact** $\rho$ using the trace pairing with the fixed trace-class $m_\rho A_f$ (bounded strong convergence suffices for this scalar pairing). Both minus signs cancel:

$$\operatorname{Tr}(m_\rho A_f P m_\ell J)=\operatorname{Tr}(m_{\rho'} A_f J).     \tag{2}$$

This avoids differentiation of the cusp as if the weight were smooth. The position integration-by-parts edge is the right side, bounded by $\|\chi'\|_\infty\|A_fJ\|_1/R$ for the scaled exhaustion. In particular there is no nonzero limiting charge in this shear on **any** finite-dimensional space of tests: Apply the bound entry by entry for $f=u_i*u_j$. This conclusion is about the shear, not about the Gram matrix of $G_a$ itself.

## Discriminating check: a restricted genuine-band core

Choose a nonzero real band profile $v_0$ from a fixed band $B_0$. For example take $\widehat d$ on the positive axis to be a nonzero smooth compact function of integral zero in $(B_0/2,B_0)$, and extend evenly. The two zero modes vanish. The sampling formula of the handoff has only the $n=1$ term where $e^{-x}$ is in that interval, so $v_0\ne0$. By Fourier injectivity and continuity, $M_{v_0}(i\tau)\ne0$ on some open interval of positive $\tau$. Fix also any nonzero real mass-zero pulse $p\in C_c^\infty(I)$. Choose three distinct $\tau_j$ in this open interval avoiding zeros of $M_p(i\tau)$, possible since the entire transform $M_p$ is not identically zero. Both transforms are then nonzero at the negative nodes by reality. These choices are independent of the width. Put $\Lambda=\{\pm i\tau_1,\pm i\tau_2,\pm i\tau_3\}$.

For an integer $N\ge1$ restrict the actual band inputs by the conditions on their output profiles

$$L_{z,k}(b)=\int x^k e^{zx}b(x)\,dx=0,\qquad z\in\Lambda,\quad 0\le k<N.$$

All these functionals are bounded on $H$ by Cauchy–Schwarz ($|x|^{2k}/w$ is integrable). Denote the restricted band closures and projectors by $V_B^{[N]}$ and $P_B^{[N]}$. The restriction is not a modification of the weight, rescaling of the convolution, or deletion of one of the zero modes.

**Same-band correction.** For $0<h<1$, $S_hv_0$ is a genuine profile in band $B_0$. Its coordinate $L_{z,k}(S_h v_0)$ equals

$$e^{zh}\sum_{m=0}^{k}{k\choose m}h^{k-m}L_{z,m}(v_0).$$

For each $z$ the polynomials through degree $N-1$ are independent, with leading coefficients $M_{v_0}(z)\ne0$. Exponential polynomials at distinct exponents are linearly independent on an interval: Apply $\prod_{z'\ne z}(\partial_h-z')^N$ to isolate the $z$ block, where the resulting polynomial operator is invertible on polynomials of degree $<N$. Thus the coordinate vectors of these shifts span $\mathbb C^{6N}$, and finitely many genuine profiles in this one band give a right inverse for $L=(L_{z,k})$. Approximate in the original metric and subtract this right inverse times the small coordinate errors. This proves $V_B^{[N]}=V_B\cap\ker L$ for $B\ge B_0$ and that their nested union is dense in $V^{[N]}=V\cap\ker L$. In particular $P_B^{[N]}\to P^{[N]}$ strongly. The constraints and the right-inverse profiles themselves did not depend on $a$.

All the covariance used in (1)–(2) holds for this restriction: The displayed translation law is triangular in $k$, so the common kernel is invariant under both signs of $h$ and the bands rescale as before. The full closure is real and reflection-invariant: Poisson swaps $d$ and $\widehat d$ and reflects $x$ for the half-twisted profiles, and the node set is invariant under both conjugation and negation. These properties are asserted for the full closure, not reflection of a single band. The original complement is now enlarged by the single orthogonal projector

$$F_N=P-P^{[N]},\qquad \operatorname{rank} F_N=6N,\qquad 1-P^{[N]}=J+F_N.$$

In particular $A_f(J+F_N)$ is trace class. Thus the same metric shear and boundary estimate apply to the restricted model, at each fixed $N$ and width.

**What survives in the whole trace.** At each fixed $\rho_R$, first take both band limits using trace-norm convergence against $m_{\rho_R}A_f$; the difference is $-\operatorname{Tr}(m_{\rho_R}A_f F_N)$. Now exhaust position. Since $A_f F_N$ has finite rank, $m_{\rho_R}A_f F_N\to A_f F_N$ in trace norm. The difference of the ordered scalars is therefore $-\operatorname{Tr}(A_f F_N)$. To compute it, use the decomposition $V^{[N]}\oplus F_NH\oplus JH$. The only contributing diagonal block is $F_N A_f F_N$. In particular $A_f F_N$ need not map $F_NH$ into itself: The cross block into $V^{[N]}$ need not have zero trace after left multiplication by $m_{\rho_R}$; its trace is zero without that multiplier. The map $L$ on $F_NH$ identifies this compression with the induced operator on $V/V^{[N]}$ since $A_f V\subset V$ and $A_f V^{[N]}\subset V^{[N]}$. In these coordinates,

$$L_{z,k}(A_f b)=\sum_{m=0}^k{k\choose m}\left(\int y^{k-m}e^{zy}f(y)\,dy\right)L_{z,m}(b).$$

The diagonal entries in the $z$ block are $M_f(z)$. The exact, aggregate difference is

$$\boxed{\quad G_a^{[N]}(f)-G_a(f)=-N\sum_{z\in\Lambda}M_f(z).\quad}                 \tag{3}$$

This is a single whole-line quotient calculation, not a sum of local rank bounds. The new charge has zero change under metric translation but need not vanish when position is exhausted.

In fact (3) is invariant under any *common equivalent Hilbert metric*, with each projector recomputed in that metric. Equivalent norms leave both band closures and the quotient unchanged, and orthogonal band exhaustion is still strong in the new norm. At fixed position the localized convolution remains trace class by bounded equivalence. After the band limit, the difference again has just a finite-rank projection onto the orthogonal difference of the two full closures in the chosen metric. Its trace after position exhaustion is the trace of the same quotient operator. This proves existence and metric independence of the **difference** of the ordered traces (exhausting the difference if the individual limits are not known). It does not assert that the unrestricted ordered trace exists in, or is independent of, every equivalent metric.

**Negative three-plane in the required test class.** Choose three real $u_i\in C_c^\infty(I)$ satisfying

$$ M_{u_i}(0)=M_{u_i}(1/2)=M_{u_i}(-1/2)=0,\qquad M_{u_i}(i\tau_j)=\delta_{ij}.$$

In fact take $u_i=q_i(-\partial_x)p$, with $q_i$ the polynomial of degree at most seven given by interpolation on the eight distinct points $\Lambda\cup\{1/2,-1/2\}$. Prescribe zero at the two real points and $q_i(\pm i\tau_j)=\delta_{ij}/M_p(\pm i\tau_j)$ at the other six. Conjugation symmetry and uniqueness give real coefficients. Integration by parts gives $M_{u_i}(z)=q_i(z)M_p(z)$, so the mass is zero as well and the support is unchanged or smaller. For $f=u_i*u_j$, $M_f(z)$ is the **product** of moments, so (3) changes the real symmetric ordered Gram matrix by $-2N\operatorname{Id}_3$. At any fixed width the matrix $[G_a(u_i*u_j)]_{i,j=1}^3$ has finite entries, and choosing $2N$ larger than its norm gives a strictly negative three-plane for the restricted ordered form, even on tests killing both polar moments. This plane lies in the fixed-pulse derivative family: The section formed from $(-\partial_x)^k p$ for $0\le k\le7$ is Hankel, since the convolution of its $i$-th and $j$-th tests is $(-\partial_x)^{i+j}(p*p)$. No cutoff differentiation is needed for this check.

One can take the **same** $N$ at all the common good widths. For this quantifier only, use the [already established scalar identification](../../obligations/trace-even-separator-q.md#short-tests-separating-the-rational-global-and-joint-local-traces) as an absolute bound, not a sign or inertia argument. Each entry is bounded by the sum of $\operatorname{ord}(\omega)|M_{u_i*u_j}(\omega)|$ over the full shifted zeta divisor. This is finite by uniform rapid ordinate decay for $|\Re\omega|\le1/2$ and the zero count with orders. It bounds every open-strip subsum uniformly. Choosing $N$ once from the nine bounds gives one restriction and one strict negative plane surviving at arbitrarily small good widths, with no assertion at $a=0$. Alternatively the fixed-width obstruction uses no scalar evaluation. The entries used here are limits in the order $B\to\infty$ at fixed $R$, then $R\to\infty$; no negative-index assertion at all finite cutoffs or bound uniform in two moving cutoffs is needed.

## Boundary of the result

The first invalid step is **zero net metric shear (or two transition edges) implies a shared budget of at most two negative coordinates for the whole ordered form**. Equations (1)–(2) hold on both sides of (3), and the exact extra negative matrix on the three-plane persists through the stated exhaustion. The restriction deliberately loses maximality as the closure of **all** admissible theta inputs; it does not preserve the unrestricted floor span or its normalized local explicit formula. It is not a counterexample to the inertia bound for $P$, nor to a mechanism using a further estimate specific to that full floor span. A next geometric step would need to control the part unchanged by translating the metric, with a hypothesis that detects this same-band restriction. Controlling the edge difference more sharply cannot do so.

**Verification.** The signs were checked by bounded similarity at fixed position and by compression to a single finite quotient after exhaustion. A focused independent reasoning check confirmed the derivative signs, quotient cross-block requirement and ordered-limit test; the nonzero profile and same-band right inverse were checked above using the handoff's sampling formula. This is an analytic obstruction, not a finite-grid experiment or a new spectral equivalence. No theorem files were changed.
