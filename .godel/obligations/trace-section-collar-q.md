# The rational section collar at fixed position support

**Scope:** Project repair and comparison for $F=\mathbb Q$, $S=\{\infty\}$,
the trivial compact isotype, the half twist, and even degree $s=2r\ge4$.
Use the common good positive widths of the [weighted trace repair](trace-hardy-diagonal-q.md#removing-the-order-defect-in-the-weighted-rational-isotype),
omitting widths with boundary zeros. This is not a Lean trace theorem or an
identification of Masullo's intended lift.

## What the thin section can represent

**Provisional text reading.** In (11.3.1.4), p. 494, the shell splits use
successive differences of the unit restrictions of (11.3.1.2), pp. 492–493.
In (11.3.2.2–3), p. 495, the two section indicators are translated by the
**same** principal and compact factors, and the trace is sampled at
$(\tau(t),\xi g\tau(t))$ for all $\xi\in\mathbb Q^\times$ and $g\in E_{\mathbb Q}^1$.
Read literally against Haar on $E_{\mathbb Q}^1$, the product of exact
section indicators integrates to zero even before imposing a shell mask:
For each $\xi$ only one angular translate could place the first input in
the section. The extraction of (11.3.2.1) has $dt/t$ but no clear outer
integral; the comparison below uses the integrated trace described on
p. 496, not a pointwise equality in $t$.

Theorem 11.1.2.1, (11.1.2.1–7), p. 480, describes the set-theoretic
limit of closed carved subspaces at fixed position on the **zero line**.
It does not provide convergence of the right multipliers of (11.3.2.3)
on kernels in the **positive-width** space, let alone trace-norm
convergence. If that right cutoff uses the same decreasing chain, it
annihilates the shell already at finite $k_1\ge k+1$. Exhausting outside
$S'$ instead fixes the mask, not the trace transfer. Proposition 12.2.2.2,
(12.2.2.1–7), p. 508, starts with a normalized indentation and a quotient
kernel, and samples $(x,h^{-1}x)$, a pair with coinciding classes. It does
not turn $(\tau(t),\xi g\tau(t))$ for arbitrary $g$ into a quotient diagonal.
Neither citation permits moving a shell mask through a Paley–Wiener
projection. These readings are from the [digest-matched PDF](../sources/masullo/README.md)
with layout and raw text extraction. No rendered-page confirmation is claimed.

**Normalized collar repair.** Use the actual rational fundamental
subgroup $D=\tau(\mathbb R_{>0})K$, with $K=\widehat{\mathbb Z}^{\times}$
and $\tau$ the positive real section with finite coordinates one. In
$G=\mathbb A_{\mathbb Q}^\times$ write $x=h_x\tau(e^u)k_x$ uniquely with
$h_x\in H=\mathbb Q^\times$ and $k_x\in K$. The [rational fundamental
window](../../Proofs/Theorems/RationalIdeleFundamentalDomain.lean) and
[unit-factor Haar normalization](../../Proofs/Theorems/RationalIdeleFiniteUnitHaar.lean)
identify the product coordinates and normalized quotient Haar $du\,dk$,
with $dk$ of mass one. For the collar use the product Haar upstairs, with
counting measure on $H$. This is direct Haar unfolding, not an application
of the connected fundamental-domain setup of Situation 12.2.2.1, p. 507:
The subgroup $D$ here is disconnected.

For a compact open subgroup $U\le K$, put $c=\mu_K(U)>0$ and
$a_U=c^{-1}\mathbf1_{\tau(\mathbb R_{>0})U}$. In both legs replace the exact
section indicator by $a_U$, and retain the simultaneous Haar average:

$$
w_U(x,y)=\sum_{h\in H}\int_K a_U(hkx)a_U(hky)\,dk
=\mathbf1_{h_x=h_y}\,c^{-1}\mathbf1_U(k_x^{-1}k_y).
$$

Indeed, the first leg forces $h=h_x^{-1}$ and the second forces $h=h_y^{-1}$.
When these agree, the two angular conditions intersect in a coset of $U$
if $k_x^{-1}k_y\in U$, and otherwise have empty intersection. Consequently
the input weight has mass one over the principal and angular coordinates
at each input norm. Merely widening the indicators without normalization
would give row mass $c^2$, not one. The single leg by itself is **not** an
$H$-indentation on all of $G$ unless $U=K$: Its principal orbit sum is
$c^{-1}\mathbf1_U(k_x)$. Its angular average is $\mathbf1_D$, but the
simultaneous average is not the product of the single-leg averages.
In fact $w_U=w_{\mathbf1_D}\,c^{-1}\mathbf1_U(k_x^{-1}k_y)$, so only the
angular factor changes from the existing base-supported lift.

## The fixed-cutoff base operator and its shell masks

Let $A_f$ be log convolution, $P$ the full weighted geometric projection,
$Q_B$ a cofinal rational real-band projector, and $M_\rho$ a smooth compact
log position multiplier. Apply the collar to the log Haar kernel of
$T_{\rho,B}=M_\rho P A_f Q_B$, **after** constructing this quotient operator.
Invariance gives $P A_f Q_B=A_f Q_B$, keeping the terminal $Q_B$;
$M_\rho A_f$ is trace class by [compact kernel smoothing](trace-hardy-diagonal-q.md#removing-the-order-defect-in-the-weighted-rational-isotype).

The unfolded input integration first removes $h_y$ and then averages
$k_y$ over the coset $k_x U$. Hence on the radial isotype the descended
operator is exactly $T_{\rho,B}$ for every $U$. This can also be checked
on each term of a summable rank-one expansion of $T_{\rho,B}$, so the
radial trace and its [regular Haar diagonal](trace-spectral.md#from-the-weighted-kernel-to-the-haar-diagonal)
are unchanged. It is not an equality of full-angular traces: There the
angular averaging is the orthogonal projection onto the $U$-invariants,
of rank $[K:U]$, not the projection onto the trivial isotype. On the full
quotient this gives trace $[K:U]\operatorname{Tr}(T_{\rho,B})$. In contrast,
the angular integral in (11.3.2.3) gives the radial input row mass; it is
not a full-angular diagonal integral.

At $x=\tau(t)$ and $y=\xi g\tau(t)$, a nonzero weight requires $\xi=1$,
so $y\in D$. More generally, for outputs represented in $D$ the lifted
operator has no input from outside the archimedean base stage. All masks
$\alpha_{k+1}-\alpha_k$ vanish there, and the $S$ mask gives the entire
operator. A right stage cutoff allowing the base does not change it. That
mask is distinct from the terminal band projector $Q_B$. These are exact
finite-cutoff statements: Neither shrinking $U$ nor summing the shells can
add a Mellin term. This collar gives a normalized analogue of the
simultaneous translations of (11.3.2.2), with the same radial operator as
the existing base-supported lift. It does **not** give the periodic orbital
operator. For example, take $p=2$ and a nonnegative radial test narrowly
supported near $\log 2$ with $f(\log 2)>0$. The collar shell is zero. The
unweighted sample in (11.3.2.1), p. 495, is $\log 2\,f(\log 2)>0$; only the
inverse uniformizer contributes. The half-twisted Poisson sum in
(11.3.2.5), p. 496, retains $2^{-1/2}$ and is still nonzero. Its cited
Theorem 7.4.2.1, p. 367, supplies the trace of convolution **induced on the
orbital quotient** $E^{S_p}$, not a map transferring a global cut-off
shell to that quotient. This test is in the above-one class of Theorem
11.3.2.1 but not the short class on p. 520, where the prime comb is zero.

## The short mass-zero control in the same cutoff order

Choose a nonzero nonnegative $b\in C_c^\infty((1,2))$ and put
$f_\delta(x)=b'(x/\delta)=(\delta b(x/\delta))'$ for
$0<2\delta<\log 2$. Then $\int f_\delta=0$ and
$M_{f_\delta}(1/2)=-\tfrac12\delta^2\int e^{\delta u/2}b(u)\,du\ne0$,
where $M_f(z)=\int e^{zx}f(x)\,dx$. With no finite prime samples, the
[checked rational scalar formula](rational-explicit-formula.md#checked-rational-radial-idelic-explicit-formula)
gives $-Z_{\rm full}(f_\delta)=J_{f_\delta}-M_{f_\delta}(-1/2)-M_{f_\delta}(1/2)$
in the positive Mellin convention. Both moments are $O(\delta^2)$.
Since the real Haar density is $1/(2x)+O(1)$ near $0^+$, one has

$$
J_{f_\delta}\longrightarrow \frac12\int_1^2\frac{b'(u)}u\,du
=\frac12\int_1^2\frac{b(u)}{u^2}\,du>0.
$$

At a fixed good width $\alpha$, the [omitted zeros have count $o(T)$](trace-carving-weight-q.md#the-short-window-detects-any-omitted-zero)
through absolute height $T$, with order. Integration by parts in the
scaled variable gives $|M_{f_\delta}(z)|\le C_N\delta(1+\delta|\Im z|)^{-N}$
uniformly for $|\Re z|\le1/2$. Split at $1/\delta$, then at dyadic multiples
of $1/\delta$. The low block costs $\delta\,o(1/\delta)=o(1)$, and the high
blocks are bounded by $C_N\sup_{T\ge1/\delta}N_{\rm omitted}(T)/T$ times a
convergent geometric sum for $N>1$. Thus $-Z_\alpha(f_\delta)$ has the same
positive limit. This estimate is not an $o(\delta^2)$ estimate.

Now **fix** a sufficiently small $\delta$. The corrected global trace in
the collar tends to $\operatorname{Tr}(M_\rho A_f P)$ as $B\to\infty$ at
fixed $\rho$, and its subsequent position exhaustion gives
$-Z_\alpha(f)$ by the [weighted trace repair](trace-hardy-diagonal-q.md#removing-the-order-defect-in-the-weighted-rational-isotype).
This exhaustion can use smooth symmetric cutoffs from Definition 9.3.3.1,
p. 427: For large $\Lambda$ take $\varepsilon=\Lambda^{-2}$ and a smooth even
log cutoff supported on $[-\log\Lambda,\log\Lambda]$, equal to one on
$[-\log(\Lambda-\varepsilon),\log(\Lambda-\varepsilon)]$. The plateau in
norm contains $[1/\Lambda+\varepsilon,\Lambda-\varepsilon]$. Some sufficiently
large member of this family therefore has nonzero level-limit global trace.
Hold that member fixed. The [actual local real level projectors in the model](trace-diagonal-q.md#local-level-exhaustion-and-the-cutoff-trace)
converge strongly to the identity, so their level-limit cutoff trace is
$\operatorname{Tr}(M_\rho A_f)=0$ at the **same** position support.

Thus the normalized section collar fails a direct same-order scalar
identification, on precisely a positive-log, mass-zero control with a
nonzero $+1/2$ moment. This does not compare with the joint-cutoff local
trace at fixed position: That local limit moves position, and gives
$J_f-M_f(-1/2)$. In the prescribed level-first global order the difference
from that joint local value is $-M_f(1/2)+Z_{\rm full}(f)-Z_\alpha(f)$;
the collar computation does not remove the omitted-zero residual.

## What to test next

The original shell route still needs a normalized lift tied to the
actual projected orbital quotient, not a different generic collar or a
limit of the same-chain mask already known to kill the shell. The
replacement route needs an analytic comparison of the base trace with the
joint local one that produces $-M_f(1/2)$ without assuming away omitted
zeros. A concrete test is to impose a **bounded moving integral** on the
actual [scaled real band](trace-joint-local-q.md#projection-and-localization-estimates),
where the uncut integral is not continuous. For a fixed smooth even window
$\eta$ supported in $1<|t|<2$, use $\int\eta(t/R)b(t)\,dt$ as a second
constraint on $Q_Y H_Y$ and compare its rank-one trace under $M_p A_f$
with $M_f(1/2)$. Take $Y\to\infty$, $R/Y\to\infty$, $L/R\to\infty$, and
$\epsilon\to0$ in the notation of the joint local calculation. The first
check is whether the projection of $W_Y^{-1}\eta(\cdot/R)$ onto $Q_Y H_Y$
changes its leading norm and dilation pairing. One falsification test is
whether this projection is asymptotically the identity on that seed in
relative norm: On the moving annulus the limiting weight ratio under
$D_g$ is $g^{2\alpha}$, so the normalized seed's limiting pairing has
absolute value at most $g^\alpha<g^{1/2}$ for $g>1$. More precisely, test
whether the limit is the pairing in $L^2(|v|^{2\alpha}\,dv)$ of the unit
normalization of $|v|^{-2\alpha}\eta(v)$ with its dilation $D_g$. For a real seed, writing
$D_g=g^\alpha U_g$ with $U_g$ unitary in that homogeneous space shows that
the pairing has derivative $\alpha$ in $\log g$ at $g=1$: The real unitary
pairing is even in $\log g$. The target $g^{1/2}$ has derivative $1/2$.
This would separate the densities even on short mass-zero tests, for
which a constant difference would be invisible. This is a test of a
separately specified exhaustion, not a condition claimed by Masullo.

**Review evidence:** `section-collar-review` (`DfYjINo`, read-only on
`73acefdb0514114c439e1b1237549d104bef68be`) independently checked the source
digest, the simultaneous angular average and its radial scope, the
cutoff citation, the positive periodic control, and the short-window
estimates through selection of a fixed nonzero annular trace. The moving
integral test is a proposed next check, not part of the reviewed result.
