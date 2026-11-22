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

## A short test excludes fixed prime-two spread weights

Apply the [Haar lift on principal translates](trace-orbital-q.md#the-right-cutoff-erases-a-fixed-shell-in-the-literal-chain)
with $p=2$ to the Haar-relative kernel of the **already formed** radial
operator $T_{\rho,B}=M_\rho P A_f Q_B$. Fix finitely supported weights
$m_j\ge0$ of sum one, at least two positive. The indentation is $m_j$
on $2^jD$ (diagonal rational $2^j$) and zero on other translates. It
normalizes the full orbit sum, not the separate base-stage sum.

For the output representative in $D$, the simultaneous two-leg weight
at an input in $2^\ell D$ is $\sum_j m_jm_{j+\ell}$. Summing all input
translates gives one. The right unit cutoff taken **outside** $2$ is one
on these translates; the signed input mask $\alpha_1-\alpha_0$ is $-1$
exactly for $\ell\ne0$ there. Unfolding with counting measure and
mass-one compact Haar therefore gives the masked radial operator

$$
T^{\rm shell}_{\rho,B}=-cT_{\rho,B},\qquad c=1-\sum_jm_j^2>0.
$$

No mask has passed through a projection. The output section matters:
With the same masks at $2^r d$ instead of $d\in D$, the unit-at-two
input has weight $\sum_j m_jm_{j-r}$, not necessarily $\sum_jm_j^2$.
The masked kernel is thus not asserted to descend independently of the
chosen section.

For the short mass-zero test above, fix a common good width and then a
sufficiently small $\delta$ so the whole ordered trace is positive. At fixed $\rho$, the band limit
retains $M_\rho A_{f_\delta}P$; only then exhaust position. Since $c$
is fixed, the ordered shell trace is strictly negative. On the same test
the half-twisted orbital circle trace is zero: With $L=\log 2$, the
samples in $L\sum_{n\in\mathbb Z}e^{-nL/2}f_\delta(nL)$ all miss the
support in $(0,L)$. Thus no such fixed spread gives the proposed
prime-two transfer even on this short class. The test does not exclude
weights concentrating on one translate as cutoffs move ($c\to0$), or a
shell operation inside the level projection. Nor does it identify the
additional norm cutoff in (11.3.2.4). It tests a replacement, not a
necessary property of every lift of the manuscript diagonal.

## A bounded moving integral does not supply the missing moment

This is a project test of a replacement exhaustion, not a constraint
claimed by Masullo. Use the [actual scaled band](trace-joint-local-q.md#projection-and-localization-estimates)
$Q_Y H_Y$, with $H_Y=L^2(W_Y(t)\,dt)$ on even functions and $Q_Y$ the
unit-band projection with value zero. The uncut integral constraint has
already disappeared in that closure. Fix $0<\alpha<1/2$ and a real,
nonzero, smooth even $\eta$ supported in $1<|v|<2$. Impose the second,
bounded condition $\ell_R(b)=\int\eta(t/R)b(t)\,dt=0$. Take
$Y\to\infty$, $R/Y\to\infty$, $L/R\to\infty$, and $\epsilon\to0$,
with the same position multiplier $p$ as in the local comparison.
The dilation is $D_g b(t)=g^{-1/2}b(t/g)$ from (12.4.1.8–9), p. 517,
and the positive Mellin convention is (12.5.1.3), p. 519 (provisional
extraction locators).

The ambient representer is $W_Y^{-1}\eta(\cdot/R)$. Under the unitary
rescaling $b\mapsto\sqrt{RW_Y(R)}\,b(R\cdot)$ into $L^2(V\,dv)$,
where $V(v)=W_Y(Rv)/W_Y(R)$, the representer is
$\sqrt{R/W_Y(R)}\,h$ with $h=\eta/V$. Off zero,
$V(v)\to |v|^{2\alpha}$, uniformly on compact annuli. The projected
band now has radius $R$ and still requires value zero. The projection of
$h$ differs from $h$ by $o(1)$ in $L^2(V\,dv)$, and its norm tends to
$\|h_\infty\|_{L^2(|v|^{2\alpha}dv)}>0$, where
$h_\infty(v)=\eta(v)|v|^{-2\alpha}$. Indeed $h-h_\infty$ tends to zero
in the moving norm by annular convergence. Approximate $h_\infty$ by even
Schwartz Fourier truncations of bandwidth at most $R$, subtracting the
value at zero times a fixed bandlimited Schwartz function of value one
there. The correction tends to zero in Schwartz seminorms. The uniform
weight bound $V(v)\le C\max(|v|,|v|^{-1})^\gamma$ with
$2\alpha<\gamma<1$ gives convergence in the moving norm as well.

Thus the new projector is $Q_Y-E$, where $E$ is the rank-one projection
onto the normalized projected representer. The same closure results if
one imposes $\ell_R$ on the original dense generators: Correct an
approximant by a scalar multiple of one generator with nonzero
$\ell_R$, which exists since the projected representer is nonzero
for large parameters. In the scaled coordinate write $e$ for the unit
projected vector and $a=h/\|h\|_{L^2(V\,dv)}$. For $g$ in the compact
test support, the ratio bound
$V(gv)/V(v)\le C\max(g,g^{-1})^\gamma$ gives uniform dilation norms.
Replacing $e$ by $a$ in the localized pairing costs at most
$2\sup_g\|D_g\|\,\|e-a\|_{L^2(V\,dv)}=o(1)$. The position cutoff
is one on the support of **$a$**, not necessarily on that of $e$:
Eventually $L-\sqrt L>2R$ and $R>2\epsilon$. Annular weight convergence
then gives, uniformly for $g$ on the test support,

$$
d(g)=\lim\langle p(R\cdot)D_g e,e\rangle
=\frac{\langle D_g h_\infty,h_\infty\rangle_{L^2(|v|^{2\alpha}dv)}}
{\|h_\infty\|^2_{L^2(|v|^{2\alpha}dv)}}.
$$

For an above-one test $f$, the old trace minus the trace with the
extra constraint therefore tends to $\int f(x)d(e^x)\,dx$. The new
trace is $J_f-M_f(-1/2)-\int f(x)d(e^x)\,dx$. The desired rank-one
subtraction would instead be $M_f(1/2)$. To distinguish them even on
mass-zero tests, put $G(x)=e^{x/2}-d(e^x)$. In the homogeneous limit,
$e^{-\alpha x}D_{e^x}$ is unitary, and its correlation with the real
smooth compact annular seed is even and differentiable in $x$. Hence
$G'(0)=1/2-\alpha>0$. Take a nonnegative nonzero smooth bump $c$
with compact support in a short subinterval of $(0,\log 2)$ on which
$G'>0$, and set $f=c'$. This radial test vanishes near norm one and has
zero mass, so it satisfies the rational radial instance of (13.3.1.2),
p. 522: Nontrivial compact characters average out, and the norm phase
of a character trivial on the compact factor cancels. But

$$
M_f(1/2)-\int f(x)d(e^x)\,dx=-\int c(x)G'(x)\,dx<0.
$$

This rules out this fixed-window constraint, with this joint limit,
as the sole source of the $+1/2$ subtraction. It does not evaluate the
global $S$-piece, identify an orbital quotient, or remove the omitted-zero
residual. Do not repeat the same constraint with a different fixed smooth
annular window: The derivative test is independent of that choice.

## Remaining comparison

The shell route still needs a normalized lift tied to the actual
projected orbital quotient, not another generic collar or a limit of the
same-chain mask that kills the shell. A replacement still owes a
comparison of the actual level-first global diagonal with the joint local
trace, including both the missing moment and the omitted-zero residual.
The [general finite-place contour majorant](hecke-right-line-majorant.md)
is independently runnable without a choice of that lift.

**Review evidence:** `section-collar-review` (`DfYjINo`, read-only on
`73acefdb0514114c439e1b1237549d104bef68be`) independently checked the source
digest, the simultaneous angular average and its radial scope, the
cutoff citation, the positive periodic control, and the short-window
estimates through selection of a fixed nonzero annular trace. `moving-integral-review` (`oLaIxDK`, read-only on
`b0aa4e006ff70a9f985fae322f8010b105253d8b`, Yah session
`01a200ad-ee1e-7cd2-bdcc-ec33f44bd141`) independently checked the rescaled
projection, the moving-limit pairing, and the admissible separating test.
These are mathematical reviews, not Lean or rendered-page verification.
`spread-shell-review` (`uLAjSbM`, read-only on
`5c735c27e6b5ab0bb8233c70737c275ef8af8d34`) independently checked the
section-dependent shell factor, rebased unit cutoff, ordered trace,
and zero circle sample for the fixed-spread exclusion. That exclusion
is reviewed mathematics, not a Lean theorem.
