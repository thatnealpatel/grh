# Weil windows: How to pack near-null directions

**Claim on paper.** For all sufficiently large $R$ there is one subspace
$V_R\subset C_c^\infty(-R,R)$ of dimension at least $e^{2R}/(4e^3)$ such that, for every
fixed $A>0$,
$$
|B(h,g)|\le C_A e^{-AR}\|h\|_2\|g\|_2
\qquad(h\in V_R,\ g\in C_c^\infty(-R,R)).
$$
The norms are unweighted Lebesgue norms. Neither the space nor the cutoff changes with
$A$, and the constant is uniform over the whole smooth companion unit ball, not just
over $V_R$.

**Convention.** Use $M_h^-(z)=\int h(v)e^{-zv}\,dv$ and $z_\rho=\rho-1/2$. Sum
$B(h,g)=\sum_\rho m_\rho M_h^-(z_\rho)\overline{M_g^-(-\bar z_\rho)}$ over distinct
nontrivial zeta zeros, each with its order $m_\rho$. Reindexing by $\rho\mapsto1-\rho$
changes both transforms to Lean's positive-exponent convention without changing the
tests or the sum. Hermiticity uses $\rho\mapsto1-\bar\rho$ instead.

**Dimension calculation.** Set $b=R-2$, $u_0=R-1$, $T=b+u_0=2R-3$, and $X=e^T$. Fix a
smooth cutoff $\chi$ equal to one on $(-\infty,0]$ and zero on $[1/2,\infty)$. Fix
$w\in C_c^\infty(1,2)$ with plateau one on $[5/4,7/4]$. For $x>0$ take
$$
f(x)=w(x)\sum_{|j|\le K}a_j e^{4\pi ijx},\qquad K=\lfloor X/4\rfloor,\qquad \int_1^2 f=0,
$$
and extend evenly. For $H_f(t)=e^{-t/2}\sum_{n\ge1} f(ne^{-t})$, take $V_R$ to be the
image $h(v)=\chi(v-u_0)H_f(v+b)$. On the left $H_f(t)=0$ for $t\le-\log 2$; on the right
the cutoff ends at $v=R-1/2$. On $-\log 2<t<0$ only $n=1$ occurs and the cutoff is one,
so
$$
\int_{-\log 2}^0 |h(t-b)|^2dt=\int_1^2|f(x)|^2dx\ge \tfrac12\sum_j|a_j|^2.
$$
The inequality is orthogonality of the carriers on the half-unit plateau. The balance
constraint costs at most one dimension, so $\dim V_R\ge2K\ge X/4$ eventually.

**Mixed estimate, independent of the dimension calculation.** For the uncut
$F(v)=H_f(v+b)$, absolute unfolding for $\Re(z+1/2)>1$ gives
$M_F^-(z)=e^{bz}\zeta(z+1/2)\int_1^2 f(x)x^{z-1/2}dx$. Poisson decay gives an entire
left side, and balance cancels the pole on the right. Hence the samples of $h$ at
$z_\rho$ are exactly those of $E=h-F$, which starts at $v=u_0$.

With Fourier phase $e^{-2\pi i x\xi}$, even Poisson summation gives
$H_f(t)=e^{t/2}\sum_{m\ge1}\widehat f(me^t)$, using $f(0)=\widehat f(0)=0$. For $t\ge T$
all frequencies $\xi=me^t$ satisfy $|\pm\xi-2j|\ge\xi/2$. The first two derivatives of
the translated envelope transforms thus cost at most $C_N\xi^{-N}$ each. Cauchy–Schwarz
on the carriers costs $O(\sqrt X\|a\|_2)$, not an order-$N$ derivative cost in $K$. Two
$t$-derivatives cost at most $\xi^2$, giving, by summing $m^{2-N}$ for $N\ge4$,
$$
\max_{0\le j\le2}|H_f^{(j)}(t)|\le C_N\sqrt X\|a\|_2 e^{-qt},\qquad q=N-5/2.
$$
The fixed cutoff has bounded derivatives. Integrate $E$ and $E''$ against $e^{-zv}$ and
use $M^-_{E''}=z^2M^-_E$ to get
$$
|M_h^-(z_\rho)|\le
\frac{C_N\sqrt X\|a\|_2 X^{-q}e^{-\sigma u_0}}{(1+|z_\rho|^2)(q+\sigma)},\qquad \sigma=\Re z_\rho.
$$
The reflected companion has evaluation norm $(\int_{-R}^R e^{2\sigma v}dv)^{1/2}$.
Together with $e^{-\sigma u_0}$ this costs at most $\sqrt{2R}e^R$ for $|\sigma|\le1/2$.
The classical zero count gives $\sum_\rho m_\rho/(1+|\Im\rho|^2)<\infty$. Using the
plateau bound now yields $C_N\sqrt R e^{(7-2N)R}\|h\|_2\|g\|_2$. Fix $2N>7+A$ before
taking $R$ large.

**What it does not show.** The mixed estimate does not supply a vanishing lower error
on the $L^2$ orthogonal complement. If a common complement error $\delta_R\to0$ were
available, write
a smooth test as its $L^2$ projection into $V_R$ plus its smooth orthogonal remainder.
The mixed estimate with error $\epsilon_R$ then gives a full-window lower error at most
$\delta_R+2\epsilon_R$, using Hermiticity. A closed-window test at radius $R$ fits in
the open window at radius $R+1$. See the [edge test](weil-complements.md) for a
necessary arithmetic estimate on actual complement vectors.

**Source.**
[`RationalWeilWindows.lean`](../../Proofs/Theorems/RationalWeilWindows.lean):
`Masullo.rationalWeilZeroForm_radial_zeroSide` gives the absolutely summable diagonal
and its radial interpretation, and
`Masullo.rationalWeilZeroForm_nonneg_iff_window_lower_bounds` trades global
nonnegativity for a common vanishing lower error on sufficiently large closed windows.
The packing and mixed estimate are paper arguments, not instances of the checked window
passage.
