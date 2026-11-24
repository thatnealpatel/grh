# The same filter at the first and third harmonics

A real high-endpoint failure forces a zeta zero at scaled depth $>1.230$ near $t$ **or** $3t$, with $t=2q^{3/5}$. Alternatively the two required depths can be set to $1.226$ and $1.50$, respectively. These are disjunctions, not improvements to $1.220$ at the first height alone. The gain comes from pricing the two signs against the *same* prime phase; there is no new cutoff search.

Use $R,V,D,g,G,Q,E,I$ and the seventeen-cutoff weight $f$ of the [single-height test](common-filter-depth.md). For $j=1,3$ set $x_j=\gamma-jt$, $b=\beta-1/2$, $d=Db$, $s_1=1$, $s_3=-1$. Let $J=(2/\epsilon)\log D$. Define $S_j(c)$ by summing

$$-s_j(1+e^{-2d})\Re Q(\beta+ix_j)-\frac{2G\cosh c}{R}\Re E(x_j+ib)$$

over right zeros with $d>c$ and $|x_j|\le J$, with multiplicity. At $j=1$ omit $|x_1|\le1.5/D$; at $j=3$ **include the center**. With $a=197/200$, the following strict bounds hold for fixed sufficiently small $\epsilon>0$ and then sufficiently large $q$ at a failure:

| $c_1$ | $c_3$ | $aS_1(c_1)+(1-a)S_3(c_3)$ exceeds |
|---:|---:|---:|
| 1.230 | 1.230 | .00047 |
| 1.226 | 1.50 | .00009 |

In each row at least one individual signed charge exceeds the tabulated bound. A large unsigned count need not supply either charge.

**One polynomial comparison.** Write $u=|\cos((t/2)\log p)|$, $z=\log(V/p)$, $d\mu=V^{-1}\sum_p(\log p)\delta_z$, and $P_j=\int f(z)T_{2j}(u)\,d\mu$ with $T_k$ the Chebyshev polynomials. Both harmonics use the original $V$. The sole angular datum is $\int z_+u\,d\mu\ge8/9-o(1)$. Put $B(v)=aT_2(v)-(1-a)T_6(v)$, $\lambda=171/50$, and

$$H(z)=\min_{0\le v\le1}\{ f(z)B(v)-\lambda z_+v\}.$$

Applying the pointwise inequality before taking limits gives

$$aP_1-(1-a)P_3\ \ge\ \lambda(8/9)+\int H(z)e^{-z}dz-o(1)\ >\ .5602789-o(1).$$

PNT is used only for the fixed continuous radial function $H$, zero below $-.6$ and $O(1+|z|)$ to the right. The tail bound for these weights is given in the [original prime comparison](filtered-one-height-packet.md#pay-for-the-combined-weight-on-the-original-failure-datum). No equality of optimizing phase laws or prime realizations is assumed.

**Checking the minimum.** For nonnegative $f_0,r$, minimize $f_0 B(v)-\lambda r v$ on a mesh of spacing $1/1024$, including both endpoints. To lower-bound the continuous minimum subtract $f_0[4a+51(1-a)]/(8\cdot1024^2)$: An interior minimizer is stationary, $T_2''=4$, and $-T_6''=-960v^4+576v^2-36\le252/5$. Use this procedure with $f_0=f(z),r=z_+$ at the endpoints of the radial mesh from $-.6$ to $1$ in steps of $1/80$. All knots of $f$ and the origin are mesh points. On each interval the minimized expression is affine in $z$ for fixed $v$, so $H$ is concave and its lower endpoint chord integrates to a lower bound. Above $1$ both radial coefficients have slope one. The minimum there is bounded below by the endpoint lower bound plus $(z-1)$ times the lower bound from $f_0=r=1$. This checks the whole half-line, not a quadrature sample. The [checker](check-common-filter-pair.py) uses exact rational minimand values and ball enclosures for the integrals. It replays the original full-strip and all-frequency tests before using the same shift distribution and envelope integral.

**Sign on the zero side.** At either fixed harmonic the Mellin identity and [reflected pair estimate](filtered-reflection-price.md) apply with $x=x_j$. For the full envelope the main term is unchanged because $\log(jt)/R\to1/3$. Multiply the residue by $s_j$, not its budget: The absolute shallow and tail bounds work for either sign. Subtract both copies of the budget on each retained pair and replace the left residue by its signed proxy with total absolute error $o_\epsilon(1)$, including the missing far-left terms. The budget is nonnegative everywhere. Inside the central hole $\Re Q\ge0$ for large $D$, so the positive harmonic's net charge there can be discarded for a lower bound. The negative harmonic has the reverse residue sign. At the trial location $x_3=0$, $b=d_0/D$ with $d_0>c$ fixed, its summand times $R$ tends to $2E(0)[g(1/2)\cosh d_0-G\cosh c]$, strictly positive for large enough fixed $d_0$. This uses $A(1/2)^2/(1/2)^2=E(0)$; it does not assert that the location is occupied. Thus separately, with no assumption about either prime price,

$$ S_j(c)\ge s_j P_j-GI\cosh(c)/3-O(\epsilon)-o_\epsilon(1). $$

Take the convex combination. Before smoothing and asymptotic errors the certified margins exceed $.0004804$ and $.0000929$, respectively. In particular the second branch is not blocked by the first-height-only ceiling at $1.226$; the extra input is the third harmonic of the very same $u$, not an independent prime law.

**Next decision.** If a conductor passes the original prime tests, first evaluate $P_1$ and $P_3$ with this same $f$. In either row select the branch with the larger $s_jP_j-I\cosh(c_j)/3$. At a sufficiently large failure it must pay the row's net margin after errors; only that branch needs its matching zero census for a contradiction. Without those prime measurements one may instead upper-bound the stated weighted charge. Keep the $1.220$ first-height-only test if $3t$ is unavailable. None of the inequalities here supplies the arithmetic upper bound on a surviving conductor or an effective conductor threshold.
