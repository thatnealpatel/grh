# Joint-cutoff traces of the real-place level at positive width

**Status:** Project proof in the rational trivial compact isotype, $S=\{\infty\}$, for tests supported away from norm one. This uses the local invariant-level model in the [level-first handoff](trace-diagonal-q.md#the-orders-being-compared), with its provisional extracted locators (11.2.1.6), pp. 488–489, and (12.4.1.8)–(12.4.1.12), p. 517. It is not a reading about the global levels of (11.2.1.8), a new visual reading, or a Lean proof. The local projection, moving cutoffs, and Haar trace are checked in the calculations below.

## Above norm one: The defect is a single Mellin moment

Fix $0<\alpha<1/2$, $r\ge1$ integral, and put $\beta=2\alpha$, $w(x)=e^{\beta|x|}(1+x^2)^r$. Work with the usual additive Fourier transform with phase $-2\pi i u\xi$. The half-twisted quotient map $f\mapsto\sqrt2 e^{x/2}f(e^x)$ is unitary from even $L^2(w(\log|u|)\,du)$ to $L^2(w(x)\,dx)$; the scalar changes no subspace. For $Y\ge1$ scale the additive coordinate by $t=Yu$. With $C_Y=Y^\beta(1+\log^2Y)^r$, the unitary sends $f$ to $(C_Y/Y)^{1/2}f(t/Y)$ in $H_Y=L^2_{\mathrm{even}}(W_Y(t)\,dt)$, where $W_Y(t)=w(\log(|t|/Y))/C_Y$. The scaled orthogonal projection $Q_Y$ has range the $H_Y$-closure of even Schwartz functions with strictly interior unit Fourier band, $f(0)=0$, and $\int f=0$. Allowing band endpoints on these Schwartz generators gives the same closure by dilation.

Let $\varphi\in C_c^\infty((1,\infty))$ have support in $[g_0,g_1]$, $1<g_0<g_1$. Quotient convolution in these coordinates is $A=\int \varphi(g)D_g\,dg/g$, with $D_g f(t)=g^{-1/2}f(t/g)$. This is **convolution on the half-twisted profiles**, as in the level-first comparison; it is not a further half twist of the input test. Let $P_d$ be the raw Fourier multiplier of $[-d,d]$, and $P_q$ an average of the $P_d$ against a probability measure on $[d_0,1]$ with fixed $d_0>0$, possibly depending on $Y$. This includes $P_1$ and smooth monotone symbols with a fixed fractional passband. Use the scaled cutoff

$$p(t)=U_L(t)(1-\chi(t/\epsilon)),\qquad U_L=\mathbf1_{[-L,L]}*\rho_{\sqrt L},$$

where $\rho_b(t)=b^{-1}\rho(t/b)$ for an even smooth nonnegative mollifier of integral one supported in $[-1,1]$. Take $\chi$ even smooth, equal to one on $[-1,1]$, zero outside $[-2,2]$, and $0\le\chi\le1$. Let $Y\to\infty$, $\epsilon\to0$, and $L/Y\to\infty$. The position lower edge times bandwidth is $\epsilon$ and the upper transition ratio tends to one. At fixed cutoffs the products are trace class, with traces equal to the normalized Haar diagonals, and

$$\lim\operatorname{Tr}(M_pAP_q)=J_\varphi,\qquad
\lim\operatorname{Tr}(M_pAQ_Y)=J_\varphi-c_\varphi,$$

where

$$J_\varphi=\tfrac12\int\varphi(g)\sqrt g\left((g-1)^{-1}+(g+1)^{-1}\right)\frac{dg}{g},\qquad
c_\varphi=\int\varphi(g)g^{-1/2}\frac{dg}{g}.$$

Thus a nonzero nonnegative test supported in $(1,2)$ rules out uncorrected diagonal agreement, and also trace-norm convergence of the difference to zero. On tests with $c_\varphi=0$, the limiting scalar diagonals agree in this regime. This last conclusion is not trace-norm agreement.

## Projection and localization estimates

Choose $\beta<\gamma<1$. Uniformly in $Y$, for $t,v\ne0$,

$$\frac{W_Y(t)}{W_Y(v)}\le C\max(|t/v|,|v/t|)^\gamma.$$

The exponential part costs exponent $\beta$ and the ratio of log-polynomial factors costs at most $C_r(1+|\log|t/v||)^{2r}$. Taking $v=1$ and reversing the ratio bounds both the weight and its reciprocal by $C\max(|t|,|t|^{-1})^\gamma$. The ratio estimate gives uniform boundedness of all $D_g$ for $g\in[g_0,g_1]$.

Let $V_Y$ be the closed full unit-band subspace, defined by distributional Fourier support, and $R_Y$ its orthogonal projection. The reciprocal bound embeds $H_Y$ continuously into tempered distributions. Choose an even real Schwartz $\psi$ whose Fourier transform is compactly supported and equals one near $[-1,1]$. Reproduction $f=\psi*f$ gives bounded evaluation at zero on $V_Y$ and polynomial bounds for all derivatives. Strictly bandlimited Schwartz functions are dense there: First dilate $f$ to $f(\lambda t)$ for $\lambda<1$, with strong convergence as $\lambda\uparrow1$ by the ratio bound and dense compactly supported smooth tests away from zero. Then multiply by $\eta(bt)$ for an even bandlimited Schwartz $\eta$ of value one at zero and $b\downarrow0$. Dominated convergence applies, and the product is Schwartz with strictly interior band for small enough $b$. To approximate a vector of value zero, first correct the value by subtracting a vanishing multiple of a fixed strictly bandlimited Schwartz function of value one. Then correct the integral by an appropriate multiple of $T^{-1}h(t/T)$ with $h$ of strictly interior band, value zero, and integral one. Such an $h$ can be made by starting with a Fourier bump of value one at frequency zero and subtracting an even bump away from zero to make its integral zero. The squared norm of the scaled correction function is at most $CT^{\gamma-1}\|h\|_{H_Y}^2$. For each approximant take $T$ large enough to absorb its scalar coefficient. Thus there is **exactly one** retained condition: $Q_Y=R_Y-E_Y$, where $E_Y$ projects onto the unit-normalized full-band evaluation representer $e_Y$.

The sharp $P_d$ are uniformly bounded even on the full weighted space. Use dyadic shells $I_j=\{2^j\le|t|<2^{j+1}\}$. For $|j-k|\le1$, unweighted Plancherel and weight comparability bound the blocks. For $|j-k|\ge2$, the sine kernel $\kappa_d(t-v)=\sin(2\pi d(t-v))/(\pi(t-v))$ is bounded by $C2^{-\max(j,k)}$. After conjugating by the square root of the weight, the Hilbert–Schmidt bound on the block is $C2^{-(1-\gamma)|j-k|/2}$ by the ratio estimate and the square roots of the two shell lengths. Summation in $j-k$ gives the uniform bound. By density and Fourier support, $P=P_1$ has range $V_Y$ and fixes that space. In particular $R_YP=P$.

For an output multiplier $b$, reproducing convolution $C_\psi$ satisfies

$$\|M_b C_\psi\|_1\le C_\psi'\sum_{n\in\mathbb Z}(1+|n|)^{\gamma/2}\|b\|_{L^2(W_Y\,dt;[n,n+1])}.$$

This can be proved on the full weighted space and restricted to the even subspace for even $b$. On the output cell expand the kernel $\psi(t-v)$ in Fourier series in $t-n$, using a smooth window equal to one on the cell and supported within a larger period. The coefficient indexed by $k$ is bounded pointwise by $C_N(1+|k|)^{-N}(1+|n-v|)^{-N}$ by integration by parts. Its input functional norm uses the reciprocal weight and is at most $C_N'(1+|k|)^{-N}(1+|n|)^{\gamma/2}$: Integrate on $|v|\le1$ using local integrability, and on the complement use $1+|v|\le(1+|n|)(1+|n-v|)$. Each output vector has norm $\|b\|_{L^2(W_Y;[n,n+1])}$. The sum of rank-one norms proves the bound. Inserting $C_\psi$ after $A$ proves trace class at fixed cutoffs, since $A$ sends $V_Y$ to the strictly smaller band $[-1/g_0,1/g_0]$.

## Only the rank-one correction survives in the trace

Choose a smooth even low-pass symbol $m$ equal to one near zero and supported in a band of radius less than $1-1/g_0$. Write $U_L^{\rm lo}=\mathcal F^{-1}(m\widehat U_L)$. Then $B=M_{U_L^{\rm lo}}A(R_Y-P)$ obeys $PB=B$ by the frequency gap and $BP=0$ by $R_YP=P$. This trace-class operator has zero trace by cyclicity. Replacing $U_L^{\rm lo}$ by $p$ changes $B$ by $o(1)$ in trace norm uniformly in $Y$: The removed central hole costs $O(\epsilon^{(1-\gamma)/2})$ by the localization estimate. On the support of $1-m$, $\widehat\rho(\sqrt L\,\xi)$ and its derivatives have arbitrarily rapid decay there, while each fixed derivative of $\widehat{\mathbf1_{[-L,L]}}$ costs at most a power of $L$. Fourier inversion and integration by parts give $U_L-U_L^{\rm lo}=O_{M,N}(L^{-N}(1+|t|)^{-M})$ for any fixed $M,N$. Use localization again. This proves vanishing of the **trace** of $M_p A(R_Y-P)$, not vanishing of that operator in trace norm.

Because $A$ sends the full band into itself, the trace of $AE_Y$ is exactly $(Ae_Y)(0)/e_Y(0)=c_\varphi$. To remove $p$ in this rank-one trace with moving $Y$, use $W_Y(t)\to W_\infty(t)=|t|^{-\beta}$. In ordinary even $L^2$, the orthogonal projections onto $W_Y^{1/2}V_Y$ converge strongly to the limit weighted-band projection. Indeed, a bounded sequence from these subspaces with weak limit $z$ gives $W_Y^{-1/2}z_Y\to W_\infty^{-1/2}z$ in distributions along the weakly convergent sequence, by the reciprocal bound and dominated convergence against Schwartz functions. Band support passes to that limit. Conversely, $W_Y^{1/2}f$ tends strongly to $W_\infty^{1/2}f$ for strictly bandlimited Schwartz $f$, a dense class in the limit band. Testing the projection identities against those approximants identifies every weak subsequential limit of projections of a fixed vector. Norms converge by the identity $\|Rv\|^2=\langle Rv,v\rangle$ for orthogonal $R$, proving strong convergence. The evaluation seeds $W_Y^{-1/2}\psi(-t)$ converge strongly, so their projected, normalized vectors $W_Y^{1/2}e_Y$ converge strongly as well. The limit projection of the seed is nonzero, as evaluation is nonzero on the limit band. Since $0\le p\le1$ tends to one off zero, $\|(1-p)e_Y\|_{H_Y}\to0$. The change in the rank-one trace is bounded by $\|A\|\|(1-p)e_Y\|$. This proves the stated defect relative to the sharp band.

## Normalized Haar and the multiplier limit

On the positive half-line the raw even kernel uses the sum, not the average, of the kernels at $t-v$ and $t+v$; the average on the whole line becomes a sum on restriction. For the orthogonal projection, evaluation of $AQ_Y$ at $t$ has a representing vector in $V_Y$ since $Q_Y$ is on the right. These vectors depend continuously on $t$ in $H_Y$ by reproduction, and reproduction in the input variable then gives joint continuity of the kernel against the weighted Hilbert measure. For either kernel, compress to a compact position set away from zero containing the output support. This preserves trace by cyclicity. Approximate the identity there by orthogonal projections onto step functions in the weighted measure with mesh tending to zero. The finite traces converge to the trace by trace class, and to the integral of the diagonal by uniform continuity of the kernel against the weighted measure. Reexpressing the density against unweighted Haar leaves that integral unchanged. In the additive half-line coordinates, conversion of the Haar diagonal against $dt/t$ gives the raw sharp-band trace

$$\int_0^\infty p(t)\int\varphi(g)g^{-1/2}\bigl(\kappa_d((g^{-1}-1)t)+\kappa_d((g^{-1}+1)t)\bigr)\frac{dg}{g}\,dt.$$

For $a=g^{-1}\pm1$ the Dirichlet integral from zero to infinity of $\kappa_d(at)$ is $1/(2|a|)$. The error is uniform in $g\in[g_0,g_1]$, $d\in[d_0,1]$: The hole costs $O(\epsilon)$ by boundedness, the transition around $L$ costs $O(L^{-1/2})$ by the $1/t$ bound, and the oscillatory tail costs $O(1/L)$ by integration by parts. This proves the raw limit $J_\varphi$ for every allowed average and completes the comparison.

## Below norm one: The defect is not a sum of Mellin moments

Keep the same weights, levels, and cutoffs. Now take $\varphi$ supported in $[g_0,g_1]\subset(0,1)$, and write $j(g)=\sqrt g/(1-g^2)$ there. The two scalar limits are

$$\lim\operatorname{Tr}(M_p A P_q)=\int\varphi(g)j(g)\frac{dg}{g},\qquad
\lim\operatorname{Tr}(M_p A Q_Y)=\int\varphi(g)g^{-\beta}\bigl(j(g)-\sqrt g\bigr)\frac{dg}{g}.$$

Consequently the projection-minus-multiplier defect has density

$$h_\beta(g)=\sqrt g\,\frac{g^{2-\beta}-1}{1-g^2}\quad(0<g<1).$$

This is not a linear combination of $\sqrt g$ and $1/\sqrt g$ on any open subinterval of $(0,1)$. Real analyticity would extend such a relation to $(0,1)$; then $h_\beta(g)/\sqrt g\to-1$ at zero would force the combination to be $-\sqrt g$. But $h_\beta(g)/\sqrt g\to-(1-\beta/2)$ at one. In particular, on $C_c^\infty((1/2,1))$ the defect functional does not vanish on the common kernel of the two Mellin functionals: If it did, it would factor through their two-component moment map, giving the excluded density identity by testing against all bumps. This produces admissible tests strictly below one with both moments zero and unequal joint-cutoff local diagonals. The support avoids all nontrivial finite-place norm powers over $\mathbb Q$; it does not establish vanishing of an orbital quotient trace.

The provisional source interface is the same local level (11.2.1.6), pp. 488–489, and the **multiplier** calculation (12.4.1.8)–(12.4.1.12), p. 517. The digest-matched extraction of Theorem 12.5.1.1, p. 519, has a norm-one-vanishing test condition, not an above-one support restriction, and (12.5.1.3) displays the two $|\cdot|^{\pm1/2}$ Mellin terms. The distinction here is between two constructed **local** operators for that two-sided class. It neither contradicts the global above-one fixed-position theorem on p. 489 nor identifies the manuscript's global geometric piece.

### Transpose the dilation before removing the cutoffs

For a fixed $g\in[g_0,g_1]$ put

$$q_{Y,g}(t)=\frac{W_Y(gt)}{W_Y(t)},\qquad b_{Y,g}(t)=p(gt)q_{Y,g}(t).$$

For $T=R_Y,E_Y,Q_Y$, self-adjointness gives

$$\operatorname{Tr}(M_pD_gT)=\overline{\operatorname{Tr}(M_{b_{Y,g}}D_{1/g}T)}.$$

Indeed, write the trace on the positive half-line via the kernel of $T$ against the weighted measure, exchange its two arguments by Hermitian symmetry, and change variables $t=gv$. The Jacobian changes $g^{-1/2}$ to $g^{1/2}$, and the change of weight gives $q_{Y,g}$. This uses the fixed-cutoff trace/diagonal argument above, not cyclicity of operators whose products have not been shown trace class. That argument applies also to each individual dilation: The reproducing convolution just needs a fixed band containing $[-1/g_0,1/g_0]$. The fixed-cutoff kernels are jointly continuous away from zero, and uniformly bounded there on the compact $g$ range by reproduction. Hence the kernel formula for the integrated test permits Fubini at fixed cutoffs.

### The full-band projection can be replaced inside the contracted trace

First sharpen the preceding cell estimate to

$$\|M_b C_\psi\|_1\le C\sum_{n\in\mathbb Z}\sup_{t\in[n,n+1]}|b(t)|.$$

Use the same Fourier series on each cell. For $|n|\ge2$ the output vector norm is at most $C W_Y(n)^{1/2}\sup_{[n,n+1]}|b|$. In the squared input functional norm multiply the reciprocal-weight integral by $W_Y(n)$, and use the weight ratio bound. On $|v|\ge |n|/2$ the ratio is bounded by $C(1+|n-v|)^\gamma$. On $|v|<|n|/2$, bound the squared Schwartz coefficient by $C_N(1+|n|)^{-2N}$ times the rapid decay in its series index; the integral of $(|n|/|v|)^\gamma$ on that interval is $O(|n|)$. The input norm thus costs at most $C W_Y(n)^{-1/2}$ times the rapid decay in the series index. The weight cancels in the product. The finitely many remaining cells use the earlier bound and uniform local integrability.

In $b_{Y,g}$ fill the central hole, costing $O(\epsilon^{(1-\gamma)/2})$ in localized trace norm by the original cell estimate and boundedness of the weight ratio. Modify $q_{Y,g}$ on $|t|\le1$ by smoothly interpolating to $g^{-\beta}$ for $|t|\le1/2$, and call the result $q^\sharp$. The sup norm error is $O(1/\log Y)$ uniformly there: With $x=\log(|t|/Y)$ the exponential ratio is exactly $g^{-\beta}$ there for large $Y$, and $F(x+\log g)-F(x)=O(1/\log Y)$ for $F(x)=\log(1+x^2)$. The sharpened estimate controls this error on the finitely many cells. Let $B_0(t)=U_L(gt)q^\sharp(t)$.

The first derivative of $q^\sharp$ is uniformly bounded in $L^1$ by the log-variable variation estimate below. The distributional second derivative has total variation $o(1)$. In fact, the first two log-coordinate derivatives of $q_{Y,g}$ are uniformly bounded off the finitely many breakpoints, so $|(q^\sharp)''(t)|\le C/t^2$ for $|t|\ge1$ off them. For fixed $t$ this derivative tends to zero since $x\to-\infty$ and the log-polynomial ratio tends to a constant with derivatives tending to zero. The jumps in the first derivative at $|t|=Y$ and $|t|=Y/g$ contribute $O(1/Y)$ to the second derivative measure. On the fixed interpolation region the differentiated error tends uniformly to zero, and the function is constant near zero. These bounds and convergences hold uniformly for $g\in[g_0,g_1]$. Since $\|(U_L(g\cdot))'\|_\infty$ and $\|(U_L(g\cdot))''\|_{L^1}$ are $O(L^{-1/2})$ by differentiating the convolution, the product rule gives $\|B_0''\|_{\rm TV}=o(1)$.

Choose an even smooth symbol $m$ equal to one near zero with support of radius less than $1-g_1$. Its inverse Fourier transform $K$ is Schwartz with integral one and first moment zero. Set $B_1=K*B_0$. Taylor's formula with second derivative measure bounds the remainder after subtracting the linear term in $B_0(t-v)-B_0(t)$ by $|v|\,|B_0''|([t-|v|,t+|v|])$, using a one-sided derivative at a corner. The linear term cancels against $K$. Taking the sup over each cell and summing, the enlarged cell intervals overlap at most $3+2|v|$ times. Hence

$$\sum_n\sup_{[n,n+1]}|B_0-B_1|\le \|B_0''\|_{\rm TV}\int|K(v)|\,|v|(3+2|v|)\,dv=o(1).$$

The sharpened localization estimate (with reproducing convolution after the dilation) now bounds the error from replacing $b_{Y,g}$ by $B_1$ in the trace of $M_{b_{Y,g}}D_{1/g}(R_Y-P)$. The operator with $B_1$ is trace class by Schwartz decay. It has range in the unit band (the contracted band has radius at most $g_1$) and vanishes upon right composition by $P$ because $(R_Y-P)P=0$. Left composition by $P$ fixes it, so cyclicity gives zero trace. Thus the original contracted trace of the full-band difference is $o(1)$ uniformly in $g$. This does not assert trace-norm convergence to zero of the full-band difference itself.

### Evaluate the two contracted pieces

For the sharp multiplier inserted after transposition, the unweighted half-line diagonal is $\sqrt g\,[\kappa_1((g-1)t)+\kappa_1((g+1)t)]$. The factors $b_{Y,g}$ are uniformly bounded, have uniformly bounded total variation on $(0,\infty)$, and tend pointwise there to $g^{-\beta}$. For the variation bound, in $x=\log(t/Y)$ the exponential weight ratio is $e^{\beta(|x+\log g|-|x|)}$, which is bounded and monotone. The other factor is $e^{r(F(x+\log g)-F(x))}$ for $F(x)=\log(1+x^2)$. Its logarithmic derivative has uniformly bounded $L^1(dx)$, since $F''\in L^1$ and $|\log g|$ is bounded. Multiplication by $p(gt)$ preserves the uniform bound on variation: $U_L$ is an average of translated interval indicators, and $1-\chi$ has finite variation. Integration by parts bounds the oscillatory tail from $T$ onward by $C/T$ using this variation bound and separation of $g\pm1$ from zero. On compact intervals dominated convergence applies. The contracted multiplier trace thus tends to $g^{-\beta}j(g)$, using the Dirichlet integral. For the original, untransposed $P_q$ the same Dirichlet integral as in the above-one calculation gives $j(g)$ uniformly in the allowed band averages; the absolute value in $|g^{-1}-1|$ matters. These estimates also bound the traces uniformly in $g$ for passage to the test integral.

For the rank-one part, $\operatorname{Tr}(D_{1/g}E_Y)=\sqrt g$ by evaluation at zero on the full band, since $D_{1/g}$ contracts the band. The strong convergence of the unit-normalized $W_Y^{1/2}e_Y$ proved above, boundedness of $b_{Y,g}$, and its pointwise limit give $\|(b_{Y,g}-g^{-\beta})e_Y\|_{H_Y}\to0$. The change of the rank-one trace upon replacing $b_{Y,g}$ by $g^{-\beta}$ is bounded by this norm times $\|D_{1/g}\|$, uniformly bounded in $g$ by the weight ratio estimate. The contracted rank-one trace therefore tends to $g^{1/2-\beta}$ and is uniformly bounded in $g$.

The above- and below-one formulas add for any smooth test whose support has positive distance from one. A separate Yah analyst checked the transpose, weighted cell estimates, cutoff errors, and both scalar factors in the below-one calculation. The manuscript locators are from digest-verified text extraction, not rendered pages.

**Still owed:** Neither one-sided calculation identifies the local invariant projection, the raw multiplier, or the normalized scalar kernel with the global geometric piece. For this cutoff family the multiplier cannot replace the local projection on the full moment-zero test class, so a bridge would have to use the actual global levels or supply additional terms. The computations also do not handle tests touching norm one, general cutoff profiles, or the orbital shell operator.
