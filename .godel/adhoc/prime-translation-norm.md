# The prime-translation norm on an expanding Weil window

**Decision.** Can cancellation among character values lower the operator cost of the prime term *before* using the archimedean energy of the same test? No. On each finite window all the unit phases can be undone in operator norm by modulation, even after an arbitrary compact correction in the Rayleigh quotient. The cost is asymptotic to $e^{D/2}$ on an interval of length $D$, not the scalar total-variation cost $4e^{D/2}$. For zeta, subtracting the two poles from the prime operator still leaves this same leading cost. These are statements about parts of the form, not negative witnesses for the Weil form.

One positive payoff is an unconditional bound on *whole* right-hand Pick matrices for primitive nonprincipal characters of large conductor $q$. Fix $0<\kappa<1$. At reciprocal budget $b\le \log\log q+\log\kappa$, with all real nodes at least $(\log\log q)^3$, the lower bound relative to the Cauchy Gram matrix is $(1-\kappa-o(1))\log q$. The previous [block-to-window argument](pick-block-weil-window.md) used a fixed fractional loss in the budget to get a positive margin. Here the loss in budget is additive. No assertion at $\kappa=1$ follows.

## 1. Norm and phases

Work on $L^2[0,D]$ with zero extension. Write $S_t u(x)=u(x+t)$ restricted to the interval. Put

$$
 T_\chi=\sum_{n<e^D}\frac{\Lambda(n)}{\sqrt n}
 [\chi(n)S_{\log n}+\overline{\chi(n)}S_{\log n}^*].
$$

Use $T$ for all coefficients untwisted, and $T_{(q)}$ for the untwisted operator omitting $(n,q)>1$. The sign in the Weil form is **minus** $T_\chi$. The strict cutoff does not affect the operator. For every $D$ and Dirichlet character modulo $q$,

$$
 \sup_{\|u\|=1}\langle T_\chi u,u\rangle=\|T_\chi\|=\|T_{(q)}\|.
$$

In fact $M_y u(x)=e^{iyx}u(x)$ multiplies each forward coefficient by $n^{iy}$ under conjugation $M_y^*T_\chi M_y$. Unique factorization implies the logs of the finitely many active primes are rationally independent. Kronecker's theorem for a continuous one-parameter flow gives $y_j\to+\infty$ such that $p^{iy_j}\to\overline{\chi(p)}$ at each active $p\nmid q$. Thus $M_{y_j}^*T_\chi M_{y_j}\to T_{(q)}$ in norm, including the prime powers. The top of the untwisted spectrum equals the norm since the absolute value of any quadratic form value is bounded by the form on $|u|$. Moreover $M_{y_j}u\rightharpoonup0$ for fixed $u$ by Riemann-Lebesgue. For every compact self-adjoint $K$ this proves

$$\sup_{\|v\|=1}\langle(T_\chi-K)v,v\rangle\ \ge\ \|T_{(q)}\|.$$

One can use smooth interior tests by density. There is no upper bound here on the modulation cost $\log(2+|y_j|)$; neglecting this cost in the *full* form would reverse the proof decision.

## 2. A sharp endpoint weight

Set $E=e^{D/2}$, $f(x)=e^{-x/2}$, $g(x)=f(D-x)$, and $w=f+g$ inside the interval. Write $\psi(X)=\sum_{n\le X}\Lambda(n)$ and $U(s)=\sum_{n\le e^s}\Lambda(n)/n$. Off finitely many endpoints one has exactly

$$ Tf(x)=f(x)[U(D-x)+\psi(e^x)], \qquad Tg(x)=(Tf)(D-x). $$

The ordinary prime number theorem gives $U(s)=O(1+s)$ by partial summation and, for any $\delta>0$, $|\psi(X)-X|\le\delta X+C_\delta$ for every $X\ge1$. Since $f(x)e^x=E g(x)$, this gives the pointwise estimate

$$|Tf-Eg|\le \delta E g+[C_\delta+O(1+D)] f.$$

Adding its reflection gives $(1-o(1))Ew\le Tw\le(1+o(1))Ew$ uniformly as $D\to\infty$ (first fix $\delta$, then let it tend to zero). The upper inequality is a Schur bound on the **whole** space: In each shift pairing use $2|u(x)u(z)|\le |u(x)|^2w(z)/w(x)+|u(z)|^2w(x)/w(z)$. The lower inequality tested on $w$ gives the reverse asymptotic. Thus $\|T\|=(1+o(1))E$. In comparison, $2\sum_{n<e^D}\Lambda(n)/\sqrt n\sim4E$ by partial summation.

A direct normalization check: For $0\le t\le D$ and $s=D-t$, the autocorrelation of $w$ is $2e^{-t/2}(1-e^{-s})+s(e^{-s/2}+e^{-(D+t)/2})$. Substitution into the finite prime-power sum gives $\langle Tw,w\rangle/(E\|w\|^2)$ about $1.05736$ at $e^D=10^4$ and $1.01059$ at $10^6$, versus normalized scalar costs $3.94932$ and $3.99381$. These floating-point comparisons are not used for the inequalities.

For growing $q$ we lose at most $O(\sqrt{\log q})$ in norm from the omitted primes. Indeed the loss is bounded by $2\sum_{p\mid q}\log p/(\sqrt p-1)$. For $p\le\log q$ use partial summation with $\psi(X)=O(X)$ to get $O(\sqrt{\log q})$; above this cutoff use $\sum_{p\mid q}\log p\le\log q$. Hence for $E\asymp\log q$, the norm of the signed prime operator alone is $(1+o(1))E$ uniformly in the character. Using *only* this norm and a scalar archimedean floor $\log q+O(1)$ cannot prove positivity past $E=(1+\delta)\log q$ for any fixed $\delta>0$.

## 3. What subtracting the zeta poles changes

The pole operator $R$ has kernel $2\cosh((x-z)/2)$, hence $R=E(f\otimes g+g\otimes f)$ with $(a\otimes b)u=a\int\overline b u$. It is not positive semidefinite. For $\Pi$ the orthogonal projection onto $\operatorname{span}\{f,g\}$,

$$ \|(T-R)\Pi\|=o(E),\qquad \sup_{\|u\|=1}\langle(T-R)u,u\rangle=(1+o(1))E.$$

Indeed $\|f\|^2=\|g\|^2=1-e^{-D}$ and $\langle f,g\rangle=D/E$. The endpoint estimate proves $\|Tf-Eg\|=o(E)$, and the Gram entries show the same for $\|Rf-Eg\|$. Reflect to handle $g$. The two-vector Gram matrix tends to the identity, proving the first assertion in operator norm. By self-adjointness, $T-R$ differs from $(1-\Pi)T(1-\Pi)$ by $o(E)$ in norm, giving the upper bound. The compact-correction argument in section 1, with untwisted coefficients and $K=R$, gives the lower bound for the supremum. Thus the leading prime mass cancels on the two smooth endpoint profiles but **not uniformly on the orthogonal complement**. A zeta proof using those pole cancellations still needs the archimedean cost of oscillation.

## 4. A whole-block conductor estimate

Use the Hermitian Pick matrix $P_\chi$ of the conductor-normalized logarithmic derivative and $C_{mn}=1/(m+n)$ as in the [block note](pick-block-weil-window.md). The archimedean form is bounded below by $(\log q-O(1))\|h\|^2$ uniformly in parity: In the log-multiplier representation $\ell$ is bounded below and the correction $G_{1/2+a}$ is in $L^1$. On a compact window of length $D$ the remaining cost is at most $\|T_{(q)}\|\le\|T\|$. To use this for growing blocks one must control **leakage**; a fixed-window limit does not suffice.

Let $A=\log\log q$, fix $0<\kappa<1$, and put $b_*=A+\log\kappa$. On any finite set of distinct real nodes $m\ge A^3$ with $\sum 1/m\le b_*$, normalize the exponential polynomial $h(x)=\sum c_m e^{-mx}$ on $[0,\infty)$ to $\|h\|_2=1$. This is Cauchy-Gram normalization. With $\eta=A^2$ and $d=2b_*+A^{-1/2}$ the half-line shift bound of the block note gives

$$ \|1_{[t,\infty)}h\|_2\le e^{H-\eta t},\qquad H=\sum_m\log\frac{m+\eta}{m-\eta},\qquad H/\eta\le 2b_*+O(A^{-1}). $$

Here the Taylor remainder after division by $\eta$ is $O(\eta^2\sum m^{-3})=O(A^{-1})$, uniformly. In particular $H-(\eta-2)d\to-\infty$. For shifts $t=\log n>d$, $|A_h(t)|\le e^{H-\eta t}$, and the prime cost there is $O(e^{H-(\eta-2)d})$ since $\sum \Lambda(n)n^{-5/2}<\infty$. For $0\le t\le d$ replace $h$ by $v=1_{[0,d]}h$: Each correlation changes by at most $2\|h-v\|_2\le2 e^{H-\eta d}=o(1)$. The sum of absolute coefficients up to $d$ is $O(e^{d/2})$, so the replacement costs $o(e^{d/2})$. This cutoff is used only in the prime term. On $v$ the upper bound on the prime operator is $(1+o(1))e^{d/2}\|v\|^2$. Since $e^{d/2}=(\kappa+o(1))\log q$, the claimed matrix inequality follows uniformly over these node sets. It proves neither GRH at fixed conductor nor a sign at the limiting critical constant.

**Follow-up after this run.** The [endpoint arithmetic test](../bob/endpoint-arithmetic-test.md) separates a necessary bound for every quadratic character of prime conductor from a sufficient bounded-frequency multiplier estimate. The [most-character result](../alice/prime-conductor-window.md) already controls localization and obtains a saving with an exceptional set at each prime conductor. What remains uniform is an arithmetic question even on the single unmodulated endpoint profile.
