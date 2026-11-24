# A first-law refit cuts the named triple-mask slack, but does not defeat it

In the [fixed-translate $(10,2)$ comparison](paired-10-2.md) at $c=39/20$, use the ordered second shifts $s=(-7,6,19)/25$ at $3t$ and the **multiplier** weights $h=(3,5,4)/12$. The [new rational first law](triple-named-refit.txt) has mean $8/9+4.0395771270\ldots\times10^{-7}$ and satisfies both first caps on the whole real line. For this law the **least** achievable normalized real response on $H(x)=\sum_j h_j e^{is_jx}$ lies in

$$ (0.00061834386,\ 0.00061834637). $$

Thus any lower separation margin for this direction uniform in the admissible first law is less than $0.000619$, more than four times smaller than the [five-law library's lower bound](three-shift-library.md). The number is positive, so the refit does **not** even annihilate the named scalar mask, let alone provide simultaneous zero answers. It does not establish a positive lower bound for arbitrary laws. A joint separator using other weights is not tested by this conclusion.

## First laws and both caps

A row gives $128z_j$ followed by integer pairs $(10^8 X,10^8 p)$ for the law of $X=\cos\theta$ on $[z_j,z_{j+1})$. Set $X=0$ before $-12$ and extend the last slab from $16$ to infinity. Check support and normalization row by row. Recompute $A=\mathbb E X$, $B=\mathbb E(4X^3-3X)$, and $U=\mathbb E\sqrt{(1+X)/2}$ from the same law, with no replacement of $B$ by the cubic of $A$. Integrating $U$ against $z_+e^{-z}\,dz$ uses differences of the tail $(1+z)e^{-z}$ on $z\ge 0$, with tail $1$ on $z\le 0$.

For $Y=A,B$ write $b_a=e^{-a/2}\Delta Y(a)$ and $G_Y=\sum_a b_ae^{iax}/(1/2+ix)$. Indeed, integrating $Y$ on slabs gives $w\int Y(z)e^{-wz}\,dz=\sum_a b_ae^{-iax}$ for $w=1/2+ix$; conjugation and division by $w$ give the first representer in [the comparison](single-shift-10-2.md). We check

$$\|G_A\|_\infty<C_{10}-10^{-7},\qquad \|G_B\|_\infty<C_1-10^{-7},\qquad
C_1=\cosh(c)/3,\quad C_{10}=C_1/(2\cos(\pi/12)).$$

The first cap permits the twelve-angle law with vanishing orders two through ten at $t$, and the second permits the circle mean $m=-G_B/C_1$ at $3t$. These first moments match all real first translates, not only those used in the numerical refit. For the cap test at value $b$, center the numerator at $-2$ (a pure phase change) and bound the real function $|N|^2-b^2(1/4+x^2)$ by Taylor expansion to order three. With $D_k=\sum_a |b_a||a+2|^k$, its global fourth derivative in absolute value is at most $\sum_{k=0}^4\binom{4}{k}D_kD_{4-k}$. Dyadic boxes check strict negativity on $[0,64]$; conjugation and $D_0/64<b$ handle the rest. The replay separately checks the slab and jump expressions at three rational frequencies.

## Exact directional minimum

Use $d\mu=dx/(2\pi|1/2+ix|^2)$ and $v=1-|m|^2$. The second disk consists of $m^2+vg$ with $|g|\le1$. For a unit circle variable $Z$ of mean $m$, necessity is $|\mathbb E(Z-m)^2|\le \mathbb E|Z-m|^2=v$. A chord in direction $e^{i\alpha}$ through $m$ has boundary second moment $m^2+ve^{2i\alpha}$ when its endpoint weights give mean $m$. Mixing opposite directions on this second-moment disk fills it. Thus the minimum real response is

$$\Re\int Hm^2\,d\mu-\int |H|v\,d\mu,$$

attained by the measurable choice $g=-\bar H/|H|$ when $H\ne 0$. The choice respects conjugation at opposite ordinates. Allowing interior depths does not improve this minimum: The [strip exit construction](three-shift-library.md) converts those first and second moments to an edge law, and the real first answers at all translates pin the conjugation-symmetrized mean by Fourier uniqueness. The sign here is **center minus capacity**, not its negative.

Let $S(s)=\int e^{isx}m^2\,d\mu$ and $R(d)=\int e^{idx}v\,d\mu$; conjugation makes both real. The [sum and difference kernels](single-shift-10-2.md#matching-with-one-shift-at-a-time) give, with $\beta_a=b_a/C_1$ formed from $B$,

$$\begin{aligned}
S(s)&=\sum_{a,b}\beta_a\beta_b (1+y_++y_+^2/2)e^{-|y|/2},\qquad y=a+b+s,\\
R(d)&=e^{-|d|/2}-\sum_{a,b}\beta_a\beta_b(2+|a-b+d|)e^{-|a-b+d|/2}.
\end{aligned}$$

In particular the center is $\sum_j h_jS(s_j)$. To compute the capacity without quadrature, put $u=13x/25$ and $|H|=\sqrt{q(u)}$, where $q=a+2b\cos u+2d\cos(2u)$ with $a=\sum_j h_j^2$, $b=h_1(h_0+h_2)$, $d=h_0 h_2$ (indices start at zero). For $\rho=1/20$, $q$ has real part at least $a-2d-b^2/(4d)-\eta>0$ on $|\Im u|\le\rho$, where $\eta=2b(\cosh\rho-1)+2d(\cosh(2\rho)-1)$. The principal square root is analytic there and bounded by $\sqrt{1+\eta}<2$, since $|\cos(j(u+iv))|\le\cosh(jv)$ and $q(0)=1$. Shifting the Fourier integrals gives $|c_k|\le 2e^{-\rho|k|}$ for the Fourier coefficients of $\sqrt q$.

The ball FFT of $n=1024$ equally spaced values gives $p_k=\sum_j c_{k+jn}$ after division by $n$. Replace the full series with $\sum_{|k|<n/2}p_k e^{iku}$, omitting the Nyquist residue. Each discarded coefficient contributes at most once to the alias error on the retained residues. The uniform error is at most twice the full discarded absolute tail, hence at most $8e^{-\rho n/2}/(1-e^{-\rho})<1.3\times 10^{-9}$. Since $0\le v\le1$ and $\mu$ is a probability, the capacity can be enclosed by applying the same error to $p_0R(0)+2\sum_{1\le k<n/2}\Re(p_k)R(13k/25)$. The checked center is $0.4245246115035\ldots$ and the capacity is in $(0.42390626514,0.42390626765)$.

**Replay.** From the repository root, run `/opt/sage-10.9/bin/python .godel/bob/check-triple-named-refit.py` (or a Python interpreter with SageMath 10.9 available; assertions enabled). It uses exact rationals and 128-bit outward-rounded Sage balls. No optimizer, sampled-cap assumption, or scratch file is required.

**Search limit and next decision.** The table came from a sampled convex refit in slabwise moment hulls with first-cap peak exchange, followed by rational atom recovery and exact replay. Finer numerical fits that did better on the scalar objective but missed moment-hull or cap constraints were not admissible. This search is not an infeasibility argument, and the checked slack applies only to the stated scalar direction. A further primal search should demand feasibility slack before pricing the second disk; a simultaneous endpoint needs either a common measurable $g$ or the support test in every real direction for one fixed law. No arithmetic prime or zero data are constructed here.
