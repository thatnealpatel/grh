# A leading-coefficient filter for the principal zero packet

This sharpens the radius in [the localized principal packet](localized-principal-packet.md) at base `7f754b7cce0daad155c9d586eb9fef3432aa1d8d`. Assume every nontrivial zeta zero has $\beta\le 7/8$, hence $1/8\le\beta\le7/8$ by reflection. Count zeros with multiplicity. Put

$$ t=2q^{3/5},\quad X=(3\log(t/2))^2,\quad D=\log X,\quad u=\gamma-t,\qquad
S_X(t)=X^{-1}\sum_{p<X}(\log p)\log(X/p)p^{-it}. $$

Suppose $\Re S_X(t)\ge47/81-o(1)$ along the heights in question as $q\to\infty$. For each fixed $L>1/(2\pi)$ and $c>0$ with $\cosh c<571343/319032$, the filter below gives a fixed $K$ and the radius $J=L\log D+K$, at which

$$ B_J(t;c):=\sum_{|u|\le J,\ \beta>1/2+c/D}\frac{1}{1+u^2}\gg_{L,c} X^{1/8}. $$

More precisely, for that filter either the signed local off-line term $\mathcal R_J$ in (4) is at least a fixed positive constant or $B_J(t;c)\gg_{L,c}\log t$. For the smaller range $\cosh c<47/27$ there is a version of the filter with $\mathcal R_J\gg_{L,c}1$ directly, without the count alternative. These are implications of the peak hypothesis, not bounds excluding peaks. The change is in the coefficient of $\log D$, with an $O_{L,c}(1)$ additive cost, not an improvement to $o(\log D)$.

## Filter and prime comparison

Set $k=1/L$ and choose fixed $0<a_0<a_1<1/2<1<b<2$ with $k(b-a_0)<\pi$, possible since $k<2\pi$. Set $d=(a_0+b)/2$, $A_*:=\cos(k(b-a_0)/2)>0$. Use $h=\log(8/7)$, except that the direct signed version takes $h=0$. For a small **fixed** $\lambda>0$ use

$$ G_\lambda(s)=\exp\{\lambda(1-\cos(k(s-d)))\},\qquad M(s)=\cosh^2(hs)G_\lambda(s). $$

This multiplier is entire. On $a_0\le\sigma\le b$,

$$ |G_\lambda(\sigma+iu)|\le \exp\{\lambda-\lambda A_*\cosh(ku)\}. \tag{1} $$

The amplitude $\lambda$ controls the prime perturbation independently of the frequency $k$ that controls the tail. With Fourier convention $\widehat f(u)=\int f(v)e^{-iuv}\,dv$, use the inverse Laplace weight

$$ W_\lambda(v)=\frac{1}{2\pi}\int_{\mathbb R} e^{(\sigma+iu)v}\frac{M(\sigma+iu)}{(\sigma+iu)^2}\,du,
\qquad a_0\le\sigma\le b. $$

It is real by conjugation and independent of $\sigma$ by contour shifting, since $a_0>0$ and (1) is uniform. Omitting $G_\lambda$ gives $W_0(v)=\mathbb E(v+Z)_+$, where $Z=V+V'$ and $V,V'$ are independent equiprobable $\pm h$: the ramp $v_+$ has Laplace transform $1/s^2$, and translation gives $e^{sZ}/s^2$. The original cutoff uses the continuous value $v_+=0$ at $v=0$, with no half-weight convention. The modified weights may be nonzero there.

On each boundary line $\sigma=a_0,b$ the $L^1(du)$ norm of $(G_\lambda(s)-1)\cosh^2(hs)/s^2$ tends to zero as $\lambda\downarrow0$, by boundedness of the numerator for $0<\lambda\le1$ and pointwise convergence. Invert on $a_0$ for $v\ge0$, on $b$ for $v<0$. Then $|W_\lambda-W_0|(v)$ is at most $o_{\lambda\downarrow0}(1)$ times $e^{a_0 v}$ and $e^{b v}$, respectively. For $v=\log(X/n)$ these envelopes have bounded mass against $X^{-1}\Lambda(n)$: Chebyshev on dyadic intervals below and above $X$ gives geometric sums with ratios $2^{-(1-a_0)}$ and $2^{-(b-1)}$. Write $\eta(\lambda)=o_{\lambda\downarrow0}(1)$ for the resulting absolute cost, uniform in $X$ with the strip, $k$ and $h$ fixed.

By convexity $W_0(v)\ge v_+$. The PNT at $Xe^{-2h},X,Xe^{2h}$ gives a total increase in prime weight of $A_h+o(1)$, where $A_h=\mathbb E e^Z-1=\cosh^2 h-1$: the mass $Y^{-1}\sum_{p<Y}(\log p)\log(Y/p)$ tends to one. Prime powers in $W_0$ contribute $O_h(X^{-1/2}D^3)$ in absolute value, by counting at most $O_h(\sqrt X D)$ of them below $Xe^{2h}$. Thus, for $T_M=X^{-1}\sum_n\Lambda(n)n^{-it}W_\lambda(\log(X/n))$,

$$ \Re T_M\ge \Re S_X(t)-A_h-\eta(\lambda)-o(1). \tag{2} $$

The sign in (2) comes from subtracting the absolute error, not from ordering the oscillatory prime sums. This comparison starts at the original cutoff and includes the weight change at its endpoint.

## Explicit formula and tail

Here are the zero estimates used in the shift and the signed comparison. For the entire completion $\xi(s)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)$, subtraction of its Hadamard logarithmic derivatives at $\sigma+iy$ and $1-\sigma+iy$, followed by reflection of the zeros, gives

$$ \sum_\rho \frac{\sigma-\beta}{(\sigma-\beta)^2+(\gamma-y)^2}=\Re\frac{\xi'}{\xi}(\sigma+iy),\qquad \sigma>1. \tag{3} $$

Indeed the functional equation and conjugation double the real part on the right before division by two; the two real zero kernels have equal sums. At fixed $\sigma>1$ the right side is $\tfrac12\log(2+|y|)+O_\sigma(1)$ by the Euler product and Stirling. At $\sigma=2$ this gives $\sum_\rho(1+|\gamma-y|^2)^{-1}\ll\log(2+|y|)$ and the corresponding unit counts. Summing the unit counts in shells gives, for $R\ge1$,

$$ \sum_{|u|>R}(1+u^2)^{-1}\ll\frac{\log(2+t)+\log(2+R)}{R}. $$

Insert the inverse weight on $b>1$ to obtain $-(\zeta'/\zeta)(s+it)X^{s-1}M(s)/s^2$. Choose the new line $\alpha\in[a_0,a_1]$ by averaging rather than requiring a fixed zero-free margin. On this interval the local expansion of $\zeta'/\zeta(\sigma+iy)$ is the sum of $(\sigma+iy-\rho)^{-1}$ over $|\gamma-y|\le1$ plus $O(\log(2+|y|))$. To see this, subtract the Hadamard derivative at $2+iy$: the distant differences are bounded by the inverse-square count, and removing the Gamma and rational factors costs at most the stated error on this left interval. In the average over $\sigma\in[a_0,a_1]$ and $y=t+u$ with weight $(1+u^2)^{-1}$, each local pole costs $O((1+|\gamma-t|^2)^{-1})$ since $1/\sqrt{x^2+y^2}$ is locally integrable in two dimensions. Hence there is an $\alpha$ off the countable set of zero real parts with

$$ \int_{\mathbb R}\left|\frac{\zeta'}{\zeta}(\alpha+i(t+u))\right|\frac{du}{1+u^2}\ll_{a_0,a_1}\log(2+t). $$

For the shift choose upper and lower horizontal ordinates tending to infinity in modulus, which after translation by $t$ stay at distance $\gg1/\log(2+|t+\Im s|)$ from every zero ordinate. Deleting small neighborhoods in far unit intervals is possible by the unit counts. The same local expansion on the horizontal slab (at large shifted height) bounds $\zeta'/\zeta$ there by $O(\log^2(2+|t+\Im s|))$; (1) kills these integrals. The new vertical costs $O(X^{a_1-1}\log(2+t))=o(1)$. The translated zeta pole contributes $+X^{-it}M(1-it)/(1-it)^2=O(t^{-2})$; neither $s=0$ nor trivial zeros are crossed. For each crossed zero the contribution is $-R_M(\rho)$, where

$$ R_M(\rho)=\frac{X^{\beta-1+iu}M(\beta+iu)}{(\beta+iu)^2}. $$

The crossed zeros with $\beta\le a_1$ cost $O(X^{a_1-1}\log(2+t))$ by the inverse-square count and $\beta\ge1/8$. Thus we can use the fixed selection $\beta>a_1$ in the residue sum irrespective of the choice of $\alpha$.

Take $J=k^{-1}\log D+K$ with $K\ge0$ fixed so that $\lambda A_*e^{kK}/2>3/8$. Using (1), the strip endpoints and the inverse-square count, the entire outer residue tail is bounded by

$$ O\!\left(X^{-1/8}\log(2+t)\exp\{\lambda-\lambda A_*\cosh(kJ)\}\right)=o(1), $$

since $\log t=\sqrt X/3+\log2$. These estimates take $q\to\infty$ only **after** fixing the strip and $\lambda$. The constant $K$ may grow as $\lambda A_*$ shrinks; no endpoint claim at $L=1/(2\pi)$ follows.

## Signed local margins

Call the zeros with $|u|\le J$ and $|\beta-1/2|\le c/D$ good; all have $\beta>a_1$ eventually. Define the signed off-line term by

$$ \mathcal R_J=-\Re\!\sum_{|u|\le J,\ \beta>a_1,\ |\beta-1/2|>c/D} R_M(\rho). \tag{4} $$

The shift and (2) show

$$ \mathcal R_J\ge 47/81-A_h-\eta(\lambda)-\sum_{\rm good}|R_M(\rho)|-o(1). \tag{5} $$

Reflection across the critical line preserves $u$ and the multiplicity. Each bad right member counted by $B_J$ accounts for itself and at most one reflected member per copy in (4). The bounded multiplier and $1/8\le\beta\le7/8$ give $|\mathcal R_J|\ll X^{-1/8}B_J$. Equality at $|u|=J$ is local, and at $|\beta-1/2|=c/D$ is good.

For the larger range use $h=\log(8/7)$. Along any sequence with $B_J=o(\log t)$, the good ordinate measure divided by $\log t$ tends to $du/(2\pi)$ against continuous kernels $O((1+u^2)^{-1})$. For this, fix $a>1/2$ and $v\in\mathbb R$ and use (3) at $\sigma=1/2+a$, $y=t+v$. Omitting bad local pairs costs $O_{a,v}(B_J)$, and omitting outer zeros costs $O_{a,v}((\log(2+t)+\log(2+J))/J)$. Replacing $\sigma-\beta$ by $a$ on the good set costs $O(D^{-1})$ after normalization. Therefore every vague limit has integral $1/2$ against $a/(a^2+(u-v)^2)$. The unit counts give vague compactness, translation-bounded limits and vanishing inverse-square tails in the limsup as $R\to\infty$. The Poisson integrals are holomorphic in $a$ for $\Re a>0$ (domination on compact subsets), so the identity extends to all real $a>0$. The Poisson approximate identity, tested on compactly supported continuous functions, identifies the limit as $du/(2\pi)$: off an enlarged support the convolved test is $O(a/(1+u^2))$ as $a\downarrow0$, so the identification is valid for these translation-bounded measures. This uses the full zero set in (3), including zeros not crossed in the shift.

For good zeros replace $|\cosh(h(\beta+iu))|^2/(\beta^2+u^2)$ by $K_h(u):=|\cosh(h(1/2+iu))|^2/(1/4+u^2)$ with additive error $O_{h,c}(D^{-1}/(1+u^2))$. In the numerator keep $X^{\beta-1}$ and pair reflected zeros: the average per copy is at most $X^{-1/2}\cosh c$, also valid on the line. With $|G_\lambda|\le e^\lambda$, the preceding measure limit bounds the good charge by $e^\lambda\cosh(c)I_h/3+o(1)$, where

$$ I_h=\frac{1}{2\pi}\int K_h(u)\,du=\mathbb E\exp((V+V'-|V-V'|)/2)=\frac{211}{224}. $$

Here the Fourier integral of $(1/4+u^2)^{-1}$ is $2\pi e^{-|v|/2}$. Since $A_h=225/12544$, fix $\lambda>0$ so small that

$$ 47/81-225/12544-\eta(\lambda)-e^\lambda\frac{211}{224}\frac{\cosh c}{3}>0. $$

Such a choice exists for $\cosh c<571343/319032$. On sequences with $B_J=o(\log t)$, (5) gives a positive liminf at least this gap. Taking a fixed fraction of the gap shows the claimed uniform alternative: otherwise a sequence with $B_J/\log t\to0$ and $\mathcal R_J$ below that fraction would contradict (5). Both branches imply $B_J\gg X^{1/8}$.

For the direct signed conclusion take $h=0$, so $A_h=0$. At $\sigma=1+1/D$, $y=t$, (3) has right side at most $\tfrac12\log t+O(D^2)$ by Stirling and $|\zeta'/\zeta|\le\sum_{n\ge2}(\log n)n^{-1-1/D}\ll D^2$. Its terms are positive, and on good zeros the kernel is $(1+O_c(D^{-1}))K_0(u)/2$ uniformly in $u$. Drop the other terms and pair the good residues as above to get $\sum_{\rm good}|R_M|\le e^\lambda\cosh(c)/3+o(1)$, with no count hypothesis. If $\cosh c<47/27$, choose $\lambda$ so that $47/81-\eta(\lambda)-e^\lambda\cosh(c)/3>0$. Then (5) gives the signed margin directly.

## Obstruction for a bounded analytic absolute tail certificate

Allow $D$-dependent multipliers $M_D$ holomorphic on $1/2<\Re s<1$ and continuous on the closed strip, with $|M_D(s)|\le B$ there and $|M_D(3/4)|\ge m>0$ for fixed $B>m$. Impose the positive-ordinate unit-count certificate, for $J\ge0$,

$$ \sum_{j\ge0}\log(2+t+J+j+1)
\sup_{\substack{1/2\le\beta\le7/8\\J+j\le u\le J+j+1}}
\frac{X^{\beta-1}|M_D(\beta+iu)|}{\beta^2+u^2}=O(1). \tag{6} $$

This is a worst-case absolute tail budget even on just the right half of the zero strip. The constructed $M$ is in this class: it is uniformly bounded there by (1) and $M(3/4)\ge1$. For its $J$, (6) is $o(1)$ by the same tail estimate, since the logarithmic unit-count weights divided by $1+(J+j)^2$ sum to $O(\log(2+t))$. Compactly supported logarithmic convolution multipliers $\int e^{sw}\,d\nu_D(w)$ with a fixed support bound and uniformly bounded total variation also satisfy the strip bound; they are band-limited in $u$ after tilting the measure by $e^{\beta w}$. They are covered if they meet nondegeneracy and are tested by (6). No prime approximation is assumed in the lower bound, so it applies also to the subclass with a sufficiently small absolute prime replacement cost. Pointwise domination of a Fourier weight alone does not give (2).

To prove the obstruction, suppose $J\le(\log D)/(2\pi)$, as otherwise the desired lower bound is immediate. At $U=J+1$ the first block of (6) and $\log t\asymp e^{D/2}$ give

$$ |M_D(\beta+iU)|\ll (1+U^2)e^{-D/6}\le e^{-D/8},\qquad 2/3\le\beta\le5/6, $$

for large $D$. On the half-strip $1/2<\Re s<1$, $\Im s<U$, let $H$ have harmonic boundary values zero on the sides and a fixed smooth nonnegative bump, nonzero and at most one, supported in $[2/3,5/6]$ on the cap. Use the bounded extension decaying down the strip. The sine expansion for width $1/2$ gives $H(3/4)\gg e^{-2\pi U}$: the first coefficient is positive and the higher modes are $O(e^{-4\pi U})$ at $3/4$ as $U\to\infty$; positivity handles bounded $U\ge1$. On the boundary, $\log(|M_D|/B)+(D/8)H\le0$ after enlarging $B$ to at least one. By subharmonic comparison this holds inside (truncate below and send the lower edge down, where $H$ tends uniformly to zero). At $3/4$ it implies $(D/8)H(3/4)\le\log(B/m)$. Consequently

$$ J\ge\frac{\log D}{2\pi}-O(1). $$

This lower bound is for uniformly bounded, nondegenerate analytic multipliers required to satisfy (6), not for the actual signed residue tail. It says nothing against genuine cancellation or stronger zero information that would remove the need to certify (6), nor against tests lacking the uniform analytic bound. A smaller-order radius would require a different argument, for example a signed outer-tail estimate at these moving heights.
