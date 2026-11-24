# A signed packet on the failing twist itself

Keep the primitive real nonprincipal twist $\chi$ of conductor $f=q|d|$ from the [endpoint test](fixed-strip-endpoints.md#signed-pairs-versus-the-gram-bound), $|d|\le V^\theta$ with $\theta$ fixed, $R=(9/5)\log q$, $V=R^2$, and $D=\log V$. Failure means the endpoint profile at its **own** cutoff $((9/5)\log f)^2$ has nonpositive quotient at $y$. This note uses nontrivial zeros of $L(s,\chi)$ at $y$, not zeros of zeta at $2y$. No fixed zero-free strip is assumed.

Set $B=6$, $M(s)=e^{2s/B}(1+s/B)^{-2}$, $g(s)=\exp(1-\cos(\epsilon s))$, and $J=(2/\epsilon)\log D$. At a zero $\rho=\beta+i\gamma$ put $x=\gamma-y$ and $s=\beta+ix$. Count with multiplicity, and define the **signed** sum

$$ T_\chi(y)=-\Re\sum_{\substack{\beta>1/2+0.1/D\\1.5/D<|x|\le J}} V^{s-1}M(s)g(s)/s^2. $$

**Result.** Fix $\epsilon>0$ sufficiently small. At every failing endpoint, uniformly in its height for sufficiently large $q$, $T_\chi(y)>0.008$. At $y=q^{3/5}$ the lower bound is $0.028$. At this named height the [zeta charge at $2y$](weil-phase-bands.md) is also required. These tests use different sums, with no common zero budget. The conclusion is stronger than the existence of an off-line zero but does not assert the existence of a failing endpoint.

## Prime cost of the multiplier

Write $\lambda=\log(f(2+|y|))/R$. The [endpoint Gamma and prime quotients](endpoint-arithmetic-test.md) and the [own-to-base cutoff comparison](fixed-strip-endpoints.md#signed-pairs-versus-the-gram-bound) give, at failure,

$$ \Re S_\chi(y)\ge\lambda-o(1),\qquad S_\chi(y)=V^{-1}\sum_{p<V}(\log p)\log(V/p)\chi(p)p^{-iy}. $$

Indeed the Gamma quotient is $\log(2+|y|)+O(1)$ uniformly, the prime mean has absolute value at most $1+o(1)$, and replacing the normalized ramp at the own cutoff by the one at $V$ costs $o(1)$ in total variation. The prefactors $(9/5)\log f$ and $R$ differ by $O_\theta(D)$; the phase is not shifted ($\chi$ is real). Thus $5/9\le\lambda\le1+o(1)$, and $\lambda=8/9+o(1)$ at the named height.

Use the even tent $F(v)=(D-|v|)_+$. Multiply its bilateral transform by $M(s)$: This averages $F(v-Z)$ for $Z=2/B-U$, where $U$ has density $B^2 u e^{-Bu}$ on $u>0$. Indeed $\mathbb E e^{sZ}=M(s)$ on $\Re s>-B$. Since $\mathbb EZ=0$ and $Z\le 1/3<\log 2$, at **every** $n\ge2$ the translated tent equals $(D-\log n+Z)_+$. Its average majorizes the old ramp by convexity. By PNT, $Y^{-1}\sum_{p<Y}(\log p)\log(Y/p)\to1$ as $Y\to\infty$ and is bounded for all $Y>0$ by Chebyshev. Apply this at $Y=Ve^Z$ and dominate by $O(e^Z)$ to see that the normalized total prime weight increase is $A+o(1)$, $A=M(1)-1$. This is an **absolute** cost on the twisted sum. Higher powers cost $O(D^3/\sqrt V)$ since the averaged weight is at most $D$ and vanishes for $\log n>D+1/3$.

The extra $g$ convolution costs $O(\epsilon)$ against $\Lambda(n)/V$ as in the [smoothed tent](opposite-phase-bands.md#use-the-unused-half-of-the-log-axis): The averaged tent is 1-Lipschitz with the same upper support bound. A further translate by $w$ costs $O(|w|e^{|w|})$ by Chebyshev. The signed inverse kernel of $g$ has integral one and modulus $\ll\epsilon^{-1}e^{-|w|/\epsilon}$. None of these costs differentiates a prime phase.

## Strip-free shift, including bounded heights

Integrate $-(L'/L)(s+iy,\chi)$ against

$$ K(s)=\frac{V^s+V^{-s}-2}{V s^2}M(s)g(s) $$

on $\Re s=2$ with factor $1/(2\pi i)$. Inversion and the Euler series give the modified prime-power sum just priced. Shift to $-1/4$. The tent's singularity at zero is removable; $-B$ is not crossed. We recall the uniform bounds behind the shift. For $K_d(x)=d/(d^2+x^2)$ and $u>1$, the [completed Hadamard identity](endpoint-zero-packets.md#price-the-part-near-the-critical-line) gives

$$ W_u(y)=\sum_\rho K_{u-\beta}(x)=\tfrac12\log(f/\pi)+\tfrac12\Re(\Gamma'/\Gamma)((u+\kappa+iy)/2)+\Re(L'/L)(u+iy,\chi), $$

where $\kappa\in\{0,1\}$ is parity. In particular $\sum(1+x^2)^{-1}\ll\log(2f(2+|y|))$ by $W_2$. As in the tent shift, subtraction of completed logarithmic derivatives at the same ordinate and at real part 2 bounds the distant zero differences by this inverse-square count. At large shifted ordinates the unit counts therefore permit horizontal sides separated from nearby ordinates by $\gg1/\log(2f(2+|\Im s+y|))$, with $L'/L$ bounded there by a squared logarithm. Send these sides to infinity at fixed $f,V,y$; $M,g$ are bounded on the slab for small $\epsilon$. On $-1/4$ the functional equation and the Euler series at $5/4$ bound $|L'/L(-1/4+iu)|\ll\log(2f(2+|u|))$, including bounded $u$ since the line avoids the Gamma poles. The new vertical costs $O(V^{-3/4}\log(2f(2+|y|)))=o(1)$. There is no principal pole. For an even $\chi$ the trivial zero at $s=-iy$ costs $O(D^2/V)$ uniformly, using $|2\sin(Dy/2)/y|\le D$, including $y=0$.

Every nontrivial zero contributes $-K(s)$ at $s=\rho-iy$. For $\beta<1/4$, $|(1-e^{-Ds})/s|\le\min(D,2/|x|)$, so these terms cost $O(D^2 V^{-3/4}W_2(y))=o(1)$. For $\beta\ge1/4$, dropping $V^{-s}-2$ from the numerator costs $O(W_2(y)/V)=o(1)$. The comparisons also give absolute convergence for fixed parameters. Thus the sum of $-\Re(V^{s-1}M(s)g(s)/s^2)$ over $\beta\ge1/4$ is at least $\lambda-A-O(\epsilon)-o(1)$ at failure.

## A nonnegative difference only after reflection

Put $a=1+1/D$, $m=a-1/2$, $\ell=m/(m+B)$, $C=e^{1/B}B/(B+1)$, $I=C\,2B/(2B+1)$, and $G=\exp(1-\cos\epsilon)$. On the critical strip $|g|\le G$. By Stirling (or bounded height) and the absolute Euler bound $O(D^2+1)$,

$$ W_a(y)-\ell W_{a+B}(y)=\tfrac{1-\ell}{2}\log(f(2+|y|))+O_B(D^2+1). $$

Partition into same-ordinate reflected orbits, of size two off the line or one on it. For one orbit let $d_i=a-\beta_i$, $e_i=d_i+B$. Then $\sum d_i=\ell\sum e_i$ and $\max d_i\le a<a+B-1\le\min e_i$. Thus its contribution $P=\sum K_{d_i}-\ell\sum K_{e_i}$ is nonnegative: In the first sum every inverse denominator exceeds every inverse denominator in the second. **Do not** assert this for a lone right member. For example at $\beta=1/2+b$, $b>0$, its entry is $-(1-\ell)b/x^2+O_B(x^{-4})$ as $|x|\to\infty$.

Write $H_v(x)=|M(v+ix)|/(v^2+x^2)$. Partial fractions give

$$ H_{1/2}(x)=C\left(\frac1{1/4+x^2}-\frac1{(B+1/2)^2+x^2}\right). $$

For $|v-1/2|\le h=D^{-1/2}$ this yields, uniformly in $x$,

$$ H_v(x)=H_{1/2}(x)+O_B(h)/(1+x^2),\qquad H_{1/2}(x)=2C(K_{a-v}(x)-\ell K_{a+B-v}(x))+O_B(h)/(1+x^2). $$

Indeed $H_v=B^2e^{2v/B}/[(v^2+x^2)((v+B)^2+x^2)]$; its $v$-derivative and each kernel's width derivative on the indicated compact width ranges are $O_B((1+x^2)^{-1})$. The second equality is exact at $a=1,v=1/2$ before perturbation.

For an orbit with $b=|\beta-1/2|\le 0.1/D$, omit all entries. The average of $R V^{\beta-1}$ is $\cosh(Db)\le\cosh(0.1)$ (one on the line). For $0.1/D<b\le h$ omit only the left member; its factor is $e^{-Db}<1$. In either case, for an orbit of size $k$ the omitted absolute cost is at most $(G k\cosh(0.1)/R)\,[H_{1/2}(x)+O_B(h)/(1+x^2)]$. Use the kernel comparison on the **whole** orbit. The summed additive errors cost $O_B(hW_2(y)/R)=o(1)$. For $b>h$ the omitted members with $\beta\ge1/4$ are on the left and cost $O_B(e^{-\sqrt D}W_2(y)/R)=o(1)$ in total. By orbit positivity the shallow orbits use at most the full difference budget. Consequently all omissions to this point from the $\beta\ge1/4$ sum cost at most

$$ \frac{2CG\cosh(0.1)}R(W_a-\ell W_{a+B})+o(1)=GI\cosh(0.1)\lambda+o(1). $$

The right residues remain signed even when their orbit was used to pay for a left residue. No further use of its Poisson credit is allowed.

## Height window and constants

Outside $|x|\le J$ the remaining absolute cost is $O_B(\exp(1-\tfrac12\cos(\epsilon)D^2)W_2(y))=o(1)$. This uses $V^{\beta-1}\le1$ and $H_\beta\ll_B (1+x^2)^{-1}$ for $\beta\ge1/2$. For $|x|D\le1.5$ the argument of $V^{s-1}M(s)g(s)/s^2$ has representative

$$ xD+2x/B-2\arctan(x/(B+\beta))+\sin(\epsilon\beta)\sinh(\epsilon x)-2\arctan(x/\beta). $$

Its modulus is at most $1.5+O_B(D^{-1})<\pi/2$, so deleting these entries can only increase the signed sum. In particular real zeros are not silently discarded at small or zero $y$. We obtain

$$ T_\chi(y)\ge (1-GI\cosh(0.1))\lambda-A-O_B(\epsilon)-o(1). $$

For the constants use $e^{1/6}<1.18137$, $e^{1/3}<1.39562$, and $\cosh(0.1)<1.00501$. The exponential upper bounds follow by summing through degree 5 and bounding the tail by $(u^6/6!)/(1-u/7)$; for cosh use $1+(u^2/2)/(1-u^2/12)$. With $G=1$ the affine lower bound at $\lambda=5/9$ exceeds $0.00831$, and at $8/9$ exceeds $0.02851$. Its slope is positive. Fix $\epsilon$ small enough to retain both stated strict margins, **then** take $q$ large, uniformly at failing heights. No effective height or conductor threshold follows.

**Next decision.** At $y=q^{3/5}$, a uniform upper bound $T_\chi(y)\le0.028$ for candidate twists suffices just as an upper bound $0.233$ on the other, zeta Weil charge at $2y$ would. At other heights this argument tests the twist alone at $0.008$. The pair of requirements is a conjunction, not a sum of independent evidence, and neither upper estimate has been proved.
