# A constant depth transfer invisible to an interior trace

The entire translated signed Poisson trace at $s_0=1/2+1/D$ does not determine which side of the $E_1$ target a general positive depth assignment occupies, even together with the common ordinate marginal and the finite Euler functional through $2V$. The ambiguity need not come from the trace multiplier at frequency $D$. At **frequency zero**, a uniform reflected layer gives zero interior trace at every vertical strictly between its two sides. The phase cut, by contrast, retains a depth-dependent fraction even of a uniform layer.

Use the prescribed $t,R,V,D$, annulus, $K=\cosh(.28)$, pair price $p$, and exact two bands of [the excess bound](deep-retained-excess.md). These are continuous local density models, not zero sets. A layer of total ordinate density $\lambda d(x)$ has **pair** density $\lambda d(x)/2$, where $\lambda=\log(t/(2\pi))/(2\pi)\sim R/(6\pi)$. The models below have $E_1$ values differing by more than $.06$ at *every* sufficiently large sample, including a putative failure. On a density-one set one value is below $.0519$ and the other above $.0658$. The latter separation across targets is **not** asserted at failures.

## Transfer with no change in the data

Fix $L=40$ (more generally any fixed $L\ge40$), $u=1.01$, $\eta=.30$, and $\alpha=.64$. Write $U$ for the convolution operator of symbol $\operatorname{sech}(L\xi/D)$. Put

$$
 l=\alpha F_{16}(Dx-2\arctan(2x)),\quad h=U(v-l)-\eta,
 \qquad v=1-\frac1{\pi\lambda}\sum_{n\le2V}\frac{\Lambda(n)}{\sqrt n}\cos((x+t)\log n),
$$

where $F_{16}(v)=|\sum_{j=0}^{15}e^{ijv}|^2/16$. In both assignments put $\lambda l$ on the critical line and a layer $\lambda h$ at depth $c=L$ (that is, at real parts $1/2\pm L/D$). Put the remaining **constant** layer $\lambda\eta$ at $c=L$ in A, and at $c=u$ in B. All sides are eventually in the critical strip. For positivity, $\|Ul-\alpha\|_\infty\le 4\alpha/(e^L-1)+o(1)$: Freeze the slow phase of each of its finitely many modes in the convolution, at cost $O_L(1/D)$ by the kernel's first absolute moment, and sum $\operatorname{sech}(kL)\le2e^{-|k|L}$ over the nonzero modes. In $U(v-1)$ the terms $n<R$ cost $o(1)$ by partial summation with the prime number theorem; on the rest $L\log n/D\ge L/2$. Their limsup cost is at most $12\sqrt{2}\operatorname{sech}(L/2)<10^{-7}$ as in the [finite Euler construction](shared-ordinate-weil-model.md). Thus $|h-(1-\alpha-\eta)|<10^{-6}$ eventually and $1-\alpha-\eta=.06$.

Both marginals are $\lambda(l+h+\eta)$. In A the integral against any of the strip-holomorphic decaying tests in the finite Euler construction equals $\lambda\int vf$: Moving $U$ to the test undoes the symmetric imaginary shift to the two sides of the $L$ layer. In B the same identity holds, since moving a constant layer between the depths does not change the integral (horizontal contour shift). For the interior trace the two kernels on the constant layer have integrals $+\pi$ and $-\pi$, regardless of its depth $c>1$. This gives **exact** agreement for every ordinate translation, not an error after smoothing or a match of just one harmonic. In fact the transfer is invisible on every vertical $1/2+a/D$ with $0<|a|<u$, and the exterior-minus-smoothed-interior traces in (3) of the excess bound also agree.

## What the transfer costs in the original bands

Write $w=g_\epsilon(x)/(1/4+x^2)$, $A_\epsilon=(6\pi)^{-1}\int w\to1/3$ as $\epsilon\downarrow0$, and $T=(\cosh 1-1)/3$. For each fixed $c>1$, write

$$ M(c)=\frac2\pi\arccos\!\left(\frac K{\cosh c}\right). $$

The limiting contribution of a constant layer of total density $\lambda\eta$ to $E_1$ is exactly $-\eta M(c)(A_\epsilon+T)$. To see this, on a compact interval $|P|^2=w+o(1)$ and $2\arg P=Dx-2\arctan(2x)+o(1)$ modulo $2\pi$ by the [two-half estimate](weil-phase-bands.md). Average the exact bands by first enlarging and shrinking the limiting angular set $|\cos v|>K/\cosh c$; its boundary has measure zero. Each nonconstant Fourier mode against a continuous compactly supported weight tends to zero by Riemann-Lebesgue on absorbing the slow phase. The angular mean of the indicator is $M(c)$ and its mean times $\cos v$ is zero by half-turn symmetry. Thus the pair charge $-2|P|^2(1+\cosh c\cos(2\arg P))/R$ costs $-\eta M(c)A_\epsilon$. In the Poisson subtraction $p\to(1/4+x^2)^{-1}$ on compacts; this time there is **no** $g_\epsilon$. Its integral on the real axis tends to $2\pi$, so $2(\cosh 1-1)p/R$ costs $\eta M(c)T$ with the pair density above. For fixed depths both integrands have an $O_{c,\epsilon}((1+x^2)^{-1})$ envelope. It justifies the tails and the $1.5/D$ central hole. This computation uses the cost of the opposite band and does not freeze an angular cut at finite $D$.

Consequently

$$ E_{1,B}-E_{1,A}=\eta\,[M(L)-M(u)](A_\epsilon+T)+o(1). \tag{1} $$

For small fixed $\epsilon$, $A_\epsilon>.33$, $.18<T<.182$, $M(40)>.999$, and $M(1.01)<.6$ (use $\cosh(1.01)<1.6$ and $\cos(3\pi/10)<.6$). The difference exceeds $.06$ with room. No typicality entered this calculation.

## Calibration to the thresholds

At density-one odd squarefree samples on $[Q,2Q]$, in the sense of convergence in density, the full normalized model charge is $-A_\epsilon+o(1)$ by the [moving-cutoff sampling estimate](shared-ordinate-weil-model.md#evaluating-the-full-and-line-charges) for the identical functional $\lambda\int vf$. The line charge is $-\alpha(1+15/16)A_\epsilon+o(1)$ at all samples, by averaging $F_{16}(v)(1+\cos v)$. Thus the full off-line charge in A is $.24 A_\epsilon+o(1)$ in density. Its full off-line Poisson cost, *before* the annular and band cuts, is $(1-\alpha)T+o(1)$ at every sample: The total Poisson sum is $\pi\lambda+O(\sum_{n\le2V}\Lambda(n)/n)=\pi\lambda+O(D)$ by the exact finite functional at $\sigma=1+1/D$. The line accounts for $\alpha\pi\lambda+o(R)$ by oscillatory averaging against $k_{\sigma-1/2}$ (these kernels converge in $L^1$).

In A the only off-line depth is $L$. Its total density divided by $\lambda$ is bounded by $1$. Cutting the center and tail costs $o(1)$ for fixed $L$ by the envelopes above. On actual gray pairs, $|\Re Z^2|\le2(1+K)|P|^2$, independent of $\cosh L$. With the angular outer cover on compacts, the limsup of the absolute lost charge plus lost price is at most

$$ [(1+K)A_\epsilon+T]\,[1-M(L)] <10^{-7}. $$

Here $1-M(L)=2\arcsin(K/\cosh L)/\pi$ and $L\ge40$. This does not assume the Euler perturbation in the layer is uncorrelated with the bands. Hence $E_{1,A}$ is within $10^{-6}$ of $.24 A_\epsilon-.36T$ outside $o(Q)$ samples, and (1) then gives

$$ .013<E_{1,A}<.0519,\qquad E_{1,B}>.0658. $$

To calibrate the *exceptional* case instead, the full charge contains the same extra $\Re S_V(t)+O(\epsilon)+o(1)$ in both assignments by the finite prime-side calculation. At a putative failure it is not legitimate to set this term to zero. For sufficiently small fixed smoothing both are then above $.0658$: The deep-only baseline is greater than $.013$, the first harmonic adds at least $47/81-o(1)$ before the $O(\epsilon)$ error, and (1) is positive. Neither the trace match nor (1) produces a low-$E_1$ model at a failure. As a sharpness check, take $\alpha=0$ in A: All mass is deep, the full Poisson cost tends to $T$, and $E_{1,A}=\Re S_V(t)-\cosh(1)/3+O(\epsilon)+O(1-M(L))+o(1)$ since $A_\epsilon=1/3+O(\epsilon)$ (split $\int(1-g_\epsilon)/(1/4+x^2)$ at $|x|=1/\epsilon$ and use $1-g_\epsilon\ll\epsilon^2 x^2$ inside). For this variant the deep density is $1+U(v-1)\le 1+10^{-6}$ eventually; the same gray estimate holds with that extra factor. One can make the two fixed errors arbitrarily small before letting $D$ grow. This is saturation relative to the **actual first harmonic** in the finite local model, not existence of a sequence attaining $47/81$.

## Discrete ordinates: Exponential closeness, not equality

For the moved constant layer, take one pair at each $x=j/N$, $j\in\mathbb Z$, with $N=\lambda\eta/2$. Keep these *same* ordinates in both assignments. Round the common line and $h$ densities identically in both (round the cumulative count once on the line, and the cumulative pair count at $L$). Each rounded measure differs from its own mass on any interval by $O(1)$, so the two counting marginals still agree exactly. The exterior Poisson data at $1<\sigma\le2$ now approximate the finite Euler values to $O(1)$ uniformly in translation: Integration by parts against each kernel costs its total variation times $O(1)$, and the widths are bounded below there. The full and line Weil charge errors are $O_{L,\epsilon}(D/R)$ by the same variation estimate as in the [rounded model](shared-ordinate-weil-model.md#if-integer-ordinate-counts-are-required). The $E_1$ thresholds and gap also survive with $o(1)$ change. On each compact, sandwich the exact indicators by enlarged and shrunken angular masks as above. These masks have $O(D)$ intervals by monotonicity of the carrier. Integrating a smooth weight on each costs $O(1)$ discrepancy (also for the cosine weight on a single period, since its variation there is bounded). After normalization the loss is $O(D/R)$. The shrinking angular boundary neighborhoods have vanishing limiting mass since the continuous densities are bounded after dividing by $\lambda$; the integrable tail envelope and unit-interval counts $O(R)$ handle the tails.

The difference of the two **discrete** interior traces is much smaller than the error of rounding either whole model separately. For $d\ne0$, the periodized sum $\sum_j k_d(y-j/N)$ has Fourier coefficients $\pi N\operatorname{sgn}(d)e^{-2\pi N|d k|}$ at harmonics $k\in\mathbb Z$, by integration over a period. In the moved pair layer the constant terms cancel at $a=1/D$, and all four widths in the trace difference have magnitude at least $(u-1)/D$. Thus with $r_*=e^{-2\pi N(u-1)/D}$,

$$ \sup_y |W^{\rm atoms}_{s_0,B}(y)-W^{\rm atoms}_{s_0,A}(y)|\le 8\pi N\,r_* /(1-r_*). $$

This is $O(R\exp(-\kappa R/D))$ for a fixed $\kappa>0$, not exact equality. It gives a precision obstruction even with a shared counting marginal, not indistinguishability from arbitrarily precise atomic data. These are local arrays, not zeros of an $L$-function.

**Next test.** Do not seek to recover $E_1$ on general assignments from the frequency-$D$ projection of this single trace. Even its entire translated function misses (1). For constant layers, sampling the signed trace on several interior verticals counts the mass in the intervening depth intervals by subtraction: Each constant layer contributes $\pi$ per unit total density above its right side and zero between its sides. In a depth interval strictly above $1$ with mass fraction $m$, the spread in its possible $E_1$ contributions is at most $m(A_\epsilon+T)\operatorname{osc} M$ there, with endpoints approachable for a free constant layer. A useful further question is whether the **nonconstant ordinate modes** can be controlled on such depth intervals at the exceptional samples. A mesh estimate for constant layers alone is not such a bound. These models do not impose the true zeta interior trace, a global Euler product, or the failing character constraint.
