# Charge both copies of the budget to a reflected packet

Use the [three-cutoff test](filtered-one-height-packet.md), including its order of limits and multiplicities. Write $c=1.20$, $d=bD$, $w_\pm=1/2\pm b+ix$, $E_b=\Re E(x+ib)$, and $B=G\cosh c$. Let $A$ be precisely the right members in (1) of that test. The **same right-member census** must satisfy a stronger signed inequality:

$$ S_*:=\sum_A\left[-(1+e^{-2d})\Re Q(w_+)-2B E_b/R\right]>.0018. $$

There is no second zero measurement. The left companion contributes with the same phase up to a summable error, not with the worst possible sign. Both members carry the same budget. In particular an arbitrarily thin depth layer just above the support cannot supply a fixed positive charge to this statistic.

**Reflection estimate.** Write $Q(w)=V^{w-1}H(w)$, with $H(w)=g(w)e^{lw}\cosh^2(hw)/w^2$. On $1/4\le\Re w\le1$ we have $|H|+|H'|\ll_\epsilon(1+x^2)^{-1}$: The derivative of $g$ introduces a sine of complex argument, dominated by its double exponential decay at large $|x|$. For $0<b\le1/4$,

$$ |Q(w_-)-e^{-2d}Q(w_+)|\ll_\epsilon \frac{b e^{-d}}{R(1+x^2)}. $$

The two carriers are both $e^{iDx}$, not conjugates. For $b>1/4$ the left term is absent from the residue sum; its proxy $e^{-2d}Q(w_+)$ costs $O_\epsilon(e^{-D/4}/(R(1+x^2)))$. Since $b e^{-bD}\le1/(eD)$ and $\sum_\rho(1+x^2)^{-1}=O(R)$, the absolute error is $O_\epsilon(1/D)$ even on an arbitrary subset. In particular no relative approximation near a zero of the multiplier is needed.

Subtract the full budget $(B/R)\sum_\rho E_b$ from the full residue sum in (2) of the three-cutoff test. The net shallow contribution is at most $o_\epsilon(1)$ by its reflected shallow estimate, counting a line member only once. Outside the shallow set group the two budgets first: $E_{-b}=E_b\ge0$. Replace the left residue, when present, by its proxy. Outside the outer radius the right and proxy together have absolute sum $o(1)$ by the same tail bound (the multiplier $1+e^{-2d}$ is bounded). Inside the central hole the new residue has nonpositive charge by the original phase estimate. Dropping these two regions cannot lower the result by more than $o_\epsilon(1)$. Thus $S_*\ge P_q-BI/3-O(\epsilon)-o_\epsilon(1)$, giving the assertion with the original strict margin.

**Gain, not a new depth record.** If $S_1$ denotes the original left side of (1), then

$$ S_1-S_*\ \ge\ \frac{G\sinh c}{R}\sum_A E_b-o_\epsilon(1). $$

Indeed on $c/D<b\le D^{-1/2}$ the modulus of the proxy is at most $(G/R)e^{-c}[E_b+O(D^{-1/2}/(1+x^2))]$ by the line-envelope comparison. Farther right it costs $o(1)$ in total. For $c<d\le c+\eta$ with $\eta>0$ fixed, the new summand is at most $2G(\cosh(c+\eta)-\cosh c)E_b/R$ up to an absolute summable error $o_\epsilon(1)$ in the upper bound, by the same comparison with $e^d(1+e^{-2d})=2\cosh d$. Reflection and the full budget bound the sum of its positive parts on this layer by $GI(\cosh(c+\eta)-\cosh c)/3+o_\epsilon(1)$. This tends to zero with $\eta$ after the large-$D$ limit. The old test has no such pointwise cancellation: For a trial location $x=\pi/D$, first $D\to\infty$ at fixed $d>c$, then $d\downarrow c$ and $\epsilon\downarrow0$, its summand times $R$ tends to $e^c K(0)-\cosh(c) E(0)>6.12$. This is a price check, not an assertion that the location is occupied.

## Calibration on the all-deep finite Euler layer

In the [continuous all-deep model](interior-trace-depth-transfer.md) at $d=L_0=40$, let $p=P_q$ be the **actual three-cutoff prime sum**. Uniformly in the center samples,

$$ S_*=p-BI/3+O(\epsilon)+o_\epsilon(1),\qquad S_1=\frac{p}{1+e^{-80}}-BI/6+O(\epsilon)+o_\epsilon(1). $$

Here sums are model integrals. Use the all-deep ($\alpha=0$, assignment A) variant of the linked model. Each reflected pair is counted once, with density $\lambda Uv/2$, where $Uv$ is bounded, and $\lambda\sim R/(6\pi)$. The average of the two imaginary shifts multiplies Fourier coefficients by $\cosh(b\xi)$, exactly inverse to $U$ at $0,\pm\log n$. Moving $U$ onto the symmetric shift of an analytic test gives its unshifted integral against $\lambda v$. This applies to $F(x)=Q(1/2+ix)$ on a fixed strip strictly inside $|\Im x|<1/2$ containing the layers for large $D$. Take real parts **after** applying the identity. For $T(y)=\mathbb E(D+L-y)_+$ with the three shifts $L=l,l\pm2h$ and their original probabilities, Fourier inversion gives

$$ (2\pi)^{-1}\int F(x)e^{-ixy}\,dx=V^{-1}e^{y/2}(T*k_\epsilon)(y). $$

This follows from $\int (a-y)_+ e^{wy}dy=e^{aw}/w^2$ for $\Re w>0$ and the even signed convolution kernel of $g$ (integral one, absolute first moment $O(\epsilon)$). Write $T_\epsilon=T*k_\epsilon$. Substitution of the two cosine frequencies gives the full modeled residue charge exactly as

$$ -\frac{2\pi\lambda}{V}T_\epsilon(0)+\frac1V\sum_{n\le2V}\Lambda(n)\cos(t\log n)\left[T_\epsilon(\log n)+n^{-1}T_\epsilon(-\log n)\right]. $$

The constant mode costs $O(\lambda D/V)=o(1)$. The $+\log n$ evaluation gives $p+O(\epsilon)+o(1)$: Smoothing a 1-Lipschitz ramp costs $O(\epsilon)$ per weight, $\sum_{n\le2V}\Lambda(n)=O(V)$, prime powers are negligible, and all three unsmoothed positive cutoff endpoints lie below $2V$. The $-\log n$ evaluation costs $O(D^2/V)$ since its coefficients are $O(\Lambda(n)(D+\log n+1)/(nV))$. This uses only the model's finite Euler functional. For the envelope test its constant mode gives $RI/3+o(R)$ and the finite prime part is $O(1)$ by the exponential Fourier decay with exponent $s_0>1/2$. Exactly half the total real envelope price belongs to each side.

For fixed $L_0$, normalized summands are bounded by $O_{L_0,\epsilon}(1/(R(1+x^2)))$, so deleting the center and tail costs $o_\epsilon(1)$ with the bounded model density divided by $R$. The reflection estimate now says that the full residue charge is $(1+e^{-80})$ times the right residue charge up to $o_\epsilon(1)$. This proves both formulas. At the angular relaxation's floor $p=P$, the iterated scalar benchmarks are respectively between $.00184$ and $.00186$, and between $.2873$ and $.2874$. See the [ball checks](check-filtered-packet.py). Substituting $P$ does **not** realize its minimizing phase law in this model. At a putative failure one cannot set $p=0$ either.

**Next test.** Seek an independent arithmetic upper estimate of $S_*$ on the remaining candidates, using the signed price above, not a bare count near $c$. The finite Euler model by itself tracks the surviving prime signal almost exactly after the subtraction; it does not supply such an estimate. No exceptional sample was measured, the filter's $1.205$ obstruction is unchanged, and this is not a bound on the original $Z$.
