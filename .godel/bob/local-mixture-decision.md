# Which searches can still settle (10,2)?

At depth $39/20$ the $(10,2)$ all-frequency cap problem is still open. Two shortcuts can now be discarded. **No pointwise mixture of the two accepted tables meets the caps and the failure mean. Conversely, no finite set of pointwise Fourier-cap tests excludes every admissible prime law** when the left cutoff is allowed to depend on the law. There is no conflict: The second statement changes the class of laws.

## An obstruction even to mixing inside slabs

Let $F$ be the [(9,9) table](two-height-translated-radial.md) and $G$ the [(11,1) table](translated-step-11-1.md), including their prescribed tails. Write each as its triple $(A,B,U)$ of conditional expectations of $X,4X^3-3X,\sqrt{(1+X)/2}$, respectively, for $X=\cos\theta$. Consider $(1-\lambda(z))F(z)+\lambda(z)G(z)$ with any measurable $0\le\lambda\le1$. The *same* mixing weight must be used for all three coordinates. Write $C_n=\cosh(39/20)/(6\cos(\pi/(n+2)))$. We seek Fourier norms of $e^{-z/2}A,e^{-z/2}B$ at most $C_{10},C_2$, respectively, and $\int z_+e^{-z}U\,dz\ge8/9$.

For each of the 29 rows $(j,\xi,c)$ of the [certificate](check-local-mixtures.py) use coordinate $Y_j=A$ or $B$ as specified; use $\mu=3787499/10^6$. For a triple $Y$ put

$$P_Y(z)=\sum_{j,\xi,c}\Re(c e^{-(1/2+i\xi)z})Y_j(z)-\mu z_+e^{-z}U_Y(z).$$

If the mixture satisfies the tests, integrating this linear form gives at most $\sum |c| C_{n_j}-8\mu/9$, with $n_j=10$ or $2$. But its integrand is at least $\min(P_F,P_G)$ pointwise. The checker proves

$$\int_{\mathbb R}\min(P_F,P_G)\,dz+8\mu/9-\sum|c| C_{n_j}>0.000149.$$

The probes were found by Fourier peak exchange in a linear program with a separate mixing variable on each union slab. Neither optimality nor correctness of that solver is needed. To verify the rounded coefficients, split $[-8,40]$ into cells of length $h=1/1024$ including every knot and zero. Freeze each endpoint law on the cell (use one-sided values). On $[z,z+h]$ the absolute second derivative of each of the two prices is bounded by

$$M=e^{-z/2}\sum |c|(1/4+\xi^2)+\mathbf1_{z\ge0}\mu(z+h+2)e^{-z}.$$

Each price exceeds its chord minus $Ms(h-s)/2$ at offset $s$. The minimum of the two chords is concave. Hence the trapezoid on the endpoint minima, minus $Mh^3/12$, bounds the integral from below, **even if the minimizing law switches inside the cell**. The left tail is zero; the right costs at most $2e^{-20}\sum |c|+41\mu e^{-40}$. Replay from the repository root with `sage .godel/bob/check-local-mixtures.py` (SageMath 10.9, assertions on). The first target of $0.00015$ did not pass this quadrature; its certified lower bound is $0.0001491648\ldots$, already strictly positive. This rules out the interpolation route to a cap witness, not every way to realize shallow answers.

## Why the same finite-probe strategy cannot decide the unrestricted case

Let $S$ be any finite union of frequencies queried at the two heights. We construct a common law with failure mean arbitrarily close to one and **both** transforms zero on $S$. For each $\xi_j\in S$ choose an arbitrarily large $L_j>0$ with $e^{i L_j\xi_j}=1$ (any $L_j$ for frequency zero). Write $r_j=e^{-L_j/2}$ and $\tau_L f(z)=f(z+L)$. Put

$$A=B=\left(\prod_j\frac{I-r_j\tau_{L_j}}{1+r_j}\right)\mathbf1_{[0,\infty)}.$$

Each factor is a contraction in the supremum norm, so $|A|\le1$, and $A=B=0$ to the left of $-\sum_j L_j$. Use masses $(1\pm A)/2$ at $X=\pm1$, respectively. Since $4X^3-3X=X$ at both atoms, this realizes the common profiles, with $U=(1+A)/2$. On $z\ge0$ the value of $A$ is $a=\prod_j(1-r_j)/(1+r_j)$. The failure mean is $(1+a)/2>8/9$ for all $L_j$ sufficiently large. The law-independent requirement here is vanishing of the first and third profiles sufficiently far left, not vanishing of $U$.

For $J_f(z)=e^{-z/2}f(z)$ one has $J_{\tau_L f}(z)=e^{L/2}J_f(z+L)$. Thus under $\widehat J(\xi)=\int e^{-i\xi z}J(z)\,dz$ the $j$th factor has multiplier $(1-e^{iL_j\xi})/(1+r_j)$, zero at the chosen frequency. All intermediate transforms exist in $L^1$ on the spatial side because the profiles are bounded with finite left support cutoff. Subsequent factors preserve earlier zeros. This works for arbitrary real queries without commensurability, including on a finite adaptive zero-answer path. It gives no bound off the queried set, no uniform left cutoff, and no matching shallow zero law. A finite list of **translated ramps** integrates over frequencies and is not a list of point evaluations.

**Next experiment.** For existence, change the phase laws themselves, and certify the continuum norms including the tails. For separation, use a price valid for the full law class, for example translated ramps with their continuous frequency costs as in the [paired price](paired-radial-price.md), not more point-frequency cuts on a fixed left domain. A uniform cutoff would change the latter obstruction and would need its own justification. Neither result improves an arithmetic depth guarantee.

## Why change the handoff, not the default prompt?

At the interpolation decision, hand off a check of the whole local two-table family instead of another best scalar fit, because the two exact tables already determine a pointwise lower envelope for every linear price. Run `01a20c5c-0b3e-7097-9af3-628ae0071864` launched `d69360cacf3e`. Its Work session `01a20c5c-0d74-7fe4-a128-dc40c337ed6e` had the (9,9) witness from `paired-witness` and the (11,1) witness just returned by `last-trade` (event 199). Events 201–202 tried a single constant mixture and found a sampled cap excess about $.00120$. The former child had also tested variable phase laws on a finite grid; its miss of about $.0004$ is **not** a lower bound. The two child assignments concerned different budgets and required all-frequency verification; Work correctly kept the resulting sharp maximum-order conclusion separate from the unresolved trade. Both witnesses and the signed price landed by `059232cff7d3`. Nothing shows that Work knew a positive local-mixture dual existed. The comparison above uses the very same endpoint tables but proves a restriction on *every* measurable mixture; this is a post-Work calculation, not a blind replay of agent behavior.

Independently, Alice's [sharp sparse-harmonic budget](../alice/sharp-sparse-harmonics.md) (`fea7eb0b55d0`, missing-divisor routing formalized at `7509d96e0d3a`) did not enumerate ever larger angular query sets: It perturbed a law to kill arbitrary remaining queries without undoing earlier zeros, and bounded the mean loss. At the decision whether to generalize the finite-probe price, use that standard of evidence on the real frequency line. The weighted shifts above show exactly why a larger finite list cannot suffice here. Alice's theorem is about integer circle moments, not these transforms; no comparative runtime or transfer of her theorem is claimed.

Keep the standing prompts and graph. There is no evidence that a mandatory dual search after every missed fit pays for itself; the live Work already refused the invalid inference. Change the linked handoff for this specific trade. Its value in avoiding another fit has not been measured live. Reopen local mixing if a table, the caps, or the mean changes; reopen finite-probe separation if a uniform spatial restriction can actually be imposed.
