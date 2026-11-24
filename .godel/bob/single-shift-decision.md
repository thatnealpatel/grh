# From one shift to two: What the next test must distinguish

At $c=39/20$ the [single-shift certificate](single-shift-10-2.md) gives one rational prime law for the whole real shift line. For **each** shift it admits a shallow zero-answer completion. At the handoff, test the shift-independent total energy before optimizing a witness for one shift, because that energy bounds both rotated energies separately. Failure of this sufficient test would not rule out the shift-specific test.

## A quantitative starting point for two shifts

Keep this law, $m=-3G_B/\cosh c$ at $3t$, and the probability measure $d\mu=dx/(2\pi(1/4+x^2))$. Let $H(x)=\sum_k b_ke^{is_kx}$ be the second-order multiplier, with real **multiplier** coefficients (the spline coefficients before smoothing are $b_ke^{-s_k/2}$). For this fixed first moment, the scalar zero answer is feasible exactly when

$$F(H):=\int |H|(1-|m|^2)\,d\mu-\left|\Re\int Hm^2\,d\mu\right|\ \ge 0.$$

Indeed, for a unit-circle variable $Z$ of mean $m$, $|\mathbb E Z^2-m^2|\le\mathbb E|Z-m|^2=1-|m|^2$. Every boundary value $m^2+(1-|m|^2)e^{2i\alpha}$ is attained by the two endpoints of the chord through $m$ of direction $e^{i\alpha}$, weighted to have barycenter $m$. Use $2\alpha=-\arg H$ or $\pi-\arg H$ to attain the two integrated extrema of $\Re(H\mathbb E Z^2)$. These choices are measurable (use any chord where $H=0$). A constant mixture attains every intermediate answer, with the same first moment. This is a test for **one scalar mask**, not two prescribed answers from the same completion.

For $H_0=a e^{isx}$ we have $F(H_0)\ge |a|(1-2\int |m|^2d\mu)$. Also $|F(H)-F(H_0)|\le\int |H-H_0|d\mu$: The two terms cost at most $1-|m|^2$ and $|m|^2$ times the perturbation pointwise. By the certified total energy $L_0$ and cutoff $T=\cosh^2(c)/18$,

$$1-2\int |m|^2d\mu=1-L_0/T>1-.70601/.714204>.01147.$$

Thus even a signed scalar mask with extra coefficients of total absolute size at most $.01147|a|$ cannot separate, at **any** locations of those translates. For a two-term search normalize the larger coefficient to one and skip this interval of ratios. Evaluate $F$ on the remaining masks first: A negative result excludes this completion strategy for this prime law, not the other prime laws. A genuine separator needs a price uniform in those laws, as in the [many-term separator](paired-10-2.md). No pair of shifts is shown to suffice here.

## Evidence for changing the handoff

Run `01a20c76-1a84-793f-8aa3-6719714f5598` launched `b773db123c29`; its Work session was `01a20c76-1cc1-7626-b588-09d88ba27c6c`. Work divided the full $(10,2)$ question into primal and dual searches. The `primal` child (`LxhfFHN`) missed the first caps by about $.000378$ at frequency zero on its rounded 423-slab fit; finer runs errored. Neither more frequency samples on that table nor treating the miss as nonexistence was justified. Work correctly used the certified signed dual instead. At the later shift decision it had the difference and sum kernels, a shift scan (events 109–110), and certificates at $s=0,1$. It correctly said that shift $1$ excluded only its raw first representer. We found no certifying alternative law in that record.

On those same raw inputs the [range replay](check-single-shift-range.py) also explains the scan: That representer fails precisely **between** two crossings, one in $(.01653,.01654)$ and the other in $(1.86812,1.86813)$. It groups the exact jump products at equal pair sums; $M=(\sum|b_j|)^2$ bounds $|S''|$ since $\int x^2/(2\pi|1/2+ix|^4)\,dx=1/2$. The chord error $Mh^2/8$, tail decay, and strict derivative signs in the two crossing boxes cover the line. Run `sage .godel/bob/check-single-shift-range.py` at the repository root. This law-specific diagnostic is **not needed** to verify the stronger replacement witness. In retrospect the total-energy objective for a free prime law was more useful than refining the old crossing locations.

Independently, Alice's [sparse-harmonic budget](../alice/sharp-sparse-harmonics.md) accounts for arbitrary queried indices, not just an index at which one grid fails. More recently her [cheap-filter kernel](../alice/cheap-filter-kernel.md) at `8cc9c789` used a monotone endpoint estimate to settle a whole range after a worst-bin test failed. The transferable decision is to look for one bound covering the parameter, not to import the arithmetic theorem or compare runtimes. Here the invariant sum of the two energies does that job. The new table and its all-frequency replay are a post-Work calculation, not a blind agent replay or a live trial of a changed prompt. Keep the standing prompts and graph; no evidence supports requiring another search or reviewer on every fit. Reopen single shifts if the depth, first constraints, or admissible laws change. Nothing here constructs primes or zeros or proves the signed measurement premise for actual failures.
