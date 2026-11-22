# The trace of the fixed-annulus local operator

**Result.** For the rational real place on the trivial compact isotype, the Hilbert trace of $B=M_p A_\phi Q_Y$ exists and has the absolutely convergent series below. The [Lean theorem](FixedAnnulus.lean) identifies its operator by its action on **every input** in weighted $L^2$, not by a formal diagonal of a kernel. The Fourier series is for the convolution test. It is not a formula for the projection.

## Space, windows, and modes

Write $x=\log t$, $d\mu=w(x)\,dx$, $w(x)=e^{2\alpha|x|}(1+x^2)^r$, and $H=L^2(\mu;\mathbb C)$. The manuscript comparison uses $0<\alpha<1/2$, integral $r\ge1$, and $Y>0$. In the [real level construction](RealLogLevel.lean), $Q_Y$ is the orthogonal projection onto the closed linear span of $2e^{x/2}h(e^x)$, where $h$ is even Schwartz, $\operatorname{supp}\widehat h\subseteq[-Y,Y]$, $h(0)=0$, and $\int h=0$. These are additive conditions **before** passage to log coordinates. Every such profile lies in $H$: The zeroth and first weighted Schwartz bounds give $|2e^{x/2}h(e^x)|\le C_h e^{-|x|/2}$, which is square-integrable against $w$ when $\alpha<1/2$. This is not the global theta projection.

Take a continuous compactly supported log cutoff $p$ and $\phi\in C_c^2(\mathbb R)$. Choose $R>0$ with both supports in $[-R,R]$. Put $D=[-2R,2R]$ and $L=8R$. Define $f$ by extending $\phi|_{[-4R,4R)}$ periodically. If $p(x)\ne0$ and $y\in D$, then $|x-y|\le3R$, so $f([x-y])=\phi(x-y)$. If $p(x)\ne0$ and $y\notin D$, then $\phi(x-y)=0$. Both facts are needed: Simply periodizing on the output interval can introduce unwanted copies of the kernel.

With $e_k(x)=e^{2\pi i kx/L}$, set

$$c_k=L^{-1}\int_{-4R}^{4R}\phi(t)\overline{e_k(t)}\,dt,\qquad u_k=c_k\,p e_k,\qquad v_k=\mathbf1_D e_k/w.$$

Two integrations by parts give $|c_k|\le L\|\phi''\|_{L^1}/(4\pi^2 k^2)$ for $k\ne0$. There are no boundary terms, and $c_0$ is finite. Thus $\sum_k |c_k|<\infty$. The output and input bounds are $\|u_k\|=|c_k|\|p\|_H$ and $\|v_k\|^2=\int_D w^{-1}\,dy$. Only local positivity and continuity of the weight are needed here, not differentiability at zero.

## Identification and trace

Use the inner product linear in its second argument. Then $\langle v_k,z\rangle_H=\int_D \overline{e_k(y)}z(y)\,dy$; omitting $1/w$ would give the wrong convolution measure. Absolute uniform convergence of the test series permits termwise integration against $z$ on $D$, since $\int_D|z|\le\|z\|_H(\int_D w^{-1})^{1/2}$. The [window map](WindowSynthesis.lean) also carries uniform convergence to convergence in the actual weighted $H$. Applying these facts to $z=Q_Y h$ gives, almost everywhere,

$$Bh(x)=p(x)\int_{\mathbb R}\phi(x-y)(Q_Y h)(y)\,dy,\qquad B=\sum_{k\in\mathbb Z} u_k\langle Q_Y^*v_k,\cdot\rangle_H.$$

The rank-one norm sum is at most $\|p\|_H(\int_D w^{-1})^{1/2}\|Q_Y\|\sum_k|c_k|$. Since a rank-one operator has trace norm equal to its operator norm, this is a trace-class presentation in the usual Hilbert-space sense. The Lean statement gives the norm sum and convergence to $B$ in operator norm; it does not use an assumed trace-ideal API. The [basis-diagonal argument](RankOneSeries.lean) gives, for every Hilbert basis $(b_i)$,

$$\boxed{\displaystyle\sum_i\langle b_i,Bb_i\rangle_H=\sum_{k\in\mathbb Z}\langle v_k,Q_Yu_k\rangle_H.}$$

Both sums converge absolutely. The adjoint on the input modes is fixed by the order of composition. Although $Q_Y^*=Q_Y$, the trace formula does not require moving $Q_Y$ past either $p$ or $A_\phi$. As a normalization check, replacing $Q_Y$ by the identity gives $\langle v_k,u_k\rangle=c_k\int p$, since $D$ contains the support of $p$. Summing gives $\phi(0)\int p$. This last simplification is **not** the trace at a general finite level.

## Verification and scope

`AdHoc.RealLogLevel.fixedAnnulus_trace` in [FixedAnnulus.lean](FixedAnnulus.lean) combines the [periodic coefficient estimate](CircleSynthesis.lean), [translated-kernel integration](TranslatedKernel.lean), [weighted operator series](WindowKernel.lean), [removal of the auxiliary window](AnnulusKernel.lean), and the concrete level construction. `integrable_translate` proves existence of the ordinary convolution integral at every output point. To check from the repository root with the pinned Mathlib available:

```sh
lake env bash -eu -c '
  src=.godel/adhoc/operator-trace
  tmp=$(mktemp -d)
  trap '\''rm -rf "$tmp"'\'' EXIT
  export LEAN_PATH="$tmp:$LEAN_PATH"
  for m in RankOneSeries WindowSynthesis TranslatedKernel CircleSynthesis RealLogLevel WindowKernel AnnulusKernel FixedAnnulus; do
    lean -R "$src" -o "$tmp/$m.olean" "$src/$m.lean"
  done
'
```

This closes the **Hilbert-space** step of the [fixed-annulus repair](../../obligations/trace-polar-free-q.md). The nuclear lift into $C_K^\infty$ for smooth data and the locally convex trace comparison there are mathematical arguments, not conclusions about a Lean-defined Fréchet-space trace. The one-sided cutoff equal to one near norm zero, adelic orbital terms, global levels, and passage to joint cutoff limits are not covered. In particular, no equality of the local trace with the global geometric term follows.
