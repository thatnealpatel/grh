# Arbitrary slab laws on two fixed meshes at depth 39/20

In the [unfolded comparison](unfolded-deletion-33.md), fix $X=0$ on the exterior left ray and allow an independent, arbitrary law on $0\le u\le1$ on each slab, including the infinite last slab. Impose both normalized pointwise first caps and the three simultaneous zero second replies at $3t$. On the 426 seed slabs, $M-8/9<-1.83\cdot10^{-6}$. On the following 3,547 slabs, $M-8/9<-2.1\cdot10^{-7}$: Keep the seed knots and add all multiples of $1/400$ in $[-4.48,0]\cup[.02,4.4]$. No knots are inserted in $(0,.02)$, before the first seed knot, or after the last. This also excludes all coarsenings with the same exterior. This is not a bound for continuously moving knots.

Here is the dual calculation. Use the unfolded notation $b_k=e^{-z_k/2}\Delta B_k/C$, $s=(-7,6,19)/25$, $h=13/25$, and $H(x)=\sum_j\lambda_j e^{is_jx}$ with $\lambda=(.73,.98,1)$. The simultaneous disk condition and the first cap imply

$$b^TKb=\int [p(hx)|V_B|^2+\Re(H V_B^2)]\,d\mu\le r=\int p(hx)\,d\mu,$$

where $p(hx)\ge |H(x)|$ also makes $K$ positive semidefinite. To obtain $p$, the checker takes a degree-192 real even Laurent approximation from 2,048 samples; it verifies the coefficient sum of the squared error polynomial $p_0^2-|H|^2$ is less than $10^{-14}$ in absolute-coefficient norm before padding. The target modulus is greater than $.1$ (split at $|\cos(hx)|=.9$), and $p_0(0)>0$, so adding $10^{-12}$ suffices everywhere. The kernel entries are the sums of translated $K_0(z_i-z_j)$ and $K_1(z_i+z_j)$ given by the difference and sum transforms in the unfolded note.

Embed the jumps of a coarser law by zeros in the full $1/400$ grid. The tabulated real vector $q$ yields $b^TKq\ge-\sqrt{r q^TKq}$ by Cauchy-Schwarz for this form. Each complex first cut likewise yields $\Re(d V_Y(x))\ge-|d|$. Adding these linear fields to the mean and adding back their prices gives an upper bound. Summation by parts expresses it as a constant plus independent slab maxima of $w u+a(2u^2-1)+bT_3(2u^2-1)$. Convex-hull bounds in degree-six Bernstein coordinates with subdivision cover all atoms, not just the support used to fit the dual.

Replay in Sage Python with assertions enabled:

```
sage -python .godel/bob/check-mesh-deletion-33.py
```

The test only uses necessary conditions. It requires neither sufficiency of a directional second price nor an arithmetic realization.
