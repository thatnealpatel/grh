# Measurable refits around all 426 delete-33 seed knots

At $c=39/20$, center a band $[z_i-r,z_i+r]$ on every knot of the [426-slab seed](unfolded-deletion-33.md), including the first, zero, and last knots. Leave $X=0$ to the left of the first band. On each band allow **any measurable law** on $0\le u\le1$ (a probability kernel in $z$). On each intervening gap and the final right ray allow one independent, **arbitrary constant law**, not necessarily its seed law. In particular this includes any number of extra splits within the bands. Impose the two unfolded first caps and the three simultaneous second replies at $(-7,6,19)/25$ as in the [mobile mesh proof](mobile-mesh-deletion-33.md).

| Radius $r$ | Upper bound on $M-8/9$ |
|---|---:|
| $1/1000$ | $-6.59\cdot10^{-7}$ |
| $7/4000$ | $-7.90\cdot10^{-8}$ |

**Why the relaxation works.** Use the same serialized mesh dual, constant price $P$, and vector of primitives $\Phi=(W,P_A,P_B)$ as in (1) of the mobile mesh proof. Write $v(u)=(u,X(u),T(u))$ and $H(e)=\max_{0\le u\le1} e\cdot v(u)$. For a constant law on $[s,t)$ we may charge $H(\Phi(s)-\Phi(t))$, with $\Phi(\infty)=0$. For a band $I$ charge instead $\int_I H(-\Phi'(x))\,dx$. Add $P$ once. Each core and band is counted exactly once; the exterior contributes zero harmonic fields and no failure weight. Unlike independently moving the endpoints of every slab, this pays no overlapping lengths. Every ordered single move per boundary induces laws in this relaxed class.

This upper price also applies without finite variation in the bands. Indeed the normalized field on a profile $Y=A,B$ is $(\bar w/w)D^{-1}\int e^{-\bar w z}Y(z)\,dz$, $w=1/2+ix$, as in the [measurable-tail proof](joint-tail-deletion-33.md#joint-price). The fixed-probe cross term in the dual is real bilinear and continuous on $L^2(\mu)$ because its two multipliers $p,H(x)$ in the quadratic form are bounded (here $H(x)$ denotes the frequency multiplier of that proof, not the atom support function). Approximate the bounded moment profiles on the compact bands by interval averages in $L^1$ and keep the core laws. The fields converge uniformly in frequency, hence in $L^2(\mu)$; the linear prices converge since the price densities are bounded on the bands. This extends the summation-by-parts identity to measurable laws. Only the limiting law needs to satisfy the caps and the necessary disk inequality. The pointwise support bound then applies directly.

For each *fixed atom*, its density price $-\Phi'\cdot v(u)$ on a cell of width $h$ is at most its endpoint chord plus $h^2D/8$. Use the bound

$$D=(L_A+L_B)e^{-\inf(I)/2}+3\,\mathbf1_{\sup(I)>0}$$

from the piecewise third derivatives of the primitives in the mobile mesh proof. Take zero as a cell endpoint whenever a band crosses it: $W'$ is continuous there but its derivative can jump. The other two second derivatives are continuous across their kernel joins. Taking the maximum over atoms **after** this inequality bounds the integral by the trapezoid sum of endpoint maxima plus $|I|h^2D/8$. It does not differentiate a maximizing atom. With 8 and 16 equal cells per band, respectively, the summed remainders are less than $1.753\cdot10^{-8}$ and $2.349\cdot10^{-8}$. Sextic Bernstein subdivision with outward ball bounds covers the full atom interval.

**Where to keep the common boundary.** At $r=1/250$ the *supremum of this dual price* on the same relaxation exceeds $5.01\cdot10^{-7}$. To bound it **below**, split each band into four equal subslabs. Independently on every subslab and core take the best lower endpoint among the actual atoms evaluated during Bernstein subdivision. Add their integrated price differences and the same price constant. Thus refining the quadrature of this particular relaxed price cannot give an exclusion at this radius. This is not a positive feasible surplus: These competing atoms need not meet even the first caps. Keeping one common boundary per band, as in the mobile mesh proof, prices a different, smaller family.

Replay from the root with assertions enabled:

```sh
/opt/sage-10.9/bin/python .godel/bob/check-swept-bands-deletion-33.py
```

The [decision record](swept-bands-decision.md) explains why the method is a local handoff, not a standing program instruction.
