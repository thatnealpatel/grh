# A one-slab release after optimizing the fixed fields

At $c_0=39/20$ on the [1,257-knot reference](joint-tail-deletion-33.md), the necessary early score is attainable without changing either first field. But even the best such law still has $M-8/9<-4.62477\cdot10^{-7}$. By changing $A$ on just **one** slab after this polish, one obtains a law at $c_1=1.9500036$ with $M-8/9>9\cdot10^{-9}$, both unfolded first caps, zero orders two through ten at $t$, and the three simultaneous zero second replies at $3t$. This improves the [previous all-real witness at 1.95001720](priced-deletion-33.md); the new law **violates** the $t$ cap at $c_0$.

## What can change while both fields are fixed?

Use the reference law on the negative side, and fix its $A(z),B(z)$ pointwise on the positive side. On each of the 763 nonnegative slabs, including the infinite last slab, the [four-column table](deletion-laws/delete-33-tail-fiber.triples) names a knot in units of $1/400$ and three candidate sites $u_i$ in units of $10^{-9}$. Write $X_i=2u_i^2-1$, $T_i=4X_i^3-3X_i$. Solve $Hp=(1,A,B)^t$ over the rationals, with columns $(1,X_i,T_i)^t$; verify $p\ge0$ and the equality. Use these weights if they give larger $U$ than the reference; otherwise keep the reference. This defines the attained law exactly. For an upper bound solve $H^t(d,\alpha,\beta)^t=(u_i)_i$; **replace** $d$ by a global upper bound for $\max_{0\le u\le1}(u-\alpha X-\beta T)$. The degree-six Bernstein subdivision from the joint checker supplies it. Thus the upper bound applies pointwise even to measurable laws that vary within a slab but preserve its moment pair. Numerical site selection used finite-site linear programs and polynomial critical points; the proof needs neither the optimizer nor its dual weights.

The positive integration weights are differences of $(1+z)e^{-z}$, with zero at infinity. The attained surplus is $-4.62709308\cdot10^{-7}$ (rounded); the upper price is $-4.62477772\cdot10^{-7}$ (rounded), leaving a bracket of width less than $2.32\cdot10^{-10}$ on the optimum. The attained $[0,1)$ gain exceeds $5.4531\cdot10^{-8}$, compared with the necessary $2.00148\cdot10^{-8}$. Here gain in $M$ **is** gain in the joint score since both moment differences vanish. The quadratic second field is also exactly unchanged, not merely on the favorable side of a tangent. Passing the local score and the second test is therefore insufficient.

## One change at fixed third harmonic

On $I=[1.96,1.965)$ replace $53/1000$ of the attained law by the single atom $v=\sqrt{(1+x)/2}$, where $x=\cos((\arccos B_I)/3)$. Then $T(x)=B_I$ and the change $\Delta A=(53/1000)(x-A_I)$ is positive. Check $M$ by adding $(53/1000)(v-U_I)\int_I ze^{-z}dz$. For the first field at $t$ the jump formula, or integration on $I$, bounds its norm change at $c_0$ by

$$D=\frac{|\Delta A|}{C_t(c_0)}\int_I e^{-z/2}dz.$$

Indeed the Fourier integrand has a phase factor of modulus one, including the factor $\bar w/w$ from integrating the two jumps. At frequency zero the change is exactly $+D$: The modified value at $c_0$ exceeds $1.00000342$. At $c_1$, put $r=\cosh(c_0)/\cosh(c_1)<1$. The reference cap at $c_0$ gives $\|V_A(c_1)\|_\infty\le r(.9999998+D)<.999999975$ on the entire line, including its tails. Use the [twelve-angle law](unfolded-deletion-33.md) at $t$. At $3t$ the original $B$ is unchanged, so mix its checked conditional circle law at $c_0$ with Haar, retaining fraction $r$. Its first moment scales by $r$ as required, and all three second replies remain zero. Thus this is a single common prime law for the comparison, not an arithmetic failure or a lower bound on the required depth.

Replay both the reference cap/Gram check and the new certificate, using Sage 10.9 with assertions enabled:

```sh
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-tail-deletion-33.py --full-negative
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-fiber-deletion-33.py
```

**At exactly $39/20$.** Do not optimize $U$ again on this fixed pair of field profiles, or refine the depth by searching the same fixed terminal slab. With fixed negative knots, keep the necessary early score but vary the field profiles and use genuine tail freedom beyond the [priced mesh family](joint-tail-deletion-33.md). Price the discarded quadratic on the changed $B$ field before adding tangents. The zero-frequency cap violation above gives a concrete cost to compensate if starting from this witness. A successful fit needs both full caps, the exact second completion, and positive surplus at the target.
