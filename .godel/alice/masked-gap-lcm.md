# Count raw gaps after removing the primes of one fixed set

Fix a first incidence, a [constructed two-label list](shared-row-labels.md) at $g=1$, and an occupied denominator $d$. For one set $S$ of $O(k)$ eligible primes write $m_S$ for the full $S$-part of $|m|$ and $m_{S^c}=|m|/m_S$ for $m\ne0$. The set may depend on $d$ and its selected reference, but is held fixed throughout the count. Write $cF_i h_i-dy_i=q\delta_i$ on an actual endpoint, with $0<|\delta_i|\le H=q^{.390+o(1)}$. Then at most $q^{.4675+o(1)}$ distinct numerators $c$ satisfy

$$\frac{\operatorname{lcm}(|\delta_1|,|\delta_2|)_{S^c}}{(h_1h_2)_S}\le q^{.660}.$$

These are the gaps themselves, not their differences from the reference. For example, even with $S$ empty, a common gap divisor of size $H^2/q^{.660}$ or larger suffices. For arbitrary $S$, large masked parts of different cofactors can contribute jointly. There is no assertion that reference supports capture a positive fraction of a fiber.

**Count directions before fixing the cofactors.** Fix $p_i=(h_i)_S$ and $D_i=(\delta_i)_S$. These have $q^{o(1)}$ choices, including powers: On $O(k)=O(\log q/\log\log q)$ primes the exponent sum of a polynomial-height integer is $O(\log q)$, so stars and bars costs $\exp(o(\log q))$. Put $P=p_1p_2$, $l_i=h_i/p_i$, $x_i=\delta_i/D_i$ (signed), $G=(x_1,x_2)>0$, and $v_i=x_i/G$. Dyadically fix $|x_i|\asymp L_i$ and $G\asymp R$ with $R\le G<2R$. Since $(cF_i h_i,dy_i)=1$, the gaps are units modulo $d$, and $(v_i,l_i)=(G,c)=1$. Set $j=(l_1,l_2)<q^{.115}$ by successive row selection, and $u_i=l_i/j$. Then

$$n=(u_2 v_1,u_1 v_2),\qquad F_2p_2 D_1 n_1\equiv F_1p_1 D_2 n_2\pmod d.$$

This follows by eliminating $c$ and cancelling $Gj$, a unit. Both coordinates are nonzero, and $n$ is primitive in $\mathbb Z^2$: The pairs $(u_1,u_2),(v_1,v_2),(u_i,v_i)$ all have gcd one. With cofactor upper bound $U=q^{.665+o(1)}$ and $d=q^{1.055+o(1)}$, the bounding box has area divided by index $O(E/j^2)$ where

$$E=\frac{U^2L_1L_2}{P d R^2}.$$

For fixed smooth $j$, select a divisor $f\mid u_1u_2$ strictly crossing $CE/j^2$ with overshoot at most $X$ for a sufficiently large absolute $C$; take one if the threshold is below one. Such a crossing exists since $E/(l_1l_2)\le q^{-.275+o(1)}$ by $L_i\ll H$, $R\ge1$, and $h_i=q^{.665+o(1)}$. Split $f=f_1 f_2$ with $f_i\mid u_i$. Imposing $f_2\mid n_1$, $f_1\mid n_2$ gives joint index $df$, since all substituted coefficients are units modulo $d$. The determinant of any two vectors in the centred box is then strictly smaller than the index, so there are at most two primitive directions, including signs. The half-power smooth count and divisor bound give $q^{o(1)}(1+\sqrt E/j)$ choices of filters and splits. Summing over smooth $j<q^{.115}$ costs $q^{o(1)}(q^{.0575}+\sqrt E)$ since the harmonic sum over smooth $j$ is $q^{o(1)}$. Divisors of the two nonzero coordinates recover $u_i,v_i$, hence $h_i$, at subpower cost.

**Recover the scalar and the endpoint.** For each recovered direction, choose $B F_1h_1\equiv qD_1v_1\pmod d$. Then $c=BG+di$ with $(G,i)=1$. Cross $2R$ with a smooth divisor $f_c\mid c$, possible since $c>Z/X>2H$ for $Z=q^{1.055+o(1)}$. There are $q^{o(1)}\sqrt R$ choices. As in [gap-direction recovery](gap-direction-rectangles.md), $BG+di\equiv0\pmod{f_c}$ has index $f_c$ since $(d,c)=1$. The centred body $|G|\le2R$, $|BG+di|\le Z$ has area divided by index $O(Z/d)=O(X)$. Its lattice points either span the plane (apply Pick's bound to their hull) or lie on a line through zero (at most two primitive points). Each $(G,i)$ fixes $c$, and the rows are forced on the list. Thus the price is at most

$$q^{o(1)}\left(q^{.0575}\sqrt R+\frac{U}{\sqrt d}\sqrt{\frac{L_1 L_2}{R P}}\right).$$

The first exponent is at most $.2525$. In a dyadic box meeting the cut, $L_1L_2/(RP)\ll \operatorname{lcm}(|x_1|,|x_2|)/P\le q^{.660}$ up to absolute dyadic factors, so the second exponent is at most $.665-.5275+.330=.4675$. Summing boxes and masked parts costs $q^{o(1)}$.

**Use on the residual.** One mask per selected reference per $d$ costs $q^{.995+o(1)}$ in total. If using all references, this is only a local outgoing allowance to subtract before squaring. Do not union over endpoint-specific masks: The support of the endpoint's own $h_1h_2$ would make the test automatic. Shared primes of $d$ give no gain since $h_i$ and $\delta_i$ are units there. The argument does not need either modular discrepancy test, so it remains valid with both imposed. The large outside lcm, small masked cofactor, far-endpoint case is open; see the [residue occupancy test](reference-projection-review.md).
