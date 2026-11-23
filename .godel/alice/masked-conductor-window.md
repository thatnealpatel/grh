# Charge the signed slice to the two endpoints

The [each-prime second-order theorem](critical-conductor-window.md) holds with $c=183/200$ in place of $3/5$. Thus for fixed $0\le a<c$, $L=\log q$, $B=\log L$, $A=2+a/B$, and $b=\log(AL)$, the floor is $(c-a-o(1))L/B$ on **every** complex compact test in $(-b,b)$ and relative to the Cauchy Gram matrix on **every** finite right-hand Pick block with distinct real nodes $m\ge B^3$, $\sum 1/m\le b$. One exceptional fraction $O(\exp(-\delta L/B))$ of the primitive characters at each sufficiently large prime suffices. We change the prime operator estimate, not the Gamma form or the block approximation.

## A profile criterion

Use the linked proof's $Y=q\exp(cL/B)$, $Z=q^\alpha$, $d=Z^{-1/2}$, $D_0=2b+B^{-5/4}$, $D=D_0+2d$, $X=e^D$, and $E=\sqrt X=AL+o(L/B)$. Work on the interval of length $D$ obtained by padding $[0,D_0]$ by $d$ on each side. Use coordinates $x,s=D-x$ measured from its two ends. Let $w\ge0$ be bounded, piecewise smooth of bounded variation and compactly supported on $[0,\infty)$; let $m\ge0$ be a smooth compactly supported mask on that half-line with a smooth compactly supported extension to the line. Write

$$I_j=\int_0^\infty e^{-jr}w(r)^2\,dr,\quad K=\int_0^\infty e^{-x}m(x)^2\,dx,\quad M=\iint_{x,z\ge0}e^{-x-z}m(x)m(z)w(x+z)\,dx\,dz.$$

It suffices that

$$e^{c/4-1/2}(I_0 I_1)^{1/4}<M/K. \tag{1}$$

Indeed choose $v$ strictly between these values. The [length-weighted moment](critical-conductor-window.md#a-length-weighted-moment-for-the-slice) gives a bound $vE$ on the **forward** slice multiplier at $|t|\le4Y$, except on the stated exceptional fraction. For clarity, its prime coefficients are $b_p=w(D-\log p)(\log p)/\sqrt p$; partial summation on the fixed log slice gives $\sum p^jb_p^2=(1+o(1))X^j D I_j$ for $j=0,1$. With $k=\lfloor\log(qY)/(D+\log(I_1/I_0))\rfloor$, the one-modulus moment is at most $Y k!(D I_0)^k e^{o(k)}$. Stirling gives the left side of (1) as the limiting peak threshold in units of $E$ since $A\to2$. Neither the moment nor the derivative bound $O(ED)$ requires a smooth cutoff at the top of the $r$ interval. The strict gap absorbs persistence loss $O(E/D)$ and the $O(D)$ cost of the prime powers.

For the edge from $z$ to $x=z+\log n$ delete the fraction $\varepsilon m(z)m(s)w(s+z)$ of its coefficient in both directions. Here $s+z=D-\log n$. Choose $\varepsilon>0$ fixed and sufficiently small that all residual weights are nonnegative. Let $u$ be the middle-frequency piece of an original unit input, and $u_I$ its spatial restriction extended by zero. If $C_\chi$ is the forward signed slice on the line and $m_L,m_R$ the two translated/reflected mask extensions, the deleted form is exactly $2\varepsilon\Re\langle m_Lu_I,C_\chi m_Ru_I\rangle$ with the shift convention of the linked proof. That proof gives $\|u-u_I\|=o(1/B)$, also for blocks. Replace $u_I$ by $u$, project both masked factors onto $|t|\le4Y$, and apply the bound $vE$ there. The projection loses $O_N(Y^{-N})\|u\|$ in norm since $\widehat u$ is supported on $|t|\le2Y$ and the mask transforms have uniformly Schwartz tails in modulus. The global operator costs $O(E)$. By $2ab\le a^2+b^2$, restoring $u_I$ gives an upper bound

$$\varepsilon vE(\|m_Lu_I\|^2+\|m_Ru_I\|^2)+o(L/B).$$

Keep this **diagonal operator**, not its norm. Add it to the unsigned residual on the interval, calling the sum $R_\varepsilon$. Its form on $|u_I|$ bounds the whole prime form up to the leakage error.

## Schur estimate including the diagonal

Put $P(s)=m(s)\int_0^\infty e^{-z}m(z)w(s+z)\,dz$, $J(s)=P(s)-vm(s)^2$, and $H=\int_0^\infty e^{-s}J(s)\,ds=M-vK>0$. For $f(x)=e^{-x/2}$ take $F(x)=f(x)(1-\varepsilon J(x))$ and $W(x)=F(x)+F(s)\asymp f(x)+f(s)$. On $F(x)$ the forward unsigned residual row costs $O(1+D)f(x)$, by $\sum_{n\le X}\Lambda(n)/n\ll 1+D$. The backward row is

$$f(x)\sum_{n\le e^x}\Lambda(n)[1-\varepsilon m(s)m(z)w(s+z)][1-\varepsilon J(z)],\qquad z=x-\log n.$$

For $x\ge D/4$ use quantitative PNT and partial summation as in the unmasked proof: The two factors have bounded variation uniformly in $s,x$ (including the jump in $w$). The error before $f(x)$ is $O(e^x e^{-\kappa\sqrt D})$. In the integral substitute $dn=e^x e^{-z}|dz|$ and extend to $z\ge0$ by nonnegativity. Since $e^x f(x)=E f(s)$ the main upper bound is $E f(s)[1-\varepsilon(P(s)+H)+O(\varepsilon^2)]$. For $x<D/4$ the whole sum before $f(x)$ costs $O(e^{D/4})$ and the proposed main upper bound is nonnegative. The reflected row has the same estimates by symmetry of the deletion in the two endpoint distances. Relative to $EW$, the combined errors are $O(e^{-\kappa\sqrt D}+(1+D+e^{D/4})/E)=o(1/B)$.

The diagonal acting on $W$ adds $\varepsilon vE[m(x)^2 f(x)+m(s)^2 f(s)]$, up to $O((\varepsilon^2+e^{-D/2})EW)$: In the support of either mask the opposite endpoint weight is $O_m(e^{-D/2})$ times the near weight. Thus it replaces $P$ by $J$ in the row estimate. Factoring $W$ back out gives

$$R_\varepsilon W\le EW[1-\varepsilon H+O(\varepsilon^2)+o(1/B)].$$

Weighted Schur for the symmetric nonnegative kernel bounds its whole-space norm on the interval. Fixing $\varepsilon$ sufficiently small gives a middle-band prime cost at most $(1-\gamma)E\|u\|^2+o(L/B)$ for a fixed $\gamma>0$. Choose $\alpha<1$ with $1+\alpha>2(1-\gamma)$. The low-band full multiplier estimate, outside a further fraction $q^{-(1-\alpha)/2+o(1)}$, is unchanged. Low and middle bands now have positive margins in units of $L$. Above $Y$ the unmasked Schur bound at $\varepsilon=0$ and the Gamma bound give $L+\log Y-O(1)-(1+o(1/B))E=(c-a-o(1))L/B$. Add the three frequency forms exactly as in the linked proof. All truncations were in prime forms only; their errors, including the omitted shifts for blocks, were per original unit input.

## A rational certificate

Set $p(x)=1+3x/2+4x^2$, $t(r)=r^2+r^3/8+r^5$. Use $m(x)=p(x)e^{-7x/5}$ up to 20, smoothly cut down to zero by 21 without increasing it. Use $w(r)=t(r)e^{-49r/20}$ up to 20, zero beyond. Before truncation the integrals are

$$\bar K=8292185/4952198,\quad \bar M=2203402669199727680000/7153014030880804126753,$$
$$\bar I_0=78287736980700000/558545864083284007,\quad \bar I_1=729034724820900000/30155888444737842659.$$

These follow by integrating each $r^j e^{-ur}$ as $j!/u^{j+1}$. In $\bar M$ the convolution polynomial $p*p=r+3r^2/2+73r^3/24+r^4+8r^5/15$ multiplies $t(r)$ at rate $u=97/20$. For $r\ge20$ the product is at most $r^{10}$ (divide by $r^{10}$ and check at 20; the ratio decreases). The lost tail in $M$ is therefore at most $20^{10}e^{-97}/(97/20-1/2)<10^{-7}\bar M$, using $\log(r/20)\le(r-20)/20$. There is no loss at $r=x+z\le20$. The other three integrals only decrease. The rational checks

$$\frac{[(1-10^{-7})\bar M/\bar K]^4}{\bar I_0\bar I_1}>\frac{169}{500},\qquad \frac{169}{500}\sum_{j=0}^6\frac{(217/200)^j}{j!}>1$$

imply (1), since $2-c=217/200$.

**Limit of the inference.** At $Y=q^{1+\beta}$ with $\beta>0$ fixed and $k\sim\kappa L/B$, the same length-weighted factorial upper bound for exceeding any fixed $vE$ has log equal at leading order to $[\max(1+\beta,2\kappa-1)-\kappa]L$. Indeed the two lengths are $Y$ and $q^{-1}(XI_1/I_0)^k$, and $k!(DI_0)^k/(vE)^{2k}=q^{-\kappa+o(1)}$. The minimum over $\kappa>0$ is $\beta/2$, not negative. This does not show that peaks exist. It explains why optimizing a fixed pair of masks at this moment bound does not reach fixed $A=2.1$; the [sparse pair test](sparse-pair-gap.md) asks for a saving of a different order.
