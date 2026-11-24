# A high-mass buffered mark would refute RH

Use the eight signed tests, the moving mass $M_{X(q)}$, and the frozen-node rule of the [principal block search](principal-block-search.md), with $a=0.587$, $X(q)=((9/5)\log q)^2$, and $Q\le q\le Q+J\le 2Q$. Write $k=\lfloor\log_2 Q\rfloor$, $\eta=1/\lfloor\sqrt{k+1}\rfloor$. A marked cell meeting its target requires, at its **left node** $t$ and its actual frozen integer $V$,

$$s\Re S_V(t)\ge c_k:=a-5\eta/8,\qquad V\le X(Q)<V+2.$$

Here $s$ is the prescribed sign. The estimator can overestimate by $\eta/8$, and its marking threshold is $a-\eta/2$. We use neither asymptotic freezing accuracy nor a converse from this necessary condition. The left node is within one unit of the target height, since the cell width is $1/(k+1)^2$.

**Result.** Suppose the cell meets the target with $M_{X(q)}>8/9$. Put $R=\sqrt V$, $D=\log V$. Then there must be a nontrivial zeta zero satisfying

$$ |\gamma-t|\le256R,\qquad \beta>\tfrac12+0.1/D,\qquad \gamma>3\cdot10^{12}. $$

In particular there is no such list under RH for **zeta**. Unconditionally, the handoff range $29\le k\le41$ is empty, including nondyadic $Q$. More generally, no such cell occurs on any block with $Q+J\le2^{60}$, or on a dyadic block $Q=2^k<2^{60}$. The exclusion for unrestricted $Q<2^{60}$ needs the height qualification below. These statements are about the specified buffered search, not the full Weil form, all endpoint heights, or a proof of RH. There is no new successor measurement.

## Direct finite certificate

For $Q<2^{17}$, even $q=2Q$ gives $q<2^{18}$. The moving mass below that edge is $<0.887560$: Between consecutive primes it is $(A\log X-B)/X$, with $A=\sum_{p\le X}\log p$ and $B=\sum_{p\le X}\log^2 p$. Price the endpoints and the stationary point $\exp(1+B/A)$ when present; below 2 the mass vanishes. This part need not rule out marks.

For $17\le k\le41$ we instead bound the frozen modulus over the **continuous** strip of target heights, enlarged by one at each end. The largest cap was $<0.395527$ and the smallest slack against its own $c_k$ exceeded $0.0352236$. On $29\le k\le41$ alone the largest cap was $<0.387083$ (at $k=30$), against thresholds at least $0.462$. Thus a narrow subset of expensive candidates from the [earlier common-height sieve](common-height-sieve.md) is not needed in this finite band.

Here is how to reproduce the certificate without trusting floating-point trigonometry or sampling maxima. On each of the 37 slabs $L\le\log_2 Q\le U$ (quarters for $17\le k\le20$, whole units thereafter), include all possible integer $V$ and all heights from $2\,2^{3L/5}-1$ through $40\,2^{3(U+1)/5}+1$. Use the endpoint weights and the maximum at $ep$ if present to enclose each $w_p$. Demodulate by $e^{-idt}$, with integer $d$ near the weighted mean of $\log p$; this leaves the modulus unchanged. Between two mesh values at distance $h$, complex linear interpolation costs at most $h^2\sum_p w_p(\log p-d)^2/8$ by the second-derivative bound. Convexity of the norm then reduces the bound to the larger endpoint norm plus this allowance. The mesh pitch is $1/4$ below $k=29$ and $1/2$ above and including it. This is a dense **finite** certificate, not a sublinear algorithm.

Factor each mesh rotation at index $1024b+i$ into two rotations, at $1024b$ and $i$. Choose a word within one of $2^{64}h(\log p-d)/(2\pi)$ and use the top 13 bits of the modular product for the phase bin. Both indices are below $2^{36}$, so the midpoint error in radians including word error is $<2\pi/8192$. Trig values at the midpoints are interval-certified integers after scaling and rounding. The outer factor has coordinate scale $H_0=128$, giving complex error $r=2\pi/8192+\sqrt2/H_0$. The inner weighted table (scale $W=32768$) uses trig scale $65536$, weights rounded at scale $2^{24}$ with the entire slab variation charged, and a final coordinate rounding of at most $1/(2W)$. If the sum of its entry errors is $e$, the aggregate product error is $\le r\sum_p w_p+(1+r)e$. All these allowances and interpolation are added before comparing with $c_k$.

On the recorded CPU backend the batched matrix products use binary32 on **integer-valued** inputs. The column bound $H_0\max_i\sum_p(|C_{pi}|+|S_{pi}|)<2^{24}$ for the inner integer tables bounds each product and every partial sum; no rounding of those integers is required. The squared norms of the integer results are exact in binary64. The actual comparisons use a squared integer threshold rounded down by interval arithmetic after checking that the unsquared threshold is positive. Unsigned 64-bit wraparound in the phase is intentional; the outer index multiplication before conversion uses signed 64-bit indices. Do not substitute reduced-precision accelerator arithmetic for these products.

## Where verified height ends

For $42\le k\le66$, enumerate each integer $V$ in the permitted range. With $H=3\cdot10^{12}$ and $T_0=H-10^9$, compute the two signed prices in the [translated Weil formula](verified-height-principal-band.md), grouping all powers of each prime at a common phase. The lower height is $2e^{R/3}-1$; the upper bound before clipping is $t_f=40\,2^{3/5}\exp(\sqrt{V+2}/3)+1$. Up to $\min(t_f,T_0)$ the slack against $c_k$ exceeds $0.0001244$. For $t>T_0$ the **numerical price only**, continuing its increasing logarithm to $t_f$, still leaves more than $7.25$ before division by $2R$, with $73<R<84$. This second bound does not drop the unverified zeros.

To extend the old $0.044$ undivided remainder from $2.8\cdot10^{12}$ to $T_0$, keep the archimedean bound $0.043$. On $H<|\gamma|\le 2H$ the unit count of positive ordinates is $<90$ by differencing the cited $N(Y)$ estimate (main-term increment $<\log(2H+1)$ and each endpoint error $<\log(2H+1)$). With $d_0=10^9$ the cost is $\le4000\cdot180(d_0^{-2}+d_0^{-1})$, summing inverse squares for both signs. Beyond $2H$, $|\gamma-t|\ge |\gamma|/2$; the dyadic count in the same note gives $16000\cdot4(2\log(4H)+2\log2)/(2H)$. These charges and $8000/t^2$ for the poles fit in $0.001$ on the extension. Below the old cap its original proof applies. For example all eight modes at $q\le2^{60}$ fit under $T_0$, but $Q=2^{60}-1$, $J=Q$ allows $q$ almost $2^{61}$, where the $17$th and $20$th do not. The first six modes do fit through $q=2^{61}$.

## Price the large-cutoff prime side

Use the [same two halves, transform $h$, and explicit formula](verified-height-principal-band.md#translated-formula-with-a-finite-error), now at the frozen cutoff. For clarity $b=f+sg$, $f(v)=e^{-v/2}$ on $[0,D/2]$ and zero elsewhere, $g(v)=f(D-v)$, and we center $b$ by translation. For $B(z)=\int b(v)e^{izv}dv$, $h(z)=B(z)\overline{B(\bar z)}$ and the real-axis mass is $2\pi K(0)=4\pi(1-1/R)$. In the upper price for $s\Re S_V(t)$, the zero cost is $-\sum_\rho\Re h(\gamma-t+i(1/2-\beta))/(2R)$. Under RH it is nonpositive. With arbitrary phase in $b$ this is also true for the modulus bound under RH.

For $k\ge67$ one has $R>83$ and $T=2^{40}<t$. Since $(9/5)\log Q< R+1/R$, one has $\log(t/(2\pi))<R/3+\log(20/\pi)+(3/5)\log2+1/(3R)+1/T<R/3+7/3$. This last inequality also holds on the unverified part of the preceding band ($R>73$, $t>T_0$). In the two-half formula the pole cost before division is $\le32R/t^2$; the explicit archimedean excess in the linked proof decreases from a value $<300/T$ at $T$. That excess bound used $\operatorname{TV}(b),\|b\|_1\le4$, not an upper bound on $D$. Including the main archimedean term gives a normalized price $<1/3+2/R+2/T$ before prime corrections and zeros.

For $n=p^m$ put $A_n=(2\log p/R)(1/n-1/R)_+$, $C_n=(\log p/V)\min(\log n,(D-\log n)_+)$, and $\Delta_n=\mathbf1_{m=1}w_p-C_n$. The normalized prime side of the formula is $\sum_n(A_n+s C_n)\cos(t\log n)$; the signed ramp differs by $\sum_n(s\Delta_n-A_n)\cos(t\log n)$. Relax the latter to $\sum_n(A_n+|\Delta_n|)$ **only in this large band**. The same upper correction works for an arbitrary projection phase using the shifted cosine on $\Delta_n$. For $83\le R\le400$, interval evaluation on each closed $[r,r+1]$ prices these corrections including prime-power entries at the larger endpoint. The largest total price ignoring zeros was $<0.470000444$, on the first interval.

For $R\ge400$, $\sum A_n\le 2R^{-2}\sum_{n\le R}\Lambda(n)\lfloor R/n\rfloor=2R^{-2}\log(\lfloor R\rfloor!)\le2\log R/R$. Both $\Delta_p$ and $C_{p^2}$ are $\le 2(\log p)\log(R/p)/R^2$ for $p\le R$, and zero above. Since $\sum_{2\le n\le R}\log(R/n)\le R$ by integration, these cost at most $4\log R/R$ together. For $m\ge3$ there are at most $R^{2/3}$ bases and $2\log R/\log p$ powers per base, of price $\le(\log p)\log R/R^2$ each. The resulting total cap is

$$ 1/3+(2+6\log R)/R+2(\log R)^2/R^{4/3}+2/T<0.470001. $$

The nonconstant powers with logs decrease from $400$, where $\log400<6$ and $400^{1/3}>7$. Thus the uniform **RH** cap is $<0.470001$, against $c_k\ge0.508875$. Here it was not necessary to estimate the negative zero terms because there are none under the premise. Next remove that premise but retain a priced zero term.

## Which zeros must pay for a mark?

This part is unconditional. In either above-cap regime $R>73$, $D>8$, $t>T$. Write $x=\gamma-t$ and $u=1/2-\beta$. For a zero with $|u|\le0.1/D$, the transforms of $b(v)\cosh(uv)$ and $b(v)\sinh(uv)$ are $C,L$ at real frequency $x$. Then $B(x\pm iu)=C\mp L$ and $\Re h(x+iu)=|C|^2-|L|^2$. Since $|v|\le D/2$, the latter odd multiplier times $b$ has $L^1$ norm $\le4\sinh(.05)$ and variation $\le4\sinh(.05)+(0.4/D)\cosh(.05)<0.251$. Integration by parts therefore prices the negative part by $0.064\min(1,x^{-2})$. This uses the product variation, including the derivative of the multiplier.

Set $P_a(x)=a/(a^2+x^2)$. With $z=\sigma+it$, the [real Hadamard identity](endpoint-zero-packets.md#price-the-part-near-the-critical-line) for the completed zeta gives

$$ W_\sigma:=\sum_\rho P_{\sigma-\beta}(x)=\Re\left(1/z+1/(z-1)-\tfrac12\log\pi+\tfrac12\psi(z/2)+\zeta'/\zeta(z)\right). $$

Reflection at the same ordinate cancels the constant, and the real sum is absolutely convergent. For $2\le\sigma\le t$, the Euler series is bounded by $\sum_{n\ge2}(\log n)/n^2<1.1$ (first summand plus integral from 2); the digamma sum-integral comparison gives $|\psi(z/2)-\log(z/2)|\le\pi/t$. Hence $W_\sigma\le\tfrac12\log(t/(2\pi))+\tfrac12\log 2+1.1+4/t<R/4$. This uses both rational terms and all zeros with multiplicity.

Put $M=256R$. On $|x|\le M$ charge the zeros with $|u|\le0.1/D$ by $0.064\cdot2.5P_{2-\beta}(x)$; the factor $2.5$ bounds $a+1/a$ on $[1,2]$. Outside $M$ use $|h(x+iu)|\le16R/x^2$ throughout the critical strip. For $a=M+2-\beta$, $x^{-2}/P_a(x)=1/a+a/x^2<2.001/M$, and $M+2<t$ since $t\ge2e^{R/3}-1$. The total loss from these two disjoint sets **after division by $2R$** is less than

$$ (0.064\cdot2.5+16\cdot2.001/256)/8 <0.036. $$

Write $\mathcal B=\{\rho:|x|\le M,\ |u|>0.1/D\}$. In the finite band above $T_0$, the undivided room $>7.25$ already allows the poles and archimedean excess ($<0.044$ together); $7.25/(2\cdot84)>0.043$. In the large band the room is $>0.038874$. It follows in **both** bands that a mark requires

$$ -\frac1{2R}\sum_{\rho\in\mathcal B}\Re h(x+iu)>0.002874. $$

It is the signed sum for the marked sign, not the number of off-line zeros alone. At least one member exists, and reflection supplies a right-hand zero at the same positive ordinate. Published verification then puts it above $H$. No converse follows. A [shorter asymptotic packet](short-buffered-packet.md) prices this signed obstruction with a smoothed test.

## Replay and decision

Run `check-buffered-frontier.py`, `check-buffered-band-edges.py`, and `check-buffered-large-ramp.py` in this directory with SageMath 10.9 Python and assertions enabled. For the first run we used `OPENBLAS_NUM_THREADS=6`, NumPy 2.5.3, and OpenBLAS 0.3.34 on x86-64 (EPYC 9554P); the phase and weight enclosures use 100-bit real intervals. The edge checker calls the existing per-prime price routines. The large checker certifies the transition intervals and the rational tail comparison, not a statement about uncomputed zero locations.

Do not move the same positive-example search to larger dyadic blocks as a routine way to compare successors: Any genuine high-mass example would already overturn verified-or-local principal positivity in the precise sense above. The [signed affine successor test](finite-successor-cap.md) and the [low-mass actual cells](selected-cell-comparison.md) still answer different questions. Neither supplies this missing input.
