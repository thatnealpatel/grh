# A fixed rectangle for the original signed screen

The positive and negative bands of the [uncut screen](uncut-screen-mean.md) can be priced **net** at one prescribed height without finding any zeros far to the right. The other input is arithmetic: Use the full, signed Weil evaluation at that very height, not its typical value. Simply truncating the original zero sum to the rectangle below would be wrong. A single distant-in-depth pair in that sum can have an exponentially large unnormalized carrier.

Use $R=(9/5)\log q$, $D=2\log R$, $a=1/D$, $A=1/2+a$, $t=2q^{3/5}$, $x=\gamma-t$, $b=\beta-1/2$, $c=bD$, $S=2\sinh 1$, and $B_0=2-2/e$. Use the original $F=g_\epsilon B^2$ from [the signed remainder](uncut-defect-price.md#the-signed-remainder), with fixed small $\epsilon>0$. Write $\ell(x)=(1/4+x^2)^{-1}$, $g=g_\epsilon(x)$, $v=\cos(Dx-2\arctan(2x))$. Sum over $b\ge0$ with weight $\nu=1$ per right member and $\nu=1/2$ per line zero, including multiplicities. For $h>1/2$ put $p_b^h=k_{h-b}+k_{h+b}$ and $W_h=\sum\nu p_b^h(x)$, the completed exterior trace at $1/2+h+it$. Here $k_u(x)=u/(u^2+x^2)$.

Fix $h\ge1$ and $C>1$. The only zero census needed is

$$\mathcal B=\{ |x|\le h,\quad 0\le c\le C\}.$$

Define the local correction (the two cases **do not** agree at the switch)

$$ U(c,x)=\ell(x)\begin{cases}2g-B_0+2g\cosh(c)v,&0\le c\le1,\\-S e^{1-c}g v,&c>1.\end{cases}$$

With $H=-\sum_\rho\Re F(x-ib)/(2R)$ evaluated by the full explicit formula, form

$$ Z_{\mathcal B}= H+B_0 W_A/R + R^{-1}\sum_{\mathcal B}\nu U(c,x),\qquad
 m_{\rm out}=(W_h-\sum_{\mathcal B}\nu p_b^h(x))/R.$$

Both exterior inputs to $Z_{\mathcal B}$ can be evaluated without the census: $H$ uses the [full prime, gamma, and pole terms](short-buffered-packet.md), and $W_A$ uses the exterior logarithmic derivative. In particular this is not a reconstruction from an unsigned count or from $W_h$ alone. At additional cost $O(\epsilon)+o_\epsilon(1)$ one may use $\Re S_V(t)-1/(3e)$ for their sum. Here $S_V(t)=V^{-1}\sum_{p<V}(\log p)\log(V/p)p^{it}$ with $V=R^2$. Indeed the translated formula gives $H=\Re S_V(t)-m_D/6+O(\epsilon)+o_\epsilon(1)$: The main gamma term uses $m_D=\int F/(2\pi)$, and the smoothed prime-side error is the Lipschitz convolution price in the linked proof. In the real-axis expansion of $F$, the carrier integrals are $o_\epsilon(1)$, and $\int(1-g)\ell=O(\epsilon)$ by $1-g\ll\min(1,\epsilon^2 x^2)$. Thus $m_D=2+O(\epsilon)+o_\epsilon(1)$. Also $W_A/R=1/6+o(1)$ since $|\zeta'/\zeta(1+a+it)|\le-\zeta'/\zeta(1+a)=O(D)$.

**Pointwise enclosure.** Set $M=2/e+2\cosh 1$, and $P(K)=\max\{K/h,2hS e^{1-C}\}$. Then at the original cutoff and ordinate,

$$ -P(S)m_{\rm out}-o(1)\ \le\ Z-Z_{\mathcal B}\ \le\ P(M)m_{\rm out}+o(1). \tag{1}$$

The errors tend to zero with $D$ for fixed $h,C,\epsilon$. There is no $O(\epsilon)$ in (1) with the exact exterior inputs. The unused mass $m_{\rm out}$ is nonnegative and at most $1/6+o_h(1)$: For fixed $h\ge1$ absolute Euler convergence and Stirling give $W_h=\tfrac12\log(t/(2\pi))+O_h(1)$. The price is a maximum, not a separate copy of this budget for each tail. For example $h=2^{14}$ and $C=24$ give asymptotic worst-case upper and lower error magnitudes below $0.000039$ and $0.000024$, respectively. Indeed $M<3.83$, $S<2.351$, $2h^2<e^{23}$, and the prices are $M/h$ and $S/h$. These are asymptotic allowances, not effective verification thresholds for a finite $q$.

**Why the growing carriers disappear.** Start with the exact all-ordinate sum for $Z$ in the [mean bound](uncut-screen-mean.md). Subtract $H+B_0W_A/R$ *before* making any cut. The remaining unnormalized summands in the $\nu$ convention are

$$\begin{cases}
\Re F(x-ib)-B_0 p_b^A(x), & b\le a,\\
-q_b(x)+B_0(\delta_b(x)-p_b^A(x)), & b>a.
\end{cases}$$

Indeed $H$ contains the same $-\Re F$ from every deep pair. The supporting pair belongs to the first row, since it contributes nothing to $Z$. Here $q_b,\delta_b$ are exactly those in the signed remainder. Only the broad second width in $\delta_b-p_b^A=k_{A+b-2a}-k_{A+b}$ changes, so this difference is $O(a\ell)$ even as $A-b\downarrow a$.

Uniformly in **all** $x,b$, the two rows are $U(c,x)+o_\epsilon(1)\ell(x)$. For the first row, shift the two-half expansion to $x-ib$. The low envelope is $2g\ell$, the reflected carriers have real parts summing to $2g\ell\cosh(c)v$, and $p_b^A=(1+O(a))\ell$. Freezing each envelope costs $O_\epsilon(a\ell)$ by the strip derivative bound and $c\le1$. For the second row the [Poisson propagation proof](uncut-defect-price.md#the-signed-remainder) gives $q_b=Se^{1-c}gv\ell+o_\epsilon(1)\ell$ through $b_0=\sqrt a$, where $\delta_b=(1+O(\sqrt a))\ell$. At $b_0$ the whole $q_{b_0}$ is $o_\epsilon(1)\ell$. Beyond $b_0$, the positive propagation of $\ell=2k_{1/2}$ is $2k_{1/2+b-b_0}=O(\ell)$, and $e^{1-c}=o(1)$. This last step is needed: An arbitrary $o(1)\delta_b$ remainder need not be $o(1)\ell$ at the narrow pole. Since $h$ is fixed and $p_b^h\gg_h\ell$, the aggregate approximation error is $o_{h,\epsilon}(1)W_h/R=o(1)$.

**Price what is missing.** On $b>b_0$ the residual $U$ is already negligible in the same budget. On $b\le b_0$ we have $p_b^h=(1+o_h(1))2k_h$ uniformly in $x$, by logarithmic differentiation in the width. For $|x|>h$ the ratio

$$ \ell(x)/(2k_h(x))=(h^2+x^2)/(2h(1/4+x^2))\le 1/h.$$

Here $-S\le U/\ell\le M$: In the first row use $0<g\le1$ and $|v|\le1$, and in the second row the absolute price is at most $S$. For $|x|\le h$ outside the census one instead has $c>C$. Now $|U|/\ell\le Se^{1-C}$ and the same kernel ratio is at most $2h$ (its value at zero). These two disjoint cases prove (1) after summation over the unused budget. No sign assumption was made on the contents of either band, and no tail of the explicit formula was deleted.

**What changes at a candidate.** This replaces a search over all depths and growing ordinate windows by a signed finite statistic in a fixed ordinate window and depth $C/D$, plus arithmetic at the original height. For arbitrarily small fixed resolution one can increase $h$ and then choose $C>1+\log(2h^2)$. If using (1) for a decision, the census must distinguish sides of $c=1$, include line multiplicities, and resolve the carrier, not just the ordinate density. A missing or uncertified entry in the rectangle is not covered at the outside price. For an incomplete census there is a simple fallback: Use the measured sublist instead of $\mathcal B$ in both $Z_{\mathcal B}$ and $m_{\rm out}$. Partition $[-h,h]$ into disjoint bins $I$. If $n_I$ bounds the number of unaccounted zeros in each bin in the *full strip*, enlarge the upper allowance by $M\sum_I n_I\sup_I\ell/(2R)$, and the lower error magnitude by the same quantity with $S$ for $M$. The missing $\nu$-weight in the box is at most $n_I/2$, whether a missing zero is on the line or part of a reflected pair. The enlarged $m_{\rm out}$ still covers both true tails. This needs only counts for the missing entries, but it charges them at the local, not the tail, rate.

As a check of the decision, the [all-deep finite Euler calibration](uncut-depth-discount.md) at depth 40 has **empty** census for $C=24$. Its exterior baseline at the minimum failure harmonic tends in the iterated small-smoothing calibration to $47/81-1/(3e)=0.45762043\ldots$. The empty box predicts that value, not zero; the full residual is bounded by $Se^{-39}/6+o(1)$ there. Thus the price does not supply a small-$Z$ conclusion from the failure harmonic alone. On actual zeros it is the signed correction to the exterior baseline that must be measured. No exceptional conductor or census for one is supplied here, and a uniform upper bound of $0.0658$ remains open.
