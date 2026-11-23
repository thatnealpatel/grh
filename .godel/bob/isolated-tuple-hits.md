# Most central prime-ratio tuples have no local partner

A source-dependent choice of replacement primes can defeat a small redraw probability. But for most of the actual central mass there is **no choice at all** of a partner on a sufficiently close support. This holds even if one can reassign all the signs and look in a wider frequency interval. It rules out one way of paying for the central positive mass, not cancellation between distant supports.

Freeze the [signed prime-ratio test](separated-signed-tuples.md) at $t=2q^{3/5}$, $X=(3\log(t/2))^2$, $D=\log X$, $L=\log t/D$. Fix $0<\gamma<1/2$, $h=\lceil(2+\gamma)L\rceil$, $n=2h=CL+O(1)$, $C=4+2\gamma$. At one shift $1\le d\le5D$ the starts are the primes $p$ with $p,p+d$ prime in $[e^{-8}X,X]$, of weight $w_p=X^{-1}\log(X/p)\log p\log(p+d)$. Require $A=\sum w_p>a_0$ for a fixed $a_0>0$. Put $\rho_p=w_p/A$, $\lambda_p=\log((p+d)/p)$, and $f(u)=\sum\rho_p e^{iu\lambda_p}$. Use the product probability of the $n$ ordered starts, with the first $h$ signs positive and the last $h$ negative. Write $\nu$ for their signed sum of labels. Require the source starts to have pairwise distance $>R$, where $R=X^{\gamma/(16(2+\gamma))}$ or $R=D^2$. Write $M$ for the mass of these separated tuples with $0<|t\nu|<1/2$.

**Isolation.** Set $c=\sigma=\gamma/100$ and $T=t^{1-\sigma}$. Among the separated sources with $|t\nu|\le2\pi$, mark a source if some other signed tuple satisfies all of the following:

* It uses $n$ starts at the same $d$ in the same prime-pair band, and contains at least $n-\lfloor cL\rfloor$ of the distinct source starts.
* Its signed incidence vector (net multiplicity at each start) is neither the source vector nor its negative.
* Its frequency satisfies $|\nu'|\le10/T$.

The total marked **source** mass is at most $t^{-\gamma/70+o(1)}M$, uniformly in the allowed shifts. The partner needs neither separation nor balance; even repeated starts are allowed. It has no sampling cost in this statement. In particular, all but this fraction of the central mass has no local partner anywhere in the negative annulus of $G(z)=(1-|z|/(2\pi))_+\cos z$. A permutation or global reversal does not change $G$. Normalization by $A^n$ is optional since it is common to both sides. On unordered signed supports the source weight must include $(h!)^2$.

## Two short intervals forced by one partner

For $j$ missing source starts, designate one occurrence of each common start in the partner. Split their **source** signed sums into $x$ (sign kept) and $y$ (flipped). Write $r$ for the removed source sum and $s$ for the remaining $j$ signed partner occurrences. Thus

$$\nu+\nu'=2x+r+s,\qquad \nu-\nu'=2y+r-s. \tag{1}$$

Both are nonzero. Indeed if integer coefficients of the $\lambda_p$ are not all zero, the exponential of their linear combination differs from one: At the least start $p$ with nonzero coefficient the prime $p$ has an uncancelled valuation, since an incoming edge could start only at $p-d$. Apply this to the sum and difference of the two incidence vectors. This is a same-shift argument.

For a shared group of size $m$, each side of its rational product in (1), including $r$ and $s$, is at most $X^{2m+2j}$. For unequal positive integers $P,Q\le H$ one has $|\log(P/Q)|\ge1/H$ by integration of $1/v$. Both expressions in (1) have absolute value at most $17/T$. Thus each of the two group sizes satisfies $m\ge(1-\sigma)L/2-j-O(1)$. In particular both are at least $k=2\lfloor L/6\rfloor$ for large $t$.

Choose the removed, kept, and flipped source labels in at most $3^n$ ways. Freeze the removed values; we will sum their product probabilities, of total at most one. Enumerate the extra $j$ signed starts in at most $(2X)^j$ ways, e.g., list them in sorted order, including repetitions. This is an existential count, **not** a product probability for the partner. No bijection of the two tuples' labeled positions has to be specified. Now (1) confines $x$ and $y$ to intervals of half-width $17/(2T)$ centered at $-(r+s)/2$ and $-(r-s)/2$. The centers depend only on the frozen data.

## Moment price for the unfrozen groups

Use the probability kernel $K_{B,S}(u)=\frac{B}{2\pi S}\operatorname{sinc}^2(Bu/(2S))$, with $\operatorname{sinc}(v)=\sin(v)/v$. Its angular transform is $(1-S|\nu|/B)_+$. Put $B=80$ and $U_m=\int K_{B,T}|f|^m$. For any interval just obtained, its indicator is bounded by twice the triangle centered there. For a group of $b$ plus and $m-b$ minus draws the expected translated triangle is the integral of $f^b\bar f^{m-b}$ against $K_{B,T}$ times a phase of modulus one. It is nonnegative and at most $U_m$. Neither balance nor even order is needed. Dropping all separation and intersection restrictions after (1) therefore bounds the source probability for the two independent unfrozen groups by $4U_m U_{m'}$, where $m+m'=n-j$.

At the even order $k$, any nonzero balanced frequency has magnitude at least $X^{-k}>B/T$: Each rational side is at most $X^k$, even with repetitions. Only the permutation diagonal contributes to $U_k$, by least-start injectivity. Given the positive draws, there are at most $(k/2)!$ possible negative lists of the same multiset. Since $\max\rho_p\ll_{a_0}D^2/X$ and $\log k=D/2+O(\log D)$,

$$ U_k\le(k/2)!\,(\max\rho_p)^{k/2}\le t^{-1/12+o(1)}. $$

In the other direction $U_n\gg X/(TnD)$: $f(0)=1$, $|f'|\ll D/X$, and on $|u|\le c_0 X/(nD)$ for small absolute $c_0>0$, $|f|^n\gg1$ and $K_{B,T}\gg1/T$. Hölder interpolation with the **same kernel** on $[k,n]$ gives

$$ \frac{U_m U_{m'}}{U_n}\le U_k^{(n+j)/(n-k)} U_n^{-(k+j)/(n-k)}. \tag{2} $$

It is the origin lower bound, not an assumed upper bound, that prices the negative exponent.

## Comparing with the actual separated core

Let $V_n=\int K_{1/2,t}|f|^n$. Partition the axis for the sum of $h$ positive labels into half-open cells of width $1/(4t)$ and write $b_i$ for their full product masses. In $U_n$, the two independent one-sided sums must be within $B/T$ to get nonzero triangular weight. There are $O(1+t/T)$ possible cell offsets, and $\sum_i b_i b_{i+v}\le\sum_i b_i^2$ for each offset $v$. Same-cell pairs get weight at least $1/2$ in $V_n$, so $U_n\ll(1+t/T)V_n$.

Apply the [full-to-separated comparison](separated-signed-tuples.md) under the **nonnegative density** $K_{1/2,t}$, not the signed off-diagonal specialization. At $R=D^2$ the same pointwise degree bounds hold, as in the [detection-radius note](detection-radius.md). The separated integral after division by $A^n$ is at most $M$: Its arithmetic multiplier is a triangle supported at $|t\nu|<1/2$ up to zero endpoints, and no separated tuple is diagonal. It is at least $e^{-\eta}V_n-t^{-1-\gamma/8+o(1)}$, with $\eta=o(n)$; the fixed mass floor absorbs $A^{-n}$ into $t^{o(1)}$. The same origin calculation gives $V_n\gg X/(tnD)$, so the error is negligible relative even to $e^{-\eta}V_n$. Consequently $U_n\le t^{\sigma+o(1)}M$.

In (2), use $j\le cL$ and drop the favorable $j$ in the exponent of $U_k$. The choices cost $X^j\exp(O(n))\le t^{c+o(1)}$, including the masks and signs. After comparison to $M$, the saving in the exponent of $t$ is at least

$$ \frac{C/12-(1-\sigma)(c+1/3)}{C-1/3}-c-\sigma. $$

At $c=\sigma=\gamma/100$ its numerator over the common denominator is $\gamma/6-(2/3)c+c^2-2c(C-1/3)\ge\gamma/15$ since $C\le5$. Division by $C-1/3\le14/3$ proves the claim.

**Sharper same-support case.** If no starts change and both hits have $|t\nu|,|t\nu'|\le2\pi$, (1) gives $|x|,|y|\le2\pi/t$ with neither zero. The two block sizes are now at least $\log(t/(2\pi))/D$, by applying rational spacing to $x,y$ without the factor two. Use $S=t$, $B=80$, and $k=2\lfloor\log(t/(2B))/(2D)\rfloor=L+O(1)$. Then $X^{-k}\ge2B/t$, the permutation bound is $U_k\le t^{-1/4+o(1)}$, and the cell comparison costs only $t^{o(1)}$. Formula (2) with $j=0$ gives the sharper relative exponent $(C/4-1)/(C-1)=\gamma/[2(3+2\gamma)]$. In particular, counting just supports with two *inequivalent* balanced near-divisors instead of all near-divisors would miss almost all the central mass.

**Decision for the signed test.** The [independent-redraw bound](tuple-redraw-cost.md) priced one proposal but allowed a rare, deliberately chosen replacement for every source. Isolation excludes even that possibility on most central mass for $j\le cL$. A direct pairing meant to pay for a fixed fraction of the central slice must reach supports changing more than $cL$ starts, or leave this same-shift test. The conclusion concerns relative mass only. No upper bound for $M$ at the detector's scale has been proved, so this estimate does not justify deleting the marked sources at sub-detection cost. Nor does isolation supply negative mass from distant supports. For a nonlocal comparison the outstanding observable is still the weighted signed shape integral in the separated test at the named center, with balanced selections and, in rounded-slot coordinates, the actual dependent prime and its gate. No independent residue law is used here.

**After Work:** [Replacement-frequency lists](replacement-frequency-lists.md) rules out a class missed by counting changed starts: Even when half the starts change, a small list of possible replacement-sum intervals cannot serve a fixed fraction of the core. The list may read a priced subset of the source; reading the entire retained sum for free invalidates the bound. It also prices one independent central-donor splice. Use these tests for a proposed transport, not as a substitute for the signed shape estimate. The [handoff replay](replacement-list-review.md) records the scope of the checks.
