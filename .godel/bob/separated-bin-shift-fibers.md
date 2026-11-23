# Which shift sums in (4) have more than one term?

In the [separated-bin test (4)](prime-pair-dispersion.md), summing over $d$ **at fixed starting primes $p,r$** before taking absolute values can save only $O(1)$, against a target of order $D=\log X$. This is not a cancellation estimate. It dictates what to leave inside a signed sum. There is a change of scale if we fix just $h=r-p$ and group nearby starts $p$: Cells of diameter $o(D^3)$ still cannot save order $D$, but at width $D^{7/2}$ we can restrict (4), up to $o(D)$, to cells with more than $D^{1/4}$ distinct shifts and a unique retained start for each shift.

Use $X=(3\log(t/2))^2$, the fixed range $cD\le d\le4D$, $T=bX/D$, and the $J$ bins of starting primes in (4). Fix an ordered separated bin pair. An entry $(p,r,d)$ has $p,p+d,r,r+d$ prime in the band. Write $z_{p,r,d}$ for its real summand in (4), including both weights, the cosine, and the sinc. In particular $|z_{p,r,d}|\le w_{d,p}w_{d,r}\le 64D^4/X^2$. Neither the support nor this cap requires an approximation to the phase at $t$.

## Count terms that can cancel inside a cell

At each **signed** $h=r-p$, partition starts $p$ into cells of diameter at most $Y$, $1\le Y\le X$. The unsigned weight $w_{d,p}w_{d,r}$ of all entries with at least one other entry in their $(h,\text{cell})$ is

$$\ll 1+Y/D^2. \tag{1}$$

Join every two distinct entries in the same cell at the same $h$. Orient by increasing $p$, breaking ties by $d$. If the second entry is $(p+a,r+a,e)$, then $0\le a\le Y$. Both $p$ and $r$ must start prime tuples with offsets $0,d,a,a+e$. For fixed $(a,d,e)$ the edge is determined by $(p,r)$: Its $h$ is already determined, not an extra choice. Dropping the cell and bin restrictions and summing over all $h$ costs at most the square of the one-start count. No disjointness or probabilistic independence between tuples is used. Charge both endpoints of every edge the single-entry cap, not its square.

For $k$ distinct offsets, [Ford, *Basic sieve methods and applications*, Theorem 2.5](https://ford126.web.illinois.edu/sieve2023.pdf) bounds the one-start count by $O_k(X D^{-k}\prod_\delta G(\delta)^k)$, with $G(n)=n/\varphi(n)$ and $\delta$ running over all positive pairwise differences with multiplicity. Apply it to primitive slope-one forms on the full start interval up to $X$, not an interval of length $Y$. The determinant product has just these differences. An inadmissible tuple has no survivors in the band for large $X$: An obstructing prime is at most $k$ and all the prime values exceed it.

* Four distinct offsets have differences $d,e,a,a+e,|a-d|,|a+e-d|$. After squaring the sieve bound, Hölder over six factors uses the prefix estimate $\sum_{n\le L}G(n)^{48}\ll L$ from the [pair note](prime-pair-dispersion.md). To bound each resulting sum over $(a,d,e)$, fix all but the longest **participating** variable (range scale $Y$ or $D$). All nonzero arguments on the slice are $O(\max\{\text{participating scales}\})$, with multiplicity at most two. We need no moment bound on an arbitrary short translated interval. The local factors thus sum to $O(D^2Y)$. Including the squared sieve count and the single-entry cap costs $O(Y/D^2)$.
* Three distinct offsets occur at $a=0$, $d\ne e$; at $a=d$; or at $a=d-e>0$. Their differences are respectively $(d,e,|d-e|)$, $(d,e,d+e)$, and $(d,e,d-e)$. For each case the local factors in the squared bound sum to $O(D^2)$ by the same argument with the 18th moment on $(d,e)$. Their total cost is $O(1)$. Two offsets would give the identical entry and no edge.

This proves (1). The $a=0$ case alone proves the fixed-$(p,r)$ assertion. Indeed singletons cost nothing in the triangle inequality, and in general

$$0\le \sum |z|-\sum_{h,C}\left|\sum_{(p,r,d)\text{ in }(h,C)}z_{p,r,d}\right|\le \sum_{\rm nonsingleton}|z|.$$

The comparison is additive. In this application we can also prove a lower bound on what the absolute values retain. At every large frozen $X$, taking all phases one in the [pair extraction](short-prime-pair-bias.md) gives $A_d=\sum_p w_{d,p}>1/8$ for $\gg D$ shifts in the chosen interior range. Thus $\sum_d A_d^2\gg D$. With $\theta_p=t\log(1+d/p)$, the sum over all starts $p,r$ of $w_{d,p}w_{d,r}\cos^2(\theta_p-\theta_r)$ is $(A_d^2+|\sum_p w_{d,p}e^{2i\theta_p}|^2)/2$. Now $|\cos|\ge\cos^2$, and the persistence choice of $b$ has $4be^8\le1$, so the sinc factor is at least $1/2$. Equal and adjacent bins together have unsigned cost $O(D/J+D^3/X)$ by (2) of the pair dispersion note. For every sufficiently large **fixed** $J$, the remaining real absolute mass is $\gg D$ at every center. Some separated bin pair therefore has mass $\gg D/J^2$. For $Y=o(D^3)$, it still has this order after taking cellwise absolute values by (1). The bin pair may depend on $t$; a fixed pair recurs along a subsequence. This rules out proving simultaneous $o(D)$ upper bounds for all separated pairs by these cellwise absolute sums. It gives no lower bound for the **signed** sum (4).

## A grouping where many shifts survive

Instead use regular intervals of width $Y$, still at fixed $h$. First delete every entry whose shift occurs more than once in its cell at its $h$. For an edge witnessing such a repetition $e=d$ and $a>0$. With $a\ne d$ the differences are $d,d,a,a,a+d,|a-d|$. The squared sieve factors sum to $O(DY)$ over $(d,a)$ by the same six-factor proof. For $a=d$ they are from $d,d,2d$ and cost $O(D)$ in the local-factor sum. The total weight deleted is $O(Y/D^3+1/D)$. Now discard cells with at most $m$ remaining entries. Across all $h$ there are $O(X(1+X/Y))=O(X^2/Y)$ cells meeting the band, so this second deletion costs only $O(mD^4/Y)$.

For $Y=D^3K$, $1\ll K=o(D)$ with $K\to\infty$, and $m=\lfloor\sqrt K\rfloor$, the combined error is $O(K+D/\sqrt K)=o(D)$. For example take $K=D^{1/2}$. Every retained cell now has more than $D^{1/4}$ distinct shifts in this example, each with exactly one retained entry. This is a support statement, not a sign estimate. It also gives a signed test involving **two different shifts**, as follows.

## What a failure forces on different shifts

Take $Y=D^{7/2}$ and $m=\lfloor D^{1/4}\rfloor$. Index the retained entries in each $(h,\text{cell})$ by $i$, and set $v_i=w_{d_i,p_i}w_{d_i,r_i}$, $\delta_i=\lambda_{d_i,p_i}-\lambda_{d_i,r_i}$, $s_i=\operatorname{sinc}(T\delta_i)$, and $U_C=\sum_{i\in C}v_i$. Omit groups of zero mass. The $C$ here records both $h$ and the cell; $\sum_C U_C\le\sum_d A_d^2\ll D$. If (4) holds, put $\eta=\varepsilon/(512J^2)$. Eventually the retained real sum is $>\eta D/2$. Weighted Cauchy therefore gives

$$\sum_C \frac{1}{U_C}\left|\sum_{i\in C} v_i s_i e^{it\delta_i}\right|^2 \gg \eta^2 D.$$

On expansion, discard even **all** pairs $|d_i-d_l|\le m$, including the diagonal. Their absolute cost per group is at most $(2m+1)\max_i v_i$: For each $i$ there are at most $2m+1$ such $l$ by uniqueness of the retained shifts, and the sum of $v_i/U_C$ is one. Across all groups this costs $O(mD^4/Y)=o(D)$. Thus (4) forces

$$\sum_C \frac{1}{U_C}\sum_{\substack{i,l\in C\\ |d_i-d_l|>m}} v_i v_l s_i s_l\cos\!\big(t(\delta_i-\delta_l)\big)\gg \eta^2 D. \tag{2}$$

In this sum $|\delta_i-\delta_l|\asymp_J |d_i-d_l|/X$. Indeed at fixed $p,h$ the derivative of $\log(1+d/p)-\log(1+d/(p+h))$ in $d$ is $h/((p+d)(p+h+d))$, of constant sign and size $\asymp_J 1/X$ in the separated bins. Moving $p$ within the same cell at fixed $h,d$ changes the difference by $O(DY/X^2)=o(1/X)$ since the $p$ derivative is $O(D/X^2)$ on the band. This comparison is **not** an approximation with error $o(1/t)$ inside the cosine.

The new question is whether (2), normalized by $D$, has nonpositive limsup for every fixed separated pair at the actual coupled centers (and arbitrarily large fixed $J$). That would exclude failure of the common dip by (4). The normalization $1/U_C$ is part of the question; deleting it, freezing the phase in a cell, or replacing the distinct shifts by an interval of consecutive integers would need another estimate. A positive value of (2) alone does not imply (4). Neither signed bound nor the fixed-radius common dip is proved here.
