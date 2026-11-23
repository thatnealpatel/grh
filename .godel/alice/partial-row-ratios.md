# Select a divisor of a forced output before counting the row

Fix one constructed two-position list at $g=1$, one occupied denominator $d$, and one actual reference $c_0$ there. Keep both modular discrepancy tests, and intersect with the complement of the [crossed-gap cut](crossed-gap-filters.md). The following additional cut does not require a short gap, a repeated prime, or a short bracket. It bounds endpoints in certain cells of **partial row ratios**, not the number of occupied cells.

For either position put $F=F_i$, $h=h_i(c)$, $n=ch$, and $y=y_i(c)$. Use $n_0=c_0h_i(c_0)$ and $y_0=y_i(c_0)$. All four integers are eligible-smooth. We have $(n,y)=(n_0,y_0)=1$ and $(nn_0,d)=1$ by row primitivity. In the hard CRT box use the [exact split](crossed-gap-filters.md) first: Reject unless $(T,u_1)(T,u_2)=T$, recover $h_2,k$, and recover the signed gaps. For each candidate integer $c$ the $y_i=(F_i h_i c-q\delta_i)/d$ are then forced. Count only actual endpoints; the projection below majorizes these without summing over the CRT filters $f$ or the scalar $T$.

**Cut.** Charge $c$ if, at either slot, there are $a\mid n$, $b\mid y$, $a_0\mid n_0$, $b_0\mid y_0$, and $e\mid d$ such that

$$q^{.120}\le ab\le q^{1.055},\qquad e\mid a b_0-a_0 b,\qquad
\frac{|a b_0-a_0 b|}{a b_0+a_0 b}\le e q^{-.120}.$$

The number of distinct charged $c$ is at most $q^{.4675+o(1)}$, uniformly in $d$ and the chosen reference. One can insist on $b>1$, or on a polynomial lower bound for $b$, at no added cost. For $e=1$ this tests alignment of smooth subproducts with a reference ratio in the reals. For $e\ge q^{.120}$ no real agreement is required. The intermediate test trades real agreement for congruence at *divisors of the actual denominator*. In particular the estimate permits a different divisor of the forced output for every endpoint; it is not the price for one prescribed output divisor.

**Planar count used twice.** In a bounded centrally symmetric convex region of area $O(mE)$, consider ambient primitive pairs of positive smooth coordinates, both units modulo $m$, in $A x\equiv B z\pmod m$ with unit coefficients (including $m=1$). If their coordinate product is at least $E$ whenever $E>1$, the count is $q^{o(1)}(1+\sqrt E)$ at polynomial heights. Choose a smooth divisor of the product first crossing $E$ within a factor $X$ (one for $E\le1$), and allocate it as $l_1l_2$ between the coordinates. For the index $m l_1l_2$ one needs the filtered coordinates to be units modulo $m$; this holds in the uses below. Indeed after substituting multiples of $l_1,l_2$ the congruence is surjective modulo $m$. The split divisors cost $q^{o(1)}(1+\sqrt E)$ in total by the half-power count and divisor bound. For each split, either the lattice points in the **whole centered region** span the plane, in which case Pick's theorem on their hull gives $O(1)$ points, or they lie on a line through zero, which has at most two ambient primitive vectors. Fixed area constants are harmless. In the uses below if an upper area bound exceeds the minimum available coordinate product by a constant factor, take $E$ smaller by that factor and keep the constant in the area bound.

**Price the small pair first.** There are $q^{o(1)}$ reference divisors, moduli $e$, and dyadic boxes $A\le a<2A$, $B\le b<2B$. Write $P=AB$ and $\eta=\min(1,e q^{-.120})$. A centered body for $(a,b)$ has area $O(P\eta)$: For $\eta<1/2$, intersect the centered box with $|a b_0-a_0 b|\le 2\eta(A b_0+a_0 B)$. In a nonempty box $A b_0\asymp a_0 B$ by the ratio test; integrating in $a$ gives the assertion. Otherwise the box alone suffices.

Do not assume $b_0$ is a unit modulo $d$. Put $t=(e,b_0)$; since $(a_0,e)=1$ we have $t\mid b$. In coordinates $(a,b/t)$ the area falls by $t$. The congruence becomes

$$a(b_0/t)\equiv a_0 (b/t)\pmod {e/t}.$$

Both coefficients and both coordinates are now units modulo $e/t$, since $(a,d)=1$. The pair stays primitive and smooth. Relative area is $O(P\eta/e)\ll Pq^{-.120}$ and the product available for filtering is at least $P/t\ge P\eta/e$. Applying the planar count **at $E=P\eta/e$** costs $q^{o(1)}(1+\sqrt{Pq^{-.120}})$ choices for the small pair. Using $Pq^{-.120}$ as the crossing threshold without checking the available product would not be justified for large $e$.

**Price completions using the forced output.** For each selected pair put $u=n/a$, $v=y/b$. These are coprime smooth integers, not two independent possibilities for a sign or a gap. They must satisfy

$$Fa u-d b v\equiv0\pmod q,\qquad |Fa u-d b v|\le qH,\qquad |u|\le N/a,$$

where $N=q^{1.720+o(1)}$ bounds $ch$ and $H=q^{.390+o(1)}$. The centered strip has area at most $4NqH/(dab)$. Its area divided by $q$ is at most $q^{1.055+o(1)}/P$, pointwise even at a varying $d=q^{1.055+o(1)}$. Coefficients and coordinates are units modulo $q$. The available $uv=q^{3.165+o(1)}/(ab)$ is more than sufficient. The planar count now costs $q^{o(1)}(1+\sqrt{q^{1.055}/P})$. This step selects factors of the *remaining* product $uv$, so it uses smoothness of $y/b$ during candidate selection, not after enumeration. A surviving point determines $n$ and $y$; enumerating $c\mid n$ recovers all actual $c$ at divisor cost. No second slot, free output, or cofactor family has been enumerated at full cost.

Multiply the two prices. Since $q^{.120}/4\le P\le q^{1.055}$, their product is at most

$$q^{o(1)}\sqrt{q^{1.055-.120}}=q^{.4675+o(1)}.$$

For one reference per denominator the additional aggregate allowance is $.995$ in the exponent. For all ordered references add the $.4675$ local allowance to the previous outgoing deletions **before squaring** the positive part; this is not a $.995$ estimate for deleted ordered pairs. Neither bound requires a common exceptional set across the references.

**Consequence for diffuse fibers.** On any set of actual endpoints left at $d$, make a graph using the displayed cut, requiring the partial product on the reference side also to lie in $[q^{.120},q^{1.055}]$. Adjacency is now symmetric, of maximum degree $q^{.4675+o(1)}$. Greedy deletion from a fiber of size $n$ gives at least $n/q^{.4675+o(1)}$ endpoints such that for every distinct pair, either slot (the same slot on the two endpoints), and *every* choice of allowed partials on both sides,

$$\frac{|D|}{a b_0+a_0 b}>q^{-.120}\gcd(d,D),\qquad D=a b_0-a_0 b.$$

Indeed take the largest admissible modulus $e=(d,D)$; this includes $D=0$. The old reference may be kept fixed for all prior cuts: The graph is on the already retained subset. Thus to prove the local target it would suffice to rule out a simultaneous family of this kind of size $q^{.003-\epsilon}$, rather than prove that one prescribed reference hits everyone. This is an implication, not a packing estimate in the reverse direction. At the $.300$ crossings the possible real ratios in one slot range over a factor $X^2$, so elementary real interval packing by itself only gives $q^{.120+o(1)}$, not $.003$. The nontrivial issue is separation for *all* choices of both output and input divisors across the two slots.

**Coverage test, not a full count.** One concrete split available everywhere chooses $a\mid h$ and $b\mid y$ by first crossing $q^{.300}$ in each, so $P=q^{.600+o(1)}$. At $e=1$ the two prices in one relative-width $q^{-.120}$ cell are $.240$ and $.2275$. The real center can in fact be prescribed per $d$ and dyadic box instead of being a reference divisor ratio: Only the first strip uses the center. Tiling all comparable ratios spends $.120$, giving $.5875$, worse than the unrestricted local $.5275$. Nor does a large denominator modulus put the selected ratios in a few residue classes. A useful next test is the number of **jointly occupied** cells for the two slots at these widths, selecting both output divisors by the specified rule and imposing the same actual $c$. For example, covering all surviving endpoints at a given $d$ by fewer than $q^{.003-\epsilon}$ single-slot cells (either slot, cells chosen with full knowledge of $d$) would suffice there by this uniform estimate. No such concentration, or alternative saving for diffuse cells, has been shown. Small raw-gap repeat and large lcm do not imply the displayed divisor alignment. There is no unrestricted list bound, all-gcd estimate, or fixed-window conclusion here.
