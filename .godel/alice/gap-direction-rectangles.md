# A count for two columns with nearly parallel signed gaps

Use the $g=1$ [shared-label rectangle](shared-row-labels.md). The row positions stay ordered. For each of the two columns write its two signed gaps as $\boldsymbol\delta_\ell=r_\ell v_\ell$, where $r_\ell>0$ is their gcd and $v_\ell$ is primitive. Order the columns by decreasing $\|v_\ell\|_\infty$, breaking a tie by decreasing $r_\ell$ (either order for exact ties). Put

$$S=|\det(v_1,v_2)|\,r_2/r_1=|\det(\boldsymbol\delta_1,\boldsymbol\delta_2)|/r_1^2.$$

For $K\ge1$ the part of the ordered count with $S\le K$ satisfies

$$R_2(S\le K)\ll q^{2.500+o(1)}(1+\sqrt K).$$

At $K=q^{.330}$ this gives $2.665$ instead of $2.890$ in the rectangle exponent. It includes all rectangles with raw gap determinant at most $K$ in absolute value. It does not require reciprocal freshness, but both rows must lie on their actual column and both columns must realize the same two labels. In the Cauchy bound $q^{.056+o(1)}\sqrt{R_2}$, splitting off these pairs costs at most $q^{1.3885+o(1)}$ by subadditivity of the square root. This does not pay for all edges on columns having such a partner.

## Recovering a column after specifying its direction

On one column drop $\ell$. Write $x_i=F_i h_i$, $cx_i-dy_i=qr v^{(i)}$, with $(cx_i,dy_i)=1$. The positive primitive rows are distinct, so $t=(x_1y_2-x_2y_1)/q$ is nonzero; it is integral by the common column congruence. We have $dt=r(x_2v^{(1)}-x_1v^{(2)})$, and $(cd,r)=1$ since a prime dividing one of $c,d$ and a gap would divide both products on that row. In particular $r\mid t$ and $d$ divides the nonzero integer $x_2v^{(1)}-x_1v^{(2)}$.

Fix the labels, the two $h_i$, and $v$. We claim at most $q^{o(1)}\sqrt R$ incidences with $1\le r\le R$, for $1\le R\le 2H$. Indeed $d$ has $q^{o(1)}$ choices by the divisor bound. Choose $b$ with $b x_1\equiv qv^{(1)}\pmod d$, possible since $(x_1,d)=1$. Then $c=br+dj$ with $(r,j)=1$ since $(r,c)=1$. The smooth $c>Z/X>2H$ has a divisor $R\le f\le RX$ by multiplying its primes up to the first crossing. Rankin gives $q^{o(1)}\sqrt R$ choices for $f$. For admissible choices $(f,d)=1$, so $br+dj\equiv0\pmod f$ defines an index-$f$ lattice in $(r,j)$. The centred parallelogram $|r|\le R$, $|br+dj|\le Z$ has area divided by covolume $4RZ/(df)\le4X$. If its lattice points are collinear their line contains zero, hence contains at most two ambient primitive points. Otherwise Pick's theorem applied in lattice coordinates to their convex hull bounds their number by twice the area ratio plus two. In either case this costs $q^{o(1)}$. The original lifts force both $y_i$. There is no smoothness heuristic in this upper bound.

Each $h_i\le A_+/W=q^{.665+o(1)}$ is smooth, hence at fixed labels enumerating the two $h_i$ together costs $q^{.665+o(1)}$. Separately, the number of first incidences with $r_1\ge R_1$, including their labels, is at most $q^{1.835+o(1)}/\sqrt{R_1}$ for $1\le R_1\le H$. Indeed the at most $q^{1.055+o(1)}$ columns each have $O(q^{.390+o(1)})$ starting rows. Apply the [normalized neighbour lemma](rich-column-rows.md) at that row with empty prime mask and parameter $W/R_1\ge1$: Every second row in question has $0<|t|\le W\le (W/R_1)r_1$. Choosing divisors for labels costs only a subpower per row pair (the anchor is fixed, not counted).

## Sieve the second direction before fixing it

Box $r_\ell\in[R_\ell,2R_\ell)$ dyadically. At a nonzero determinant put $D_0=\min(2H^2,2KR_1/R_2)$. Then $1\le |\det(v_1,v_2)|\le D_0$. Pure geometry gives only $O(D_0)$ candidate directions (each determinant fiber is a translate of $\mathbb Z v_1$). The common column gives a square-root improvement **before** its exact reconstruction above.

Fix the first incidence and the second pair of $h_i$, so $x_i=F_i h_i$ on the second column are known. The possible $v_2$ lie in the centred convex body $\|v_2\|_\infty\le \|v_1\|_\infty$, $|\det(v_1,v_2)|\le D_0$, of area at most $4D_0$: Integrate along the coordinate whose coefficient in the determinant is of maximum modulus. Since $d_2>Z/X>2H^2$, it has a smooth divisor $D_0\le e\le XD_0$. There are $q^{o(1)}\sqrt{D_0}$ choices for $e$. The linear form $x_2v_2^{(1)}-x_1v_2^{(2)}$ vanishes modulo $e$, by the identity for $d$ above. Since $(x_1,d_2)=1$, the direction lattice has index $e$. Its primitive points in the body cost $O(1)$ by the same centred-body argument: The ratio of area to covolume is at most four. Thus the $O(D_0)$ directions are replaced by $q^{o(1)}\sqrt{D_0}$, without guessing $d_2$ at full cost. Now recover $d_2$ among divisors of the nonzero linear form, as above, then sieve $c_2$ in $(r_2,j)$, not in direction space.

The counts for the first incidence, the second $h$ pair, the direction, and the remaining reconstruction multiply to

$$\frac{q^{1.835+o(1)}}{\sqrt{R_1}}\ q^{.665+o(1)}\ \sqrt{2KR_1/R_2}\ q^{o(1)}\sqrt{2R_2}.$$

At determinant zero, $v_2=\pm v_1$ and $r_2\le r_1$, so the same calculation with two directions costs $q^{2.500+o(1)}$. Sum the dyadic boxes and allow a factor two to restore the original column order. This proves the bound.

More generally, after fixing the first incidence, the boxes, and the second pair of $h_i$, one can impose **any** centred convex restriction on $v_2$ of area $O(B_0)$ for $1\le B_0\le 2H^2$. The sieve by $e\mid d_2$ costs $q^{o(1)}\sqrt{B_0}$ directions. It need not be a strip parallel to $v_1$. An affine strip cannot be substituted without checking the collinear case.

## Why angular pigeonholing alone does not cover the complement

Consider just the box $r_1=r_2=1$, $\|v_1\|_\infty,\|v_2\|_\infty\asymp H$. One might partition the full circle into $B\asymp H^2/K$ equal sectors, $1\le K\le H^2$, so that two incidences in the same sector have $S\ll K$. On a fixed label list let $m_b$ be its occupancy in sector $b$ in this box, with $m=\sum_b m_b$. The bound $m^2\le B\sum_b m_b^2$ converts same-sector control to control of all pairs, but it costs the full sector count unless one exploits the actual occupancies. After summing over lists the repeated-column terms in $\sum_b m_b^2$ cost at most $q^{1.835+o(1)}$; the distinct terms are covered by the strip proof, which did not use reciprocal freshness. For $K=q^\kappa$, $0\le\kappa\le .780$ up to subpower endpoint factors, the resulting all-angle exponent is

$$ (.780-\kappa)+(2.500+\kappa/2)=3.280-\kappa/2\ \ge\ 2.890.$$

Thus using narrower equal sectors with only this Cauchy bound moves in the wrong direction, even if only a bound for fresh pairs is ultimately wanted. This is a limitation of the estimate, not evidence that many actual smooth columns occupy each sector.

## What the other determinant does not supply

Set $a_\ell=h_{1\ell}y_{2\ell}$, $b_\ell=h_{2\ell}y_{1\ell}$, and $D=b_1a_2-a_1b_2$. The within-column relations $F_1a_\ell-F_2b_\ell=qt_\ell$ already give $F_2D=q(a_1t_2-a_2t_1)$. Thus $q\mid D$ is not another independent cycle congruence. Reciprocal freshness excludes $D=0$: It would give $a_1t_2=a_2t_1$, hence the full part of $a_1$ outside column 2's support would divide $t_1$, impossible since it is at least $q^{1.880}$ and $0<|t_1|\le W$. This argument does not exclude parallel **gap** vectors.

There is no geometric savings over counting the $K$ determinant values alone: For $M\asymp H$ and $1\le j\le K\ll M$, $(M,M-1)$ and $(M-j,M-j-1)$ are primitive and have determinant $-j$. These are directions in the box, not exhibited smooth rectangles. For $S>q^{.330}$ the unrestricted estimate still gives $2.890$. Using the $q^{1.835+o(1)}$ first-incidence budget, a sufficient next test is an average second-column count below $q^{.833}$ by a fixed power for that complement. It needs arithmetic information on the reconstructed columns or rows, not another charge for $q\mid D$. No all-gcd bound or fixed $A=2.1$ window follows.
