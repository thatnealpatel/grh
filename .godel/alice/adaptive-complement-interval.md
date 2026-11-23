# Adaptive intervals for jointly completable rows

Use the actual two-position [shared lists](shared-row-labels.md) at graph $g=1$. Fix the first incidence. Fix $0\le\beta\le .3325$. There are two ways to price concentration of the **second complement ratio** $c/d$, and a separate test with no concentration assumption. None uses a prime mask, the gap direction, or common divisibility of the two signed products.

* One interval of radius $q^{-\beta}$, prescribed before the second cofactors, costs $q^{1.055-\beta/2+o(1)}$ partners. Here one really uses that **both** $c$ and $d$ are smooth.
* The interval may instead be prescribed **separately for every second cofactor pair** $(h_1,h_2)$. The total cost over the pairs is still $q^{1.055-\beta/2+o(1)}$. In fact this second bound works for one arbitrary interval of radius $L=q^{1.445-\beta+o(1)}$ for the forced output $y_1$ at each such pair. The centre may depend on the first incidence, the shared list, and both second cofactors, but not on the second outputs or complement. This estimate uses smoothness of $y_1$ and row uniqueness; it upper bounds genuine completions but does not charge another saving for smoothness of their complements.
* With **no interval restriction**, if the cofactor slope admits a sufficiently short lattice vector as quantified below, all second realizations together cost $q^{.9955+o(1)}$ partners per first incidence.

Indeed $x_i=F_i h_i=q^{1.445+o(1)}$ and $|y_1-(c/d)x_1|\le qH/d=q^{.335+o(1)}$, so the stated ratio test fits the output test. In particular this prices an adaptive correlation, not the union of the entire range of possible ratios. All estimates are uniform in the interval centres.

## One ratio before choosing the cofactors

For a prescribed real $\alpha$, let $J=Z^2 q^{-\beta}$. All counted complements are ambient primitive points in the centred parallelogram $|d|\le Z$, $|c-\alpha d|\le Z q^{-\beta}$ of area $4J$. If $cd\le J$, enumerate this smooth product and split it at cost $q^{o(1)}\sqrt J$. Otherwise choose a smooth divisor $J/X<f\le J$ of $cd$, split as $f=f_1 f_2$ with $f_1\mid c,f_2\mid d$. At most $q^{o(1)}\sqrt J$ splits occur by Rankin and the divisor bound. The rectangular lattice has index $f$; in the centred parallelogram it has at most $O(1+J/f)$ primitive points, by Pick in rank two and primitivity in rank one. On the fixed list the column identifies its two rows. Thus no cofactor enumeration multiplies this price. This argument alone does **not** allow a different centre for each cofactor pair.

## A translated strip at fixed cofactors

Set $W=q^{.780+o(1)}$ as in the list construction, and write
$$t(z)=(x_1 z_2-x_2 z_1)/q,\qquad \Lambda=\{z\in\mathbb Z^2:t(z)\in\mathbb Z\}.$$
Use coordinates $(z_1,t(z))$. Here $\Lambda$ has covolume $x_1$: Its projection on the first coordinate is surjective since $q\nmid x_1$, and at fixed first coordinate the step in $t$ is $x_1$. In particular $u\mid z_1$ cuts out an index-$u$ sublattice for any $u\ge1$. This is the original row slope congruence, not a second modulus-$q$ condition.

The strip in these coordinates is a translated rectangle of half-widths $L,W$; put $V=LW/x_1=q^{.780-\beta+o(1)}$. Select a smooth $e\mid y_1$ with $64V<e\le64XV$, possible since $y_1\ge A_->64XV$. At most $q^{o(1)}\sqrt V$ values of $e$ occur. For each, all points of the $e$-sublattice in the rectangle are collinear: A determinant of two differences has absolute value at most $8LW<ex_1$. Cases with at most one point already cost $q^{o(1)}\sqrt V$ in total.

For a line with at least two points let $v$ be its step primitive **in $\Lambda$**, chosen up to sign. Neither coordinate $v_1,v_2$ in the original $z$ plane can vanish: A vertical nonzero difference has $|t|\ge x_1$, and a horizontal one has $|t|\ge x_2$, both larger than $2W$. The line step in the $e$-sublattice is $kv$ for $k=e/(e,|v_1|)$; thus $e/k\mid v_1$. If the line has at least $m+1$ lattice points in the rectangle, then
$$|v_1|\le 2L/(mk),\qquad |t(v)|\le 2W/(mk).$$

There is at most one primitive direction in $\Lambda$ with $|v_1|\le L/(2\sqrt V)$ and $|t(v)|\le W/(2\sqrt V)$: Two such vectors have determinant at most $x_1/2$ in strip coordinates. Call this the exceptional direction, if present. All other directions in the preceding tail have $mk\le4\sqrt V$. For each $k$, choose a smooth divisor $u\mid e/k$ strictly exceeding $8V/(mk)^2$ and at most $X\max(1,8V/(mk)^2)$ (use $u=1$ if the threshold is below one). This crossing exists since $e>64V$. There are $O(q^{o(1)}\sqrt V/(mk))$ possible $u$, including when the threshold is below one. Now $u\mid v_1$; in the centred difference rectangle for $v$ the determinant bound is $8LW/(mk)^2<ux_1$. Thus at most two base-lattice primitive vectors are possible per $k,u$. Each nonzero $v_1$ supplies at most $q^{o(1)}$ possibilities for its divisor $e/k$. Summing over $k$ gives $q^{o(1)}\sqrt V/m$ nonexceptional $e$ with at least $m+1$ points. Summing the tail over $m$ costs another logarithm. This part of the bound does not use smoothness along an affine line.

For the exceptional direction set
$$R=\min(2L/|v_1|,\ 2W/|t(v)|),$$
omitting the second term if $t(v)=0$. Only directions supporting at least one nonsingleton $e$ enter this definition of the cost. For each such $e$, $k\le R$, and along its unique line $y_1$ is a nonconstant integral affine function of an integer parameter ranging over an interval of length at most $R/k$. There are at most $q^{o(1)}\sqrt{R/k}$ parameter values with positive smooth $y_1$. Indeed divide the affine function by its coefficient gcd; its smooth reduced values at most $R/k$ can be enumerated injectively. Larger ones have a smooth divisor in $((R/k)/X,R/k]$, coprime to the reduced step, fixing one residue of the parameter with $O(X)$ representatives. This is the [affine line sieve](rich-column-rows.md), with the step taken in the **$e$-sublattice**. For $K\le k<2K$ there are $q^{o(1)}\sqrt K$ smooth $k$, and $e/k$ divides the single fixed $v_1$. Hence this entire exceptional-direction contribution is $q^{o(1)}\sqrt R$ across all $e$. This handles large content, where simply summing a rounded-up centred divisor bound over $k$ would not suffice.

A recovered $y_1$ on a counted point gives $(x_1,y_1)$ and at most one actual column by row uniqueness. The count before summing the cofactors is therefore $q^{o(1)}(\sqrt V+\sqrt R)$, omitting the $R$ term if absent. It need not be $O(q^{o(1)}\sqrt V)$ for this argument to work.

## Averaging the exceptional run

Fix the list throughout. If $t(v)=0$, the primitive direction is $(x_1,x_2)/(x_1,x_2)$: This integer vector already belongs to $\Lambda$. As $(F_2,x_1)=1$, $(x_1,x_2)\mid h_2$. Hence $R\le 2L h_2/x_1=q^{.665-\beta+o(1)}<V$; this uses the row-coordinate gcd, not the graph gcd.

For any direction with $R\le V$ the exceptional cost is already at most $q^{o(1)}\sqrt V$. Otherwise box $R\asymp q^\rho$, $.780-\beta-o(1)\le\rho\le .780+o(1)$, and $T=t(v)\ne0$. Enumerate the nonzero integer $T$ in $q^{.780-\rho+o(1)}$ ways. Since $q|T|/x_1\ll L/q^\rho$ and $x_2/x_1=q^{o(1)}$, the original second coordinate satisfies $0<|v_2|\le q^{1.445-\beta-\rho+o(1)}$. Enumerate the smooth $h_1$ at cost $q^{.3325+o(1)}$. The equation
$$x_1 v_2=qT+F_2h_2v_1,\qquad (x_1,F_2)=1,$$
puts $v_2$ in one residue class modulo $F_2>W$. In general the interval count is $q^{\max(0,.665-\beta-\rho)+o(1)}$, including rounding. In this tail it is only $O(1)$ because $.665-\beta-\rho\le -.115+o(1)$. Then $h_2$ divides the known **nonzero** $x_1v_2-qT$, at divisor cost. This enumerates cofactors admitting a direction, not a distributional claim about smooth inverses. After the $\sqrt R$ price the total exponent in a box is at most
$$.3325+.780-\rho/2\le .7225+\beta/2+o(1)\le 1.055-\beta/2+o(1).$$
The last inequality is exactly the stated range $\beta\le .3325$. The ordinary term costs $.665+(.780-\beta)/2=1.055-\beta/2$. Summing dyadic boxes proves the adaptive bound. For example, at $\beta=.117$ the total is $.9965$, without any saving assumed for the smooth cofactors beyond their usual half-power count.

## Short cofactor slopes with unrestricted outputs

In the same lattice for the second cofactors, take the full output scale $L=A_+$ and $S_0=q^{.586}$. Count a cofactor pair if **any** nonzero $v\in\Lambda$ has $|v_1|\le2A_+/S_0$, $|t(v)|\le2W/S_0$. This is a property of the cofactors alone, independent of the actual second outputs, their prime factors, and the signed-gap direction. Here too axis vectors are excluded by the $t(v)$ bound. For $t(v)\ne0$ use the preceding enumeration with $\beta=0$ and $S_0$ instead of $R$: At most $q^{.194+o(1)}$ values of $T$, $q^{.3325+o(1)}$ smooth $h_1$, $q^{.079+o(1)}$ values of $v_2$ in its residue class, and a divisor loss for $h_2$. For $t(v)=0$ the primitive direction forces $G=(x_1,x_2)\ge q^{.586-o(1)}$. After fixing $h_1$, enumerate $G\mid x_1$ by divisors, and use $G\mid h_2$ to enumerate the smooth $h_2/G\le q^{.079+o(1)}$. Thus the union costs at most $q^{.6055+o(1)}$ cofactor pairs per list.

For **each** such pair the [full gap square](short-label-ratios.md) costs at most $q^{.390+o(1)}$ actual completions. Its proof selects a divisor of the smooth $d$ and recovers $c$ in its true size interval, so this step does not multiply two independent smoothness densities. The claimed $.9955$ follows. This is an unconditional cut even for dispersed outputs and small common divisibility; no assertion is made that this cofactor event is frequent.

## Pair price and limit

In a retained popularity bin there are at most $q^{.780+o(1)}M$ first incidences. Dividing the adaptive subcount by $DM$ with $D=q^{\sigma+o(1)}$ gives $q^{1.835-\sigma-\beta/2+o(1)}$ in the [weighted reduction](overlapping-lift-count.md). At top degree $\sigma=.390$, $\beta=.117$ gives $1.3865$; $\beta=.229$ gives at most $1.3865$ uniformly for $\sigma\ge.334$. The unrestricted-output short-slope cut costs $1.3855$ at top degree. These are prices for the indicated pairs and list incidences only. They remain valid on the small-common-divisor residual.

The remaining test is occupancy **outside** prescribed intervals at nonshort cofactor slopes. Paying the adaptive bound once per centre to cover a ratio range of order one costs exponent $(1.055-\beta/2)+\beta$, worse than taking $\beta=0$. In particular, at $\beta=.117$ the result gives no more than $.0015$ of dictionary exponent below the top $.998$ benchmark. A useful next target is to bound occupied ratio intervals for the actual primitive smooth complements, jointly with their admissible cofactors, or to count the complement/cofactor incidences across intervals directly. Row uniqueness only bounds completions *after* an output is known; it does not show that most intervals are empty.

**After Work:** The [two-cofactor count](two-cofactor-strips.md) extends the adaptive range to $\beta=.780$, lowers the full-output shortness threshold to any fixed $s>.447$ near that endpoint, and prices an unprescribed close pair of ratios *within the same cofactors*. Use its separated residual and dictionary budget for the across-interval question above.
