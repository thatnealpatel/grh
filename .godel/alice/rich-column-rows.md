# Which rows can account for a rich smooth column?

At one prime, use the [shared-complement graph](shared-complement-count.md) on the residual at $T=q^{1.11}$. Its light columns, of degree $s\le q^{.334}/\sqrt g$, cost $q^{1.389+o(1)}$ edges in total. We give a more restrictive sufficient collision count on the other columns. The restrictions apply **per starting row on its actual column**; they do not bound the number of rich columns.

Write a row as $(a,b,\delta)$, where $ac-bd=q\delta$ at column $(c,d)$, $0<|\delta|\le D=H/g$, and $(ac,bd)=1$. Here $Z/X<c,d\le Z$, and
$$A_-:=NB^{-4k}/(gZ)\le a,b\le A_+:=NX/(gZ)=q^{1.445+o(1)}/g,\qquad A_+/A_-=q^{o(1)}.$$
For a distinct neighbour $(x,y,\delta')$, let $t=(ay-bx)/q$, $r=(|\delta|,|\delta'|)$. Both $t$ and $r$ are nonzero integers: The rows are primitive, positive, and satisfy the same slope congruence modulo $q$. The identities $ct=y\delta-b\delta'$ and $dt=x\delta-a\delta'$ give
$$0<|t|\le U:=2A_+D/d\le q^{.78+o(1)}/g^2.$$
A column with $U<1$ has degree at most one. All subpower bounds below are uniform. Put $L=\log q$ and $B=\log L$.

## Determinant normalized by known prime factors

At the starting row choose any set $S$ of $O(k)$ primes. For example, take the eligible primes dividing $gabcd$, together with up to $k$ eligible primes dividing $\delta$. Fix the set across the neighbours being counted, but it may depend on the column and on the starting row. Write $m_x,m_y$ for the full $S$-parts of $x,y$, and $m=m_xm_y$. For every $J\ge1$,
$$\#\{(x,y):0<|t|\le Jrm\}\le q^{o(1)}\sqrt J.$$
This uses size, not the assertion $m\mid t$, which can be false for crosswise shared primes.

Indeed $r\mid |\delta|$ gives $q^{o(1)}$ choices by the divisor bound. The two masked parts likewise have $q^{o(1)}$ choices: Each exponent vector has sum at most $k$ on $O(k)$ primes, and the number of such vectors is $\exp(O(k))$. If $xy/m\le J$, enumerate that remaining product by the half-power Rankin bound $\Psi(J,X)\le q^{o(1)}\sqrt J$, then split it between the two coordinates in $q^{o(1)}$ ways. Otherwise it has a divisor $J/X<f\le J$, split as $f=f_1f_2$ with $f_1\mid x/m_x$, $f_2\mid y/m_y$. There are again at most $q^{o(1)}\sqrt J$ choices including the split (only products with at most $2k$ factors need be considered).

For each choice the neighbour is an ambient primitive point in the lattice
$$m_x f_1\mid x,\qquad m_y f_2\mid y,\qquad cx-dy\equiv0\pmod {qr}.$$
For a choice admitting a row its covolume is $qrmf$: On substituting multiples in each coordinate, $cm_xf_1$ is a unit modulo $qr$, since $q>X$ and $(cx,\delta')=1$. In the centred parallelogram $|x|\le A_+$, $|ay-bx|\le qJrm$, the ratio of area to covolume is $4(A_+/a)J/f=q^{o(1)}$. If the lattice points are collinear their line contains zero, hence at most two ambient primitive vectors. Otherwise their convex hull is a lattice polygon; Pick's theorem bounds the number by twice the area ratio plus two. Thus the divisor choices suffice. With $S$ empty and $J=\max(1,U)$ this also gives $s\le1+q^{.39+o(1)}/g$ when $U\ge1$.

## Two forms of concentration

**Prime factors.** At a starting row, even after inspecting its neighbours, choose a set $P$ of at most $L^{1.85}$ eligible primes. At most $q^{.3315+o(1)}/g^{.85}$ neighbours have $P$-part of $xy$ at least $U$, for $U\ge1$. Use $\sigma=.425+B^{-1/2}$: The Euler product over $P$ at $\sigma$ is $q^{o(1)}$, since its logarithm is $O(L^{1.85}(X/B^4)^{-\sigma})\le L\exp(-2\sqrt B+O(\log B))=o(L)$. Hence the number of $P$-smooth divisors up to $U$ is at most $U^{.425}q^{o(1)}$. Select a divisor of the $P$-part in $(U/X,U]$ and split it between $x,y$. The preceding lattice argument with bounding determinant $U$, modulus $q$, and no mask costs $q^{o(1)}$ points per split. This gives the claim since $.425\cdot.78=.3315$. The estimate is for **one chosen set** per starting row, not the union over all possible sets.

**Affine directions.** Take $0\le a_0<d$ with $ca_0\equiv q\pmod d$, and $b_0=(ca_0-q)/d$. In the unique coordinates $x=dj+a_0\delta'$, $y=cj+b_0\delta'$, we have $|j|,|\delta'|\le K=A_+/d+D\le q^{.39+o(1)}/g$. An affine line through the starting point with primitive direction of sup norm $h$ and at least one neighbour contains at most $q^{o(1)}\sqrt{2K/h}$ actual points. Indeed $h\le2K$ and the integral line parameter ranges over an interval of length $\ell=2K/h\ge1$. At least one of $x,y$ is nonconstant since the coordinate map is nonsingular. Divide this integral affine form by its coefficient gcd. Its positive smooth reduced values at most $\ell$ cost $q^{o(1)}\sqrt\ell$ by Rankin and injectivity. Each larger smooth reduced value has a divisor in $(\ell/X,\ell]$ coprime to the reduced step; this fixes one residue class of the parameter with $O(X)$ representatives. Rankin counts the divisors. Thus for any list of $M$ unoriented primitive directions chosen at the starting row, at most $q^{o(1)}\sqrt K M^{3/4}$ neighbours lie in them: The $i$-th smallest direction height is $\gg\sqrt i$. This bound does not assume the affine line passes through zero.

## A sufficient residual, not a fixed window

On a rich column ($s>q^{.334}/\sqrt g$) we have $g<q^{.113}$ for all large $q$, by the full degree bound. For each starting row choose $S,P$ as above and any list of up to $q^{.184}$ directions, such as the most populated ones. Retain only ordered distinct neighbours satisfying all three conditions:

1. $|t|/(rm)>q^{.666}/g$. In particular $rm<q^{.114+o(1)}/g$.
2. The $P$-part of $xy$ is less than $U$.
3. The displacement in $(j,\delta')$ is outside the list.

The excluded neighbours number $o(s)$ uniformly: The determinant and direction bounds each cost at most $q^{.333+o(1)}/\sqrt g$ (use $.195+3(.184)/4=.333$), and the prime-set bound is smaller. Consequently if $D_g^*$ counts just the retained collisions on rich columns, $\sum_{\rm rich}s^2\le (1+o(1))D_g^*$. Cauchy-Schwarz with at most $q^{1.055+o(1)}$ columns per gcd and $\sum_{g\ {\rm smooth}} g^{-1/2}=q^{o(1)}$ bounds all rich edges by
$$q^{.5275+o(1)}\left(\sum_g\sqrt g\,D_g^*\right)^{1/2}.$$
Thus $\sum_g\sqrt g\,D_g^*\le q^{1.725-\epsilon}$, for any fixed $\epsilon>0$, suffices together with the light edges. This does **not** claim that all excluded collisions themselves satisfy that budget.

The one-divisor estimate on unrestricted cross-products gives only $1.835$, still short by more than $.110$ in the collision exponent. A concrete next test at $g=1$ is to count columns admitting many rows after discarding prime factors shared with a specified previous row and excluding its populated directions. On a rich column, one may even take $P$ to be the union of the prime supports of a previously selected list of $\lfloor L^{1.85}/(2k)\rfloor$ rows, as long as $|P|\le L^{1.85}$: Most next rows must introduce a product of factors outside that set of size at least $A_-^2/U=q^{2.11+o(1)}$. This is an input for counting successive rows, not independence of their smoothness events. No upper bound for the retained count or for the number of such columns is known here. The proved window remains the [second-order one](stopped-conductor-window.md).

**Complementary dual route:** At the same height, the [dense detector cost](dense-detector-cost.md) is at least $q^{1.055-o(1)}$ even with optimal smooth coefficients for one witness. A long-quotient sieve of the specified positive type still pays this diagonal cost. Test a signed Gram estimate on shorter blocks if pursuing duality; this does not replace the successive-row experiment or prove its premise.
