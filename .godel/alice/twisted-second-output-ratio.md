# The twisted second-output ratio at a denominator pair

This is a companion to the [common-input triple count](same-input-second-bracket.md). The second rows give a recoverable label without guessing the common prefix, but the rational dictated by the two denominators cannot serve as a support-free small-bracket reference at the required price.

Fix one actual constructed two-label list $(F_1,F_2)$ in $g=R=j=1$ and fix distinct ordered output prefixes $d,e$. An object is a common complete input $v$ of the two columns, with its deterministic sorted input prefix $c$. On these columns write

$$
 v=cF_1a=dY+q\alpha=eY_0+q\alpha_0,
 \qquad cF_2h=dZ+q\beta,
 \qquad cF_2k=eZ_0+q\beta_0.
$$

The last two rows are primitive: $(cF_2h,dZ)=(cF_2k,eZ_0)=1$. The gaps are signed, nonzero, of absolute value at most $H=q^{.390+o(1)}$; the prefixes are $q^{1.055+o(1)}$, the row outputs $q^{1.445+o(1)}$, and $h,k\le U=q^{.665+o(1)}$ with both $h,k=q^{.665+o(1)}$. Smooth coordinates have only eligible primes $\le X=q^{o(1)}<q$. In particular they are units modulo $q$. Labels satisfy $F_i>W=q^{.780+o(1)}$ and each label specifies at most one row on an actual column. Restrict to the second-row escape from that count, namely

$$
 |k\beta-h\beta_0|> T A B M,\qquad
 T=q^{.272},\quad A=(h,k),\quad B=(|\beta|,|\beta_0|),\quad M=(dZ,eZ_0).
$$

This is an actual pair with a shared $c$; arbitrary solutions of the congruences below are not assumed to belong to the list.

## Exact recovery

Put $K=(Z,Z_0)$, $D=(d,e)$, and write $h=Ar$, $k=As$, $Z=K u$, $Z_0=K w$. Then

$$
 S=\frac{kZ}{hZ_0}=\frac{x}{y},\qquad x=su,\quad y=rw.
$$

This fraction is reduced: $(r,s)=(u,w)=1$, and $(r,u)=(s,w)=1$ by the two row primitiveness conditions. The second rows give

$$
 E=\frac{dx-ey}{q}\in D\mathbb Z,\qquad
 K E=r\beta_0-s\beta,\qquad |k\beta-h\beta_0|=AK|E|.
$$

Here $q\nmid KD$ gives the integrality and divisibility. In fact $E\ne0$ even before escape: If $E=0$, then $dZ/h=eZ_0/k$. Both fractions are reduced by the respective row primitiveness conditions, so $dZ=eZ_0$. Its deterministic sorted prefix must then be both $d$ and $e$, a contradiction. On escape, since $DK\mid M$,

$$
 |E|>TBD,\qquad AK\le\frac{2UH}{|E|}.
$$

Given $S$ at the fixed $d,e$, enumerate $s\mid x$, $r\mid y$ and recover $u,w$ by division. This has subpower cost since $x,y$ have polynomial height. For one split, use the equation at the column whose reduced cofactor is larger, interchanging columns for the uniqueness proof if necessary. Write the following proof with $r\ge s$. The positive $K$ and signed $\beta$ satisfy

$$
 K\le 2rH/|E|,\qquad |\beta|\le H,\qquad duK+q\beta\equiv0\pmod{F_2r}.
$$

This congruence defines a lattice of index $F_2r$ since $q$ is a unit modulo $F_2r$. Two solutions in the box have determinant of absolute value at most $4rH^2/|E|<F_2r$ for all sufficiently large $q$: use $|E|>q^{.272}$ and the stated $F_2,H$ sizes. The determinant is divisible by the index, so it is zero. Actual pairs $(K,\beta)$ are primitive: A common factor divides $dZ$ and $cF_2h$. Since $K>0$, there is at most one actual pair per split. The recovered integer

$$cA=(duK+q\beta)/(F_2r)$$

gives at most subpower choices of $c$ by divisors. The label $F_1$ on $(c,d)$ gives at most one $v$. Thus **each exact $S$ has at most $q^{o(1)}$ common inputs** at the prescribed denominator pair. This did not use a guess of $c,A,K$ before $S$. Subpower recovery holds even without escape: In a dyadic bin $L\le K<2L$, distinct slopes $\beta/K$ are separated by at least $F_2r/(4L^2)$ inside an interval of length $2H/L$. Thus there are $O(1+HL/(F_2r))=q^{o(1)}$ primitive pairs per bin, since $L\le 2rH/|E|$, $|E|\ge1$ and $H^2/F_2\le q^{o(1)}$.

For the same split, the other congruence is not a second lattice index. In fact $q(s\beta+KE)\equiv s(duK+q\beta)\equiv0\pmod r$, so $\beta_0=(s\beta+KE)/r$ is integral, and

$$ ewK+q\beta_0=\frac{s}{r}(duK+q\beta).$$

Consequently the other divisibility by $F_2s$ follows automatically. Its gap width and sign conditions, row primitiveness, sizes, and actual list membership remain tests. The small area of the lattice box relative to its index gives uniqueness, not a proportion of occupied boxes as $S$ varies.

## Canonical-reference obstruction and the one-reference price

Put $d'=d/D$, $e'=e/D$. The natural rational $e'/d'$ has the same residue modulo $q$ as $S$, and the two actual second rows give

$$
 \frac{S}{e/d}=\frac{1+q\beta_0/(eZ_0)}{1+q\beta/(dZ)}
 =1+O(q^{-1.110+o(1)}).
$$

Nevertheless its support-free divided bracket has the following **lower** bound on every surviving triple:

$$
 \frac{|xd'-ye'|x}{qe'}=|E|\frac{x}{e}
 \ \ge\ q^{1.055-o(1)}\frac{|E|^2}{2UH}
 \ \ge\ q^{.544-o(1)}(BD)^2.
$$

Use $x/e=kZ/(AKe)$ and $1.055+2(.272)-.665-.390=.544$. Thus the canonical reference cannot pass a support-free $q^{.160}$ cut even though its real relative error is small. If the cut divides this bracket by the full $\operatorname{supp}(de)$-part of $xy$, a pass instead **requires** that part to be at least $q^{.384-o(1)}(BD)^2$. This necessary condition does not rule out the masked cut on large support parts.

For comparison, fix **one** actual $S_*=x_*/y_*$ per occupied pair, and take its support $P=\operatorname{supp}(x_*y_*)$. With $J=q^{.160}$ the passing condition

$$
 |xy_*-yx_*|x/(qx_*)\le J(xy)_P
$$

costs at most $q^{.080+o(1)}$ common inputs. To see the price, fix the full parts $m_x,m_y$ on $P$ and bin $x$ dyadically. These choices cost subpower: $O(\log q/\log\log q)$ eligible factors with multiplicity on that many primes give subpower-many exponent vectors. Write $m=m_xm_y$. For two candidates in the same bin with these choices, the displayed inequality gives $|x_1y_2-x_2y_1|/q\le4Jm$, by expressing the left side using their two brackets with the reference. If the outside-support product is at most $4J$, enumerate that entire product and its split. Otherwise enumerate a divisor $f$ of it strictly crossing $4J$ with $f\le4JX$ and its split between $x,y$. For a common choice both $mf$ and $q$ divide the determinant, and are coprime. Since $mf>4Jm$, the fractions coincide. The smooth half-power bound prices both enumerations by $q^{o(1)}\sqrt J$; apply the exact-$S$ recovery. The argument also prices the canonical masked passing class if used instead: It only needs an eligible-smooth reference in the common residue class, not an actual input.

There are at most $q^{1.055+o(1)}$ ordered denominator pairs. A single test chosen per pair therefore costs $q^{1.135+o(1)}$ triples total. The target is $q^{1.136-\epsilon}$ for the residual: If $I$ is the remaining incidence count and $C$ the ordered distinct-denominator triple count after priced deletions, then $I\le q^{.9965+o(1)}+q^{.430+o(1)}\sqrt C$ as in the common-input count. The one-reference estimate pays only for its passing class; it cannot be summed over an unpriced number of references. The canonical lower bound is an obstruction to that support-free method on actual escaping pairs, not evidence that the residual contains many pairs, or even that a prescribed pair is occupied. To continue with this ratio, one needs an occupancy or covering bound for the large-bracket class, using conditions beyond the two dependent divisibilities once the ratio is fixed. No such bound is shown here; the unrestricted $.998$ target remains open.
