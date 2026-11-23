# Short directions counted with both smooth cofactors

Fix a first incidence on an ordered, two-position [actual list](shared-row-labels.md) at graph $g=1$. Write $x_i=F_i h_i$ for the second realization, $W<F_i\le WX$, $A_-\le x_i\le A_+$, with $W=q^{.780+o(1)}$, $A_\pm=q^{1.445+o(1)}$, and $X=q^{o(1)}$. Both $h_i=q^{.665+o(1)}$ are products of eligible primes at most $X$, $(F_2,x_1)=1$, and $q\nmid x_1x_2$. Use the list's half-power bound: There are at most $q^{o(1)}\sqrt D$ eligible smooth integers up to $D$ in the polynomial size range $D\ge1$. Divisor counts in this range cost $q^{o(1)}$.

**Cofactor count.** Let $b,s\ge0$, $b+2s\ge .780$, and $s\le .780$. Count a cofactor pair once if it admits *any* nonzero integer vector $v$ with

$$ |v_1|\le C A_+q^{-b-s},\qquad |T|\le CWq^{-s},\qquad T=(x_1v_2-x_2v_1)/q\in\mathbb Z, $$

for fixed $C$. The number of such ordered cofactor pairs is at most

$$ q^{o(1)}\left(q^{1.055-b/2-s}+q^{(.780-s)/2}\right). \tag{1} $$

This counts neither all vectors nor just primitive witnesses. For example, it prices all partners sharing cofactors with **two ratios close to each other anywhere** on this list, not just partners close to a ratio prescribed before the count.

### Switch to one lattice for the whole list

First take $T\ne0$. Write $(U,V)=(h_1v_2,h_2v_1)$ in the lattice $\Gamma$ given by $F_1U-F_2V\equiv0\pmod q$. Both entries are nonzero: A vector on an axis with nonzero quotient has $|T|\ge\min(x_1,x_2)$, since the other original coordinate is a nonzero multiple of $q$. The map to $(V,T)=(V,(F_1U-F_2V)/q)$ sends $\Gamma$ to a lattice of covolume $F_1$, by the index $q$ of the congruence and the absolute Jacobian $F_1/q$. The centered box in these coordinates has half-widths bounded by $M=C(A_+/W)A_+q^{-b-s}$ and $N=CWq^{-s}$. Put $B=MN/F_1=q^{2.110-b-2s+o(1)}$. We need a count that works even if many vectors of the box lie on a single line.

Write $(U,V)=jw$ with $j\ge1$ and $w$ primitive **relative to $\Gamma$**. Since $T$ is a nonzero integral functional value, $j\mid T$; in particular $j\le N$. Set $k_i=(h_i,j)$ and $\ell=\operatorname{lcm}(k_1,k_2)$. Only $\ell$, not necessarily $j$, is smooth. We have $\ell\mid j$, $h_1/k_1\mid w_U$, and $h_2/k_2\mid w_V$. Count $w$ in the box scaled by $1/\ell$ rather than enumerating $j$.

For fixed $\ell,k_1,k_2$ set $D=\max(1,B/\ell^2)$. In the product $(h_1/k_1)(h_2/k_2)$ choose a smooth divisor $f$ crossing $D$, so $D\le f\le XD$; use $1$ at $D=1$. If the product is too small, use the whole product. In either case split $f=f_1 f_2$ with $f_i\mid h_i/k_i$, assigning prime factors with multiplicity. Imposing $f_1\mid w_U$ and $f_2\mid w_V$ has relative index $f$ in $\Gamma$: On substituting multiples the congruence still has index $q$ in the new integer coordinates. No coprimality between $f_1$ and $f_2$ is needed. The new area divided by covolume is $4B/(\ell^2 f)$. In the crossing case this is at most 4. In the whole-product case we use $k_1 k_2\le\ell^2$ to obtain

$$ B/(\ell^2 f)\le B/(h_1h_2)\le q^{.780-b-2s+o(1)}\le q^{o(1)}. $$

If the points of the divisibility lattice in the scaled box span rank two, their convex hull is a lattice polygon. By Pick's theorem it has $O(1+B/(\ell^2 f))$ lattice points, including its boundary. At rank one the line passes through zero, so it contains at most two vectors primitive in the base lattice. At rank zero there are none. Thus only $q^{o(1)}$ candidate $w$ are needed for each split. Its two nonzero entries have polynomial size (use $F_1U=qT+F_2V$); their divisors recover $h_1/k_1,h_2/k_2$. This directly bounds the number of *pairs*, without reconstructing the content $j$.

Each smooth $\ell\le N$ gives divisor cost for $k_i\mid\ell$ and at most $q^{o(1)}(1+\sqrt B/\ell)$ choices of $f$ and its split. Sum the first term by the half-power bound and the second by $\sum_{\ell\le N}1/\ell=O(1+\log(1+N))$. This gives (1); if $N<1$ there is no nonzero $T$. The same proof allows subpower distortions in the widths and $o(1)$ slack in the exponent inequalities.

For $T=0$ a nonzero vector is a nonzero multiple of $(x_1,x_2)/G$, $G=(x_1,x_2)$. Hence $G\ge q^{b+s-o(1)}$, and $G\mid h_2$ since $(F_2,x_1)=1$. Fix smooth $h_1$, enumerate $G\mid x_1$, and count the smooth quotient $h_2/G$. The cost is at most $q^{.665-(b+s)/2+o(1)}$ if nonempty (otherwise zero). This fits in the first term of (1) since $s\le .780$.

### Three consequences

1. **A cheaper cut even with unrestricted outputs.** At $b=0$, $.447<s\le.6$, multiply (1) by $q^{.390+o(1)}$ for the [full gap square](short-label-ratios.md) at each such cofactor pair. That square counts actual completions including the recovery of $d,c$; do not apply another smoothness density. The price for **all** these partners is $q^{1.445-s+o(1)}$. This is strictly below $.998$ in the exponent for fixed $s>.447$ in this range, versus $s=.586$ in the [previous cut](adaptive-complement-interval.md). The equality endpoint gives no fixed power margin.

2. **Close ratios without prescribing their location.** On the same list and cofactor pair, let two distinct actual columns have $|c/d-c'/d'|\le q^{-.896}$. Take $v=y-y'$ from their forced outputs. It is nonzero by row uniqueness. Each column has an integral determinant quotient of absolute value at most $W$, so $|T|\le2W$. The two row equations give

   $$ |v_1|\le A_+q^{-.896}+2qH/d_{\min},\qquad qH/d_{\min}=q^{.335+o(1)}. $$

   Thus $|v_1|\ll A_+q^{-.896}$, of exponent $.549$. A zero quotient would require $|v_1|\ge x_1/G\ge x_1/h_2=q^{.780+o(1)}$. At $b=.896,s=0$, (1) prices the qualifying cofactor pairs by $q^{.607+o(1)}$. Charging all their columns by the full square costs $q^{.997+o(1)}$ partners per fixed first incidence. This is **not** a count of ordered pairs of close partners with multiplicity. Outside the cut, *within each cofactor pair*, distinct ratio values from distinct columns are separated by more than $q^{-.896}$; nothing separates different cofactor pairs.

3. **One adaptive interval down to radius $q^{-.780}$.** Let $0\le\beta\le .780$. Prescribe one ratio interval of radius $q^{-\beta}$ for each cofactor pair. The price is $q^{1.055-\beta/2+o(1)}$. Indeed the row equation confines $y_1$ to an interval of half-width $L=q^{1.445-\beta+o(1)}$, even with the $qH/d_{\min}$ error. More generally use one translated output interval of this size per cofactor pair. Enlarge $L$ to at least $A_+/W$ so $J=LW/x_1\ge1$, without changing its exponent. The [translated strip proof](adaptive-complement-interval.md) up to the exceptional average gives $q^{o(1)}(\sqrt J+\sqrt R)$ per pair, dropping the second term if no exceptional direction supports a nonsingleton line. That proof needs $64XJ< A_-$, $2W<\min x_i$, and $R/k\ge1$ for a nonsingleton line of step $kv$; these hold throughout. Here $R=\min(2L/|v_1|,2W/|T|)$ for the exceptional primitive direction, omitting the second entry if $T=0$. The zero case has $R/J\le2h_2/W=o(1)$. Sum the ordinary term, and absorb $R\le J$, using $q^{.665+o(1)}$ cofactor pairs.

   For $R>J$ split into $Q\le R<2Q$, dyadic $Q\ge1$. The witness has $|v_1|\le2L/Q$, $0<|T|\le2W/Q$. Apply the proof of (1) with these widths: Its relative area parameter is $B_Q\ll (A_+/W)(L/Q)(W/Q)/F_1$. In the whole-product case $B_Q/(h_1h_2)\ll q^{o(1)}J/Q^2\ll q^{o(1)}$ since $Q>J/2$. This covers rounded endpoints without assuming a power margin. Multiplying the pair count by $\sqrt{2Q}$ costs at most $q^{o(1)}(q^{1.055-\beta/2}/\sqrt Q+q^{.390})$ per box, within the stated bound over $O(\log q)$ boxes. In particular the exponent is $.665$ at $\beta=.780$. The old $\beta\le.3325$ cutoff came from the exceptional average, not the translated-strip sieve.

**Remaining count.** After charging the two full-output cuts, use their complements, not a union of all possible narrow intervals. For instance, at $\beta=.780$ a dictionary of at most $q^{.333-\epsilon}$ intervals per cofactor pair costs at most $q^{.998-\epsilon+o(1)}$ for fixed $\epsilon>0$, by summing the uniform one-interval estimate. Can one cover the actual ratios on the residual by such dictionaries, or bound directly the completions not covered? The fine separation in item 2 gives no such upper bound on occupied intervals, and neither a chosen interval for each individual output nor a tiling of the full range receives the one-interval price. The unrestricted average target $q^{.333}$ per cofactor pair, the all-gcd estimate, and the fixed-window conclusion remain open.
