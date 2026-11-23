# Count repeated primes of the crossed gap coordinates

Fix a first incidence, its constructed two-position list at $g=1$, and an occupied denominator $d$. Use the [raw-gap count](masked-gap-lcm.md) with empty mask. The actual rows satisfy $cF_i h_i-dy_i=q\delta_i$ with $0<|\delta_i|\le H=q^{.390+o(1)}$, $h_i=q^{.665+o(1)}\le U$, where $U=q^{.665+o(1)}$, and $d=q^{1.055+o(1)}$. Write

$$R=(|\delta_1|,|\delta_2|),\quad j=(h_1,h_2),\quad v_i=\delta_i/R,\quad \ell_i=h_i/j,\quad n=(\ell_2v_1,\ell_1v_2).$$

Let $M$ be the full eligible-prime part of $|n_1n_2|$ and $C=M/\operatorname{rad}(M)$, including $C=1$ for $M=1$. At most $q^{.4675+o(1)}$ distinct actual $c$ at this $d$ satisfy

$$\operatorname{lcm}(|\delta_1|,|\delta_2|)/C\le q^{.660}.$$

Unlike a fixed prime mask, this cut allows repeat primes discovered on the endpoint. It pays to select them. The estimate does not rely on the reference CRT test below.

**Select one combined divisor.** As in the raw-gap count, $n$ is primitive, with nonzero coordinates prime to $d$ and $F_2n_1\equiv F_1n_2\pmod d$. Use dyadic lower bounds $L_i\le |\delta_i|<2L_i$ and $D\le R<2D$; do not sum over individual $R$. For fixed smooth $j<q^{.115}$ put

$$K=\max(1,L_1L_2/(2D q^{.660})),\qquad V_j=16U^2L_1L_2/(dD^2j^2),\qquad A=\ell_1\ell_2.$$

The cut gives $C\ge K$. A determinant of two vectors in the centred direction box has absolute value at most $dV_j/2$. We need a smooth divisor large enough to beat this determinant, but with few possible radicals.

1. Take $s=1$ if $K=1$. Otherwise take a divisor $w$ of $C$ first crossing $K$ by successive prime factors, so $K\le w\le XK$ where $X=q^{o(1)}$ bounds eligible primes. Set $s=w\operatorname{rad}(w)$. Then $s\mid M$ and $s/\operatorname{rad}(s)=w$. These powers need not all be available in the cofactors: The gap can supply repeats. The seed fits, since for $K>1$,
   $$\frac{V_j}{X^2 K^2}=\frac{64 U^2 q^{1.320}}{d j^2 X^2 L_1 L_2}\ge q^{.585-o(1)},\qquad s\le X^2 K^2.$$
2. If $V_j\le1$, take $m=1$ (then $K=1$). Otherwise extend $s$ to a divisor $m\in[V_j,XV_j]$ of $M$ by multiplying factors of $A/(A,s)$ as needed. There is enough left: $A\mid M$, so $sA/(A,s)=\operatorname{lcm}(s,A)\mid M$, and
   $$V_j/A=16U^2 L_1 L_2/(dD^2 h_1h_2)\le q^{-.275+o(1)}.$$
   The extension does not spend any prime power twice. Repetition is nondecreasing under divisibility, so $m/\operatorname{rad}(m)\ge K$, and $\operatorname{rad}(m)\le X V_j/K$ when $V_j>1$.
3. Enumerate only the *final* divisor $m$ and its split between coordinates, before counting directions. The half-power count on smooth radicals costs $q^{o(1)}(1+\sqrt{V_j/K})$ choices. For a fixed radical there are $q^{o(1)}$ exponent lists and coordinate assignments: At polynomial height there are $O(\log q/\log\log q)$ eligible factors with multiplicity by the eligible-prime lower bound. Each prime is in just one coordinate of the primitive $n$. For an admissible split $m_i\mid n_i$, $m_1m_2=m$, the index with the congruence is $dm$ since all factors and both coefficients are units modulo $d$. This exceeds the determinant bound, so there are at most two ambient primitive vectors including signs. The count pays for *all* endpoint-dependent filters, not just one favorable choice.

Divisors of the nonzero coordinates recover $\ell_i,v_i$ at subpower cost. For the fixed $h_i,v_i$ so obtained, the [scalar recovery](masked-gap-lcm.md) costs $q^{o(1)}\sqrt D$ numerators. Summing over $j$ uses the smooth count $q^{.0575+o(1)}$ for the constant term and $\sum 1/j\ll\log q$ for the area term. The box price is therefore at most

$$q^{o(1)}\left(q^{.0575}\sqrt D+\frac{U}{\sqrt d}\sqrt{\frac{L_1L_2}{DK}}\right).$$

The first exponent is at most $.2525$; the second is at most $.665-.5275+.330=.4675$ since $L_1L_2/(DK)\le2q^{.660}$. The dyadic sums cost $q^{o(1)}$. With one reference per $d$, at most $q^{.5275+o(1)}$ denominators give aggregate cost $q^{.995+o(1)}$. With all references subtract the local allowance before squaring. Both modular discrepancy tests can be kept. Outside the cut, for $R=j=C=1$ and two full-width gaps, the direction count without repeat credit (use $K=1$) only gives $.5275$ locally. It does not show that many endpoints exist.

## A bounded CRT candidate: What the output test adds

In the separate $r=e=b=1$ bracket box of the [reference projection](reference-projection-review.md), fix $f\mid h_1$ crossing $q^{.120}$ and write $k=h_1/f$, $T=kh_2$. With $a_i=h_i(c_0)$, $A_i=\delta_i(c_0)$, $s_i=a_i\delta_i-A_i h_i$, and $(m_1,m_2)=(h_2s_1,ks_2)$, a bounded positive smooth candidate $T$ satisfies the two CRT residues making these integral:

$$u_1=(m_1+A_1 fT)/a_1,\qquad u_2=(m_2+A_2T)/a_2.$$

The primitive split test is $(T,u_1)(T,u_2)=T$. Indeed a split gives $u_1=h_2\delta_1$, $u_2=k\delta_2$, with $(k,\delta_1)=(h_2,\delta_2)=1$. Conversely set $h_2=(T,u_1)$ and $k=(T,u_2)$: Their product is $T$, so division gives both coprimalities. This tests precisely these conditions, not full row primitivity or the gap widths.

**Price on a complete residue square.** For $p^t\parallel T$, let $z_i$ be the valuation of $u_i$ truncated at $t$ (so $z_i=t$ on zero modulo $p^t$). The rule is $z_1+z_2=t$. Of the $p^{2t}$ residue pairs, the two end splits admit $2\varphi(p^t)$, and each of the $t-1$ interior splits admits $p^t(1-1/p)^2$. By CRT the fraction admitted on the full square modulo $T$ is exactly

$$\frac{1}{T}\prod_{p^t\parallel T}\big[2(1-1/p)+(t-1)(1-1/p)^2\big]\le \tau(T)/T.$$

This is **not** a density bound on occupied candidates. The forced output numerators do not give a second such saving. For a candidate $c$ satisfying the row congruences at $d$, form the integers

$$w_1=(F_1 fTc-q u_1)/d,\qquad w_2=(F_2Tc-q u_2)/d.$$

For $(T,qd)=1$, $w_i\equiv -q d^{-1}u_i\pmod T$. Thus the gcd-product test on $(w_1,w_2)$ is *identical* even on rejected candidates. What can be new is that on an actual endpoint $(w_1,w_2)=(h_2 y_1,k y_2)$ are positive eligible-prime products. After the primitive split, testing smoothness of these crossed products is equivalent to testing smoothness of the forced outputs, because $T$ is eligible-smooth and the divisors $h_2,k$ are the same gcds on both sides. Positivity, output ranges, original row conditions, and list membership still matter.

**Next decision.** Count distinct $c$ admitting *smooth* crossed products, not two independent copies of the split test. One alternative to enumerating all $T$ is to index candidates by $w_1=h_2y_1$ itself: The [cross-product recovery](shared-row-labels.md) gives at most three choices for $h_1y_2=f w_2$ using $|F_1 f w_2-F_2 w_1|\le qW$ and divisibility by $q$. This projection is across $d$, before choosing $f$; enumerating all smooth $w_1\le q^{2.110+o(1)}$ alone still costs $q^{1.055+o(1)}$. Can joint smoothness and the actual gap constraints save more than $.057$ there, or give a bound below $.4105$ per $d,f$ in the hard CRT box? The full-square fraction does not supply either estimate. Nothing here proves the unrestricted $.998$ target or a fixed-window statement.
