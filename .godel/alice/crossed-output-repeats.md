# Count joint repeat factors in two successful outputs

Use an actual [constructed ordered list](shared-row-labels.md) at $g=1$. Define
$$a=h_1 y_2,\quad b=h_2 y_1,\quad t=(F_1a-F_2b)/q\ne0,\quad J=(a,b),\quad L=(F_1,b/J).$$
Let $w$ be the eligible-prime part of $|t|/(JL)$ and put $e(n)=n/\operatorname{rad}(n)$. For $1\le V\le W$, the number of actual columns on the list satisfying
$$ |t|\le V e(abw) $$
is at most $q^{.665+o(1)}\sqrt V$, **across denominators**. In particular at $V=q^{.660}$ this costs $.995$ in the exponent. One may use just $e(y_1y_2)$ in the test, since $y_1y_2\mid abw$. No sparse matching is needed: Even repeats on disjoint supports in the two outputs count toward the same threshold. The [original joint-repeat cut](joint-radical-gap.md) on the smooth input collision applies to $(cx_i,dy_i)$ for each row separately, not to this product on two rows. This distinction alone does not show that a rich list populates the new cut.

**Normalize both terms.** The second label $F_2$ avoids $x_1$, and is coprime to $y_2$ by row primitivity, so $(F_2,a)=1$. Also $(F_1,y_1)=1$, hence $L$ divides the part of $h_2$ on the support of $x_1$, giving $L<q^{.115}$. Now $JL=(F_1a,F_2b)$ divides $t$ because $(q,JL)=1$. Write $\alpha=a/J$, $\beta=b/(JL)$. The two terms $(F_1/L)\alpha$ and $F_2\beta$ are coprime by this exact normalization. In particular $(\alpha,\beta)=1$.

Fix a dyadic block $T/2<|t|\le T\le2W$. Put
$$S=UA_+/F_2=q^{1.330+o(1)},\quad E_0=ST,\quad Q=J^2L,\quad E=E_0/Q,\quad K=\max(1,T/(2V)).$$
The centred strip $|\alpha|\le UA_+/J$, $|(F_1/L)\alpha-F_2\beta|\le qT/(JL)$ has area at most $4qE$. Here $E\ge S/T\gg1$ since $JL\le T$. We reserve $Q$ in the divisor count; $ab=Q\alpha\beta$.

**Construct the final divisor before enumerating the coordinates.** In the cut, $e(Q\alpha\beta w)\ge K$. If $e(Q)\ge K$ take seed $s=1$. Otherwise cross $K/e(Q)$ with a divisor $u$ of $e(Q\alpha\beta w)/e(Q)$, overshooting by at most $X$. For primes $p^i\parallel u$ on the support of $Q$ put $p^i$ in $s$; for all other primes put $p^{i+1}$ in $s$. Prime valuations show $s\mid\alpha\beta w$ and $e(Qs)=e(Q)u$. It fits: $e(Q)\ge J$, and in this branch $K=T/(2V)\le T$, so
$$s\le X^2(K/e(Q))^2\le X^2T^2/J^2<E$$
by $X^2 TL/S\le q^{.780+.115-1.330+o(1)}$. Extend $s$ with unused prime occurrences of $\alpha\beta w$ to a divisor $m\in[E,XE]$. There is enough since $\alpha\beta/E=ab/(ST)\gg1$ by the row-coordinate lower bounds. The final smooth integer $u'=Qm$ is at most $XE_0$ with radical at most $XE_0/K$.

Enumerate **only** these final integers, in $q^{o(1)}\sqrt{E_0/K}$ choices: The radical is eligible-smooth, and at polynomial height there are $O(\log q/\log\log q)$ eligible factors with multiplicity, so assigning exponents on a given radical costs $q^{o(1)}$. Recover $J,L$ as divisors of $u'$, calculate $m$, and split it as $f_1 f_2 f_t$ from $\alpha,\beta,w$, respectively. All these choices cost only divisors. In coordinates $\alpha=f_1 z_1$, $\beta=f_2 z_2$ use
$$ (F_1/L) f_1 z_1-F_2 f_2 z_2\equiv 0\pmod{q f_t}.$$
Any split admitting an actual incidence has coprime coefficients because they divide the two coprime normalized terms. Thus this **single** form has index $q f_t$ in the substituted coordinates. The ambient index is $qm$, not two independent tests on the raw determinant. The strip has area divided by ambient index at most four. By Pick's bound on a spanning lattice hull there are $O(1)$ points, or on a line through zero only two ambient primitive $(\alpha,\beta)$ are possible. Divisors of the recovered $a,b$ give the rows, which admit at most one actual column by [row uniqueness](shared-row-labels.md). This is an upper bound on original positive primitive successes; no relaxation changes the list construction. Since $E_0/K\le2SV$, dyadic summation proves the claim. There is no outer sum over independently guessed $J$.

**Scope.** This is a savings from repeated prime factors in the forced products, not a density estimate for smooth quotients in general. In the $|t|\asymp W$ block, repeat weight $q^{.120+o(1)}$ reaches the $.995$ threshold up to the displayed exact size test. At $e(abw)=1$ the method still costs $q^{1.055+o(1)}$ at full width. Retain the [translated-progression test](translated-determinant-progressions.md) as a distinct pointwise test on that residual: A divisor of a difference from a nonzero reference is not repeat weight in $abw$. Neither bound pays for arbitrary full-width successful shifts.
