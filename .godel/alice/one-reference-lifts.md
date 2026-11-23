# One actual reference per denominator

Use the $g=1$ [simultaneous cuts](simultaneous-output-cuts.md) for a fixed first incidence and ordered two-position list. On each nonempty remaining fiber $C_d$ choose **one actual numerator** $c_0=c_0(d)$, for instance its least. This keeps two genuine reference rows for subtraction without having to count all ordered pairs. Write $h_i^0=h_i(c_0)$, $\delta_i^0=\delta_i(c_0)$, $z=(c-c_0)/d$ in the field, and $\Delta=c-c_0$ in the integers.

Let $M$ count endpoints $c\in C_d$, summed over $d$, satisfying all four tests:

1. $\min_i\|F_i h_i^0 z\|_q>q^{.880}$;
2. $\max_i\|F_i z\|_q>q^{.900}$;
3. both signed brackets $s_i=\delta_i(c)h_i^0-\delta_i^0 h_i(c)$ have $|s_i|>q^{.935}$;
4. $(\Delta,d)<q^{.120}$.

Then the original partner count per first incidence is at most $M+q^{.995+o(1)}$. In particular it suffices to beat $.998$ by a fixed margin for $M$ for **one specified choice** of the reference rule. The reduction holds for every rule, but the needed upper bound on $M$ need only be proved for one. An arithmetic proof that fixes the reference at one $d$ cannot hold its row multipliers fixed when summing over other $d$. The all-pairs alternative may still be preferable if it gains from averaging the reference rows.

**First two tests.** The deleted full cofactor fibers already cost $q^{.995+o(1)}$. On the rest, the number of failures of tests 1 or 2 at $d$ is at most $2B+E_d$ for the *chosen* reference. The [local band estimate](modular-complement-bands.md) gives $B=q^{.4675+o(1)}$ for an arbitrary row multiplier; the two-band estimate gives $\sum_d E_d\le q^{.995+o(1)}$ for the fixed list multipliers $F_i$. There are at most $q^{.5275+o(1)}$ denominators. Summing these allowances once per $d$ suffices. There need not be a common exceptional set for all choices of $c_0$.

**Price of a short bracket.** At fixed $d,i,c_0$, enumerate the smooth $h=h_i(c)$ in $q^{.3325+o(1)}$ ways. The bound $|s_i|\le q^{.935}$ puts $\delta_i(c)$ in one translated interval of half-width $K=q^{.935}/h_i^0=q^{.270+o(1)}$. The row equation gives

$$\delta_i(c)\equiv a c\pmod d,\qquad a=F_i h/q\pmod d.$$

Here $a$ is a unit for all actual rows: $q\nmid d$ and $(x_i,d)=1$ as in the [affine square count](short-label-ratios.md). This modulus is **$d$, not the prime $q$**. The number of smooth numerators $Z/X<c\le Z$ in this modular band is at most $q^{o(1)}\sqrt V$, $V=ZK/d=q^{.270+o(1)}$.

Here is the pointwise strip argument. The graph lattice $u\equiv ac\pmod d$ has determinant $d$ and full first projection; adding $e\mid c$ multiplies the determinant by $e$, **even for composite $d$**. Cross $64V$ with a smooth divisor $e\mid c$, so $64V<e\le64XV<Z/X$. At fixed $e$ all filtered points of the rectangle are collinear: Two differences have absolute determinant at most $8ZK<ed$. Singleton filters cost $q^{o(1)}\sqrt V$ altogether.

On a nonsingleton line take its direction $v$ primitive in the graph lattice. Since $2K<d$, it cannot be vertical. The filtered step is $kv$, $k=e/(e,|v_c|)$, so $e/k\mid v_c$. Put $R=\min(2Z/|v_c|,2K/|v_u|)$, ignoring the second entry when $v_u=0$. Then $k\le R\le2V$: If $v_u\ne0$ use $K\le V$, and otherwise the unit condition gives $d\mid v_c$, so $R\le2Z/d$. For a dyadic block $Q\le R<2Q$, $Q\ge1$, fix $k<2Q$. Cross $8V/Q^2$ strictly with a divisor $f\mid e/k$ (take one if the threshold is below one). This is possible since $e/k>32V/Q$. With overshoot at most $X$, the number of choices for $f$ is $q^{o(1)}(1+\sqrt V/Q)$. In the centered direction box of half-widths $(2Z,2K)/Q$, two vectors with $f\mid v_c$ have absolute determinant at most $8ZK/Q^2<fd$. There is therefore at most one base-primitive direction up to sign. Recover $e/k$ at divisor cost from $v_c\ne0$. For a recovered $e$ there is at most one occupied line with two or more points, by the first determinant test.

On that line $c$ is a nonconstant integral affine function on a parameter interval of length at most $2Q/k$. Such a progression of length $L\ge1$ contains at most $q^{o(1)}\sqrt L$ positive smooth values of polynomial height: Divide the initial value and the step by their gcd. Count reduced smooth values at most $L$ directly; larger ones have a smooth divisor in $(L/X,L]$ coprime to the reduced step. Each such divisor selects one parameter class with $O(X)$ representatives. Summed over smooth $k<2Q$, the line prices before the factor $q^{o(1)}(1+\sqrt V/Q)$ cost $q^{o(1)}\sqrt Q$, since $\sum_{k\le2Q,\ k\ \mathrm{smooth}}k^{-1/2}=q^{o(1)}$ by dyadic summation of the half-power count. The whole block costs $q^{o(1)}(\sqrt Q+\sqrt{V/Q})\ll q^{o(1)}\sqrt V$, including the horizontal direction. Summing the logarithmically many blocks proves the strip bound without an average over moduli or multipliers.

Thus one short bracket costs at most $q^{.3325+.135+o(1)}$ endpoints per $d$. The other row need not be counted: A fixed list and column determine their rows. Taking the union over the two positions and then all $d$ gives $.995$ in the exponent. This charges actual endpoints, not every realization sharing a cofactor with one of them.

**Price of a common divisor.** If $(\Delta,d)\ge q^{.120}$, enumerate that divisor $e\mid d$ at subpower cost. Then $c=c_0+je$ with the parameter $j$ in an interval of length at most $Z/e$. Since $(c_0,d)=1$, all values are coprime to $e$. Put $L=\max(1,Z/e)$. Values at most $L$ cost $q^{o(1)}\sqrt L$ by smoothness; any larger smooth value has a divisor in $(L/X,L]$, coprime to $e$. Each such divisor selects one progression class of $j$ with $O(X)$ choices. Thus this cut costs at most $q^{.4675+o(1)}$ per $d$ as well. It includes $c=c_0$.

**Remaining lift test.** At fixed $d$ and its reference, try to bound the number of *distinct* $\Delta$ giving both large brackets with the same numerator $c_0+\Delta$. In addition to the two modular discrepancy tests, both satisfy

$$ q s_i\equiv F_i h_i(c)h_i^0\Delta\pmod d,\qquad (s_1,d)=(s_2,d)=(\Delta,d)<q^{.120}. $$

These are necessary congruences for the exact lifts, obtained by subtracting the two row equations after cross multiplication; their coefficients are units modulo $d$. The brackets must be actual signed differences with smooth row and column coordinates; in particular $|s_i|\le2HU=Z/X<d$. Count integer $\Delta$, not just its class modulo $q$: A residue may represent $1+O(Z/q)$ shifts. A bound $q^{.4705-\epsilon+o(1)}$ uniformly per occupied $d$, or directly $q^{.998-\epsilon+o(1)}$ in aggregate, would suffice. Only the four excluded parts have been priced. In particular fixing a reference does not of itself reduce the number of far endpoints, and none of this bounds the unrestricted average or gives a fixed-window result.

All four allowances are uniform at a given denominator. Thus the all-references reduction can also impose tests 3 and 4: Subtract their additional $q^{.4675+o(1)}$ allowance from $n_d$ before squaring, not from the resulting pair count.
