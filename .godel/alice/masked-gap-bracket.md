# Count common-input columns in a reference determinant test

Use the actual [two-label list](same-input-second-bracket.md) in $g=R=j=1$. Fix a complete first input $v$ and an actual reference column at $v$. Write the two rows of a candidate column as

$$v=cA=dY+q\alpha,\qquad cBh=dZ+q\beta,\qquad A=F_1a=v/c,\quad B=F_2.$$

The sorted prefix fixes $c$ from $v$. Use the signed vector $x=(\beta,h\alpha)$ and denote its reference value by $x_0$. Choose a set $S$ of $O(\log q/\log\log q)$ primes and an integer linear form $\ell$ of polynomial height with $\ell(x_0)\ne0$. Both choices may depend on the input and reference but are held fixed while counting candidates. Write $n_S$ for the full $S$-part of $|n|$ when $n\ne0$. Define

$$L=(A,h),\qquad t=\frac{AZ-BhY}{qL},\qquad C=L\,(|\beta h\alpha|/L)_S\,(d|t|)_S.$$

For $1\le T\le q^{O(1)}$, at most $q^{o(1)}\sqrt T$ **actual columns at this input** pass

$$|\det(x,x_0)|\,|\ell(x)|\le TC\,|\ell(x_0)|.\tag{1}$$

In particular, take the union of the two coordinate forms. This prices the directed skew $\min_i|x_i/x_{0i}|$, not just the unweighted determinant. With $S=\operatorname{supp}(|x_{01}x_{02}|e)$ for reference denominator $e$, the credit contains $(|x_1|,|x_{01}|)(|x_2|,|x_{02}|)(d,e)$: In fact $C=(|x_1x_2|d)_S (L/L_S)(|t|)_S$. Taking both orientations therefore includes the gcd test with the minimum of the two directed skews. It does **not** assert that $C$ divides the reference determinant. For example, in the local congruence $x_1-x_2\equiv0\pmod d$, the primitive vectors $(1,9;d=8)$ and $(1,17;e=2)$ have determinant $8$. The three gcds have product $2$. At $T=1$ even the symmetric skew gives $8(9/17)>2$, but the candidate's masked denominator alone supplies $8$. This illustrates different tests, not occupancy by actual rows.

## Why the full credit is available

The [actual row equations and primitivity](rich-column-rows.md) give $q\mid AZ-BhY$ and $A\beta-Bh\alpha=-d(AZ-BhY)/q$. The two positive primitive rows are distinct, hence their determinant is nonzero. Since $L\mid A,h$ and $(L,q)=1$, $t$ is a nonzero integer. In the coordinates $u=(\beta,h\alpha/L)$ this is one equation

$$(A/L)u_1-Bu_2=-dt.$$

The [label construction](shared-row-labels.md) chooses $B$ away from the entire first row, so $(A,B)=1$. Row primitivity gives $(A,\alpha)=(Bh,\beta)=1$; $R=1$ gives $(\alpha,\beta)=1$. Consequently $x$ is primitive. Put $m_i=(u_i)_S$, $m_d=d_S$, $m_t=t_S$. Then $((A/L)m_1,Bm_2)=1$: Besides the preceding coprimalities, $(A/L,h/L)=1$. All data have polynomial height. Guess $L$ as a divisor of the fixed $A$, then the four full masks at subpower cost. Indeed, $O(\log q)$ total exponents on $K=O(\log q/\log\log q)$ fixed primes have at most $\binom{O(\log q)+K}{K}=q^{o(1)}$ distributions, including when $S$ contains small gap primes. The support of any fixed polynomial-height integer is allowed since $r$ distinct primes have product at least $(r+1)!$.

The candidates with $\ell(x)=0$ lie on one line through zero. For the others, bin $|\ell(x)|$ dyadically, using its polynomial upper bound and integral lower bound one. In a common bin and mask group, the signed identity

$$\ell(x_0)\det(x,x')=\ell(x)\det(x_0,x')+\ell(x')\det(x,x_0)$$

and (1) bound the **mutual** determinant by $4TC$, even for opposite signs. Neither candidate need be close in both coordinates; no divisibility by the candidate masks is imposed on $x_0$.

If $d/m_d\le4T$, enumerate this smooth quotient; knowing $d$ fixes the column at $v$. Otherwise choose $f\mid d/m_d$ strictly crossing $4T$ by successive eligible prime factors. Thus $4T<f\le4TX$ with $X=q^{o(1)}$. Both enumerations cost $q^{o(1)}\sqrt T$ by the [smooth half-power bound](shared-complement-count.md). For a fixed occurring $f$ put $N=m_dfm_t$. This divides $dt$ **with multiplicities**, whether or not $d,t$ share primes. On substituting $u_i=m_i z_i$ the one congruence modulo $N$ has index exactly $N$ by the coprimality of the two coefficients. Intersecting separate conditions modulo $m_df$ and $m_t$ and multiplying their indices would not justify this step. Transforming back to raw $x$ gives index $Lm_1m_2N=Cf>4TC$. Every mutual determinant is divisible by that index and hence vanishes.

On each resulting line there are at most two primitive signed $x$, including in the $\ell(x)=0$ branch. Both coordinates are nonzero. Enumerate positive divisors $h\mid |x_2|$, recover $\alpha=x_2/h$, and take the sorted prefix of $v-q\alpha=dY$ to recover $d$. The list forces its two rows. This is subpower multiplicity back to the original objects, not just a bound on directions.

## Spending the estimate

* **Every reference:** Sum over $I'$ retained incidences and restore the reverse order. At $T=q^{.273}$ the new coordinate tests add $q^{.1365+o(1)}I'$ ordered pairs with their common inputs, within the [existing deletion allowance](private-output-radicals.md). No price on the complement follows.
* **One pair of directions per input:** Choose any two actual nonparallel directions $x_0,x_*$ before counting at $v$. Set $\ell(x)=\det(x,x_*)$. Then (1) becomes the symmetric product test $|\det(x,x_0)\det(x,x_*)|\le TC|\det(x_0,x_*)|$. The mask can contain both references' data. If there is no nonparallel pair, primitive recovery already prices the whole fiber at $q^{o(1)}$. One chosen pair per input at $T=q^{.272}$ costs at most $q^{.860+.136+o(1)}$ columns on the list. This permits choosing the pair to fit the actual fiber; it is not a sum over all possible pairs.

* **During attachment selection:** In the same-input packet construction linked above, the live degree exceeds $q^{.137}$. Keep its existing restrictions. Demand, in addition, that the next gap vector not be parallel to any preceding one, and that it fail the product test at $T=q^{.272}$ for every pair of preceding directions at that input, counting the root among them. For each pair fix its own mask, for instance the support of the product of its two denominators and all four vector coordinates. There are only $q^{o(1)}$ prior pairs. Parallel lines cost $q^{o(1)}$ by primitive recovery, and all passing product tests together cost $q^{.136+o(1)}$ at this choice. Even the earlier exclusions cost only $q^{.1365+o(1)}$ there. Thus the next attachment exists with all the old properties and these new inequalities. This is a pointwise construction, not a density model for completed packets.

A concrete sufficient next test is to choose up to $q^{.001}$ such pairs and masks per input **after the column pruning but before forming partners**. The union still costs at most $q^{.997+o(1)}$ columns, without counting the choices of covers: The local price is uniform for every fixed reference pair and mask. Bound the remaining ordered pairs among uncovered columns by $q^{1.136-\eta}$ for a fixed $\eta>0$ after the existing pair deletions. That would give the required incidence bound by the [common-input Cauchy inequality](same-input-second-bracket.md). The full gap box alone allows determinants up to $q^{1.445+o(1)}$ from $|\beta|\le H$, $|h\alpha|\le q^{.665+o(1)}H$; it does not supply a cover at $T=q^{.272}$. Neither a cover nor the residual occupancy estimate is proved here.
