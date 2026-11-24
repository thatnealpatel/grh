# Charge the prime powers of one determinant difference together

Fix the same constructed two-label list at $g=1$, one occupied $d$, and one actual reference at $d$ as in the [progression bound](translated-determinant-progressions.md). Fix a set $S$ of $O(\log q/\log\log q)$ primes before counting the remaining numerators. It may depend on the list, $d$, and the reference. For a nonzero integer $z$ put
$$C_S(z)=\prod_{p^a\parallel |z|,\ p\notin S}p^{\min(a,c_p)},\qquad c_p=\begin{cases}1& p\text{ eligible},\\2& p\text{ otherwise}.\end{cases}$$
Then each of these two tests costs $q^{.4675+o(1)}$ numerators per $d$:

* For the signed raw difference $z=t-t^0$, count $z=0$ or $C_S(z)\le q^{.660}$.
* For the projective difference $z=\det(n,n^0)/d$, count $z=0$ or $|z|/C_S(z)\ge q^{.120}$.

Thus their union costs $q^{.995+o(1)}$ columns per list across denominators. The two bounds use different lattices. Neither is a claim that a common shift normally passes a test.

## The two costs of a family of steps

Take from $|z|$ the full powers on $S$, the full powers of exponent at least two on the other eligible primes, and the full powers of exponent at least three elsewhere. Write the resulting divisor as $b=b_0 b_1 b_2$ in that order. For any such step set $c(b)=\operatorname{rad}(b_1)\operatorname{rad}(b_2)^2$, including $c(1)=1$. Prime by prime,
$$ C_S(z)=(|z|/b)c(b). $$
Although $b$ is selected from the endpoint, the **menu** of steps of this form up to height $Y$ is prescribed independently. For $1\le Y\le q^{O(1)}$ it satisfies
$$ \#\{b\le Y\}\le q^{o(1)}Y^{1/3},\qquad \sum_{b\le Y}c(b)^{-1/2}\le q^{o(1)}. $$
Indeed $b_0$ has subpower cost by exponent-vector counting on $S$. For any fixed radical the assignments of exponents likewise cost $q^{o(1)}$: A polynomial-height radical has $O(\log q/\log\log q)$ distinct primes (their product is at least the factorial of their number), with total exponent $O(\log q)$. For the first estimate put $b_1,b_2$ in dyadic boxes of upper sizes $Y_1,Y_2$ with $Y_1Y_2\le4Y$. Their radicals are at most $Y_1^{1/2},Y_2^{1/3}$; the first is eligible-smooth and costs $q^{o(1)}Y_1^{1/4}$ by the [half-power count](shared-complement-count.md), the second costs at most $Y_2^{1/3}$. For the second estimate sum $r^{-1/2}$ on eligible radicals $r$ using that same Euler product, and $s^{-1}$ on arbitrary radicals $s\le Y$ using the harmonic sum. This counts products with several exponent patterns, not a union requiring one pattern to give all the saving.

**Raw difference.** For $z\ne0$ take $Y=2W$. At a prescribed $b$ the raw test lies in $t=t^0+bi$ with $|i|\le V/c(b)$, $V=q^{.660}$. Omit $c(b)>V$; the remaining half-lengths are at least one. Apply the raw progression bound at the **fixed** step $b$ before summing the menu. In a block $D\le R<2D$, $D\le q^{.121}$, the two terms give
$$q^{.1375+o(1)}\big(\sqrt D\,(2W)^{1/3}+\sqrt V\big).$$
Their exponents are at most $.458$ and $.4675$. This keeps the rounding term even for a progression with a single nonzero multiplier. Equality has the one-window bound, and the existing large-$R$ estimate needs no step.

**Projective difference.** Use the homogeneous estimate from the same [progression note](translated-determinant-progressions.md#a-separate-homogeneous-test-for-the-projective-discrepancy). At fixed $D,j$, a prescribed divisor $b\mid z$ costs $q^{o(1)}\sqrt D(1+\sqrt{V_0/b})$ including scalar recovery, with $V_0=(UH/(Dj))^2/d$. For $z\ne0$ take $Y=2(UH)^2/(Djd)$. As $b/c(b)=|z|/C_S(z)$, sum only steps with $b^{-1/2}\le q^{-.060}c(b)^{-1/2}$. The area term after summing $j$ is $q^{.4675+o(1)}/\sqrt D$, using $\sum_{j\le q^{.115}}1/j\ll\log q$. The rounding term per $j$ is $q^{o(1)}\sqrt D\,Y^{1/3}$, the same upper bound as for cube bases. Summing $j^{-1/3}$ over eligible-smooth $j<q^{.115}$ by dyadic half-power counting costs $q^{.115/6+o(1)}$; the total exponent is at most $1.055/3+(.121+.115)/6<.392$. Equality and large $R$ are already paid as in that note.

**Strict arithmetic comparison.** Even with $S$ empty and only ineligible primes, $z=p^3 r^4 u$ with distinct primes of sizes $p=q^{.050+o(1)}$, $r=q^{.040+o(1)}$, and $u\asymp W/(p^3r^4)$ can have full width. Choose $u$ between $W/(2p^3r^4)$ and $W/(p^3r^4)$ by Bertrand's postulate. The joint credit $|z|/C_S(z)=p r^2=q^{.130+o(1)}$ suffices. Even taking the whole part supported on primes of multiplicity at least three gives only exponent $.310<.360$; the fourth-full part has exponent $.160<.240$, and there is no nontrivial fifth-full part. Conversely, if $e\mid z$ is $k$-full (all nonzero exponents at least $k\ge3$), then $|z|/C_S(z)\ge e/\operatorname{rad}(e)^2\ge e^{1-2/k}$. Thus all single-multiplicity cutoffs $e\ge q^{.120k/(k-2)}$ are retained at full width up to the following endpoint convention. At the exact raw boundary one can use $V=2W/q^{.120}$ to include every old $.360$ cube without an endpoint constant; the proof works for any $V=q^{.660+o(1)}$. The [finite check](check-charged-differences.py) compares the capped product with the best divisor price, including rejected inputs. Neither kind of example is an occupied column.

**Next decision.** Use this as one exclusion at a fixed reference, not as a new menu of reference choices. At $R=j=1$, a full-width difference supported on distinct primes outside $S$ can get no credit. For the remaining common-shift problem one still needs a bound on occupied seed/residue classes or on successes inside them. Opposite outputs still determine the residues; this counting lemma does not make them prescribed.
