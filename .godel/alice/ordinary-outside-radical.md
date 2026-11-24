# Count ordinary labels by their fresh squarefree product

Use the hypotheses and notation of [the ordinary outside-product count](ordinary-outside-product.md). Fix **one** set $P$ of at most $(\log q)^{1.10}$ eligible primes. It may depend on the list. In a dyadic $J_0$-bin write $t=\log_q J$, $\mu=\min(t/2,.223)$, and $b=7.110-2t$. Each occupied reduced $L=N/M$ has $NM\le q^{b+o(1)}$ and costs at most $q^{\mu+o(1)}$ ordinary triples. Let $r$ denote the log-base-$q$ of the product of the **distinct** primes of $NM$ outside $P$.

**Claim.** Across the entire actual list, the number of distinct ordinary labels in this bin with $r\le2.760$ is at most $q^{1.134715-\mu+o(1)}$. The bound does not require that the outside product *with multiplicities* be small. In particular, the price for passing ordinary triples, summed over bins, is at most $q^{1.134715+o(1)}$.

**Split in decreasing order of multiplicity.** Bin $N$, the product of the two full $P$-parts, and the total outside product dyadically; write the last two products as $q^{u+o(1)}$ and $q^{h+o(1)}$. Take bin parameters with $u+h\le b+o(1)$. Enumerate both signed $P$-parts at cost $q^{.05u+o(1)}$: The signed Rankin product at $.05+1/\sqrt{\log\log q}$ on this many eligible primes is $q^{o(1)}$ by the eligible floor $(2.1\log q)^2/(\log\log q)^4$. For two labels with these same parts, their product $m=N_P M_P$ divides the determinant $\Delta=N_1M_2-N_2M_1$. Since $q$ is prime to $NM$ and $q\mid\Delta$, one has $m\mid\Delta/q$. All labels lie within relative width $q^{-1.110+o(1)}$ about $1$, so the bin on $N$ gives

$$|\Delta|/(qm)\le U=q^{h-2.110+o(1)}.$$

Choose a uniform positive upper bound including the width and bin constants. If $U<1$, the parts already force equality. Otherwise, on each candidate order its outside prime powers $p^e$ by **decreasing $e$**, breaking ties by prime. Stop at the first full power taking the accumulated product strictly above $U$. The outside product exceeds $U$ for large $q$. Before crossing, the radical accumulated has log at most $(r/h)\log U+o(\log q)$: The weighted average of $e$, with weights $\log p$, in any nonempty prefix is at least that over the entire product. Here $h\ge 2.110-o(1)$ in the crossing branch. The crossing prime adds only $o(\log q)$ to the log radical even if its *power* is large.

Enumerate the radical of this stopped product by the smooth half-power count. Once its primes are specified, their signed exponents have only $q^{o(1)}$ possibilities: There are $O(\log q/\log\log q)$ factors even with multiplicity, so stars and bars and sign choices suffice. Two candidates with the same encoding share the full signed prime powers, whose product divides $\Delta/(qm)$ and is larger than $U$. Thus the determinant vanishes and the reduced labels agree. Splitting prime copies in an arbitrary order need not give the radical discount used here.

**Price.** For $h>2.110$ the label exponent is at most

$$ .05u+\tfrac12(2.760)(1-2.110/h). $$

In the other bins $.05u+o(1)$ suffices (also for $h=2.110+o(1)$). In the displayed bound replace $h$ by $b-u$. The resulting expression decreases with $u$, since $1.380(2.110)/(7.110)^2>.05$. Thus after charging multiplicity, the maximum in this branch is at most $\max_t\{\mu+1.380(1-2.110/b)\}$. It occurs at $t=.446$: Before this point the derivative is $.5-2(1.380)(2.110)/b^2>0$, and afterwards only the decreasing term varies. At that point the value is $.223+1.380(1-2.110/6.218)<1.134715$. The noncrossing exponent including multiplicity is at most $.05(7.110)+.223$. Summing the subpower many bins proves the claim.

**Decision.** A violating ordinary bin must supply a new label with outside radical $>q^{2.760}$ after *any* such pool. Choose the next pool by adjoining only the six raw supports of the selected actual triple. Each step adds $O(\log q/\log\log q)$ primes, so this forces at least a constant times $(\log q)^{.10}\log\log q$ selections, with mutually disjoint fresh squarefree products at that threshold. There is no sum over pools. One can simultaneously require the [two recoverable ratios](joint-valuation-escape.md) to have fresh squarefree products $>q^{2.20}$ and $>q^{2.05}$, respectively, at each selection. These are compatible necessary conditions, not an exclusion: Even the product of all eligible primes has log of order $(\log q)^2$, more than the log product forced by this sequence. Use the common-input lifts within each selected triple before claiming an occupancy saving on the complement.

## Moving the pool onto the vertices and both lifts

One can also force *distinct complete inputs*, not merely distinct labels, in the preceding selection. This uses a different price. For an eligible integer $m$ write $r_P(m)=\log_q\operatorname{rad}(m_{\rm out})$. On either column of a triple write $(h_1,h_2)=(a,h)$ and $(y_1,y_2)=(Y,Z)$ (use $a,k,Y_0,Z_0$ on the other). Each of the five keys

$$cd,\quad h_i y_j\quad(1\le i,j\le2)$$

has size at most $q^{2.110+o(1)}$ and [recovers that actual column](shared-row-labels.md) up to subpower choices. In particular this last assertion includes the two cross-row keys: Their partners obey $F_i h_i y_j-F_j h_j y_i=qt$ with $|t|\le W<F_j$, hence only boundedly many $t$ given the first product. Each column fixes $v$. At that $v$ there are at most $q^{.195+o(1)}$ choices of the other column, since a divisor of its first complete output strictly crossing $2H$ costs $q^{.195+o(1)}$ choices and determines the signed gap and sorted prefix. This is a pointwise degree bound, not a bound on the number of first columns.

An integer key of exponent at most $b_0$ with $r_P\le s\le b_0$ costs $q^{.05 b_0+.45s+o(1)}$: Bin its outside radical at $q^r$, price that radical and its exponents as above, and use inside height at most $q^{b_0-r+o(1)}$. For **any** one of the five keys on **either** column having $r_P\le1.855$, the triple price is therefore at most

$$ .05(2.110)+.45(1.855)+.195=1.13525 $$

in the exponent. The fixed number of tests does not affect it. In particular each of the four individual outputs $Y,Y_0,Z,Z_0$ must have outside radical exponent $>1.190-o(1)$ on escape (strip off $h_i\le q^{.665+o(1)}$). Each cofactor $a,h,k$ must have outside radical exponent $>.410-o(1)$, and each of $c,d,e$ must exceed $.800-o(1)$ in outside radical exponent. This tests actual second outputs separately, rather than only $ZZ_0$ after stripping off $hk$ from $S$.

There is a separate test on $v/F_1=ca$ of height $q^{1.720+o(1)}$. An exact value determines $v$ but neither column; pay the pointwise degree **twice**. The price for $r_P(ca)\le1.465$ is at most $.05(1.720)+.45(1.465)+2(.195)=1.13525$ in the exponent. Thus, when enlarging $P$, include the supports of $c,d,e,a$ as well as the six raw factors. This still adds only $O(\log q/\log\log q)$ primes per step. Every selection in an over-budget bin can fail all tests at once: It then has $r_P(ca)>1.465$, each of the ten key tests fails, and $r>2.760$ for $NM$. In particular neither the input nor either output prefix can repeat one from an earlier step. This conclusion uses the shared $v$ *within* a triple, not a fixed $v$ along the sequence. The additional necessary conditions do not price triples passing none of the tests.
