# Count the part of the double ratio private to each column

Fix one actual ordered two-label list in $g=R=j=1$ and one pool $P$ of at most $(\log q)^{1.10}$ eligible primes. Use the [common-input notation](global-double-ratio.md):

$$v=cF_1a=dY+q\alpha=eY_0+q\alpha_0,\qquad cF_2h=dZ+q\beta,\qquad cF_2k=eZ_0+q\beta_0.$$

The counted objects are ordered pairs of distinct columns **with their common complete input**. Write $L=kZY_0/(hZ_0Y)$ and $r$ for log-base-$q$ outside-$P$ radical, on rationals using nonzero signed valuations. Call a prime private to $d$ if it divides $YhZ$ but not $Y_0 kZ_0$; define privacy to $e$ symmetrically. We count the pairs where either endpoint supplies too little private support to the reduced $L$. All exponents below allow $q^{o(1)}$ factors.

* On the original list, at cost at most $q^{1.135+o(1)}$ pairs, one can require **each** endpoint to contribute at least $2.055-o(1)$ in private outside-prime weight to $L$. In particular this prices all pairs with $r(L)\le4.109$ without pruning or a multiplicity charge.
* For the incidence objective, first spend $q^{.996+o(1)}$ **columns**. On that graph, at cost $q^{.136+o(1)}I'$ pairs for $I'$ retained columns, one can require at least $2.407-o(1)$ from **each** endpoint. This prices $r(L)\le4.813$ after pruning, not on the original list. Neither conclusion requires ordinary multiplicity or bounds the number of pairs contributing large private parts.

## A single column, before its partner is known

The product of the two crossed keys is $uw$, where $u=aZ$, $w=hY$, both of height $q^{2.110+o(1)}$ with matching lower bounds. Use either of the following rows of parameters:

| Radical cutoff $b$ for $uw$ | Credit exponent $k_*$ | Column cost exponent | Local pair exponent $s$ to be used later |
|---:|---:|---:|---:|
| 3.960 | .232 | .939 | .080 |
| 4.088 | .118 | .996 | .136 |

Here is a weighted form of the [crossed-key strip](crossed-output-repeats.md). For an eligible integer $n$ use the credit $D(n)=n_P^{.9}n_{\rm out}/\operatorname{rad}(n_{\rm out})$. If $r(uw)\le b$, then $D(uw)\ge q^{.9(4.220-b)-o(1)}>K=q^{k_*}$. The strict slack holds in both rows. The credit is monotone under divisibility. There is a seed divisor $s_0\mid uw$ with $D(s_0)\ge K$ and $s_0\le X^2 K^2$: On $P$ take copies one at a time, and off $P$ start a repeated prime with two copies before adding single copies. Ignore outside singletons. In the seed every added group contributes at least its square root in credit, and the crossing group has size at most $X^2$.

Normalize **before** paying for a filter. Put $J=(u,w)$, $B=(F_1,w/J)$, $Q=J^2 B$, $U_1=u/J$, and $U_2=w/(JB)$. The [crossed-key normalization](crossed-output-repeats.md) gives coprime terms $(F_1/B)U_1,F_2 U_2$ with difference $q\tau/(JB)$, $0<|\tau|\le W=q^{.780+o(1)}$. In particular $JB\le W$. Use the **full** width even for a smaller $\tau$. Set $E_0=(UA_+/F_2)W=q^{2.110+o(1)}$, with $U$ the upper cofactor bound and $A_+$ the upper row-coordinate bound. Within $uw$ extend $\operatorname{lcm}(Q,s_0)$ by unused prime copies to a final divisor $n\in[4E_0,4XE_0]$. This is possible: $Q\mid uw$ and $Q s_0\le q^{1.560+2k_*+o(1)}<E_0$, whereas $uw=q^{4.220+o(1)}$. In particular there is no sum over separately enumerated seeds and normalizations.

Enumerate just $n$ with $D(n)\ge K$. In a dyadic bin $n_P\asymp A$ its inside part costs $q^{o(1)}A^{.05}$ by restricted Rankin, and its outside radical is at most $4XE_0/(KA^{.1})$. Enumerate this radical at half power, and the exponents on its specified primes at subpower cost (only $O(\log q/\log\log q)$ eligible factors with multiplicity). Thus the total is $q^{o(1)}\sqrt{E_0/K}$. Recover $J,B$ as divisors and split $n/Q=f_1 f_2$ with $f_i\mid U_i$. The congruence $(F_1/B)U_1-F_2 U_2\equiv0\pmod q$ gives index $q f_1 f_2$ in ambient coordinates including the divisibilities, since all coefficients and filters are units modulo $q$. For two qualifying vectors the determinant has absolute value at most $2qE_0/Q$, by substituting the difference in one column of the determinant and using $U_1\le UA_+/J$. The index is larger; the primitive positive vectors therefore agree. Divisors of the keys recover the actual column. This proves the two column prices in the table. The pool in this argument cannot depend on the column or its future partner.

## Two masks at the actual input

Fix one endpoint at $v$ as reference. Let $S$ be the support of its three factors $Y_0,k,Z_0$. For an integer $n$, $(n)_S$ is the full supported part. The following are **pointwise** costs per reference; they do not assume the candidate cofactor $h$ fixed. For each row of the table we may remove at most $q^{s+o(1)}$ partners so that on escape

$$ (dY)_S<q^{.390-2s},\qquad (hdZ)_S<q^{1.055-2s}. $$

For the first inequality enumerate $m=(dY)_S$ at subpower cost, since $S$ is one reference support of size $O(\log q/\log\log q)$. If $m$ is at least the threshold, extend it inside $dY$ just beyond $2H$ by a divisor $f$ of the remainder (use $1$ if already beyond). There is enough smooth product, and $f\le q^{2s+o(1)}$. Then $v-q\alpha\equiv0\pmod{mf}$ fixes the signed gap and $dY$ fixes its sorted prefix. This is the first-lift mask.

For the second inequality enumerate both full supported parts of $h$ and $dZ$, with product $m$. If $m$ reaches the second threshold, extend it inside $hdZ$ strictly beyond $2UH$; again the extra divisor costs at most $q^{s+o(1)}$ since $UH=q^{1.055+o(1)}$. Split the final filter into $f_h\mid h$, $f_N\mid dZ$ according to this construction. The directions $(h,\beta)$ satisfy $f_h\mid h$ and the **one** congruence $cF_2h-q\beta\equiv0\pmod {f_N}$, with $c$ fixed by $v$. Their index is $f_h f_N$ by substitution and $(q,f_N)=1$. The mutual determinant has absolute value at most $2UH$; it is zero on this filter. The vectors are primitive since $(h,dZ)=1$ and the equation implies $(h,\beta)=1$. Positivity of $h$ gives at most one such vector, which fixes $dZ$ and the sorted $d$. We only use the two masks as a union of deletions, not as two independent congruence indices. Apply the pointwise price in both orders, summing over the actual references on the graph being counted.

## What survives reduction of the fraction

When $r(uw)>b$, stripping $a\le q^{.665+o(1)}$ gives $r(YhZ)>b-.665-o(1)$. Remove all primes in $S$ from this support. Their total weight is bounded by the sum of the two mask exponents (the first covering $Y$, the second $hZ$). At an outside prime still present, no factor from the opposite endpoint can affect the valuation in $L$. The local fraction is $Z/(hY)$ or its reciprocal. Since $(Z,h)=1$, a prime of its raw support can vanish only if it divides both $Z$ and $Y$. The full second-row part supported on the first row is below $q^{.115}$ by [successive-row freshness](shared-row-labels.md), so this loss costs at most $.115$. Thus the private surviving weight at that endpoint is at least

$$ b-.665-(.390-2s)-(1.055-2s)-.115-o(1). $$

The two private sets are disjoint by definition. For the first row of the table charge a bad column its $q^{.195+o(1)}$ possible partners at the actual input, in either order, costing exponent $.939+.195=1.134$. Charge a failed mask $q^{s+o(1)}I$ with the unconditional list bound $I\le q^{1.055+o(1)}$, costing $1.135$. For the second row delete bad columns **as incidences first**. Only now form ordered pairs, and sum the two reciprocal mask prices over the retained incidences. These calculations prove the stated bounds with fixed slack at the displayed radical cutoffs.

**Remaining decision.** Intersect the second-row-of-table test with the [previous retained-pair tests](two-ratio-radical.md), including their endpoint deletions. The additional column charge fits $q^{.9965+o(1)}$ and the linear pair charge fits $q^{.1365+o(1)}I'$. The exceptional price is unchanged. An over-budget ordinary residual must now have large *separate private parts*, not just a large radical distributed arbitrarily over $L$. They do not contradict the height $NM\le q^{7.110-2t+o(1)}$ even at $t=.466$. To reach the incidence target one still needs, for example, average $q^{.276-\eta}$ ordered residual pairs over the $q^{.860+o(1)}$ input allowance. A mask consisting of the opposite actual endpoint was paid **per reference**; replacing it by a union of all possible opposite supports would invalidate the subpower enumeration. No restriction on how often two large private parts are occupied is proved here. The subsequent [masked gap determinant bound](masked-gap-bracket.md) prices a further class on this same residual. It allows two reference directions chosen per input, with an explicit budget for taking more pairs; what remains is to cover the actual columns economically or count pairs outside the cover.
