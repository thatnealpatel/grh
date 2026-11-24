# Isolate a recoverable divisor of a punctured relation at one input

Fix one actual ordered two-label list, $g=R=j=1$, and the prescribed prime pool of the [private-output bound](private-output-radicals.md). Write $v=cF_1a=dY+q\alpha$ and $cF_2h=dZ+q\beta$. At a fixed complete input $v$ the prefix $c$ is known. Take an **actual** reference $e$ there, with factors $Y_0,k,Z_0$. Use the three valuation directions on the eligible primes

$$ D=[d/e],\qquad E=[Y/Y_0],\qquad G=[(Z/h)/(Z_0/k)]. $$

In particular $G-E=[L]$ for the actual double ratio. Prescribe a rational linear space $W$ per reference. Say a candidate passes at radius $r$ if there are rational coefficients $(i,j,k')$ of the specified type and a set $S$ of eligible primes of product at most $q^r$ such that $iD+jE+k'G$ agrees with an element of $W$ off $S$. Both the coefficients and $S$ may depend on the candidate; coefficients need not be bounded. This is a count of actual partners, not just of labels.

**Result.** For $\dim W\le(\log q)^{1.15}$, each row below costs at most $q^{.0798+o(1)}$ partners per actual reference after the indicated cuts. Smaller radii are included.

| Required coefficients | Original-list radius | Column-pruned radius |
|:---|---:|---:|
| Any nonzero triple | .544 | .664 |
| $(j,k')\ne(0,0)$ | .796 | .924 |
| $jk'\ne0$ | 1.855 | 1.983 |

On the pruned graph there is another useful tradeoff: For $\dim W\le(\log q)^{1.10}$ the mixed row at radius $1.935$ costs only $q^{.05275+o(1)}$ per reference. The argument isolates a *divisor* of one lift before interpolating any valuation vector. It never has to infer which combination extends from a projection to the full set of coordinates.

## Cuts and weights available for isolation

Write $A=.390$, $B=1.055$ for the exponents of $2H$, $2UH$, respectively. On the original list use $b=3.960$, $d_0=.816$; on the column-pruned graph use $b=4.088$, $d_0=.936$. Require $\operatorname{rad}(d)>q^{d_0}$ and the outside radical of $aZhY$ to exceed $q^b$. The latter is the cited private-output cut with its pool chosen **before** the candidate. For the former, enumerate the small radical at half power, then the valuations on its support at subpower cost. There are at most $q^{.5275+o(1)}$ possible $c$, and $(c,d)$ specifies the column on the actual list. On the original list the two bad-endpoint charges in either orientation are, respectively, $q^{.408+.5275+.195+o(1)}$ and $q^{1.134+o(1)}$ triples, using the degree bound at the input. On the pruned graph the combined charge is $q^{.996+o(1)}$ **columns before partners**, since $.468+.5275<.996$. Do not use that price as a triple count on the original list.

A coordinate is usable for an active raw factor if it survives erasure, occurs in that factor, and occurs in no *other active* raw factor among $d,Y,Z/h$. For $Z/h$ use $(Z,h)=1$. Write weights as sums of $\log_q p$ over distinct primes. Drop the single boundary prime $P^+(d)$ at cost $o(1)$ in radical weight. No other prime of $d$ can occur in $Y$ or $Z$ since $d$ is the common sorted prefix of $dY,dZ$; also $(d,h)=1$. The following guarantees are uniform:

* For a pure denominator relation the usable $d$ weight is $\ge d_0-r-o(1)$. If $j\ne0,k'=0$, the usable $Y$ weight is $\ge 1.445-(4.220-b)-r-o(1)$. If $j=0,k'\ne0$, the usable $hZ$ weight is $\ge 2.110-(4.220-b)-r-o(1)$. Indeed the full product $aZhY$ has height exponent $4.220$ and radical exponent at least $b$, so the repetition loss of each subproduct is at most $4.220-b+o(1)$. The last two claims allow arbitrary $i$.
* If $jk'\ne0$, the sum of usable $Y$ and $hZ$ weights is $\ge b-.665-.115-r-o(1)$. Strip $a$ at cost $.665$; from the union of $Y,hZ$ drop their intersection, whose radical is bounded by the [second-row part on the first support](shared-row-labels.md) of weight at most $.115$. The two remaining sets are disjoint, so erasure costs $r$ only once. Again $i$ is arbitrary.

## Count a partially supported lift

Let $s>0$, $s<1/2$, with $\dim W\le (\log q)^{1+2s}$. Suppose at least $u>0$ in usable radical weight is available in **one** active factor. Use threshold exponent $C=A$ for $d$ or $Y$ (first lift), and $C=B$ for $Z/h$ (second lift). For $u\le C$ the candidates with that witness cost at most

$$ q^{s u+(C-u)/2+o(1)}\qquad\text{per fixed }(v,e). $$

Here and below a lower bound $u-o(1)$ suffices, by reducing the selected width by that uniform $o(1)$. To prove the price, choose usable primes successively to obtain a squarefree product of size $q^{u+o(1)}$, crossing $q^u$ if available. The largest prime is $X\asymp(\log q)^2$. Call the selected set $J$. We do **not** enumerate $J$ at half power.

There is a fixed family of $q^{o(1)}$ binary masks on the eligible primes such that one mask $T$ contains $J$ and avoids both $S$ and all raw candidate primes not in $J$. Indeed the required and forbidden sets are disjoint; the sum of their cardinalities is $O(m)$, $m=\log q/\log\log q$, since the eligible primes are at least $X/(\log\log q)^4$ and the raw products and the erased product have bounded height exponents. A fair independent binary mask has success probability at least $2^{-K m}$ for a fixed $K$. On $N\le X$ coordinates there are at most $(N+1)^{O(m)}$ prescriptions, so $O(2^{K m}m\log(N+1))=q^{o(1)}$ masks suffice by a union bound. Fix one such family for all candidates. These masks do not change the pool in the column cut.

For a fixed mask count candidates certified by it. Enlarge $W$ by the three **known** reference vectors $[e],[Y_0],[Z_0/k]$ and project to $T$. On this mask the raw relation belongs to that projected space. Since only one *active* factor occurs there, dividing by its nonzero rational coefficient shows that the valuation vector of that factor restricted to $T$ belongs to the space. Its support is exactly $J$. Inactive factors can overlap $J$ without entering the relation. This argument holds for each occupied mask without naming $S$, $J$, or the coefficients in advance.

Choose coordinate pivots for the projected space, at most $(\log q)^{1+2s}+3$ primes specified by the space and the mask. The radical of the active factor on the pivots divides the product on $J$, hence is at most $q^{u+o(1)}$. Enumerate this pivot radical at cost $q^{su+o(1)}$: In Rankin's bound at $s+1/\sqrt{\log\log q}$ the logarithm of the Euler factor is $o(\log q)$ by the eligible prime floor. Enumerate all signs and multiplicities on the resulting support at subpower cost: The total multiplicity of the **raw factor** is $O(m)$ on $O(m)$ named primes, giving $\exp(O(m))$ possibilities by stars and bars. There is no need to bound exponents in the witnessing relation. Pivot restriction is injective, so this code determines the raw valuation vector on $T$, and in particular the selected prime product $f$ there. Ignore inconsistent codes.

The recovered $f$ divides $dY$ for the first lift or $hdZ$ for the second. Extend it by prime copies from the corresponding full product until it strictly exceeds the actual width $2H$ or $2UH$, unless already above. There is enough product. Only the **extra** multiplier, of size at most $q^{C-u+o(1)}$, is counted at smooth half power. In the first lift the combined filter fixes the signed $\alpha$ from $v-q\alpha\equiv0$ modulo the filter, hence $dY$ and its deterministic prefix. In the second, split the combined filter by divisors as $f_h f_N$ dividing $h,dZ$, respectively. Then $f_h\mid h$ and $cF_2h\equiv q\beta\pmod{f_N}$ define a lattice of index $f_h f_N>2UH$ since $q$ is a unit modulo $f_N$. The mutual determinant of any two admissible $(h,\beta)$ is at most $2UH$, hence zero. These vectors are primitive and $h>0$, so the direction fixes the vector, then $dZ$ and its sorted prefix. This is where fixing $v$ (thus $c$) matters; $h$ was not fixed. Summing over the mask family proves the claimed bound on **columns**, not merely on filters.

## Widths and the decision on occupancy

For a desired local exponent $t\ge sB$ below $A/2$, set

$$ u_A=\frac{A/2-t}{1/2-s},\qquad u_B=\frac{B/2-t}{1/2-s}. $$

These lie in $(0,A]$, $(0,B]$. Either usable weight reaching its own $u_C$ suffices by the lift estimate. In the mixed case it suffices that the sum reaches $u_A+u_B$, with no multiplication of the two prices. For $s=.075,t=.0798$ one has $u_A=576/2125$, $u_B=4477/4250$. Substitution in the raw weight bounds gives the displayed table (rounding the radii down). In particular $1.055+.0798=1.1348$ prices passing triples across **all** references, including the original-list exceptions at their stated budgets only for the original-list radii. For $s=.05,t=.05275$ use $u_A=569/1800$, $u_B=B$; on the pruned graph $4.088-.665-.115-1.935>u_A+u_B$. Using one reference per input instead would count at most $q^{.860+t+o(1)}$ passing columns, not all ordered triples. The all-reference estimate on a graph with $I'$ incidences is $q^{t+o(1)}I'$.

After the indicated column cuts, an ordinary residual of more than $q^{1.135}$ triples with private weights at least $2.407-o(1)$ forces a fixed $(v,e)$ with $q^{.080-o(1)}$ such partners, by $I'\le q^{1.055+o(1)}$. At this reference grow $W$ by adjoining the three directions of a partner outside the three passing classes, starting at zero. While $\dim W\le(\log q)^{1.15}$ their union costs $q^{.0798+o(1)}$, strictly fewer than the partners. Thus there are more than $(\log q)^{1.15}/3$ successive choices. At each step their three new directions are independent modulo the old span even after erasing any prime product up to $q^{.664}$; no mixed combination lies in the old span even after erasure up to $q^{1.983}$. This uses only a price uniform in the *current* span, not a union over selection histories.

**Next occupancy test.** It would suffice to cover the ordinary large-private partners' $[L]$ at each reference of degree above $q^{.080}$ in the residual by at most $q^{.027}$ spaces of dimension $(\log q)^{1.10}$, allowing individual erased products up to $q^{1.935}$. The covered heavy contribution would cost exponent $1.055+.027+.05275=1.13475$; light references cost $1.135$. The cover can be chosen using the actual fiber but must be paid in full for that reference. Equivalently for this sufficient test one can cover the unreferenced $[Z/(hY)]$ by affine translates and absorb the translation and reference by adding $O(1)$ dimensions. The price does not assert that such a cover exists. In particular the private lower bound gives no upper bound on the support outside one of these spaces, and the independent sequence does not exhaust the eligible universe. Large-private occupancy and the unrestricted incidence target remain open.

### After Work: A fraction in one space suffices

For the incidence objective, the cover above asks more than is needed. In fact its capacity $q^{.027+.05275+o(1)}$ is strictly below the heavy degree $q^{.080}$: Proving a *full* cover at every such reference would prove that there are no such references. This does not invalidate that sufficient condition.

Keep the column cuts, then let $J$ be the retained incidence count, $N\le q^{.860+o(1)}$ the number of complete inputs, and $C$ the number of ordinary large-private ordered triples still to price. All counts below are on this retained graph unless specified. At each actual $(v,e)$ let $h(v,e)$ be the maximum number of **its residual partners** passing the mixed $[L]$ test in one space of dimension at most $(\log q)^{1.10}$ and radius $1.935$. The maximum exists on the finite partner set. The space may depend on the reference and on its fiber; the price is uniform over spaces, not a sum over them. Thus $H_*:=\sum_{v,e}h(v,e)\le q^{.05275+o(1)}J$.

**Test a fraction, not a full cover.** It suffices to prove

$$ C\le q^{.085+o(1)}H_* + q^{1.1355+o(1)}. $$

For instance, outside the absolute allowance, it suffices that one space chosen per reference sees a $q^{-.085-o(1)}$ fraction *in aggregate* of the remaining triples. No claim about every heavy reference or about covering its complement is required. A full cover by $q^{.085+o(1)}$ spaces per reference would imply the test by taking the best space, but is not necessary.

Indeed $J^2\le N\sum_v \deg(v)^2$. The diagonal and reciprocal deletions cost $q^{.1365+o(1)}J$ in that sum, by summing the directed prices over actual references in each order, **not** a pointwise bound on the reverse deletion. The other previously priced pairs cost $q^{1.1355+o(1)}$ in total by the [retained-pair bound](two-ratio-radical.md) and [private cuts](private-output-radicals.md). The new term costs $q^{.085+.05275+o(1)}J$. Under the proposed test this gives

$$ J^2\le q^{.99775+o(1)}J+q^{1.9955+o(1)}. $$

Either term dominating gives $J\le q^{.99775+o(1)}$. Restore the $q^{.9965+o(1)}$ incidences deleted *before* pairing to bound the original incidence count by the same exponent. Only now does the new linear charge imply an absolute price: $q^{.13775+o(1)}J\le q^{1.1355+o(1)}$, so $C\le q^{1.1355+o(1)}$ on the retained graph, not a triple price for the removed columns. More generally the fraction exponent must be strictly below $.998-.860-.05275=.08525$ for this fixed-power argument.

**Remaining experiment.** At a fixed actual reference, sample at most $\lfloor(\log q)^{1.10}\rfloor$ residual partners and use the span of their $[L]$ vectors. Count hits by *further* partners after puncturing. Normalize the sampling weights to sum to one **per reference** before adding these counts: Each expected hit count is a lower bound for $h(v,e)$, with no union over all possible spans. A large enough aggregate would prove the fraction test; the generators themselves give only polylogarithmically many hits per reference. The local theorem is an *upper* bound on $H_*$; neither that theorem nor the private weights give the required lower bound. See the [decision record](incidence-cover-decision.md).
