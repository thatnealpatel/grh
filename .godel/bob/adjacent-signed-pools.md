# Opposite signed pool totals one replacement apart

Can the whole coefficient of an unsigned pool in the [joint arc test](jointly-separated-arc-test.md) be negative, or are there just individual negative terms inside nonnegative pool totals? It can be negative, even one replacement away from a pool supporting a central pair. This is a **finite arithmetic example** including the rounded gates, not an asymptotic estimate. In particular, positivity after angular averaging over all pools does not give a pointwise sign rule for these coefficients.

Take the prime $q=100000007$, $t=2q^{3/5}$, $d=6$, and $\gamma=1/4$. Here $1099<X<1100$, $49<D^2<50$, $R_*<2$, and $h=4$. Form the following pool $P$ from two balanced copies, displaying plus and minus starts separately:

| Plus starts | Minus starts | $t\nu$ (approx.) |
| --- | --- | ---: |
| $61,677,821,1063$ | $131,191,251,367$ | $-0.14645$ |
| $307,613,733,1013$ | $433,503,557,877$ | $0.17664$ |

For example, omitting $61,307$ gives rounded candidates $60.99921,307.02242$ respectively. This pair is central. Form $Q$ by replacing just $61$ by $947$ in the unsigned pool. In each pool all endpoints are primes in range, the starts are at least $50$ apart, both lists have full privacy, and no starts approach the opposite support at $R_*$. The shift is mass-rich: Even the four starts $61,131,191,251$ together with $307,367,433,503,557,613,677$ contribute more than $1/4$ to $A$.

Let $S(V)$ sum **all ordered gated terms** on the unsigned pool $V$, using $T(a)T(a')\cos(a-a')$ with both actual $|y|\le8$ cuts. For either joint radius, putting $c(V)=2(3!\,4!)^2\prod_{p\in V}w_p$ gives
$$
 59<S(P)/c(P)<60,\qquad -15<S(Q)/c(Q)<-14.
$$
Thus signs can differ even with fifteen of sixteen starts held fixed. The negative total offsets only about $3.5\%$ of the positive one *in original weights*: The factor $c(Q)/c(P)=w_{947}/w_{61}$ is about $0.1404$. This example does not contradict [relative isolation](joint-pool-isolation.md), which allows exceptional central sources and bounds a mass fraction only as $t\to\infty$.

## Finite certificate

Run `python3 .godel/bob/check-adjacent-pools.py`. Here is why its integer filter and error bounds suffice. Put the least start in the first plus block and the least remaining start in the second plus block, to enumerate unordered block pairs modulo the two sign reversals. For a plus four-set $A$ and a minus four-set $B$ write the ratio as $u/v$, with $u=\prod_{p\in A}(p+d)\prod_{p\in B}p$ and $v$ the reversed product. If either orientation contributes, then $|y|\le8$ and $|a|<2\pi$ force $|y|<6.29$. Since $126191<t<126192$, this implies the symmetric necessary condition $19000|u-v|\le\min(u,v)$. Only one joint split on $P$ and seven on $Q$ pass this coarse filter. Test both orientations of each block; their gates need not agree. For each designated positive $p$ the rounded candidate is
$$
 x=\frac{dup}{v(p+d)-up}.
$$
Require a positive denominator and $|p-x|<1/2$, tested by integer arithmetic (no ties). Such an $x$ automatically meets the size cuts here. If $i,j$ designated choices pass, there are $ij(3!\,4!)^2$ orderings for this pair of orientations, and interchanging the two copies gives the other factor of two. Gates are not replaced by a uniform success rate.

For numerical certification put $s=u/v-1$. On the filter $|s|\le1/19000$ so the $|ts|\le8$ cut passes in either orientation. Use $126191$ for $t$ and $3.14159$ for $\pi$. The first substitution changes $a=t(s-s^2/2)$ by less than $0.000053$, and the two substitutions together change $T(a)$ by less than $0.000011$. The argument of the difference cosine therefore changes by less than $0.000106$ before rounding it to the nearest $1/10000$. Its absolute value after rounding is less than $14$; the Taylor polynomial through degree $64$ has error at most $14^{65}/65!$. Since cosine is $1$-Lipschitz and the two tapers are in $[0,1]$, the total error per term is less than $1/5000$. All polynomial evaluations and the summed error intervals in the certificate use rationals.

**Decision.** Neither termwise positivity nor positivity of the entire unsigned-pool coefficient can exclude cancellation across pools in the actual arithmetic test. Conversely even the existence of a neighboring pool with negative total does not price the deficit at detector scale. This single-center witness gives no uniform supply of negative pool weight on the required shifts.

**How much can *all* one-start replacements pay?** At this same $q,d$, use $r=D^2$ and keep the displayed source $P$. Of its 107 admissible one-exchange neighbors, seven have positive pool total, four negative, and 96 exactly zero. In units of $c(P)$, the sum of **all four negative magnitudes** lies in $(20,20.2)$, versus $S(P)/c(P)>59$. Even allocating their entire weight exclusively to $P$ cannot pay $35\%$ of its pool total. Any allocation canceling all of $S(P)$ with negative pool totals at this shift has to obtain over $65\%$ from pools missing at least two starts. This prices capacity after grouping, not individual negative terms, and it does not assert that such an allocation exists.

Run `python3 .godel/bob/check-adjacent-pools.py --neighbors`. Trial division supplies every possible new start ($1099<X<1100$, $e^{-8}X<2$). Replace exactly one old start, require a gap of at least 50 from every retained start, and run the same ordered-split certificate to exhaustion. Each neighbor is generated exactly once, because its missing start and new start are unique. The normalizations differ: Multiply the interval for $-S(V)/c(V)$ by an enclosure for $w_s/w_p$ when $s$ replaces $p$. The checker cancels $X^{-1}$ and bounds each positive log factor with correctly rounded decimal logarithms widened by one representable step, then sums rational bounds. This is a finite obstruction even for a source **known to have** a negative neighbor; it is not the asymptotic relative-mass isolation theorem or a bound at the smaller radius.

**Full-shift follow-up.** At this same center and radius the unsigned family size lets us compute the entire signed observable, not just two coefficients, at other shifts. See [the full-shift balance and its limits](complete-shift-balance.md): Two shifts have no pair in both compact windows; at the first nonempty example, negative pool totals pay about 47% of the positive pool totals. Use this full-band fixture before selecting more examples by sign. It does not replace a weighted estimate over the required shifts.
