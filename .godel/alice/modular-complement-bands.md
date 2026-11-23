# Two cuts on modular complement ratios

Fix a constructed two-position list at graph $g=1$ and a first incidence. For the two estimates as stated here, fix one unit $A\bmod q$. Cut 2 at the application widths also allows a separate unit for each slot at each denominator, as proved below. For example $A=F_1$ tests $u=F_1c/d=y_1/h_1$ in $\mathbb F_q$. Write $Z=q^{1.055+o(1)}$ and $X\asymp(\log q)^2$. There are two different subcounts, each costing at most **$q^{.995+o(1)}$ actual partners**, even across unprescribed *real* ratios:

1. Count **every** partner on any denominator $d$ admitting integers $a,b$ with $0<|ab|\le q^{.880}$ and $da\equiv Ab\pmod q$. No interval or direction needs prescribing. After this cut, for two different numerators on the same remaining denominator with $0<|c-c'|<q$, one has $|c-c'|\,\|A(c-c')/d\|_q>q^{.880}$, where the norm is the absolute least residue.
2. For each possible second denominator $d$, prescribe one interval of radius $q^{.880}$ in $\mathbb Z/q$ for $Ac/d$. Its centre may depend on $d$, the list, and the first incidence. Count the partners whose modular ratio is in their denominator's interval. No closeness of their real ratios or restriction on their gap directions is needed. This cut does not charge other partners on the same denominator.

In both cases count smooth pairs $(c,d)$ in $(Z/X,Z]^2$, dropping even ambient primitivity for an upper bound. A column fixes its two rows on the [constructed list](shared-row-labels.md), so there is no cofactor multiplicity to restore. These are restrictions on the existing slope, not an additional charge for satisfying it.

## Count denominators before counting vectors

For $1\le U,B\le q^{O(1)}$ with $UB\le q^{1+o(1)}$, count smooth $Z/X<d\le Z$ admitting *some* nonaxis witness $0<|a|\le U,\ 0<|b|\le B,\ da\equiv Ab\pmod q$. The count is at most

$$q^{o(1)}\big(\sqrt B+\sqrt{ZUB/q}\big). \tag{1}$$

Use the fixed lattice $\Gamma=\{(n,b):n\equiv Ab\pmod q\}$, of index $q$ and with full first projection. Write $(da,b)=jw$ with $j\ge1$ and $w$ primitive **in $\Gamma$**. Put $k=(d,j)$. Then $k\le j\le B$, $k$ is smooth, and $d/k\mid w_n$. Let $E=ZUB/q$. For fixed $k$ the centred box for $w$ has half-widths $ZU/k,B/k$. Select a divisor $f\mid d/k$ crossing $\max(1,E/k^2)$ by successive smooth primes with overshoot at most $X$; use one at threshold one and use the whole $d/k$ if too small. Imposing $f\mid w_n$ multiplies the covolume by $f$. The area divided by this covolume is $4E/(k^2 f)$, at most four in the crossing case, and at most $4XUB/(kq)=q^{o(1)}$ as an upper bound in the whole-product case. In rank two the convex hull of the lattice points in the box has at most twice its normalized area plus two points by Pick. In rank one it lies on a line through zero and contains at most two base-primitive vectors. Thus per $k,f$ there are $q^{o(1)}$ candidate $w$, each giving $d/k$ at divisor cost from $w_n\ne0$. No enumeration of the nonsmooth content $j$ is required.

The half-power smooth count gives $q^{o(1)}(1+\sqrt E/k)$ choices for $f$. Sum the one over smooth $k\le B$ and the $1/k$ by the harmonic bound. This proves (1). Dyadically box $|a|,|b|$ for $|ab|\le P=q^{.880}$. Then $UB\le4P$, and $B\le2P$. The union costs $q^{o(1)}\sqrt{ZP/q}=q^{.4675+o(1)}$ denominators since $Z>q$. All smooth numerators on them cost a further $q^{.5275+o(1)}$ per denominator, proving cut 1. For the spacing statement take $b=c-c'$ and the least residue $a=A b/d$; neither is zero under the specified size condition.

## Translated modular bands, averaged over denominators

More generally, take widths $1\le L\le Z$, $1\le K<q/4$, and put $V=\max(1,LK/q)$, assuming $64XV<Z/X$. For each $d$ prescribe a translated interval of half-width $L$ for $c$ and a cyclic interval of radius $K$ for $u=Ac/d$. The total count is at most

$$q^{o(1)}\sqrt{ZV}. \tag{2}$$

Lift the cyclic interval to an integer interval, with at most one representative of a residue. The lattice in coordinates $(c,u)$ has determinant $q$ and full first projection. We give the details of transferring the [translated-strip sieve](adaptive-complement-interval.md) since the denominator varies and a horizontal direction is possible here. Select a smooth $e\mid c$ in $(64V,64XV]$. For each $e$, imposing $e\mid c$ gives covolume $eq>8LK$, so all filtered points in the rectangle lie on one affine line if there are at least two. Singleton cases over $e$ cost $q^{o(1)}\sqrt V$ for this $d$.

Let $v=(v_c,v_u)$ be the base-lattice primitive direction of such a line, up to sign. Then $v_c\ne0$ since a vertical difference would have size at least $q>2K$. The filtered step is $kv$ with $k=e/(e,|v_c|)$. For at least $m+1$ points, $|v_c|\le2L/(mk)$ and $|v_u|\le2K/(mk)$. At most one primitive direction has both coordinates bounded by $(L,K)/(2\sqrt V)$, by the determinant test. Except for that direction, $mk\le4\sqrt V$. Select a smooth divisor $f\mid e/k$ strictly exceeding $8V/(mk)^2$ with overshoot $X$, or take one if this threshold is less than one. It exists since $e>64V$. For each $k,f$, imposing $f\mid v_c$ puts the centred direction rectangle in rank at most one by the determinant test. There are at most two primitive $v$, and $e/k\mid v_c\ne0$ recovers $e$ at divisor cost. There are $q^{o(1)}\sqrt V/(mk)$ choices for $f$ (use $mk\le4\sqrt V$). Summing in $k$ and then over occupancy tails $m\ge1$ costs $q^{o(1)}\sqrt V$.

For the exceptional direction write $R=\min(2L/|v_c|,2K/|v_u|)$, dropping the second entry if zero in the denominator. For nonsingleton $e$, $k\le R$ and the parameter length on its line is at most $R/k$. A nonconstant integral affine function on a parameter interval of length $D\ge1$ assumes at most $q^{o(1)}\sqrt D$ positive smooth values in our range: Divide by the gcd of step and initial value, count reduced values up to $D$ directly, and for larger ones choose a smooth divisor in $(D/X,D]$. It is coprime to the reduced step, so fixes one class with $O(X)$ representatives. Apply this to $c$ on the filtered line. For $k$ in a dyadic block $[k_0,2k_0)$ there are $q^{o(1)}\sqrt{k_0}$ smooth $k$ and only divisor cost for $e/k\mid v_c$. Thus all exceptional lines together cost $q^{o(1)}\sqrt R$ for this $d$.

The ordinary term, and exceptional terms with $R\ll V$, sum to $q^{o(1)}\sqrt{ZV}$ by smoothness of $d$. A horizontal direction forces $q\mid v_c$ and $R\le2L/q\le2V$. Otherwise, in a dyadic block $Q\le R<2Q$ with $R>4V$ the nonaxis vector witnesses (1) with $U=2K/Q$, $B=2L/Q$. Empty blocks with a width below one do not contribute. Here $UB\le4qV/Q^2\le q^{1+o(1)}$. Multiplying (1) by $\sqrt{2Q}$ costs at most $q^{o(1)}(\sqrt L+\sqrt{ZV/Q})$. This proves (2), uniformly in all translations, without multiplying local smoothness heuristics. Taking $L=Z$, $K=q^{.880}$ yields $V=q^{.935+o(1)}$, hence exponent $.995$ for cut 2.

## Decision for the residual

The top-bin comparison multiplies each partner price by $q^{.780-.390+o(1)}$, giving $1.385$ for the indicated incidences only. For either cut the critical exponent replacing $.880$ is $.886$ (equality gives $.998$, not a fixed margin). Neither cut is an unrestricted count. In particular a tiling of the modular circle costs exponent $.995+.120=1.115$. Even with no short modular direction, a lower bound on spacing is not an upper bound on the number of occupied bands sufficient for the target. A test for the residual is whether the simultaneous identities $y_i/h_i=F_i c/d\pmod q$ restrict the actual values for $i=1$ to a dictionary of at most $q^{.003-\epsilon}$ such bands per $d$, or price the incidences outside it. Row uniqueness supplies no such cover. In fact the slots may be optimized on each whole denominator fiber; see the pointwise estimate below. No large-$S$, unrestricted cofactor average, all-gcd, or fixed-window conclusion follows.

## Full numerator width: Rotate each denominator separately

In cut 2 at $L=Z\ge q$, the exceptional average is unnecessary. If $v_u\ne0$, then $R\le2K\le2V$ by integrality. If $v_u=0$, then $q\mid v_c\ne0$ and $R\le2Z/q\le2V$. Hence the local proof above gives, for **each** $d$, uniformly in **both** the unit $A$ and the cyclic interval $I$ of radius $K=q^{.880}$,

$$\#\{Z/X<c\le Z:c\text{ smooth},\ Ac/d\bmod q\in I\}\le B,\qquad B=q^{.4675+o(1)}.$$

Indeed $64XV<Z/X$ at $V=ZK/q=q^{.935+o(1)}$. Thus the total covered by $s_d$ slots $(A,I)$ at each $d$ is at most $B\sum_d s_d$. The slots can be chosen after inspecting the entire fiber, even by maximizing coverage; a different slot for each tested partner is not free. A total budget $\sum_d s_d\le q^{.5305-\epsilon}$ suffices, not necessarily distributed equally. This does **not** change cut 1: Taking $A_d=d\bmod q$ there would give the short witness $(1,1)$ at every denominator. Nor have we dispensed with the exceptional average for arbitrary $L<q$.

**Test without constructing a dictionary.** Fix the first incidence and its list. At each occupied $d$, let $C_d$ be the numerators of the actual partners to be bounded, retaining the row conditions and any residual cuts. Put $n_d=|C_d|$, $D=\#\{d:n_d>0\}\le q^{.5275+o(1)}$, and $N=\sum_d n_d$. Count ordered pairs $c',c\in C_d$ on the **same denominator** for which both actual row discrepancies satisfy

$$\left\|h_i(c')\,y_i(c)/h_i(c)-y_i(c')\right\|_q>K,\qquad i=1,2.$$

The divisions are in $\mathbb F_q$: The eligible prime factors of $d,h_i,F_i$ are smaller than $q$. Write $P$ for this pair count. For each anchor $c'$ take $A_i=F_i h_i(c')$ and center $y_i(c')$. Then the discrepancy is the least-residue norm of $A_i(c-c')/d$, by the two row identities. At most $2B$ choices of $c$ fail one or both inequalities, by applying the **local** estimate once per row with the anchor fixed. Varying the anchor here costs its multiplicity: We are counting pairs, not covering all columns with two slots. The fixed list and column determine the rows, so no cofactor multiplicity enters. Consequently

$$P\ge\sum_d n_d(n_d-2B)_+\ge\sum_d (n_d-2B)_+^2,\qquad N\le 2BD+\sqrt{DP}.$$

The last step is Cauchy-Schwarz. Thus an upper bound $P\le q^{1.4685-\delta+o(1)}$ uniformly per first incidence for fixed $\delta>0$ would suffice: The two terms cost $.995$ and $.998-\delta/2$ in the exponent; the resulting saving is $\min(.003,\delta/2)$ before subpower factors. The target is for actual pairs with both discrepancies large, not independent costs for the two rows. No such upper bound is proved. The [handoff replay](band-handoff-review.md) records why the pointwise bound matters here.
