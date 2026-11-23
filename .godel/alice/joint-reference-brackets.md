# Counting two signed brackets at one actual reference

Fix the first incidence and its ordered constructed list at $g=1$. Use the [one-reference reduction](one-reference-lifts.md), with both modular discrepancy tests unchanged. Fix any occupied $d$ and an actual $c_0$ on it. Write $a_i=h_i(c_0)$, $\delta_i^0=\delta_i(c_0)$, $h_i=h_i(c)$, $s_i=a_i\delta_i-\delta_i^0 h_i$, and $\Delta=c-c_0$ in the integers. Use a common upper bound $U=q^{.665+o(1)}$ for the cofactors, all of which are $q^{.665+o(1)}$, and $S=2HU=q^{1.055+o(1)}$ for $|s_i|$. All counts are of actual endpoints, not the number of witnesses in a relaxed lattice. We show that the following deletions together cost $q^{.4675+o(1)}$ endpoints at this $d$, uniformly in the reference.

## One bracket divided by its common factors

For any positive $N\le q^{O(1)}$ fixed before the endpoint, either specified position costs at most the stated price under $|s_i|\le q^{.935} (s_i,N)$. In particular take $N=d a_i |\delta_i^0|$. These factors are pairwise coprime by reference-row primitivity. The lift $qs_i\equiv F_i h_i a_i\Delta\pmod d$ has unit coefficients, and reduction of $s_i$ modulo $a_i$ and $|\delta_i^0|$ gives

$$(s_i,N)=(\Delta,d)(h_i,a_i)(\delta_i,\delta_i^0).$$

Thus even a product of three individually small overlaps is useful. After this deletion, both $s_i$ are nonzero and each $(h_i,a_i)<S/q^{.935}=q^{.120+o(1)}$.

**Proof.** Drop $i$, put $T=q^{.935}$, and enumerate $f\mid N$ at divisor cost. Impose $f\mid s$ and $|s|\le Tf$. With $A=(a,f)$ we have $A\mid h$ since $(a,\delta^0)=1$. Fix such an $h$. Put $m=f/A$; the allowed $\delta$ are in one class $\rho+mj$. Intersecting $|\delta|\le H$ and $|a\delta-\delta^0 h|\le Tf$ restricts $j$ to an interval of half-width at most $K=\min(H/m,TA/a)$. For $K<1$, the row congruence fixes $c\bmod d$ in $O(1)$ ways, costing $O(X)$ ordinary numerators. Otherwise put $V=ZK/d$. The affine strip

$$Fh c\equiv q(\rho+mj)\pmod d,\qquad Z/X<c\le Z$$

has at most $q^{o(1)}\sqrt V$ smooth numerators coprime to $d$. Here are the details needed to apply the [translated-strip argument](one-reference-lifts.md) when $m$ is not a unit. The difference lattice has index $d$ because $Fh$ is a unit modulo $d$. Filtering by $l\mid c$ multiplies this index by $l$ for $(l,d)=1$, by CRT. All smooth divisor filters of an actual numerator, and their divisors, meet this condition. A nonzero vertical difference has $j$-length at least $d/(d,m)>2H/m$; a horizontal difference has $c$-length at least $d$.

Cross $64V$ strictly with a smooth divisor $l\mid c$ (possible since $64XV<Z/X$). For each filter all points are collinear by the difference determinant bound $8ZK<ld$. Singleton filters cost $q^{o(1)}\sqrt V$. Otherwise let $v$ be the line direction primitive in the unfiltered difference lattice, and $k=l/(l,|v_c|)$ the filtered step multiplier. We have $v_c\ne0$ and $k\le R=\min(2Z/|v_c|,2K/|v_j|)\le 2V$, ignoring the second entry for a horizontal direction. Dyadically fix $L\le R/k<2L$, $L\ge1$. For fixed $k,L$ cross $8V/(kL)^2$ strictly with a divisor of $l/k$ (one suffices below one); $l/k>64V/k$ ensures existence. There are $q^{o(1)}(1+\sqrt V/(kL))$ such choices. Each divides $v_c$, so two directions in the centred box of half-widths $(2Z,2K)/(kL)$ have determinant strictly smaller than their required lattice index. This fixes $v$ up to sign, and $l/k$ is a divisor of $|v_c|$. At each recovered filter the smooth values on the line cost $q^{o(1)}\sqrt L$: Divide the numerator progression by the gcd of its coefficients, count reduced values $\le 2L$ directly, and otherwise choose a smooth divisor in $(2L/X,2L]$ coprime to the reduced step. Each divisor leaves $O(X)$ parameters. Summing $\sqrt L(1+\sqrt V/(kL))$ over smooth $k\le2V/L$ costs $q^{o(1)}\sqrt V$ by the half-power smooth count and the harmonic sum. This proves the strip bound uniformly in its translate. Summing over smooth multiples $h$ of $A$ costs at most $q^{o(1)}\sqrt{U/A}$. Since $K\le TA/a$ and $Z/d\le X$, the nontrivial strip case costs $q^{o(1)}\sqrt{UT/a}=q^{.4675+o(1)}$; the case $K<1$ costs less.

## A common direction for the two remaining brackets

Let $r=(s_1,s_2)>0$, $v_i=s_i/r$, $e=(r,d)=(\Delta,d)$, $D=d/e$, $b_i=(v_i,a_i)$, and $b=b_1b_2$. Form the *signed* vector and quotient

$$n=(h_2 v_1,h_1 v_2)/b,\qquad k=(F_2a_2 n_1-F_1a_1 n_2)/D.$$

We may delete the union of the following two subsets at the same local price:

$$\frac{e|v_1v_2|}{b^2}\le q^{.660},\qquad\text{or}\qquad \frac{\max(1,|k|)\min(|v_1|,|v_2|)}{b}\le q^{1.715}.$$

The first cut uses both bracket lengths; the second can act even when both are large. The signed $k$ is integral. In fact, writing $t=(x_1 y_2-x_2 y_1)/q$ on the endpoint and $t^0$ on the reference gives $rbk=e(a_1a_2t-h_1h_2t^0)$ by the two ordinary row identities.

**Vector and lattice.** Row primitivity gives $(\delta_i,h_i)=(\delta_i^0,a_i)=1$, so $(s_i,h_i)=(s_i,a_i)=(h_i,a_i)$. In particular $(v_i,h_i)=b_i$. Put $g_i=h_i/b_i$, $u_i=v_i/b_i$. Then $n=(g_2u_1,g_1u_2)$ with $(g_i,u_i)=(u_1,u_2)=1$; its exact content is $j=(g_1,g_2)$. By the [successive row construction](shared-row-labels.md), the second cofactor's part supported on the first row is below $q^{.115}$, hence $j<q^{.115}$ and $(a_1,a_2)<q^{.115}$. Eliminating the same $\Delta$ between the two lift congruences and cancelling $r$ leaves

$$F_2a_2 n_1\equiv F_1a_1 n_2\pmod D.$$

Indeed $b$ is a unit modulo $d$; the same holds for $j$ since it divides a row cofactor. Thus $w=n/j$ is ambient primitive in this index-$D$ lattice. Both coordinates are nonzero.

**Filter before enumerating $w$.** Fix $e\mid d$, $b_i\mid a_i$, and dyadic sizes $|v_i|\asymp L_i$. In the original coordinates the rectangle for $n$ has area divided by covolume at most a constant times

$$E_1=U^2 L_1L_2/(D b^2).$$

Alternatively fix $\max(1,|k|)\asymp Q$ and choose $i$ with smaller $L_i$. The linear change $n\mapsto(n_i,k)$ gives lattice covolume $F_i a_i$: Its determinant has absolute value $F_i a_i/D$. The rectangle in these coordinates has relative area $O(E_2)$ with

$$E_2=U L_i Q/(b F_i a_i).$$

This includes $k=0$. Use the corresponding box pulled back to $n$-space so primitivity is always tested in the original coordinates. Under the respective cuts $E=E_1$ or $E_2$ is at most $q^{.935+o(1)}$: The exponents are $1.330-1.055+.660$ and $-.780+1.715$. Constant dyadic losses are immaterial.

Fix smooth $j<q^{.115}$. The pulled-back centred body for $w$ has relative area $O(E/j^2)$. The smooth product $p=(g_1/j)(g_2/j)$ provides a divisor filter: Cross $C E/j^2$ strictly with a divisor $l\mid p$ for a sufficiently large absolute $C$ (use one below one). The crossing exists for large $q$, since

$$E/(g_1g_2)\le q^{.935-1.330+.240+o(1)}=q^{-.155+o(1)}$$

by the first deletion, which bounds $b\le q^{.240+o(1)}$. Split $l$ according to its two factors in $p$ and impose the corresponding coordinate divisibilities on $w$. Their index cost is exactly $l$ on top of $D$: After substituting both coordinate multiples the congruence is still surjective modulo $D$, since both multipliers are units. The determinant of any two allowed vectors is now strictly smaller than the joint index in absolute value (a centred parallelogram bounds the determinant by a constant times its area). Thus all are collinear through zero, with at most two primitive $w$ per split. Counting smooth filters and their splits costs $q^{o(1)}(1+\sqrt E/j)$, not a full enumeration of $g_1,g_2$. Summing over smooth $j$ costs $q^{o(1)}(q^{.0575}+\sqrt E)$, within the local price.

**Recover actual endpoints.** At fixed $n=jw$ recover $g_i,u_i$ from divisors of its nonzero coordinates, hence $h_i,v_i$, at subpower cost. The two conditions $r v_i\equiv-\delta_i^0 h_i\pmod{a_i}$ and $e\mid r$ give either no class or one class modulo $e\operatorname{lcm}(a_1/b_1,a_2/b_2)$, since $(d,a_1a_2)=1$. It has $O(1)$ representatives in $1\le r\ll S/\max L_i$: The length divided by modulus is at most a constant times

$$\frac{S (a_1,a_2)b}{e\max(L_1,L_2)a_1a_2}\le q^{1.055+.115+.120-1.330+o(1)}.$$

Here $\max L_i\gg\sqrt b$ since $b_i\mid v_i$. Once $r$ is fixed, the lift fixes $\Delta\bmod d$, with $O(X)$ ordinary numerators. No relaxation modulo $q$ identifies different integer shifts. The list and column fix their rows.

## What is still needed

Summing these deletions for one actual reference per occupied $d$ costs $q^{.5275+.4675+o(1)}$. In an all-references count subtract the extra $O(q^{.4675+o(1)})$ outgoing allowance at each reference **before squaring** the positive residual fiber size, as in the [simultaneous-cut proof](simultaneous-output-cuts.md). Neither accounting proves scarcity on the complement. For example, the exponent ranges with $r=e=b=1$ and both brackets of order $q^{1.055+o(1)}$ need not satisfy either direction cut; this is a parameter test, not an existence claim. At those widths $E_1=q^{2.385+o(1)}$, even larger than the whole available cofactor product of size $q^{1.330+o(1)}$. Extending the same centred determinant sieve at the local target would require effective relative area at most $q^{.941-\eta+o(1)}$ for some fixed $\eta>0$, not just recovering cofactors after enumerating vectors. One remaining source of information is the pair of residue conditions modulo $a_i$ used only at scalar recovery: At $r=1$ they already prescribe $v_i\bmod a_i$ once $h_i$ is known. Exploiting these without paying the full $q^{.665+o(1)}$ enumeration of both cofactors per denominator remains open.

**After Work:** The [reference residue test](reference-projection-review.md) computes the projected index in the hard box and gives a bounded cofactor product to test instead. The [raw-gap lcm cut](masked-gap-lcm.md) costs the same local allowance for one prime set fixed across the counted endpoints. Neither bounds the remaining occupancy.
