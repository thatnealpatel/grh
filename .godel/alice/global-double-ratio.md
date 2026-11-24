# Count a double ratio across moving denominator pairs

Fix one actual constructed two-label list in $g=R=j=1$. Use the notation of [the twisted ratio](twisted-second-output-ratio.md):

$$v=cF_1a=dY+q\alpha=eY_0+q\alpha_0,\qquad cF_2h=dZ+q\beta,\qquad cF_2k=eZ_0+q\beta_0.$$

Here $d\ne e$ are ordered, $v$ is the complete first input, and the two primitive rows on each column are the actual ones identified by the list. All exponent estimates below allow $q^{o(1)}$ factors. Consider the *global* rational label

$$L=S/z=\frac{k Z Y_0}{h Z_0 Y}=N/M,\qquad z=Y/Y_0=n/w,\qquad S=kZ/(hZ_0)=x/y,$$

all displayed two-letter fractions $N/M,n/w,x/y$ being reduced. Both $S$ and $z$ equal $e/d$ modulo $q$ and differ relatively from $e/d$ by $O(q^{-1.110+o(1)})$. Hence $L\equiv1\pmod q$ and $L=1+O(q^{-1.110+o(1)})$ *without fixing any prefix*. We show how much it costs to forget both prefixes. This is a count of triples, not an estimate on independent gap events.

**Mask before changing fibers.** In the reciprocal deletions of [the shared-input count](same-input-second-bracket.md), at a fixed $v$ and actual reference take $P$ to contain all primes of its two rows and column. We may require $m=(dY)_P<q^{.118}$ for the other column, in both orders; the subscript means the full supported part. Indeed there are subpower many $m$ on this fixed support (there are $O(\log q/\log\log q)$ primes and at most that order of factors with multiplicities). For $m\ge q^{.118}$, select an eligible divisor $f$ of $dY/m$ such that $mf>2H$ by the first crossing, taking $f=1$ when $m>2H$. A crossing is available since $dY>2H$. Then $f\le\max(1,2HX/m)$ where $X$ bounds the eligible primes. Each $mf$ fixes at most one signed gap in $[-H,H]$ through $v-q\alpha\equiv0\pmod{mf}$, hence at most one $d$ by the sorted prefix. The smooth half-power price is $q^{.136+o(1)}$ per reference. Summing both orders costs that times the incidence count $I$, absorbed by the existing $q^{.1365+o(1)}I$ deletion. This argument makes the mask containing $k$ legitimate at the *smaller* $.118$ threshold; it does not infer this from a bound on the gcd of the two first outputs.

**Exact $z$ across the whole list.** First recover the primitive pair $(d',e')=(d,e)/D$, where $D=(d,e)$. The slope $e'/d'$ lies in an interval about $z$ of length $q^{-1.110+o(1)}$ (the ratios themselves are $q^{o(1)}$). Two distinct slopes in a bin $J\le d'<2J$ differ by at least $q/(4J^2)$ by their common residue. As $d'\le q^{1.055+o(1)}$, there are only subpower many primitive pairs. For each, $t=(d'n-e'w)/q$ is an integer and is nonzero: Otherwise $dY=eY_0$ would have two distinct deterministic prefixes. With $G=(Y,Y_0)$ one has $|DGt|=|\alpha_0-\alpha|\le2H$. Now $u=DG$ (not just $G$) and $\alpha$ are coprime by first-row primitiveness, and $d'nu+q\alpha\equiv0\pmod{F_1}$. In a bin $J\le u<2J$ the primitive slopes $\alpha/u$ lie in an interval of length $2H/J$ with spacing at least $F_1/(4J^2)$. This costs $O(1+HJ/F_1)=q^{o(1)}$ since $J\le2H$, $H^2/F_1=q^{o(1)}$ or smaller. Each solution gives $v=d'nu+q\alpha$ and only divisor-many splits of $u$. Thus each exact $z$ recovers at most subpower many ordered triples even with $d,e$ varying. Actual membership remains a test.

**Hidden factors in $L$.** Put $C_+=(n,x)$, $C_-=(w,y)$ and $J_0=C_+C_-$. Then $N=(x/C_+)(w/C_-)$ and $M=(y/C_-)(n/C_+)$. These are exact, including all multiplicities. From $L$ split its two reduced coordinates at divisor cost. Guessing $C_+,C_-$ then gives $z$, which suffices by the global recovery. Now $C_+\mid Y$ and $C_+\mid kZ$, so $C_+\le (Y,k)(Y,Z)$. The first factor is bounded by the enlarged reciprocal mask and the second by actual successive-row freshness $<q^{.115}$. The swapped argument gives the same price for $C_-$. Thus $J_0\le q^{.466+o(1)}$. In a dyadic bin $J\le J_0<2J$ the multiplicity of $L$ is only $q^{o(1)}\sqrt J$ by enumerating the smooth product and splitting. No supposition that all canceled primes are absent from $NM$ is needed.

**A global rank price.** Both $N$ and $M$ are at most $q^{3.555+o(1)}/J$ in the bin, from the original products $kZY_0,hZ_0Y$. For any two such $L$ the determinant divided by $q$ is integral and bounded by $Q=q^{5+o(1)}/J^2$, using the relative width about 1. Use a uniform upper bound including the subpower factors. Prescribe *one* affine valuation space of dimension at most $\lfloor(\log q)^{1.44}\rfloor$ for the whole list. Choose at most that many eligible pivot primes giving injection on the space restricted to the eligible coordinates of actual ratios (equivalently, on the affine span of its actual members). The [signed pivot sieve](output-path-packets.md) costs $q^{o(1)} Q^{.22}$ labels in the space in this bin. Indeed at exponent $\sigma=.22+1/\sqrt{\log\log q}$ the signed Euler factor on the pivots is $q^{o(1)}$ since the eligible primes are at least $(2.1\log q)^2/(\log\log q)^4$. Enumerate the absolute pivot product with signs up to $Q$, stopping at the next factor if it crosses $Q$; the extra signed prime costs subpower. In the noncrossing case projection gives uniqueness, and in the crossing case the shared signed factors have product $>Q$ dividing the inter-ratio determinant divided by $q$, so equality is forced.

Writing $J=q^s$, the price for *triples* in this stratum is therefore at most

$$q^{.22(5-2s)+s/2+o(1)}\le q^{1.12796+o(1)}\quad(0\le s\le .466+o(1)).$$

Sum over the logarithmically many bins. The $-2s$ matters: Paying the worst multiplicity on full-height labels gives $1.333$, not a saving. No $q^{1.055}$ pair count multiplies this estimate. Even a cover of the residual by $q^{.008}$ such spaces would fit the $1.136$ triple budget with a fixed margin. There is no proof of that cover. This global statement does not allow one space *per denominator pair* at the same price.

**Why the support-free reference 1 does not give coverage.** The exact label $L=1$ is already deleted: It means the same ratio $Z/(hY)$ on both columns at $v$, passing the same-input bracket. For $L\ne1$, $|N-M|/q\ge1$. With $A=(h,k)$, $K=(Z,Z_0)$, one has $N J_0=kZY_0/(AKG)$ by row primitiveness. On the residual $G\le q^{.118}$ by the reciprocal mask and $AK\le q^{.783+o(1)}$ by the [second-row escape](twisted-second-output-ratio.md) ($.665+.390-.272=.783$). Consequently

$$J_0\, |N-M|N/q\ \ge\ N J_0\ \ge\ q^{2.654-o(1)}.$$

In contrast, the usual divisor-before-vector bracket test against 1 at $|N-M|N/q\le T$ costs $q^{o(1)}\sqrt{TJ}$ triples in the bin (common residue and exact-label price above). To use this price at $q^{1.135}$ one sets $TJ=q^{2.270}$. Not one nontrivial escaping triple can pass this cut for large $q$. The issue is not whether the real quotient is close to 1; it is the height after all cancellations. A useful next count must address occupancy outside the global translates or exploit more than the bare bracket against 1, for example the simultaneous smooth multiples of the visible factors $n/C_+$ and $w/C_-$ dividing $v-q\alpha$ and $v-q\alpha_0$. Fixing $L$ does not give two independent congruences modulo $q$: The congruences $d n=e w$ and $d x=e y$ modulo $q$ agree after substituting $L\equiv1$. No unrestricted triple or column saving is proved here.

## A three-dimensional test on the visible split

There is a pointwise obstruction to attaining the hidden-factor price. Fix the visible split just described, with $P=n/C_+$, $Q_0=w/C_-$. They are coprime, prime to $F_1q$, and **both** at least $q^{1.212-o(1)}$. Indeed $GC_+\mid Y$, $C_+\mid kZ$. The factors of $GC_+$ on the reference support cost at most $q^{.118}$ altogether, since $G\mid Y_0$. The remaining part divides both $Y$ and $Z$, hence costs at most $q^{.115}$. This bounds $GC_+$ by $q^{.233}$, not $q^{.351}$; use the reciprocal direction for $GC_-$. Divide the lower row-output heights by these bounds.

Set $m=v/F_1$, $V=q^{1.720+o(1)}$ a uniform upper bound for $m$. Use the box of radii $(V,H,H)$ for triples $(m,\alpha,\alpha_0)$ in the lattice $\Lambda$ given by

$$F_1 m=q\alpha\pmod P,\qquad F_1m=q\alpha_0\pmod {Q_0}.$$

Each actual vector is primitive (already $(m,\alpha)=1$) and fixes $v,d,e$ by the sorted prefixes. The lattice index is $P Q_0$ by solving for the last two coordinates at each $m$. If there are three linearly independent lattice vectors in the box, *even non-actual ones*, the entire box costs $O(VH^2/(P Q_0))\le q^{.076+o(1)}$. To see the volume bound, take the sublattice generated by those vectors; in each coset the fundamental parallelepipeds at the points counted are disjoint up to boundary and fit inside four times the box. Multiply by the index of this sublattice in $\Lambda$. Rank at most one costs $O(1)$ primitive vectors.

In rank two take the primitive integral normal $(a,b,c_0)$ to the span, and let $g$ be the gcd of its values on $\Lambda$. Here $c_0$ is a plane coefficient, not an input prefix. Put $\lambda=P Q_0/g$ and

$$D_0=\sqrt{(aV)^2+(bH)^2+(c_0H)^2},\qquad R_0=VH^2/(\lambda D_0).$$

The index of the lattice in the primitive integral plane, relative to the latter, is $\lambda$: Take images under the primitive normal to factor the ambient index $P Q_0$. In particular $g\mid P Q_0$. The integral plane has covolume $\|(a,b,c_0)\|$ (adjoin an integer vector on which the normal is 1 and use its perpendicular height). Scaling to unit box radii thus gives the plane lattice covolume $1/R_0$, by the area scaling formula. Two independent vectors in the scaled unit box have parallelogram area at most 3.

**Select a smooth factor before paying plane area.** Let $j>0$ generate the image of the plane lattice under projection to $m$ (zero image gives no actual points). Select a divisor $f\mid m/j$ strictly crossing $3R_0$, or enumerate $m/j$ itself below the cutoff. If $3R_0<1$ the box cannot contain independent points. The selected divisor costs at most $q^{o(1)}(1+\sqrt{R_0})$ choices including the overshoot by $X$. In the below-cutoff branch fixing $m$ fixes its gaps since $P,Q_0>2H$. In the crossing branch the condition $f\mid m/j$ multiplies the plane covolume by exactly $f$, by surjectivity of the divided projection. No two independent vectors now fit; count primitive actual points. Using $m$ instead of $m/j$ here need not give the index multiplier. This test works without an initial smooth-factor payment to force rank at most two: Rank three has already been priced.

For $a=0$, write $(\alpha,\alpha_0)=t(c_0,-b)$ by primitivity of the normal. Then $m$ is one residue times $t$ modulo $P Q_0$ by CRT, $|t|\le H$, and $2VH<P Q_0$. The determinant of any two $(m,t)$ therefore vanishes; primitivity gives $O(1)$ vectors. For $a\ne0$ the lattice contains $(q,F_1,F_1)$, so

$$\ell=(qa+F_1(b+c_0))/g\in\mathbb Z.$$

If $\ell=0$, then $F_1\mid a$ and $R_0\le H^2/(\lambda |a|)\le q^{o(1)}$. Otherwise, using $|a|\le D_0/V$ and $|b|,|c_0|\le D_0/H$ gives

$$R_0\le\frac{q H^2+2F_1 V H}{P Q_0 |\ell|}\le q^{.466+o(1)}/|\ell|.$$

Consequently the global exact label costs at most $q^{.223+o(1)}$ triples *outside* the following split class (sum divisor-many splits): Rank two, $a\ne0$, $0<|\ell|<q^{.020}$, and $R_0>q^{.446}$. Even there $\lambda |a|<q^{.334+o(1)}$, and $qa\equiv g\ell\pmod{F_1}$ for a divisor $g$ of the known $P Q_0$. Near-saturation also requires $J_0>q^{.446}$ to exceed the same price in the hidden-factor count. These are requirements, not contradictions. At fixed $P,Q_0$ the width term $VH^2/(P Q_0)$ alone misses the entire plane contribution. At varying $P,Q_0$ even the pointwise $q^{.223}$ cost does not count the labels. One next arithmetic test is to bound the number of **occupied visible splits** with the small nonzero normal evaluation, rather than assigning every split a full-rank volume or interpreting the existence of a plane as a density saving.

**After-Work occupancy bound.** The [normal fraction count](normal-fraction-occupancy.md) charges all triples on exceptional splits with $|a|/\gcd(|a|,|\ell|)\le q^{.160}$ together at $q^{1.135+o(1)}$ per actual list. Its last paragraph gives the narrower remaining test. This does not bound the unrestricted residual.
