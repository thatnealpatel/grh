# Discard joint repeats and power gaps at one prime

Use the [height-adjusted pair test](fixed-window-height.md) at $A=2.1$, $\nu=5/2$, with $t=1.11$ or $1.2$. Fix a sufficiently large prime $q$, $L=\log q$, $B=\log L$, the test's $X\sim(2.1L)^2$, $k=\lfloor(5/2)L/\log X\rfloor$, $N=X^k$, $T=q^t$, and $H=2N/(qT)$. Count ordered distinct **values** $n,m$, each a product of $k$ primes in $[X/B^4,X]$, with $q\mid n-m$ and $|n-m|/q\le H$. Put $g=(n,m)$, $u=n/g$, $v=m/g$, $h=|u-v|/q$, and $e(y)=y/\operatorname{rad}(y)$. Thus $h\ge1$ is integral and $gh\le H$. We give two cuts that include all gcds. Neither bounds the remaining pairs.

## Normalize the full gap by the joint repeat factor

For $S\ge1$, the number with $|n-m|/q\le S e(nm)$ is $\ll q^{o(1)}\sqrt{NS}$. This includes the [previous cut](sparse-pair-gap.md#also-discount-repeated-factors-on-both-sides) $h\le S e(u)e(v)$ since

$$e(nm)=g\,e(g)F_g(u)F_g(v),\qquad F_g(y)=e(gy)/e(g)=e(y)\gcd(\operatorname{rad}g,\operatorname{rad}y).$$

Here the first identity uses $(u,v)=1$. In particular, the same result with $S=\max(1,H/R)$ bounds all pairs with $e(nm)\ge R$; there is no independent large-repeat conjecture.

For fixed $g$, the count of $X$-smooth $y\le z$ with $\Omega(y)\le k$ and $F_g(y)\ge U$ is $\ll q^{o(1)}\sqrt{z/U}$ (zero if $z<U$). Fix $s=\gcd(\operatorname{rad}g,\operatorname{rad}y)$ in at most $2^k$ ways. The remaining radical is $X$-smooth and at most $z/U$, so the [half-power Rankin bound](sparse-pair-gap.md) applies. Once $\operatorname{rad}y$ is known there are at most $2^k$ exponent lists, including the case $y=1$. All losses are uniform: $\prod_{p\le X}(1-p^{-1/2})^{-1}=q^{o(1)}$ and $2^{O(k)}=q^{o(1)}$.

Orient by $F_g(u)\ge F_g(v)$. Use dyadic lower endpoints $G,W,U,V$ for $g,e(g),F_g(u),F_g(v)$, and $J/2<h\le J$ with dyadic $J\ge1$. Put $Z=\min(V,\sqrt J)$. A divisor $w$ of $F_g(v)$ can be chosen in $[Z/X,Z]$ by multiplying its prime factors up to $Z$. Realize it as $F_g(d_0)=w$ for $d_0\mid v$: For $p^j\Vert w$ use $p^j$ when $p\mid g$ and $p^{j+1}$ otherwise. This gives $d_0\le w^2\le J$. Extend $d_0$ by factors of $v/d_0$ to get $J/X<d\le J$, $F_g(d)\ge w$. This is possible since $v\ge NB^{-4k}/H=q^{1+t-o(1)}>2H\ge J$ in every nonempty box.

The counts of $g$, of $u$ for fixed $g$, and of candidate $d$ for fixed $g$ are at most $q^{o(1)}$ times $\sqrt{G/W}$, $\sqrt{N/(GU)}$, and $\sqrt{J/Z}$, respectively. These follow from the preceding radical count, taking $g=1$ as the mask parameter when counting gcds, and absorbing $\sqrt X$. For each sign $d\mid u\pm qh$ fixes one residue for $h$ modulo $d$, so there are $O(X)$ partners. The resulting box count is

$$\ll q^{o(1)}\sqrt{NJ/(WU\min(V,\sqrt J))}.$$

If $V>\sqrt J$ the radical factor $U\ge V$ already bounds this by $q^{o(1)}\sqrt N$. Otherwise the normalized cut gives $J\ll SWUV$, proving the assertion after summing the $O((\log q)^5)$ boxes and both orientations.

## Gaps close to powers, including squarefree endpoints

Fix an integer $j\ge2$. Write $h=a r^j$ uniquely with $a$ free of $j$th powers. For $Q\ge1$, the count on $a\le Q$ is

$$\ll_j q^{o(1)}\sqrt N\,H^{1/(2j)}Q^{1-1/(2j)}.$$

Fix $n$ (at most $q^{o(1)}\sqrt N$ choices), $g\mid n$ (at most $2^k$ choices), and $a\le Q$. Omit $ga>H$; otherwise set $P=(H/(ga))^{1/j}\ge1$. Every candidate has $1\le r\le P$, and $v>P$ by the previous lower bound. Multiply factors of $v$ until first reaching $P$, obtaining $d\mid v$ in $[P,PX]$ (use $1$ if $P=1$). For fixed $d$, $u\pm qa r^j\equiv0\pmod d$. Since $(u,v)=1$, both $u$ and $qa$ are units modulo every admissible $d$. Each prime dividing $d$ exceeds $j$ for sufficiently large $q$. Modulo such a prime the resulting unit $j$th-power equation has at most $j$ roots; each lifts uniquely at every higher power since the derivative is a unit. Thus there are at most $j^{\omega(d)}\le j^k=q^{o(1)}$ classes by CRT, including the single class when $d=1$. Since $P\le d$, each class gives at most one positive $r\le P$, hence one partner per sign. The number of possible $d$ is $\ll q^{o(1)}\sqrt P$ by smoothness and Rankin, absorbing $\sqrt X$. Sum $\sqrt P\le H^{1/(2j)}a^{-1/(2j)}$ over $a\le Q$ to get the bound. It does not require gaps with small $a$ to be common, or the endpoints to have repeats.

**Decision at $t=1.11$.** Take $S=q^{.27}$ and, for $j=2$, $Q=q^{.05}$. Together the two discarded classes cost $q^{1.385+o(1)}$: The exponents are $1.25+.27/2$ and $1.25+.39/4+3(.05)/4$. For the same floor and exceptional fraction in the [height test](fixed-window-height.md), it now suffices to prove $O(q^{1.39-\xi})$ for some fixed $\xi>0$ on the joint residual

$$q^{.27}e(nm)<|n-m|/q\le H,\qquad h=a r^2,\quad a>q^{.05}\text{ squarefree}.$$

In particular $e(nm)<2q^{.12}$. Even for coprime squarefree products and squarefree $h\asymp H$, the existing row bound is $q^{1.445+o(1)}$, not a saving. A new estimate needs to count how often a smooth starting value has a smooth completion, not merely bound each row by its possible small divisors.

**At the original $t=1.2$.** Use $S=q^{.09}$ for the joint repeat cut, at cost $q^{1.295+o(1)}$. The square-gap estimate costs $q^{1.325+o(1)}$ even at $Q=1$, above the $1.30$ budget. It does remove gaps with small fourth-power-free part: For $j=4$ and $Q=q^{.01}$ the exponent is $1.25+.30/8+7(.01)/8=1.29625$. No saving on general large gaps, or cancellation up to $q^{1.2}$, follows.
