# Can one-sidedness or conductor sampling hide a principal peak?

Fix $A=9/5$ and let $q$ range over conductors of primitive real characters. At the larger height $y=q^{3/5}$ in the [nonresonant test](resonant-endpoint-heights.md#what-remains), the answer to the title question is **no for a uniform fixed-margin estimate**. In fact, writing

$$S_X(u)=\frac1X\sum_{p<X}\log p\,\log(X/p)\,p^{iu},\qquad X(u)=(3\log(u/2))^2\quad(u>2),$$

we have the unconditional identity

$$ L:=\limsup_{q\to\infty}\Re S_{(A\log q)^2}(2q^{3/5})
     =\limsup_{u\to\infty}|S_{X(u)}(u)|. \tag{1} $$

Thus a uniform gap below $47/81$ in the named one-sided mean requires the same gap in a continuous maximum modulus problem. But the threshold for excluding an *actual endpoint failure* by a uniform principal bound need not be as low as $47/81$. Failure along an unbounded sequence implies $L\ge s_*=0.58664126\ldots$, by testing the first and third harmonics together. This is stronger than $47/81=0.58024691\ldots$. Neither lower bound is asserted unconditionally for $L$.

## Rotate first, then sample

For fixed $X$ put $D=\log X$ and $F(v)=e^{-ivD}S_X(v)$. Chebyshev's $\vartheta(w)=\sum_{p\le w}\log p\ll w$ gives

$$ |F'(v)|\le X^{-1}\sum_{p<X}\log p\,\log^2(X/p)=\frac2X\int_1^X\vartheta(w)\log(X/w)\,\frac{dw}{w}\ll1. $$

The uncentered sum has derivative $O(D)$ since its positive weight mass $M_X$ is $O(1)$ (indeed $1+o(1)$ by PNT). Cutoff variation costs $O(|\Delta\log X|)$ uniformly in frequency: As a function of $r=\log X$, each weight $e^{-r}\log p\,(r-\log p)_+$ is continuous, and the sum of absolute derivatives is at most $e^{-r}\vartheta(e^r)+M_{e^r}$ away from entries. Integrate across entries as well.

Now fix $u\to\infty$, $X=X(u)$, and choose $|\delta|\le\pi/D$ with $e^{i\delta D}S_X(u)=|S_X(u)|$ (zero needs no rotation). The centered derivative bound gives $S_X(u+\delta)=|S_X(u)|+O(1/D)$. Put $x=((u+\delta)/2)^{5/3}$. Every odd squarefree integer $q>1$ is an admissible conductor since one of $q,-q$ is a fundamental discriminant. For $0<H\le x$ their count in $(x,x+H]$ is

$$ \frac4{\pi^2}H+O(x^{1/3}+H/x^{1/3}). \tag{2} $$

Indeed expand $\mu^2(n)=\sum_{d^2\mid n}\mu(d)$ for odd $n$. Odd $d\le R=x^{1/3}$ give $H/(2d^2)+O(1)$ before weighting; extending the main term costs $O(H/R)$ and gives the odd Euler product. For $d>R$ write $n=md^2$; summing $O(1+H/\sqrt{mx})$ over $m\le 2x/R^2$ costs $O(x/R^2+H/R)$.

Taking $H=Cx^{1/3}$ with large fixed $C$ supplies a conductor whose height $v=2q^{3/5}$ differs from $u+\delta$ by $O(x^{-1/15})$. At the frozen cutoff the extra cost is $O(Dx^{-1/15})$; replacing $X(u)$ by $X(v)$ costs $o(1)$ since $(\log X(u))'=2/(u\log(u/2))$. This proves the nontrivial direction of (1). The other follows from $X(2q^{3/5})=(A\log q)^2$ and $\Re z\le |z|$. The proof samples all admissible conductors, not only primes.

More quantitatively, if $|S_{X(u)}(u)|>47/81+\eta$ with $\eta>0$ fixed, use $H=c_\eta x^{2/5}/D$ in (2). The uncentered phase error throughout this interval after rotation is $O(DHx^{-2/5})=O(c_\eta)$ and the moving-cutoff error is $o(1)$. For small $c_\eta$ and sufficiently large $u$, this gives $\gg_\eta x^{2/5}/D$ conductors with named real mean $>47/81+\eta/2$, all within $O_\eta(x^{2/5}/D)$ of $(u/2)^{5/3}$. This counts necessary prime-mean peaks, not failing twists.

## If the first harmonic barely passes, price the third

Keep the larger witness $y=q^{3/5}$ and $X=(A\log q)^2$. Take the probability on primes given by the weights of $S_X$ divided by $M_X$. Put $U=|\cos(y\log p)|\in[0,1]$, and $c_j=\mathbb E T_{2j}(U)=\Re S_X(2jy)/M_X$, where $T_n(\cos v)=\cos(nv)$. Failure at its own cutoff forces $\mathbb EU\ge8/9-o(1)$ by the [endpoint identity with Gamma](endpoint-zero-packets.md#spend-the-gamma-margin) and the modulus bound on real character values. In particular $c_1=2\mathbb E U^2-1\ge47/81-o(1)$.

Let $a\in(0.85,0.87)$ be the unique root there of $(1+a)(1+(4a^2-1)^2)=9$, and set $s_*=1-2(1+a)/9$. We claim

$$ \max(c_1,-c_3)\ge s_*-o(1),\qquad c_1\le7/12+o(1)\ \Longrightarrow\ c_3\le-791/1024+o(1). \tag{3} $$

It suffices to prove the assertions with $\mathbb EU\ge8/9$ and no errors, by weak compactness of probability measures on $[0,1]$ and continuity of all the moments used. Put $d=1-\mathbb EU\le1/9$. If $d=0$, both moments equal one and the second premise is false. Otherwise tilt the law by $(1-U)/d$ and call its new mean $b$. Since $1-T_2(u)=2(1-u)(1+u)$ and $1-T_6(u)=(1-T_2(u))(4u^2-1)^2$, we have

$$ c_1=1-2d(1+b),\qquad 1-c_3\ge 2d(1+b)(4b^2-1)_+^2. $$

For the second inequality use Jensen on the convex minorant $(1+u)(4u^2-1)_+^2$: The positive part is nonnegative, increasing, and convex on $[0,1]$, as is its square; multiplication by the nonnegative increasing affine factor preserves convexity there.

If $c_1\le s_*$, then $1-c_1\ge2(1+a)/9$ and $d\le1/9$ force $b\ge a$. Thus $1-c_3\ge(1-s_*)(4a^2-1)^2=1+s_*$. The same argument for $c_1\le7/12$ gives $b\ge7/8$ and $1-c_3\ge(5/12)(33/16)^2=1815/1024$. This proves (3). The constant $s_*$ is **sharp for these two signed moments of an abstract law**: Put mass $1/(9(1-a))$ at $a$, the rest at one. Then $d=1/9$, the tilted law is a point mass, and $c_1=-c_3=s_*$. No realizability by prime phases is assumed.

At $6y$, $\log X(6y)-\log X=O(1/\log q)$, so the moving cutoff costs $o(1)$ there too. Now (3) and (1) imply the asserted lower bound on the common limsup in the event of infinitely many failures. Locally (3) also strengthens the [zeta packet test](endpoint-zero-packets.md): For every fixed $c>0$ with $\cosh c<3s_*$, at least one of $2y,6y$ must have $B_\zeta(\cdot;c)\gg_c X^{1/8}$ at a high failure. Indeed both pole terms are $o(1)$ and the near-line costs at both heights are $\cosh(c)/3+o(1)$. In the branch $c_1\le7/12+o(1)$, the packet at $6y$ is necessary even for $\cosh c<3\cdot791/1024$. This uses the same external strip hypothesis as the packet estimate; (1) and the moment comparison do not use it.

## What averaging would and would not decide

For comparison the [ambient quadratic floor](local-quadratic-twists.md) already controls all of these small twists simultaneously for all but $O_\varepsilon(Q^{1/2+\varepsilon})$ real primitive bases of conductor $Q\le q\le2Q$. Apply that result with its base equal to $1$ and radius $R=2Q(A\log(2Q))^{2\theta}$: Every allowed primitive product has conductor $c=q|d|\le R$. The theorem's parameter $F=1$ and fixed $A$ satisfy its size condition eventually. Each exceptional product character has at most $O((\log Q)^{2\theta})$ preimages as base/twist pairs, since choosing $d$ recovers the base by primitive induction. Apply the ambient bound with a smaller epsilon and absorb all polylogarithms. This even gives a compact-window floor at the individual product cutoff away from that base exception set. It does not bound the height-only principal mean for an exceptional base, or imply that a principal peak makes a product exceptional.

**Remaining decision.** A bound $L<s_*$ suffices to exclude the named failure, not to exclude the weaker necessary condition by itself. Alternatively, in a near-threshold first-harmonic branch, one can attack a *large negative* third harmonic, not an unrestricted second product-character mean. No estimate here supplies the needed uniform gap, and no actual failing endpoint, zeta packet, or unrestricted floor at an individual exceptional base has been established.
