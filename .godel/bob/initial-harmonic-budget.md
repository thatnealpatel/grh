# How many initial harmonics does a real endpoint need?

In [Alice's single-twist endpoint test](../alice/single-endpoint-harmonics.md), write $K=2/\pi$, $1<A<\pi/2$, and $\Delta=1/A-K$. For $n\ge2$ put

$$ C_n=\frac{1}{n\sin(\pi/(2n))},\qquad L_n=(1-1/n)C_n. $$

If $C_n<1/A$ and $L_n\cosh c\le1$ for fixed $c>0$, a failure at $|y|\ge Y$ forces $\max_{1\le j<n}B_\zeta(2jy;c)\gg_{A,n,c} X^{1/8}$ for a sufficiently large fixed $Y$. The twist and own-cutoff failure are exactly Alice's. Here $X=(A\log q)^2$ and, under the same external zeta $7/8$ strip, $B_\zeta(t;c)$ counts zeros with $|\gamma-t|\le X^{3/8}\log X$ and $\beta>1/2+c/\log X$, with multiplicity and weight $(1+(\gamma-t)^2)^{-1}$. In particular this works for $K\cosh c\le1$. As $A\uparrow\pi/2$ the number of ordinates needed is $O(\Delta^{-1/2})$, rather than the $O(\Delta^{-1})$ sufficient truncation length obtained by paying the absolute Fourier tail. This counts local estimates that would suffice, not elapsed research time. The parameters are fixed before $q\to\infty$; the packet radius has not been reduced here.

## A sharp constant for degree less than $n$

Write $s=2v-\pi$ modulo $2\pi$, so the angular envelope $|\cos v|$ is $f(s)=\sin(s/2)$ on $[0,2\pi]$. The $n$ nodes $s_l=(2l+1)\pi/n$, $0\le l<n$, annihilate every nonconstant mode through $n-1$ on averaging. Their average of $f$ is $C_n$, by the finite geometric sum. Thus every degree-$<n$ trigonometric majorant has constant coefficient at least $C_n$.

To attain it, take $x=\cos(2v)=-\cos s$ and interpolate $g(x)=\sqrt{(1+x)/2}$ at the distinct $x_l=-\cos s_l$. Use value and derivative at each interior node, and just value at $x=1$ when $n$ is odd. There are $n$ conditions, none at $-1$. Let $P$ be the polynomial interpolant of degree at most $n-1$. The Hermite remainder for $g-P$ is $g^{(n)}(\xi)/n!$ times the product with those multiplicities. For even $n$ the derivative is negative and the product is a square; for odd $n$ the derivative is positive and the product has the extra factor $x-1$. Thus $g\le P$ on $(-1,1]$, including the interpolation nodes, and at $-1$ by continuity. The polynomial majorizes globally, with equality on the grid. The grid average therefore gives its constant coefficient exactly.

## The height cost of this same majorant

Write $p(s)=P(-\cos s)=C_n+\sum_{k=1}^{n-1}d_k\cos(ks)$. Not just the constant term matters: Each nonconstant mode also costs part of the Gamma margin. The coefficients are all negative in this shifted convention. More precisely, for $j=n-k$ and $z=\pi/(2n)$,

$$ d_k=\frac{(j-1/2)\csc((2j-1)z)-(j+1/2)\csc((2j+1)z)}{n^2}. $$

Indeed $p=f$ and $p'=f'$ at the nodes (at $s=\pi$ both derivatives vanish). For a grid function $h$, take its coefficient at $k$ to be $n^{-1}\sum_l h(s_l)e^{-iks_l}$. For half-integral $a$, the node average of $e^{ias_l}$ is $i\csc(a\pi/n)/n$. Set $U=\csc((2k-1)z)$, $V=\csc((2k+1)z)$. The coefficients of the sampled $f,f'$ at $k$ are respectively $F=(V-U)/(2n)$ and $G=-i(U+V)/(4n)$. Writing $p_m$ for the complex Fourier coefficients of $p$, aliasing on these nodes gives $F=p_k-p_{k-n}$ and $G/i=(k-n)F+np_k$. Hence $d_k=2p_k$ has the stated value, reflecting the cosecants about $\pi/2$. This also works at $2k=n$. Since $x/\sin x$ increases strictly on $(0,\pi)$, each $d_k<0$, and telescoping gives $\sum_{k=1}^{n-1}|d_k|=L_n$. In fact $L_n<K$: Concavity gives $\cos u\ge1-2u/\pi$ on $[0,\pi/2]$, so $\sin z\ge z(1-1/(2n))>z(1-1/n)$.

## Transfer and scope

Let $r=\log(2+|y|)/\log q$. At failure, $(1+r)/A-o(1)\le h_d(y)\le\sum_{p<X}b_p|\cos(y\log p)|$ and $r=O(1)$. Integrate the majorant with these nonnegative weights of total mass $1+o(1)$. Shifting $s$ by $-\pi$ changes coefficient signs, not their absolute sum. Apply [the principal packet estimate](endpoint-zero-packets.md#price-the-part-near-the-critical-line) to each fixed frequency, with the pole bounded by $(1+4Y^2)^{-1}$ and $\log(2+|2jy|)=r\log q+O_n(1)$. For some fixed packet constant $C>0$ this gives

$$ C L_n X^{-1/8}\max_{j<n,\ j\ge1}B_\zeta(2jy;c)\ \ge\ (1/A-C_n)-\frac{L_n}{1+4Y^2}+(1-L_n\cosh c)r/A-o(1). $$

Choose $Y$ to spend less than half the positive constant margin. Since $C_n-K=\pi/(12n^2)+O(n^{-4})$, choosing $C_n-K\le\Delta/2$ lets one also take $Y=O(\Delta^{-1/2})$ as $\Delta\downarrow0$. For example, take $A=157/100$, $c=1/2$, and $Y=45$. Budget half of $\Delta$ for the angular error and a quarter for the pole. Here $C_{41}-K<0.000156<\Delta/2$, so **40** ordinates suffice. Alice's absolute tail $K/(2J+1)$ first fits the same half-budget at **1972** ordinates. Both estimates use the same cutoff, radius, and height floor. This comparison is per candidate height, not a list of fixed heights for every conductor.

Conversely, the grid lower bound shows the order $\Delta^{-1/2}$ in degree is necessary for a majorant with constant strictly below $1/A$. This is not a lower bound for arbitrary sparse sets of high frequencies or for other arithmetic tests. At $A=3/2$, $C_3=2/3$ is equality and $C_4<2/3$: Three ordinates suffice as [already known](three-ordinate-endpoint.md). That certificate has smaller coefficient mass $49/108$ and handles a larger $c$ there. The gain here is for the range of $A$, not a further reduction from three at that example. No individual packet upper bound is proved.

At the particular half-budget above, the [shifted-grid obstruction](exact-sparse-harmonic-count.md) now proves that 40 is optimal even in the number of arbitrarily chosen positive integer harmonics. It tests full-circle laws, not prime phases.
