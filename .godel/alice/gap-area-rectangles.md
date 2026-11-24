# Which common-denominator counts can help?

Use the [fixed-list simple graph and reciprocal deletions](same-input-second-bracket.md) at $g=R=j=1$. Write $V,D$ for the sets of complete first inputs and denominators. Their size exponents are $.860,.5275$, respectively. The objective is a power saving below $.998$ for the edge count $I$. There are two quite different uses of input pairs.

**A pointwise bound on their common denominators is not enough as stated.** Even a bound of **two** does not suffice from these sizes alone. For an arbitrarily large scale prime $q$, choose a prime $p\asymp q^{.360}$ (Bertrand). Use a subset of $\mathbb F_p$ of size $\lfloor q^{.1675}\rfloor$ as evaluation sites. Denominators in this abstract example are site/value pairs. Inputs are the polynomials $a x^2+b x+c$ with $a$ in a set of $\lfloor q^{.140}\rfloor$ elements and $b,c\in\mathbb F_p$. Join each polynomial to its evaluation at each site. Two distinct polynomials agree at no more than two sites. The two vertex exponents are exactly the allowed exponents, but the edge exponent is $.860+.1675=1.0275$. This is a graph counterexample, **not** a configuration satisfying the smooth lift equations. In contrast, a bound of **one** forbids rectangles, so any two denominators also share at most one input. That gives $I^2\le |V|(I+|D|^2)$ and an exponent at most $.9575$. It is repeated coincidences, not all common denominators, that matter in this reversal.

## Delete small gap areas before counting rectangles

Fix distinct ordered $d,e$. Let $t_{de}$ count their shared inputs surviving the reciprocal same-input tests. One may also remove the one-reference and chosen-translate classes from the linked note, charging at most $q^{1.134+o(1)}$ to the triple count, but need not do so. At each shared input $v$ write $Y=(y_d,y_e)$ for the first outputs' complements and $b=(b_d,b_e)$ for their signed gaps:

$$v=d y_d+qb_d=e y_e+qb_e,\qquad G=(y_d,y_e),\quad k=(|b_d|,|b_e|),\quad g_*=(d,e).$$

Use primes for a second input at the same pair. Let $A=\det(b,b')$ and $L=\det(Y,Y')/q$. The integrality of $L$ follows from $dy_d\equiv ey_e\pmod q$ at both inputs and $q\nmid e$. Then

$$de L=v(b'_d-b'_e)-v'(b_d-b_e)+qA.$$

Both inputs are multiples of $F_1$, and $(F_1,qde)=1$: Each first input is coprime to its incident output products. Thus fixed $A$ fixes $L\bmod F_1$. Also $eL=y_d(b'_d-b'_e)-y'_d(b_d-b_e)$; $|b_i|\le H=q^{.390+o(1)}$, $y_i\in[A_-,A_+]$ of exponent $1.445$, and $e=q^{1.055+o(1)}$. Hence $|L|\le q^{.780+o(1)}$ and fixed $A$ costs at most $q^{o(1)}$ possible $L$, using $F_1>W=q^{.780+o(1)}$. Strict domination of this entire range by $F_1$ is unnecessary.

Fix the unprimed input as reference and require $G\le G'$. If $L=0$, the reduced output ratio agrees with the reference, so there are only $q^{o(1)}$ inputs by the linked dyadic slope argument. If $L\ne0$, $G'\mid L$ since $q\nmid G'$. Enumerate the divisors $G'$ at subpower cost. For each, the vector $Y'/G'$ is constrained by its determinant with the known primitive vector $Y/G$. All integer solutions, if any, differ by integer multiples of $Y/G$. The first-coordinate interval therefore gives $O(1+(A_+/A_-)G/G')=q^{o(1)}$ possibilities. The known $y'_d$ fixes $b'_d\bmod F_1$ from $d y'_d+qb'_d\equiv0$; $2H<F_1$ fixes the gap and then $v'$. Each $(v',d)$ is a single edge, not a free list realization.

Now $g_*\mid b_d-b_e$ and likewise at $v'$, since $q$ is a unit modulo $g_*$. Thus $g_*\mid A$; also $k\mid A$. They are coprime since any prime dividing $d,b_d$ would divide $d,v$, impossible. Consequently $|A|\le q^{.079}g_* k$ costs $O(q^{.079})$ possible signed multiples, including zero. Per reference it costs $q^{.079+o(1)}$ other inputs **in the stated orientation**.

Let $B_{de}$ count ordered distinct surviving input pairs with $L\ne0$ for which the small-area test fails at every reference of minimal $G$ (both on ties). The diagonal and the zero-determinant pairs are charged, and each small-area deletion may be charged in the cheaper orientation at cost at most a factor two for input order. Uniformly,

$$ t_{de}^2\le q^{.079+o(1)}t_{de}+B_{de},\qquad
 C=\sum_{d\ne e}t_{de}\le q^{1.134+o(1)}+q^{.5275+o(1)}\sqrt{B},\quad B=\sum_{d\ne e}B_{de}.$$

Indeed $t_{de}\le q^{.079+o(1)}+\sqrt{B_{de}}$, and there are at most $q^{1.055+o(1)}$ ordered denominator pairs. The inherited estimate $I\le q^{.9965+o(1)}+q^{.430+o(1)}\sqrt{C}$ (or with the optional charge added to $C$) gives

$$ I\le q^{.997+o(1)}+q^{.69375+o(1)} B^{1/4}.$$

**Sufficient job on the input-pair side.** Bound $B$ by $q^{1.217-\epsilon}$ for fixed $\epsilon>0$. Fixing ordered $v\ne v'$ first is legitimate here: Count ordered pairs of *distinct* common denominators with the reciprocal cuts, nonzero determinant, and large normalized area just derived. Without cuts the count is $\sum_{v\ne v'} u(v,v')(u(v,v')-1)$, with $u$ their common-denominator count. A uniform $u\le q^{.081-\epsilon}$ for small $\epsilon$ is not this estimate; even the abstract example above with $u\le2$ rules out the direct inference to $I$. No estimate of $B$ is established. Use the second successful row in all four incidences to test scarcity, or pursue the original triple bound directly. In neither order may the second-row costs be multiplied as independent densities.
