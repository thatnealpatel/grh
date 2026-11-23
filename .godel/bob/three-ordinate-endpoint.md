# Three ordinates suffice at $A=3/2$

In Alice's [single real endpoint test](../alice/single-endpoint-harmonics.md), take $A=3/2$ and $|y|\ge5$. For every fixed $c>0$ with $\cosh c\le108/49$, failure of one twist at its own cutoff forces

$$\max_{j=1,2,3} B_\zeta(2jy;c)\gg_c X^{1/8}.$$

Here $X=(A\log q)^2$, $D=\log X$, and $B_\zeta(t;c)$ counts, with multiplicity and weight $(1+(\gamma-t)^2)^{-1}$, the zeros with $|\gamma-t|\le X^{3/8}D$ and $\beta>1/2+c/D$. This uses the same external zeta $7/8$ strip and the same real-base, coprime small twists as the cited test. The implicit bound is uniform in the twist and the height for large $q$ at fixed twist-range exponent. In particular at $c=1/2$ one need test three ordinates, not the fifty in the earlier example. There is no change here to the radius of those packets.

**An angular certificate.** Put $x=|\cos v|$, and write $T_n$ for the Chebyshev polynomial $T_n(\cos v)=\cos(nv)$. The following identity on $[0,1]$ gives an upper bound with no truncation error:

$$71+42 T_2(x)-6T_4(x)+T_6(x)-108x
=(1-x)^2(2x-1)^2(8x^2+24x+22)\ge0.$$

The three even polynomials are unchanged by the absolute value. The constant coefficient of the majorant in the cosine basis is $71/108$, just below $1/A=72/108$. Its nonconstant coefficients have absolute sum $49/108$.

**Pay the pole and the height cost separately.** Write $s=\log(2+|y|)/\log q$, $b_p=X^{-1}\log p\log(X/p)$ for $p<X$, and $S_X(t)=\sum b_p p^{-it}$. At failure, the own-cutoff Gamma identity and reality give

$$ (1+s)/A-o(1)\le h_d(y)\le\sum b_p|\cos(y\log p)|\le1+o(1). $$

In particular $s=O(1)$ and all three modes are in the domain of [packet estimate (1)](endpoint-zero-packets.md#price-the-part-near-the-critical-line). For $j=1,2,3$ it bounds $|\Re S_X(2jy)|$ by

$$ (1+4j^2 y^2)^{-1} + \cosh(c)s/A + C X^{-1/8}B_\zeta(2jy;c)+o(1). $$

Indeed $\log(2+|2jy|)=\log(2+|y|)+O(1)$ uniformly. Average the majorant against the prime weights of total mass $1+o(1)$. Charge each mean by its absolute value, including the one with coefficient $-6/108$. Using $|y|\ge5$ for all three poles gives

$$ \frac{49C}{108} X^{-1/8}\max_{j\le3}B_\zeta(2jy;c)\ \ge\ \frac{1-49/101}{108} + \left(1-\frac{49}{108}\cosh c\right)\frac{s}{A}-o(1). $$

The height coefficient is nonnegative, even at the stated upper endpoint for $c$. The constant is $13/2727>0$, proving the implication. This is a disjunction, not a lower bound on the packet at $2y$ alone.

**What two initial cosine moments miss.** Put angular mass $1/3$ at $v=0$ and $2/3$ at $v=\pi/3$. Both the $2v$ and $4v$ cosine means vanish, yet $\mathbb E|\cos v|=2/3$. Thus no universal majorant using just those two cosine modes has constant coefficient *strictly* less than $1/A$. This is an obstruction to the fixed angular margin used above as $s\to0$, not to a different arithmetic argument with two heights. The law is not asserted to occur at prime phases. No packet upper bound, failure, or new RH implication for arbitrary Weil tests has been established.
