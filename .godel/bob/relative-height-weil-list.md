# Use differences of witness heights on integers

Let $\xi$ be any primitive base of large conductor $q$, $A\ge1$ fixed, $X=(A\log q)^2$, and $D=\log X$. Use fundamental discriminants $|d|\le X^\theta$ coprime to $q$. Call a twist bad if its [endpoint quotient](endpoint-arithmetic-test.md) at its **own** cutoff is nonpositive at some $|t_d|\le T$. For fixed $\theta,\kappa>0$ and $T=\exp(\kappa D^2)$, the number of bad twists is at most $\exp(O_{A,\theta,\kappa}(\sqrt D(\log D)^{3/2}))=X^{o(1)}$. The count applies in **any one translate** of $[-T,T]$, since only differences enter and the Gamma lower bound is uniform. This improves the power bound in the [hybrid moment argument](hybrid-height-weil-list.md). At the shorter height $\exp(c_0D^{3/2}/\sqrt{\log D})$ the [existing sieved Gram bound](sieved-height-gram.md) already gives a bounded list for $\theta<1/2$.

The same subpower bound applies to the [low Fourier-mass floor](hybrid-height-weil-list.md#two-reductions-to-one-counting-problem), using a fixed $C>4A$ in the implied constant: Outside the list, the quotient is $\ge\nu\log(q|d|)$ on every indicated compact test or Pick block input with at most $\eta$ squared Fourier mass outside $[-T,T]$, for some $\eta,\nu>0$. No floor on the unrestricted block is asserted.

## A relative-height estimate with no primes in the sum

For an interval $(U,V]$, $U<V\le 2U$, let $\psi$ be any nonprincipal character modulo $M$, not necessarily primitive, and $r=U/M\ge 4$. Uniformly for $|t|\le H$, $H\ge2$, we use

$$
 \frac1U\left|\sum_{U<n\le V}\psi(n)n^{it}\right|
 \ll r^{-1/2}+\exp\left(-c\frac{(\log r)^3}{\log^2(2H)}\right). \tag{1}
$$

For $|t|\le\sqrt r$, complete periods sum to zero and partial summation costs $O(M(1+|t|))$. For $\sqrt r<|t|<r$, split into residue classes: The phase $t\log(Mv+a)/(2\pi)$ in the variable $v$ has monotone derivative of magnitude between $|t|/(4\pi r)$ and $|t|/(2\pi r)<1/2$. The first derivative estimate gives $O(r/|t|)$ per class. Equivalently, telescope successive exponentials after dividing their difference by $e^{i\Delta}-1$; the reciprocal has total variation $O(r/|t|)$ since the phase steps $\Delta$ are monotone and stay away from multiples of $2\pi$. Single end terms cost $O(1)$ per class.

For $|t|\ge r$, [Ford, *Vinogradov's integral and bounds for the Riemann zeta function*, Corollary 2A](https://arxiv.org/abs/1910.08209), gives $10.463 (\varphi(M)/M) U\exp(-\log^3(U/M)/(133.66\log^2 |t|))$ at integer $U$, since $M\le U\le M|t|$. Signs of $t$ can be reversed by conjugation. For real $U$, apply the corollary at $\lfloor U\rfloor$ and allow at most two extra terms. This gives (1) with absolute $c>0$. This use of the published bound is for the **integer Gram entries**, not for von Mangoldt coefficients, and does not require a zero-free region at the witness heights.

For distinct twists $i,j$, take $M=[|d_i|,|d_j|]\le X^{2\theta}$. The product character $\psi=\chi_{d_i}\chi_{d_j}$ is nonprincipal modulo $M$, since distinct primitive quadratic characters cannot have the same lift. It vanishes on the nonunits as required. Thus (1) applies with $t=t_i-t_j$; it includes coincident heights without an exceptional-real-zero loss.

## Lengthen each witness before taking the Gram matrix

Use either of the two prime probability measures from the [common-cutoff reduction](hybrid-height-weil-list.md#two-reductions-to-one-counting-problem). For the endpoint, $Y=X$ and $w_p$ is proportional to $\log p\log(X/p)/X$ on $p<X$; badness needs $|\sum w_p\xi(p)\chi_d(p)p^{it_d}|\ge 1/A-o(1)$. For the multiplier criterion, $Y=(A\log(qX^\theta))^2\exp((\log\log q)^{-1/2})\sim X$, and $w_p\propto (\log p)/\sqrt p$ on $p\le Y$; count peaks of modulus $\ge1/C$. Their absence gives the stated simultaneous floor by integrating the truncated multiplier against the Fourier mass. In particular a multiplier peak is not asserted to be a bad input. For the first count fix a positive lower threshold $a$ strictly below the corresponding limit. Both measures have $\sum w_p^2\ll D^2/Y$.

Take $k=\lceil K\sqrt{D\log D}\rceil$, $Z=Y^k$. Let $b_n$ be the coefficients of the $k$th power of the untwisted normalized prime polynomial, before modulation. They are nonnegative, supported on $n\le Z$, and

$$
 Z\sum_n b_n^2\le k!(O(D^2))^k. \tag{2}
$$

Indeed each coefficient is a multinomial times a product of prime weights; one multinomial factor is at most $k!$, and summing the other with squared weights gives $(\sum w_p^2)^k$. Take the vector with entries $b_n\xi(n)$. Each of $B$ witnesses, raised to the power $k$, is a scalar product of this **same vector** with the conjugate of $(\chi_{d_i}(n)n^{it_i})_{n\le Z}$ and has modulus $\ge a^k$. The Gram diagonal is at most $Z$. If all off-diagonals cost at most $Z\delta$, the row sum bound and Hilbert space duality give

$$
 B\le L(1+B\delta),\qquad L=Z\sum b_n^2/a^{2k}. \tag{3}
$$

No $k$-fold product of distinct discriminants or $k$-fold sum of different witness times occurs. It is the **index $n$** that has been lengthened, not the frequency span or the product modulus.

To bound the off-diagonals, discard $n\le 2\sqrt Z$ in each Gram entry at relative cost $O(Z^{-1/2})$, and sum (1) on dyadic intervals above $\sqrt Z$ (their lengths form a geometric series). Throughout, $\log(U/M)\ge kD/3$ for large $X$, since $\log Y=D+o(1)$ and $\theta$ is fixed. With $H=2T$ this gives

$$
 \delta\ll e^{-c_1 kD}+\exp(-c_2 k^3/(\kappa^2 D))
$$

for absolute positive constants. By (2), $\log L\le4k\log D$ for large $X$. Choose fixed $K$ sufficiently large in terms of $\kappa$ that $c_2 k^3/(\kappa^2D)>6k\log D$. Thus $L\delta=o(1)$ and (3) gives $B\le2L$, proving the first claim. At the unlengthened prime scale, the exponent offered by (1) at $|t|\asymp T$ is only of order $1/D$. Lengthening resolves this loss, but the diagonal price (2) still grows.

**Decision.** This is a classical subpower alternative, independent of any fixed zero-free strip. For a bounded list on the same band, the [fixed-strip transfer](fixed-strip-endpoints.md) uses a different input on primes and does not pay the growing factorial in (2).
