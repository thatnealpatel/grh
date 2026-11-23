# A necessary arithmetic test for a uniform Weil window

The [prime-translation note](../adhoc/prime-translation-norm.md) asks for savings on low-archimedean-energy tests when $E=e^{D/2}=(1+\delta)\log q$, with $\delta>0$ fixed. What would that require even at frequency zero? For quadratic characters of prime conductor, **a positive fraction of the log-weighted prime mass below $X=E^2$ must consist of nonresidues**. This is a necessary condition for uniform window positivity, not an unconditional estimate for nonresidues.

Use the same $w(x)=e^{-x/2}+e^{-(D-x)/2}$ on $[0,D]$, zero elsewhere. Its squared norm is $N=2(1-X^{-1})+2D/E$. For a primitive nonprincipal character $\chi$, write $u_y(x)=e^{iyx}w(x)$ and $z_n=\Re(\chi(n)n^{iy})$. The exact prime quotient on $u_y$ is

$$
 \frac{\langle T_\chi u_y,u_y\rangle}{N}
 =\frac{2}{N}\sum_{n<X}\Lambda(n)z_n
 \left[\frac{2}{n}(1-n/X)+\frac{\log(X/n)}{E}(1+1/n)\right].
$$

Indeed the first part of the bracket comes from the two same-endpoint products in the correlation at $t=\log n$, and the second part from the two opposite-endpoint products, after multiplication by $n^{-1/2}$. This is a signed sum; the term is **subtracted** in the Weil form. As $D\to\infty$, the quotient equals

$$
 E\,H_\chi(X,y)+O(1+D),\qquad
 H_\chi(X,y)=\frac1X\sum_{n<X}\Lambda(n)\log(X/n)z_n.
$$

The error is uniform in $\chi,y$: $\sum_{n<X}\Lambda(n)/n=O(1+D)$ and $\sum_{n<X}\Lambda(n)\log(X/n)=\int_1^X\psi(v)dv/v=O(X)$. Thus the $1/n$ correction in the second term costs $O(D(1+D)/E)$, and replacing $2/N$ by $1$ costs $O(1+D)$.

The Gamma quotient on this same profile is $\log(2+|y|)+O(1)$, **without** the conductor. In fact $|\widehat w(s)|\ll (1+|s|)^{-1}$ by integrating each exponential, uniformly for $D\ge1$, and $N$ is bounded below. The Gamma symbol differs from $\log(2+|s|)$ by a bounded amount in either parity. After shifting the Fourier density by $y$, replacing $\log(2+|y+s|)$ by $\log(2+|y|)$ costs at most the average of $\log(2+|s|)$, which is bounded. The endpoint jumps are admissible for the log form: Contract the support and mollify in the log-weighted Fourier norm as in [the block note, §3](../adhoc/pick-block-weil-window.md). For each fixed $D,q,y$ this also preserves the finite prime form in the limit.

Consequently nonnegativity of the whole window would imply, for every $y$,

$$
 H_\chi(X,y)\le\frac{\log q+\log(2+|y|)+O(1+D)}{E}.
$$

For a quadratic character of prime conductor $q$ and $y=0$, we have $q>X$ eventually. The untwisted $H(X,0)$ is $1+o(1)$ by the same integral and the prime number theorem. Prime powers of exponent at least two cost $o(1)$ in $H$ (at most $O(\sqrt X\log^3 X/X)$ by counting bases and exponents). Hence uniform positivity at the proposed diameter would require

$$
 \frac{1}{X}\sum_{p<X:\,\chi(p)=-1}\log p\,\log(X/p)
 \ \ge\ \frac{\delta}{2(1+\delta)}-o(1).
$$

Even existence of one such prime for every sufficiently large prime conductor would be a least-quadratic-nonresidue estimate at the $\log^2 q$ scale. Finding one small nonresidue would not by itself pay the required mass. Nor does ignoring the character and positing only residues give a counterexample: No such sequence of conductors is exhibited.

There is an unconditional negative result for the *comparison* that keeps the full Gamma energy but charges absolute prime correlations. At $y=0$ all the correlations of $w$ are nonnegative. Along prime conductors $q>X$ the unsigned prime quotient is $(1+o(1))E$ by the preceding formula and the prime number theorem. Hence this comparison on $w$ gives $(-\delta+o(1))\log q$, or $o(\log q)$ at $\delta=0$. Merely replacing the scalar Gamma floor by the exact Gamma form cannot repair the unsigned proof. This is not the signed Weil quotient.

These necessary tests also apply to a bound asserted for **every** node block with $m\ge(\log\log q)^3$ and $\sum 1/m\le D/2$. For each fixed $q$, first approximate the normalized endpoint profile by smooth interior tests, then recover each test by exponential polynomials on escaping blocks of budget tending to $D/2$ from below, using §§2–3 of the block note. The weighted derivative and function convergence there controls the Gamma term and the prime correlation error integrated against the absolute prime measure (also after taking correlation moduli, by the reverse triangle inequality). Take the minimum node as large as needed for that $q$. This tests the all-block quantifier; it supplies no uniform rate of recovery for a prescribed block.

**Necessary versus sufficient.** For comparison let $p_\chi(y)=2\Re\sum_{n<X}\Lambda(n)\chi(n)n^{iy}/\sqrt n$ be the multiplier of the *uncompressed* finite prime operator. A fixed positive margin for $\log q+\log(2+|y|)-p_\chi(y)$ in units of $\log q$ throughout $|y|\le2q^\alpha$ with $\alpha>\delta$ would be sufficient for a fixed window margin. Indeed the low piece of the smooth square partition in the [most-character window](../alice/prime-conductor-window.md) then has that margin up to $O(1)$; its high piece has margin $(\alpha-\delta-o(1))\log q$ after the enlarged-support Schur estimate, up to $o(\log q)$ per original unit test. This localization implication does not require averaging over characters. For blocks one must use the slightly enlarged cutoff in that note. A peak of $p_\chi$ does not itself give an admissible witness. By contrast $H_\chi$ above was obtained from an actual window test.

**Next decision.** Before seeking a *uniform* frequency-localization theorem, test whether the last one-sided weighted prime estimate is available for the family in question. If not, name it as an arithmetic obligation even for the unmodulated profile. If it holds, it removes only this obstruction, not the other modulations or the need to bound all tests. The [most-character window](../alice/prime-conductor-window.md), adopted after Bob's run, already controls the frequency split with leakage for most characters at each prime conductor and $1<E/\log q<2$. Its exceptional set can contain the quadratic character for every $q$. Do not repeat that split as if it would dispose of this uniform question.

**Local consequence.** For $1<A<2$, the [two-twist endpoint bound](local-quadratic-twists.md#a-sharper-alternative-for-the-unmodulated-endpoint-alone) shows that if this profile has nonpositive quotient at a prime $q$, it has positive margin on every nontrivial quadratic twist by $|d|\le(\log\log q)^K$ for each fixed $K$. It uses signed prime mass, not a least-nonresidue estimate, and does not determine the sign on the base.
