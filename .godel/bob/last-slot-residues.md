# A last-slot residue test for signed prime-ratio moments

At a genuine center $t=2q^{3/5}$ freeze $X=(3\log(t/2))^2$, $D=\log X$. We reduce the **positive and negative parts separately**, at the same integer shift and below the precision of [the signed test (1)](dyadic-prime-pair-moments.md). The remaining comparison concerns a reduced residue at a prime-pair-dependent integer; no equidistribution of these residues is proved.

Fix $0<a<1/16$, $0<\gamma<1/2$, $L=\log t/D$, $h=\lceil(2+\gamma)L\rceil$, $n=2h$. Take any integer $1\le d\le5D$ with $A=A_d>a$. Draw $n$ labeled starts independently from $\rho(p)=w_p/A$, where $p,p+d$ are primes in $[e^{-8}X,X]$, $w_p=X^{-1}\log(X/p)\log p\log(p+d)$. Let $b_0=8D^2/(aX)$, an upper bound on $\rho$. As usual $\nu$ is the sum of $\log((p+d)/p)$ with $h$ signs of each kind. Write $G(z)=(1-|z|/(2\pi))_+\cos z$, $G_+=\max(G,0)$, and $G_-=\max(-G,0)$. We normalize all masses by $A^n$ until the end.

**Discard only tuples with a priced total cost.** Put $\xi=\gamma/(16(2+\gamma))$. A slot is private if its start lies at distance greater than $X^\xi$ from the start of every other slot, counting repetitions. If $s$ slots are private, then

$$\Pr(|t\nu|\le8,\ s\le(1+\gamma)L)\le t^{-1-\gamma/8+o(1)}. \tag{1}$$

To see this, mark the private labels. Every component on the other labels under the distance-$X^\xi$ adjacency has size at least two. Select a rooted spanning tree in each, with $e\ge(n-s)/2$ forest edges altogether. For a given $s,e$, there are at most $2^{O(n)}n^e$ choices of private labels, roots, and parent pointers. In root-first order each child costs at most $(2X^\xi+1)b_0$. Ignore the absence of edges not in this forest.

Leave $r=\min(s,\kappa)$ marked labels unrevealed in a prescribed order, where $\kappa=\lfloor\log(t/32)/(2D)\rfloor$. Given the other slots, the forest constraints are already decided. Two unequal values of the missing signed log-sum differ by at least $X^{-2r}$: Each product ratio has numerator and denominator at most $X^r$, so compare the logs of distinct integer cross products. Only one value fits in the remaining interval of width $16/t$. The log-sum fixes the signed edge multiplicities: At the least start at which multiplicities differ the incoming multiplicity difference is zero, so the prime valuation differs. Among completions respecting the private labels, all missing starts are distinct, so no opposite counts at the same start can be hidden. At most $r!$ assignments remain. This costs at most $r!b_0^r$ under the original product law, **without conditioning that law on privacy**.

Now $\log n=D/2+O(\log D)$, and $n=o(\log t)$. Combining these costs and the enumeration, the saving exponent in units of $\log t$ is at least $(e+r)/(2L)-\xi e/L-o(1)$. Bound $\xi e/L\le\gamma/8+o(1)$, or for the sharper bound use that the expression increases with $e$ and substitute $e=(n-s)/2$ throughout. Then $\xi(n-s)/(2L)\le\gamma/16+o(1)$. For $s\le\kappa$, $((n-s)/2+r)/(2L)\ge 1+\gamma/2$; for $\kappa<s\le(1+\gamma)L$ it is at least $1+\gamma/4-o(1)$. Summing over $s,e$ costs $t^{o(1)}$. This proves (1). Also $\Pr(|t\nu|\le8)\le\kappa!b_0^\kappa=t^{-1/4+o(1)}$ as an upper bound, by leaving $\kappa$ **positive** slots unrevealed: Their multiset is fixed by injectivity even without privacy.

**Recover a single dependent slot, retaining its sign and weight.** Omit one fixed positive label and write the reduced product from the other $n-1$ slots as $M/N$. For an original completion with $|t\nu|\le8$ one has $M/N=e^\nu p/(p+d)<1$. With $x=dM/(N-M)$, direct subtraction gives

$$ x-p=\frac{p(p+d)(e^\nu-1)}{d-p(e^\nu-1)}=O(X^2/(dt)). $$

Thus keep only bases with $M<N$ and $e^{-8}X/2\le x\le2X$, and try only $p$ nearest to $x$ (ties immaterial). Reject nonedges or $s\le(1+\gamma)L$ in the **completed** tuple. Call the resulting gate $J$; it does not test the size of $\nu$. Multiply by $\rho(p)$, since one specific independent label was removed. As $X^\xi>d$ eventually, the two prime endpoints of each private slot occur nowhere else. On $J$, at least $s-1$ such slots survive the omission, so both $M$ and $N$ exceed or equal $(e^{-8}X)^{s-1}\ge t^{1+\gamma-o(1)}$. In the full product there is a unit prime valuation; in particular neither exact equality nor a proper rational power survives.

All unreduced endpoint factors are units modulo $d$, and the numerator and denominator agree modulo $d$ term by term; this persists after reduction. Hence $k=(N-M)/d$ is a positive integer, $x=M/k$, and $\gcd(M,k)=1$. Define

$$\ell=M-kp,\qquad y=\frac{td\ell}{Np},\qquad V=\frac{Np}{td}. $$

Here $\ell$ is the centered reduced residue of $M$ modulo $k$, not a freely chosen displacement. In fact $1+y/t=M(p+d)/(Np)$. On the union of the supports of $G_\pm(y)$ and $G_\pm(t\nu)$, one has $|t\nu|\le8$ and $y=t\nu+O(1/t)$. Using Lipschitz continuity and the preceding $\kappa$-slot bound, replacement costs $t^{-5/4+o(1)}$ after restoring the last-slot probability. Consequently, for each sign separately, with expectation on the right over the base only,

$$ \mathbb E[1_{\nu\ne0}G_\pm(t\nu)]
 = \mathbb E_{\rm base}[J\rho(p)G_\pm(\ell/V)] + O(t^{-1-\gamma/8+o(1)}). \tag{2} $$

Take rejected terms as zero without forming undefined ratios. This formula does not compare two different shifts or allow independent replacement choices on the two sign slices.

**How much imbalance comes from the primitive-residue constraint alone?** Keep each gated base, its rounded edge, its weight, $k$, and $V$, and compare its kernel value to the mean under a uniform centered unit modulo $k$. This is a reference measure, not a conditional law for the actual $M$. On $J$ one has $N=k(x+d)$, hence

$$ k\ge t^{1+\gamma-o(1)},\qquad V/k=(x+d)p/(td)\asymp X^2/(td)=o(1). $$

Also $k\le X^{n-1}=t^{O(1)}$. For $H=G_+$ or $G_-$, Möbius inversion and bounded variation give the explicit reference value

$$ \frac1{\varphi(k)}\sum_{-k/2<j\le k/2\atop (j,k)=1} H(j/V)
 =\frac{V}{k}\int_{\mathbb R} H(z)\,dz + O\!\left(\frac{2^{\omega(k)}}{\varphi(k)}\right). \tag{3} $$

Indeed the support lies strictly inside the residue interval, and for each $m\mid k$, the sum on multiples of $m$ differs from $(V/m)\int H$ by at most the total variation of $H$, by integrating over successive mesh cells. The error in (3) is $t^{-1-\gamma+o(1)}$ since $2^{\omega(k)}=k^{o(1)}$ and $k/\varphi(k)=k^{o(1)}$ (already $\omega(k)!\le k$ suffices). The two main terms **agree**: $\int G=2\int_0^{2\pi}(1-z/(2\pi))\cos z\,dz=0$. Thus even at fixed admissible $p,k,V$, the forced coprimality of the defect produces no signed imbalance at the required precision in this reference. Both reference slices are positive, of order $V/k$ before weighting. There is no assertion that either actual slice separately approximates its reference.

**Restoring some exact endpoint congruences still leaves the reference balanced.** For each base choose a divisor $Q$ of $MN$ with $Q\le t^{\gamma/2}$. In the reference restrict also to $j\equiv\ell\pmod Q$, using the *actual* residue. For instance this can retain the congruences on any $\lfloor\gamma L/2\rfloor$ distinct private endpoint primes left after omission: Each is at most $X$, and each divides $MN$. As $(k,MN)=1$, for every $m\mid k$ the restriction to $m\mid j$ is now a single translated progression of step $mQ$. Thus the reference class has $\varphi(k)/Q+O(2^{\omega(k)})$ centered units. On this class the **unnormalized signed** sum is $O(2^{\omega(k)})$ by the same mesh estimate and $\int G=0$. Its conditional mean is $O(Q2^{\omega(k)}/\varphi(k))\le t^{-1-\gamma/2+o(1)}$. This works with a different choice of $Q$ on each base. It prices the congruence restrictions in isolation, not the cost of replacing the actual defect by a draw from the class. The latter replacement erases any finer correlations.

**Remaining arithmetic question.** With $\overline G(k,V)$ the difference of the two means (3), the signed sum in the dyadic note equals

$$ A^n\mathbb E_{\rm base}\big[J\rho(p)\{G((M-kp)/V)-\overline G(k,V)\}\big]+O(t^{-1-\gamma/8+o(1)}). $$

Here $A^n=t^{o(1)}$ on $A>a$ by the two-form bound, so all discarded errors are smaller than $(aX/(hDA))a^n/t=t^{-1+o(1)}$. On mass-rich shifts the oversized central slice is still present among the retained tuples, by (1) and the central-cell lower bound (the entire nonprivate-core loss is negligible). A proof using this test must bound the **positive excess** of the displayed discrepancy below the detection scale except on $o(D)$ labels, with the genuine product residues and the same prime-pair gate. A uniform-residue substitution without such a bound, even one conditional on all the retained sizes, does not estimate the negative slice. For instance $M\bmod k$ is completely determined by a fixed base. A local cluster cover in height also leaves this discrepancy at an isolated cluster untouched.

If proposing to transfer the oversized core to a negative partner, first fix the source and price the free slots with their original weights. The [partial-redraw bound](tuple-redraw-cost.md) covers every choice of retained slots, even an unbalanced or source-dependent one. It limits unnormalized forward proposals, not the negative marginal; supply a reverse-weight or target-multiplicity estimate before claiming cancellation. This [post-Work check](tuple-partner-review.md) does not alter the residue target above.

The [separated signed comparison](separated-signed-tuples.md) transfers a signed upper bound on the all-private subfamily to this full target with $\exp(o(n))$ loss and sub-detection additive error. It does not prune the two sign slices separately.
