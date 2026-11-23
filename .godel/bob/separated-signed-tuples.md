# Comparing a signed prime-ratio moment with its separated tuples

One can keep only tuples in which **every** start is isolated, provided the comparison is made on the signed moment, not on its two slices separately. The comparison loses $\exp(o(n))$ at order $n$ and has a power-saving additive error. It applies to the original gated residue discrepancy without assuming a spike. In the remaining arithmetic test the two integers whose ratio is nearly one are coprime squarefree products, each with exactly $n$ prime factors. Their signed near coincidences are not estimated here.

Use the notation of the [last-slot test](last-slot-residues.md): $t=2q^{3/5}$, $X=(3\log(t/2))^2$, $D=\log X$, $h=\lceil(2+\gamma)\log t/D\rceil$, $n=2h$, $0<\gamma<1/2$, and $0<a<1/16$ fixed. All comparisons are at a **single** shift $1\le d\le5D$ with $A=A_d>a$. Write $w_p=X^{-1}\log(X/p)\log p\log(p+d)$ for the starts with $p,p+d$ prime in $[e^{-8}X,X]$, $w_*=\max w_p\le8D^2/X$, $\lambda_p=\log(1+d/p)$, and $Z(u)=\sum_pw_pe^{iu\lambda_p}$. Even $A\le Xw_*=O(D^2)$ suffices below. Set $R=X^\xi$, $\xi=\gamma/(16(2+\gamma))$. Say an ordered tuple is separated if all its starts are pairwise at distance $>R$, including across signs. Let $J_0$ be the full signed off-diagonal sum in [the dyadic test (1)](dyadic-prime-pair-moments.md), and $J_R$ the same sum restricted to separated tuples. In both cases the multiplier is $G(t\nu)=(1-|t\nu|/(2\pi))_+\cos(t\nu)$, with $\nu$ the sum of the first $h$ log labels minus the sum of the other $h$.

**Comparison.** For some $\eta=o(n)$, $\eta\ge0$, and $E=t^{-1-\gamma/8+o(1)}$, uniformly over these shifts,

$$ e^{-\eta}J_0-E\ \le\ J_R\ \le\ e^\eta J_0+E. \tag{1} $$

In particular $J_0\le e^\eta J_R+ t^{-1-\gamma/8+o(1)}$. These are additive inequalities, not assertions about the ratio of two possibly small signed quantities. They hold also with both sums replaced by their respective *actual minus reference* residue discrepancies as specified below. The proof first compares real polynomials under a nonnegative measure. Applying a tuple-counting error bound to the deleted terms in absolute value would not prove (1).

## Excluding close starts in a real projection

For real $u,\theta$ put $x_p=w_p\cos(\theta+u\lambda_p)$ and $S=\sum_p x_p$. On the graph of starts joined at distances $\le R$ (distinct vertices), form the independence polynomial

$$ P(z)=\sum_{I\ {\rm independent}} z^{|I|}\prod_{p\in I}x_p,\qquad F_m=m![z^m]P. $$

Let $\Delta\le2R$ be the maximum degree and $B=C(1+\Delta)w_*$ for a sufficiently large absolute $C$. Write $b_j=j[z^j]\log P$. Then $b_1=S$ and

$$ |b_j|\le 4A B^{j-1}\qquad(j\ge1). \tag{2} $$

Here it matters that the prefactor is $A$, not $A\Delta$. To see this, use the same polynomial $P_H$ on induced subgraphs. On $|z|\le r=1/B$ put $\alpha_v(H)=zx_vP_{H-N[v]}/P_{H-v}$, where $N[v]$ includes $v$ and its neighbors in $H$. By vertex deletion $P_H/P_{H-v}=1+\alpha_v(H)$. Induct on $|H|$ starting with $P_\varnothing=1$: Delete the at most $\Delta$ neighbors successively from $H-v$. The inductive bounds $|\alpha_j|\le2|z|w_j$ give $|P_{H-N[v]}/P_{H-v}|\le(1-2rw_*)^{-\Delta}\le2$. This proves the bound for $\alpha_v(H)$ and nonvanishing of $P_H$. Counting each selected vertex once gives $zP'/P=\sum_v\alpha_v/(1+\alpha_v)$. Hence $|P'/P|\le4A$ on the disk, and Cauchy's bound proves (2).

The coefficient identity $P'=P(\log P)'$ gives the recurrence, with $F_0=1$,

$$ F_m=S F_{m-1}+\sum_{j=2}^m (m-1)_{\underline{j-1}} b_j F_{m-j}. $$

Put $s=|S|$ and $s_0=t^{-(1+\gamma/8)/n}$. We may change every $x_p$ to $-x_p$ to make $S=s$, since this does not change $F_n$. Two small parameters control the entire recurrence:

$$ nAB/s_0^2\le X^{-5\gamma/(16(2+\gamma))+o(1)},\qquad nB/s_0=o(1). $$

Indeed $n=X^{1/2+o(1)}$, $B\ll X^{-1+\xi}D^2$, and $s_0=X^{-(1+\gamma/8)/(4+2\gamma)+o(1)}$; the second estimate also follows from the first and $A>a$.

For $s\ge s_0$, inductively suppose the previous ratios $F_i/F_{i-1}$ are $\ge s/2$. The relative error in the leading term $s F_{m-1}$ has magnitude at most $(4A/s)\sum_{k\ge1}(2mB/s)^k\ll mAB/s^2$. This is $o(1)$ even at $m=n$, closing the induction. Multiplication of all ratios gives

$$ e^{-\eta}s^n\le F_n\le e^{\eta}s^n,\qquad \eta=C' n^2 AB/s_0^2=o(n). $$

For $s<s_0$, let $U=(1+\epsilon)s_0$, where $\epsilon=C''nAB/s_0^2=o(1)$ and $C''$ is sufficiently large. Given $|F_i|\le U^i$ for $i<m$, the recurrence divided by $U^m$ costs at most $1/(1+\epsilon)+(4A/U)\sum_{k\ge1}(nB/U)^k\le1$. Hence $|F_n|,s^n\le U^n=t^{-1-\gamma/8+o(1)}$. This small-$s$ estimate is essential: A comparison proved only near a fixed-size spike would not transfer an upper bound for the full discrepancy.

## Project back to the same signed arithmetic test

Average over $\theta$ uniformly on a circle and multiply by $C_n=2^n/\binom{n}{h}=O(\sqrt n)$. On $S^n$ this gives exactly $|Z(u)|^n$. On $F_n$ it gives the sum of $(\prod w_p)e^{iu\nu}$ over the separated ordered tuples: Expansion of the cosines keeps exactly $h$ signs of each kind, and for each independent $n$-set and plus subset the net multiplicity is $n!/\binom{n}{h}=(h!)^2$. The sum is real by interchanging the two sides. Thus for **any nonnegative probability density in $u$**, its integral of the separated sum lies between $e^{\pm\eta}$ times the integral of $|Z|^n$, up to additive $t^{-1-\gamma/8+o(1)}$ on each side. Indeed off $s<s_0$ the pointwise comparison holds, and on the discarded region even $C_n e^\eta U^n$ fits the error.

Use $t^{-1}\operatorname{sinc}^2(\pi(u/t-1))$, with $\operatorname{sinc} x=\sin(x)/x$. Its angular transform has real part $G(t\nu)$, so both integrals see precisely the same signed kernel. The full integral includes a diagonal of mass $\le h!(Aw_*)^h\le t^{-1-\gamma/2+o(1)}$ by the permutation argument of the dyadic note. The separated integral has **no** diagonal: Since $R>d$ eventually, its $2n$ prime endpoints are all distinct. This proves (1).

Use the original [rounded-slot formula (2)](last-slot-residues.md) for $J_0$. For $J_R$ intersect its completed-tuple gate $J$ with separation, calling the result $J^{\rm sep}$. Separation implies all $n$ slots are private. On the support of either slice the same base $M/N$ determines the same unique candidate $p$ nearest to $dM/(N-M)$; it must still pass the prime-pair and band tests and retain its original factor $\rho(p)=w_p/A$. The pointwise replacement $t\nu\mapsto \ell/V$ costs no more after adding a gate to the absolute error bound. The signed reference $\overline G(k,V)$ is negligible base by base on either gate. Consequently (1) applies to the two quantities

$$ A^n\mathbb E_{\rm base}\big[J'\rho(p)\{G((M-kp)/V)-\overline G(k,V)\}\big],\qquad J'=J,\ J^{\rm sep}, $$

with the same error exponent, since $A^n,e^\eta=t^{o(1)}$. Here $k=(N-M)/d$ and $V=Np/(td)$ as before. On the separated gate $M,N$ already have $n-1$ distinct prime factors each, and $M(p+d)$ and $Np$ are coprime squarefree products of $n$ primes each. Their difference is exactly $d\ell$. No uniform replacement of $\ell$ has been made.

## Why this does not price the two deleted slices

The retained positive core itself remains large. Apply the integral comparison with the probability density $(4\pi t)^{-1}\operatorname{sinc}^2(u/(4t))$, of transform $(1-2t|\nu|)_+$. Since $Z(0)=A$ and $|Z'|\ll AD/X$, on $|u|\le cX/(nD)$ we have $|Z|^n\gg A^n$ for a small absolute $c>0$. Thus the separated tuple mass at $0<|t\nu|<1/2$ is $\gg e^{-\eta}XA^n/(tnD)$, after absorbing the power-saving error. There $G$ is bounded below by a positive constant.

At the same time the **deleted** positive slice need not be negligible. Prescribe just the first plus and first minus labels to coincide, gaining the factor $\sum_p w_p^2\ge A^2/X$. For the remaining $h-1$ labels per side, bin the one-sided sums in cells of width $1/(2t)$ as in the dyadic note. Their span is $O(hD/X)$ so same-cell pairs have weight $\gg XA^{n-2}/(thD)$, less a negligible permutation diagonal $\le (h-1)!(Aw_*)^{h-1}$. Every nonzero such difference with the prescribed match is central and fails separation. This gives deleted positive mass $\gg A^n/(thD)$ even after the low-private discard of the original gate (cost $t^{-1-\gamma/8+o(1)}$). On $A>1/4$ this alone exceeds the original detection scale by a factor $\gg (A/a)^n/X$; the [consecutive-gap lemma](matched-prime-overlap.md) supplies $\gg D$ such shifts. Thus (1) is not a negligible-error pruning of the separate slices.

**A count on which to try the remaining estimate.** For an unordered separated support $I$ of size $n$ let $P_I=\prod_{p\in I}p(p+d)$. For $B\subset I$ of size $h$ put $v_B=\prod_{p\in B}(p+d)\prod_{p\in I\setminus B}p$. These are distinct divisors of $P_I$, and $v_{I\setminus B}=P_I/v_B$. Define $N(z)$, for $0\le z\le2\pi$, by counting just these $B$ with

$$ \sqrt{P_I}e^{-z/(2t)}\le v_B\le \sqrt{P_I}e^{z/(2t)}, $$

summing over $I$ with weight $(h!)^2\prod_{p\in I}w_p$. This counts the original labeled separated tuples at $|t\nu|\le z$, not all divisors near a square root. In particular $N(0)=0$. Integration by parts and $\int_0^{2\pi}G=0$ give the exact identity

$$ J_R=-\int_0^{2\pi}G'(z)\left[N(z)-\frac{z}{2\pi}N(2\pi)\right]dz. $$

Thus even the slope of a linear main term need not be predicted: It is the variation in the *shape* of the actual weighted counts across these nested intervals that matters. The identity is after summing supports; demanding this accuracy on each support would lose possible cancellation. Replacing the constrained divisors by general smooth numbers discards the one-endpoint-per-pair and balance conditions and is not this count. For example, [Ford, *The distribution of integers with a divisor in a given interval*](https://arxiv.org/abs/math/0401223), counts integers up to a cutoff with at least one (or exactly $r$) unrestricted divisors in a common interval. Here the integer is the weighted $P_I$, the interval moves with $I$, and even on a single $P_I$ only balanced endpoint selections count. An order of magnitude for the ambient count does not bound the signed difference in this identity.

**Decision.** For any fixed $0<a'<a$, a signed upper bound $J_R\le (a')^n e^{o(n)}/t$ outside $o(D)$ labels would put the actual full residue excess below $(aX/(hDA))a^n/t$ there. The fixed gap absorbs the comparison loss; the same constant-factor assertion at identical $a$ does not follow. It now suffices to estimate the signed excess for coprime, squarefree numerator and denominator with *all* starts separated, at the original shift, weights, and height. An unsigned bound on even this family still confronts the oversized positive core. Neither the comparison nor the reference mean proves cancellation at the named center.

**After Work:** Before choosing the radius for the shape integral, see [separation at the detection amplitude](detection-radius.md). For the common-dip implication, reducing the support radius to $D^2$ retains a constant fraction of the window-scale signal at the exact threshold $1/16$ on $\gg_\varepsilon D$ shifts. The larger radius above still gives the smaller divisor family if there is fixed amplitude slack. Neither family has the requisite signed upper bound. The [replay finding](detection-radius-review.md) records why this is a local handoff, not a new standing dispatch.
