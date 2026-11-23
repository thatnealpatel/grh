# What does it cost to redraw an opposite-sign partner?

Fix the shift, center, and original tuple size in the [dyadic signed test (1)](dyadic-prime-pair-moments.md). A central tuple need not split into smaller central blocks. One might instead keep some of its labeled slots and redraw the others from their original prime-pair law. Even choosing the slots after seeing the entire source, the fraction of redraws reaching the negative annulus is at most $t^{-1/4+o(1)}$. This is a **conditional proposal cost**, not a comparison of the two marginal slice masses.

## Uniform redraw bound

Let $t=2q^{3/5}$, $X=(3\log(t/2))^2$, $D=\log X$, $h=\lceil(2+\gamma)\log t/D\rceil$ with fixed $0<\gamma<1/2$, and $n=2h$. Take $1\le d\le5D$ with $A_d>a>0$ for fixed $a$. Each start $p$ has $p,p+d$ prime in $[e^{-8}X,X]$, log label $\lambda_p=\log((p+d)/p)$, and probability $\rho(p)=w_p/A_d\le b=8D^2/(aX)$ with the original weights. Denote by $\mu=\rho^{\otimes n}$ the ordered tuple law and by $\nu$ its sum of labels with $h$ signs of each kind.

Fix **any** admissible source with $|t\nu|\le2\pi$. Keep its signs and redraw any specified mask of $k$ slots independently with law $\rho$. Write $\nu'$ for the new sum and put $K=\lfloor\log(t/32)/(2D)\rfloor$. Uniformly in the source and mask,

$$\Pr\{ |t\nu'|\le2\pi,\ \nu'\ne\nu\}\le t^{-1/4+o(1)}. \tag{1}$$

This includes sign changes in **either** direction for the triangular cosine test. It even excludes a literal log-frequency change when $k\le K$. It need not bound the probability of revisiting the *same* frequency.

**Pay for cancellations among the new slots.** In a successful redraw, match off opposite signs at identical new starts as far as possible. Let $e$ be the number of disjoint pairs, and $m=k-2e$ the number of unpaired new slots. After removing the unchanged slots and those $e$ pairs, the displacement $\nu'-\nu$ is the log of a rational with numerator and denominator at most $X^{k+m}$. For unequal positive integers $u,v$, $|\log(u/v)|\ge1/\max(u,v)$. Hence

$$X^{-2(k-e)}\le |\nu'-\nu|\le4\pi/t,\qquad k-e>K.$$

For a given $e$, enumerate candidate pairings by choosing the paired plus labels and injecting them into the minus labels. This costs at most $2^n n^e$. Each specified pairing costs at most $b^e$ in probability, since the partners are independent. We do not condition the remaining draws on the pairing being maximal.

Among the $m$ unpaired slots leave $r=\min(m,K)$ fixed labels unrevealed. After revealing the other draws, the permitted log sums of these $r$ slots must lie in an interval of length $4\pi/t$. Distinct values are separated by at least $X^{-2r}\ge32/t$ by cross multiplication, so at most one value fits. A value uniquely determines the **net** signed start multiplicities: At the least differing start the prime valuation differs, since its only possible incoming edge starts lower. For completions with no opposite-sign duplicate among the unpaired labels, the net multiplicities on the $r$ missing labels determine each sign's multiset there. Thus at most $r!$ labeled completions fit. Count these completions under the original independent law at cost $r!b^r$; ignoring the no-duplicate requirement *in this count* would be incorrect for mixed signs.

Now $e+r\ge K$: Either $r=K$, or $e+r=k-e>K$. Since $r!\le n^r$ and $nb<1$, summing over $e$ costs in total at most $(n+1)2^n(nb)^K$. Here $\log n=D/2+O(\log D)$, $K D=\tfrac12\log t+O(D)$, and $n=o(\log t)$, giving (1). No growing-moment independence between nearby frequencies has been assumed.

## What this rules out, and what to test instead

A source-dependent choice or mixture of masks costs nothing extra. Even trying all $2^n$ masks and taking any success costs only $t^{o(1)}$ in the bound, provided each mask's proposed fresh values have their joint product law. Dependence *between* trials does not defeat the union bound. A proposal dominated by $B$ times the original redraw law after fixing source and mask pays the factor $B$.

On $C=\{0<t|\nu|\le1/2\}$ the positive multiplier is bounded below by a constant. The mass transported from $C$ to the negative annulus in one unnormalized redraw is at most $t^{-1/4+o(1)}\mu(C)$, also when credited with the absolute value of the negative multiplier (at most one). On $A_d>1/4$, $a<1/16$, the dyadic note shows that the core's positive mass already dwarfs the normalized detection scale. Thus a proposal meant to pay for a fixed fraction of that core directly needs a combined trial or density factor at least $t^{1/4-o(1)}$. This does **not** bound the actual negative mass by that fraction of the positive mass. Conditioning on a rare hit changes the normalization; a weight-preserving map need not be dominated by a cheap redraw.

For example, there is a precise reverse check for a fixed mask. Let $T$ redraw it, $f=1_{\nu\ne0}G_+(t\nu)$, $g=G_-(t\nu)$, and $P=\mu(f)$, $M=\mu(g)$ with $G$ as in the [last-slot test](last-slot-residues.md). When $P,M>0$, let $\alpha=\mu(fTg)/P$, $\beta=\mu(gTf)/M$. Given the untouched slots, old and new draws are iid, hence $P\alpha=M\beta$. Both rates are $\le t^{-1/4+o(1)}$ by (1). If $\beta>0$, it is the *ratio* that matters: $P-M=P(1-\alpha/\beta)$. For masks of at most $K$ slots both fluxes are identically zero. For a mask depending on the source the symmetry need not hold. A dependent transfer should specify its reverse mass or target multiplicities and deliver the **signed** precision of the dyadic test; neither small forward probability nor a single annular witness does that. No estimate for that ratio is proved here.
