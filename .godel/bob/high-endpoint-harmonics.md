# The high endpoint gains little from more harmonics

Let $\mathcal K$ be the probability laws on $[0,1]$ with $\mathbb EU\ge m=8/9$, and write $c_j=\mathbb E T_{2j}(U)$. For a nonempty finite set $J$ of positive integers let

$$ v(J)=\min_{\mu\in\mathcal K}\max_{j\in J}|c_j|,\qquad v_\infty=\min_{\mu\in\mathcal K}\sup_{j\ge1}|c_j|. $$

The [two-mode lemma](sampled-principal-peaks.md#if-the-first-harmonic-barely-passes-price-the-third) gives $v(\{1,3\})=s_*=0.58664126022351\ldots$. The following are **strict rational brackets**, not claims of exact equality between the sparse and prefix optima. Each row bounds both $v(J)$ and $v(\{1,\ldots,N\})$:

| Signed indices in the lower certificate (absolute indices form $J$) | $N$ | Lower | Upper |
|:--|--:|--:|--:|
| $1,-3,6$ | 6 | 0.58702475785 | 0.58702475786 |
| $1,-3,6,-8$ | 8 | 0.58709557246 | 0.58709557248 |
| $1,-3,6,-9,11,-14,17,-20$ | 20 | 0.58712243824 | 0.58712243825 |

The sixth is the **best single index** to add to $\{1,3\}$, including among arbitrarily large fixed indices. It gains more than $0.00038349762$ over $s_*$. The eight-index certificate gains more than $0.00048117801$, while even all the harmonics together gain less than $0.00048356978$:

$$ 0.58712243824 < v_\infty < 0.58712483. $$

The relevant prior comparisons are [Alice's angular Fourier envelope](../alice/single-endpoint-harmonics.md), the [sharp sparse zero-moment bound](../alice/sharp-sparse-harmonics.md), and the [initial-block majorant](initial-harmonic-budget.md). The optimization here is at nonzero moments near $0.587$, not the zero-moment or small-error regime.

## Exact finite checks

For each row [the checker](check-high-endpoint-harmonics.py) gives decimal **rational** coefficients $d_j$ of the listed signs, $\sum|d_j|=1$, $\lambda>0$, and verifies

$$ P(u)=\sum_j d_j T_{2j}(u)-\lambda(u-m)-\ell>0\qquad (0\le u\le1), $$

where $\ell$ is the row's lower endpoint. Integrating shows that even the **signed** maximum $\max_{j\in J}\operatorname{sgn}(d_j)c_j$ exceeds $\ell$. This uses the lower bound on the mean with the indicated sign. For a polynomial $\sum_{i=0}^n p_i u^i$, the checker uses Bernstein coefficients $b_k=\sum_{i\le k}p_i\binom{k}{i}/\binom{n}{i}$ (expand the power $u^i$ in the degree-$n$ binomial basis). It bisects in this basis until every coefficient is positive on each piece. The 31, 27 and 43 pieces include both endpoints and cover the full interval. A separate exact Sturm replay also found positive endpoints and no roots in $[0,1]$ for each polynomial.

The respective upper witnesses are laws with two, three and five atoms; the checker solves for the last two masses from total mass one and mean $m$, checks all masses positive and nodes in $[0,1]$, and checks **every** prefix moment through $N$. For example, the two nodes are near $0.8538902753,0.9857190713$ with masses near $0.7345146535,0.2654853465$. Grid LPs and their contact patterns suggested the data; no grid inequality or floating-point solver result is used in the bounds. Replay with `python3 .godel/bob/check-high-endpoint-harmonics.py`.

### Why no other single extra index wins

One exact law in the checker handles all $j\le17$ except $6$ simultaneously, with $|c_j|<0.586846$. For $j\ge18$, let $\theta=2\arccos U$ under the two-mode extremizer for $s_*$. Independently add $\pm1/j$ with equal probabilities and map back by $U'=|\cos(\theta'/2)|$. This multiplies the $k$th cosine moment by $\cos(k/j)$ and gives mean at least $m\cos(1/(2j))$. Mix with $U=1$ at weight $p$ chosen to bring this *lower bound* to $m$. Then $0\le p\le m(1-\cos(1/(2j)))/(1-m)\le j^{-2}$. The mixed $|c_3|$ is at most $\max(s_*,p)=s_*$, and the mixed $|c_j|$ is at most $\cos 1+p\le13/24+1/324<s_*$. With $r=j^{-2}$ the mixed first moment is positive and at most

$$ s_*+r\left[1-s_*-(1-r)s_*(1/2-r/24)\right]. $$

This follows from $c_1=(1-p)s_*\cos(1/j)+p$ and $1-\cos(1/j)\ge r/2-r^2/24$. The checker bounds the expression by $0.587018$ using $r\le1/324$ and rational bounds on $s_*$. Both upper-witness bounds are below the lower certificate for index $6$, without truncating the search over $j$.

## All fixed harmonics

Weak compactness and continuity give $v_\infty=\lim_{N\to\infty}v(\{1,\ldots,N\})$: Take a weakly convergent subsequence of prefix minimizers; each fixed constraint holds in the limit, and the reverse inequality is immediate. No finitely supported law has supremum less than one: simultaneous rational approximation of its finitely many angles by a common multiple makes all their cosines arbitrarily close to one. In particular the finite upper certificates are not all-harmonic upper certificates.

For a uniform upper obstruction, choose center $\theta_i=\pm2\arccos u_i$ with the two signs equally weighted and with the normalized weights of the checker's `BOX` data (35 centers before reflection). Independently add uniform noise on $[-h,h]$, $h=1/125$, and set $U=|\cos((\theta_i+\text{noise})/2)|$. Its mean is at least $\operatorname{sinc}(h/2)\sum_i w_i u_i\ge(1-h^2/24)\sum_i w_i u_i>m$. Its moments are

$$ c_j=\operatorname{sinc}(jh)\sum_i w_i T_{2j}(u_i),\qquad \operatorname{sinc}(x)=\sin(x)/x. $$

For $1\le j\le212$, $jh<2$, so the positive sinc is bounded above by its alternating Taylor sum through degree 12; all 212 comparisons to $0.58712483$ are rational. For every $j\ge213$, $|c_j|\le125/j\le125/213<0.58712483$. The resulting symmetric phase law even has zero sine moments, so abstract complex moduli have the same ceiling. This is a law for **all** indices at once, not a sequence of long-prefix tests.

## Actual principal-peak threshold

At a failing high endpoint $y=q^{3/5}$, $X=((9/5)\log q)^2$, the [own-cutoff comparison](sampled-principal-peaks.md) gives $\mathbb EU\ge8/9-o(1)$ and $c_j=\Re S_X(2jy)/M_X$, $M_X=1+o(1)$. For each fixed $j$ the moving-cutoff change is $o(1)$ by the variation estimate there, since $\log X(2jy)-\log X=O_j(1/\log q)$. Thus infinitely many failures imply $L:=\limsup_{t\to\infty}|S_{X(t)}(t)|\ge v(J)$ for every fixed $J$ (by weak compactness), hence $L\ge v_\infty$. Equivalently, a strict upper bound $L<v_\infty$ suffices; equality is not excluded by this argument. The eight-mode row already makes $L\le0.58712243824$ sufficient by its strict lower bracket. This raises the sufficient exclusion threshold from $s_*$; it is not an unconditional lower bound on $L$.

Under the [external zeta strip used for packets](endpoint-zero-packets.md), the good-residue cost at every selected $2jy$ is $\cosh(c)/3+o(1)$, with an $o(1)$ pole. For any fixed $c>0$ with $\cosh c<3\cdot0.58712243824$, the eight signed tests therefore force $B_\zeta(2jy;c)\gg_c X^{1/8}$ at some selected ordinate at a failure. The angular comparison and the moving-cutoff implication do not use the strip. The packet result is a disjunction, not an upper estimate on any packet.

The all-harmonic obstruction concerns only abstract phase laws and the mean constraint. It does not realize the untwisted prime phases at their own cutoff, make the chosen character signs possible, or show any actual failure. The [band phase controls](prime-band-phase-controls.md) explain the distinction between free phases or frozen cutoffs and that coupled arithmetic problem. The next useful step is a principal estimate at the coupled scale (or a joint signed packet estimate on the sparse list), not a larger general-purpose harmonic search for more than another $0.000002392$ in the threshold.
