# How long do the same real shifts survive?

In the [flagged genuine cell](conductor-interval-search.md#finite-checks-and-the-flagged-cell), six fixed retained shifts do clear $1/16$ together, for more than 18.46 height units, but no six do so for 18.65 units. Eight can clear a fixed margin on a shorter window. **Only four can be positive hits at once.** The absolute-real window is therefore not a window of six positive correlations of the kind forced by a principal peak. We can test the peak implication without a choice of six: Even after replacing every shift contribution by its positive part, the full box sum on this cell is too small for a peak.

Use $q=2^{127}-1$, $t=2q^{3/5}$, $X(v)=(3\log(v/2))^2$, $D=\log X(t)$, $n=24$, $\ell=X(t)/(D\sqrt n)$, $u=t+44\ell$, and $\Delta=\ell/8192$. All statements are on $[u,u+\ell]$ with **moving** cutoff $Y=X(v)$, genuine phases, and no auxiliary twist. For $d$ let $C_d=\Re Z_d(v;Y)$, the sum of $w_p\cos(v\log(1+d/p))$ with $w_p=Y^{-1}\log(Y/p)\log p\log(p+d)$ on the clipped prime pairs. The trim $\log Y\le d\le4\log Y$ is $11,\ldots,40$. For the run tests retain $n^2 C_d^{\rm coll}((\log Y)^2)\le61$ with the ordered collision mass including the diagonal as in [the overlap test](quadratic-overlap.md). The only deletions are 12, 24, 30, and 36; odd shifts vanish.

| Closed window (in units of $\Delta$ from $u$) | Level | Fixed labels above level | Fixed labels below minus level |
|:--|--:|:--|:--|
| $[1728,1750]$ | $0.064$ | 14, 20, 22, 34 | 18, 32, 38, 40 |
| $[2366,2386]$ | $1/12$ | 14, 20, 22, 34 | 18, 40 |

Over the whole cell the maximum pointwise retained count at $1/16$ is exactly eight in absolute real part and exactly four on the positive side. For the *supremum of lengths* of windows with six fixed retained labels above $1/16$ in absolute value, the enclosure is $[299\Delta,302\Delta]$. A lower witness starts at index 2273 with labels 14, 18, 20, 32, 34, and 40. No endpoint of a maximal continuous run is identified. This is consistent with the already certified common dip elsewhere in the same cell.

**Certificate.** Run [check-real-run-length.py](check-real-run-length.py) in SageMath 10.9 Python with assertions enabled. The 160-bit interval computation verifies common integer support and pressure decisions, then uses tiles of 32 closed fine cells. At a tile midpoint expand the cosines to degree seven, enclosing the error by $\sum_p w_p(r\lambda_p)^8/8!$ for tile radius $r$ and $\lambda_p=\log(1+d/p)$. Rotate from the genuine large height before expanding in a local displacement. For each individual evaluation use the weights at that height in the expansion; interval weights contain them all. No derivative of the moving cutoff is used. On each fine cell classify each absolute real part as definitely above, possibly at or above, or below. For either hit mask keep each label's consecutive age; the sixth largest age is the longest common six-label suffix ending there. Every actual window is covered by consecutive possible cells for its six labels, and every consecutive definite run certifies its entire closed interval. Rounding ambiguous cells in opposite directions gives the two bounds.

## Price all positive shifts, not just the retained overshoots

Here is a finite version of [the box test](short-prime-pair-bias.md) requiring no PNT error or approximation of the lower edge. Write $H=4\log Y$, $b_d=2(1-d/H)/H$ for $1\le d<H$, and use **all** clipped shifts, including the pressure deletions and $d<11$. In this fixture the clipped primes are exactly those in $[9,Y]$. Put $S_Y(v)=Y^{-1}\sum_{p\le Y}\log(Y/p)\log p\,p^{iv}$. For $9\le R\le Y$ put a length-$H$ box at $s$ with prime sum

$$F_R(s)=H^{-1}\sum_{9\le p\le R,\ s<p\le s+H}\log p\,p^{iv}.$$

Integrate over $9-H\le s\le R$ and $9\le R\le Y$ with measure $ds\,dR/(YR)$. Its mass is $A=[Y-9+(H-9)\log(Y/9)]/Y$. The integral of $F_R$ is exactly the clipped ramp: Each prime has $s$-length $H$ and enters at $R=p$. In the square a pair $p,p+d$ has $s$-overlap $(H-d)_+$ and enters at $R=p+d$. Cauchy thus bounds the squared clipped modulus by $A$ times the diagonal $J=(YH)^{-1}\sum_{p\ge9}^{p\le Y}\log(Y/p)\log^2 p$ plus the signed pair sum, with $A$ multiplying **both** terms. In that pair sum the log ramp is $\log(Y/(p+d))$ rather than $\log(Y/p)$. Correcting it in absolute value gives the bound

$$|S_Y(v)|\le T+\sqrt{A\left(J+\sum_{d<H} b_d(C_d)_+ + E\right)},\qquad
E=\sum_{d<H}\frac{b_d}{Y}\sum_{p}\lambda_p\log p\log(p+d),$$

where the inner sum uses the clipped pairs and $T$ is the positive ramp mass on $2,3,5,7$. For the entire cell the checker encloses $\sum b_d(C_d)_+<0.026$, $J<0.199$, $E<0.0035$, $A<1.010$, and $T<0.00184$. Using unrounded enclosures gives $|S_Y(v)|<0.482<47/81$. This is an upper certificate **from the pair observable**, not a claim that a direct prime-sum calculation needs pair data. In particular the absolute-real overlap is genuine but does not come close to paying the full positive box cost here. This finite cap is not a bound at the center $t$ or on an unbounded sequence of conductors.

**Decision.** For the absolute-real common dip, do not exclude all shorter six-label windows: Some exist even with spare amplitude. For principal-peak exclusion the stricter target is the triangularly weighted positive mass, including shifts outside the retained list. A finite grid cap distinguishes these targets; a uniform arithmetic bound on this mass at the required heights is still missing. Neither test prices the smaller excursions in the per-shift shell budget.

**After Work.** At the named center itself, [the component test](short-edge-components.md) gives a sharp upper radius below $0.04136604$ from the full termwise short ratios. This is stronger data at a different ordinate, not a refinement of the whole-cell enclosure. At arbitrarily large named centers aligned short edges can accompany either near-unit or vanishing principal means in fixed multiplicative controls. The missing relative rotations and the genuine-phase limitation are explicit there.
