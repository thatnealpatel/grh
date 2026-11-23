# Finite principal ramp bounds from verified zeta zeros

For $y=q^{3/5}$, $X=((9/5)\log q)^2$, set $w_p=X^{-1}\log p\log^+(X/p)$, $M=\sum_p w_p$, and $S(t)=\sum_p w_p p^{it}$. There are three different finite exclusions:

* For every real $2^{18}\le q\le2^{60}$ and $2y\le t\le40y$, $|\Re S(t)|<0.585948$. In particular none of the eight signed modes gives an **unbuffered** $0.587$ hit.
* For the dyadic blocks $Q=2^k$, $42\le k\le59$, $J=Q$, no **buffered** signed cell of the [principal search](principal-block-search.md) meets the named height interval. This uses the frozen cutoff, not the moving bound above.
* For every real $2^{18}\le q\le2^{67}$, the modulus of **every real-signed ramp** $\sum_p \epsilon_p w_p p^{iy}$, $|\epsilon_p|\le1$, is $<0.823572$. This includes the direct projection obtained with the signs of the real parts. On $2^{19}\le q\le2^{67}$, $M>0.889556>8/9$: Mass alone does not give this rejection. Thus any buffered cells in the untested part of this band still cannot be raw $8/9$ projection hits. We have not exhibited such a cell or measured its successor gaps.

These statements concern principal sums, not the positivity of a whole Weil form. They are unconditional *finite* consequences of published zeta verification. They do not imply a strict asymptotic margin.

## Translated formula with a finite error

Write $R=\sqrt X$, $D=\log X$, and put $f(s)=e^{-s/2}$ on $[0,D/2]$, zero elsewhere. Set $g(s)=f(D-s)$, $b=f+e^{i\phi}g$, $K(v)=\int b(s+v)\overline{b(s)}\,ds$. All estimates below are uniform in $\phi$, $6<D<9$, and $3000\le t\le2.8\cdot10^{12}$. With $B(z)=\int b(s)e^{izs}ds$ take $h(z)=B(z)\overline{B(\bar z)}$. Thus $h$ is entire, equals the transform $\int K(v)e^{izv}dv$, and is nonnegative on the real axis. Its mass divided by $2\pi$ is $K(0)=2(1-1/R)$. Recenter the support at zero (the transform phase cancels in $h$). Including the midpoint jump, the variation is at most $2+2e^{-D/4}+2(1-e^{-D/4})=4$, and $\|b\|_1\le4$. Integration by parts against $db$ therefore gives

$$ |h(z)|\le16e^{D|\Im z|}/|z|^2,\qquad 0\le h(v)\le16\min(1,v^{-2})\quad(v\in\mathbb R). $$

Apply the [Guinand–Weil formula, Carneiro, Chirre, and Milinovich, §2](https://arxiv.org/abs/1710.10362) to $F(u)=h(u-t)$; the decay holds on any fixed strip. In the convention $(2\pi)^{-1}\int F(u)e^{-iuv}du=e^{-itv}K(v)$, the prime sum subtracted in that formula is

$$ P=2\sum_n \Lambda(n)n^{-1/2}\Re[e^{-it\log n}K(\log n)]. $$

The remaining right side is the sum of $F(\pm i/2)$ and $A=(2\pi)^{-1}\int F(u)[\Re\psi(1/4+iu/2)-\log\pi]du$; the left side is the sum of $F((\rho-1/2)/i)$ over nontrivial zeros with multiplicities. Evenizing $F$ gives the same summed formula by zero reflection and the even archimedean symbol. This also handles complex endpoint rotations, for which $h$ need not be even.

By [Platt and Trudgian, Theorem 1](https://arxiv.org/abs/2004.09765), the zero terms through $|\Im\rho|\le H=3\cdot10^{12}$ are nonnegative (use conjugation and the alternating eta series on the real interval $(0,1)$). Elsewhere $|\gamma-t|\ge|\gamma|/15$, and $|h(x+iu)|\le4000/x^2$ for $|u|\le1/2$. [Hasanalizade, Shen, and Wong, Corollary 1.2](https://arxiv.org/abs/2107.06506) gives $N(Y)\le Y\log Y$ for $Y\ge H$: Their error from the usual main term is at most $.1038\log Y+.2573\log\log Y+9.3675<\log Y$. Each shell $Y<|\gamma|\le2Y$ has count at most $4Y\log(2Y)$. Summing at $Y=2^jH$, the total absolute cost of unverified zeros and the two poles is at most

$$ (16000\cdot15^2/H)(2\log(2H)+2\log2)+8000/t^2<0.001. $$

For the archimedean term compare the [digamma series](https://dlmf.nist.gov/5.7.E6) with the integral of $(s+z)^{-1}$ on each unit interval. The sum-integral difference is bounded by $\int_0^\infty|s+z|^{-2}ds$, so at $z=1/4+iu/2$ we have $|\psi(z)-\log z|\le\min(4,\pi/|u|)$. At $u=t+v$, subtract $\log(t/(2\pi))$ from the symbol. For $|v|\le t/2$ the result is bounded above by $(|v|+1+2\pi)/t$, using $\sqrt{u^2+1/4}\le t+|v|+1$. The truncated first absolute moment of $h$ is at most $16+32\log(t/2)$. For $r=|v|>t/2$ the symbol difference is at most $4+\log(4r/t)$; integrate against $16/r^2$. Altogether

$$ A-K(0)\log(t/(2\pi))\le\frac{16+32\log(t/2)}{2\pi t}+\frac{2(1+2\pi)}t+\frac{32(5+\log2)}{\pi t}<0.043. $$

The last expression decreases from $t=3000$. Dropping the verified zero terms now gives $P<K(0)\log(t/(2\pi))+0.044$.

## Keep small-prime powers together

For $n=p^m$, $v=\log n$, the correlation divided by $R\sqrt n$ and multiplied by $\log p$ is $A_n+e^{i\phi} C_n$, where

$$ A_n=\frac{2\log p}{R}(1/n-1/R)_+,\qquad C_n=\frac{\log p}{X}\min(v,(D-v)_+). $$

Indeed each same-half product integrates to $e^{-v/2}(1-e^{v-D/2})_+$, and the cross product integrates to $e^{(v-D)/2}\min(v,(D-v)_+)$ before rotation. Dividing the explicit inequality by $2R$ therefore bounds $\sum_n A_n\cos(tv)+C_n\cos(tv-\phi)$ by $G=((1-1/R)\log(t/(2\pi))+0.022)/R$.

Let $\Delta_n=\mathbf1_{m=1}w_p-C_n$. For $m=1$ this is $X^{-1}\log p\,(D-2v)_+$, and all corrections vanish for $p>R$. For either $s=\pm1$ use $e^{i\phi}=s$ and bound the remainder **once per prime**, not once per power:

$$ s\Re S(t)\le G+\sum_{p\le R}\max_{0\le\theta\le\pi}\sum_{m:p^m\le X}(s\Delta_{p^m}-A_{p^m})\cos(m\theta). $$

For arbitrary rotation the triangle inequality instead gives $|S(t)|\le U=G+\sum_n(|\Delta_n|+A_n)$ by choosing $\phi=\arg S(t)$. At $t=2y$ this suffices: Project the signed ramp on its own argument $\alpha$, then use Cauchy–Schwarz and the double angle formula to bound its modulus by

$$ \sum_p w_p|\cos(y\log p-\alpha)|\le \sqrt{M(M+|S(2y)|)/2}. $$

## Replay and scope

Run `sage -python .godel/bob/check-weil-principal-band.py` with SageMath 10.9 and NumPy. The checker covers intervals of width $1/32$ in $\log_2 q$; it encloses the coefficients and mass on the *whole interval*, with positive parts at prime entries. The time enters only through the increasing logarithm in $G$ and the verified range. For each cosine polynomial it rounds coefficients and cosine nodes separately with explicit errors, checks integer dot-product range, and adds $\|P''\|_\infty(\pi/1024)^2/2$ to the maximum on 513 nodes: The derivative vanishes at an interior maximizer, and both endpoints are sampled.

For a dyadic block beginning at $Q=2^k$, the allowed frozen integer is either $\lfloor X(Q)\rfloor$ or one less. Enclose both and price every left-node height within one unit of $[2Q^{3/5},40(2Q)^{3/5}]$. This contains the nodes of every cell intersecting a named harmonic range, regardless of pruning or padded-grid behavior elsewhere. The worst frozen value is below $0.587-5\eta/8$ by more than $0.0001029$, where $\eta=1/\lfloor\sqrt{k+1}\rfloor$. Even adding the allowed $\eta/8$ estimation error cannot mark a cell. This argument does not spend an unverified finite freezing or interpolation allowance.

The first open dyadic search *above the buffered exclusion* starts at $Q=2^{60}$. The verified-height input is a genuine restriction for high harmonics there. Below $2^{42}$ the moving result need not exclude frozen marks; if seeking a buffered comparison there, first price the actual candidate node and only then the $d=6,8$ second-successor terms. Neither a free-phase optimizer nor a point passing a relaxed upper bound supplies that node.
