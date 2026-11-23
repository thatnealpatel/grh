# A fixed zero-free strip bounds the twist list at different heights

Let $q\to\infty$, $1<A<2$, $X=(A\log q)^2$, $D=\log X$, and fix $\theta,\kappa>0$. Twist a primitive base $\xi$ of conductor $q$ by distinct fundamental discriminants $|d|\le X^\theta$ coprime to $q$, including $d=1$. Write $c_d=q|d|$ and $Q_d(y)$ for the unit Weil quotient on the [endpoint profile](endpoint-arithmetic-test.md) at its own diameter $2\log(A\log c_d)$ and modulation $y$.

**Result using a fixed strip.** Suppose primitive nonprincipal quadratic Dirichlet $L$-functions have no zero in $\Re s>\beta_0$, for some fixed $0<\beta_0<1$. Take $T=\exp(\kappa D^2)$, or more generally $T=\exp(X^a)$ for any fixed $0<a<1-\beta_0$.

* For a **real base**, at most **one** $d$ has $Q_d(y)\le0$ anywhere in $[-T,T]$. In fact all but at most one have $Q_d(y)/\log c_d\ge 1-A/2-o(1)$ throughout this band. If any twist fails, all the others have the stronger margin $2-A-o(1)$. The base need not be good.
* For an **arbitrary primitive base**, there are at most $\lfloor A^2\rfloor$ endpoint exceptions in each single interval $[H-T,H+T]$, uniformly in $H$. This list may depend on $H$. Only this Gram argument, not the real signed-pair argument, needs difference heights alone.
* For any fixed $C>4A$, outside a possibly different list of at most $\lfloor C^2\rfloor$ twists, the quotient is $\ge\nu\log c_d$ on every unit compact input at the specified diameter and every [specified Pick block input](short-cell-weil-list.md#turn-the-prime-measure-into-one-crossing-operator) with at most $\eta$ of its squared Fourier mass outside $[-T,T]$. Here $\eta,\nu>0$ are fixed and sufficiently small. This last argument also works for $A\ge1$.

## What supplies the hypothesis

[OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8*, Theorem 1.1, p. 4, September 30, 2026](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) states the half-plane for **every Dirichlet character**, with the principal pole allowed and the boundary not included. Thus its stated Dirichlet theorem supplies $\beta_0=7/8$, even at real ordinates and without a conductor-dependent exception. Only its quadratic nonprincipal case is used here. The PDF checked has SHA-256 `8fe93046f8cf5ef1ba5969c89addc02d76311adc4ee907509ff9cd96f7ec99e7`.

The [upstream solution declaration](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean) concludes nonvanishing of Mathlib's `DirichletCharacter.LFunction` with the strict real-part and principal-pole hypotheses. It is distinct from the placeholder in the comparator **challenge**. A [separate comparator log](https://github.com/mathcommunity/oai-math-revised/blob/e257182a114c268898c89d221ec491cb2d9cd7fa/checks/comparator-2026-10-26/logs/DirichletSevenEighths.log) records default-kernel acceptance. An [independent rebuild report at the exact upstream pin](https://github.com/tomoto0/quasi-riemann-hypothesis-7-8-verification/tree/b83a73c6cb626a391e551baafdb7d0cceafaa55a) includes the retyped Dirichlet signature and `#print axioms` output for the solution declaration: `propext`, `Classical.choice`, and `Quot.sound`. These are external verification records, not a local rebuild, a check of every manuscript step, or a formalization of the transfers below. The paper argument here isolates the exact dependency; the [subpower count](relative-height-weil-list.md) does not use it.

## The product mean at the original endpoint weight

Put $m=[|d_i|,|d_j|]\le X^{2\theta}$ for $i\ne j$, and let $\psi=\chi_{d_i}\chi_{d_j}$ modulo $m$. If it were principal, the two primitive quadratic characters would have equal lifts and hence equal primitive inducers. Thus its inducer $\psi^*$ is nonprincipal, of conductor $f\mid m$, including when one input is $d=1$. There is **no base conductor $q$** in this bound.

Fix $\beta_0<\sigma<1$. On $\sigma\le\alpha\le2$ we have uniformly

$$ |L'/L(\alpha+iu,\psi)|\ll_{\sigma,\beta_0}\log(2m(2+|u|)). $$

Indeed, take the disk about $2+iu$ of radius $2-(\beta_0+\sigma)/2$. For the primitive inducer its logarithm is holomorphic there, normalized to the bounded Euler-product logarithm at the center. The real part is bounded above by $O_{\beta_0,\sigma}(\log(2f(2+|u|)))$: Partial sums of the character are $O(f)$ by complete periods, so $L(z)=z\int_1^\infty (\sum_{n\le v}\psi^*(n))v^{-1-z}dv$ gives polynomial growth on the disk. Apply Borel–Carathéodory on a smaller concentric disk of radius strictly between $2-\sigma$ and the original radius, then Cauchy's derivative estimate inside radius $2-\sigma$. The missing Euler factors $1-\psi^*(p)p^{-z}$ for $p\mid m$, $p\nmid f$, cost in total $O_\sigma(\log m)$ in the logarithmic derivative. We have used neither nonvanishing on the boundary nor a bound for the principal logarithmic derivative.

Mellin inversion of $\log^+(U/n)$ gives

$$ \sum_{n<U}\Lambda(n)\psi(n)n^{iv}\log(U/n)=-\frac{1}{2\pi i}\int_{(2)}\frac{L'}{L}(s-iv,\psi)\frac{U^s}{s^2}\,ds. $$

Shift to $\Re s=\sigma$; there is no residue. At horizontal heights $V\to\infty$, $V>2|v|+2$, the log bound and $|s|^{-2}$ make the horizontal integrals vanish. On the new vertical the logarithm is bounded by $O(\log(2m(2+|v|))+\log(2+|\Im s|))$, integrable against $|s|^{-2}$. Write $M_p(U,v)$ for the same sum restricted to primes. For $U\ge 3$ this gives

$$ |M_p(U,v)|/U \ll_{\beta_0,\sigma} U^{\sigma-1}\log(2m(2+|v|))+U^{-1/2}\log^3(2U). \tag{1} $$

For the last term there are at most $O(\sqrt U\log U)$ prime powers of exponent at least two, each costing at most $\log^2 U$. Imprimitive erasures are already in (1). At $U=X$, $|v|\le2T$, the right side is uniformly $o(1)$: For $T=\exp(\kappa D^2)$ any fixed $\beta_0<\sigma<1$ works; for $T=\exp(X^a)$ choose $\beta_0<\sigma<1-a$. Both savings survive fixed powers of $D$. At $a=1-\beta_0$ this step does not give the required precision.

## Signed pairs versus the Gram bound

Set $b_p=X^{-1}\log p\log(X/p)$ on $p<X$, of total mass $1+o(1)$ by PNT, and $h_d(y)=\Re\sum b_p\xi(p)\chi_d(p)p^{iy}$. The [endpoint identity](endpoint-arithmetic-test.md) gives, uniformly in $y$,

$$ Q_d(y)/\log c_d=1+\log(2+|y|)/\log c_d-Ah_d(y)+o(1). \tag{2} $$

Here $X_d=(A\log c_d)^2$ differs from $X$ by a relative $O_\theta(D/\log q)$; the change in the normalized log weight in total variation is $O(\log(X_d/X))$ by partial summation and Chebyshev. Prime powers at $X_d$ cost $O(X_d^{-1/2}\log^3 X_d)$ in the mean. Neither error differentiates the phase. The Gamma term in (2) may be kept as a **lower** bound even at very large translated heights. A failure needs $h_d(y)\ge1/A-o(1)$.

If $\xi$ is real, put $u_i=\chi_{d_i}(p)\cos(y_i\log p)$. Pointwise $\xi(p)(u_i+u_j)\le|u_i+u_j|\le1+u_i u_j$ even at vanishing character values (square the last inequality using $(1-u_i^2)(1-u_j^2)\ge0$). The cosine product identity gives

$$ h_{d_i}(y_i)+h_{d_j}(y_j)\le1+o(1)+\frac{1}{2X}\Re\{M_p(X,y_i+y_j)+M_p(X,y_i-y_j)\}=1+o(1) $$

for any two distinct twists and any two heights in the centered band, by (1). Two failures require $2/A-o(1)>1+o(1)$. More precisely, the second largest twist maximum of $h_d$ is at most $1/2+o(1)$, and if one maximum is at least $1/A-o(1)$ the others are at most $1-1/A+o(1)$. Substitution in (2) gives the two positive margins above. This counts distinct twists, not the number of bad heights on one twist.

If the base is complex, normalize $b_p$ to probability weights. Form the Gram matrix of $\overline{\chi_{d_i}(p)p^{iy_i}}$ on a fixed sublist of $J$ witnesses. The diagonal is at most one; off the diagonal (1) gives $o(1)$ since only $y_i-y_j$ occurs. The top eigenvalue is at most $1+o(1)$ by the row sum bound. The sum of squared peak moduli is at most this eigenvalue since the common vector $\xi(p)$ has norm at most one. For $J=\lfloor A^2\rfloor+1$ this contradicts $J(1/A-o(1))^2>1+o(1)$, including when $A^2$ is an integer. An arbitrary translation does not affect this proof.

## The sharp multiplier has a different weight

Use the enlarged $Y=(A\log(qX^\theta))^2\exp((\log\log q)^{-1/2})\sim X$ and $S=\sum_{p\le Y}\log p/\sqrt p\sim2\sqrt X$. To use the Gram argument with weights $\log p/(S\sqrt p)$ we need its off-diagonal to be $o(1)$ for these weights, not merely for $b_p$.

For $X/D^2\le U\le 2X$, difference the **unnormalized** $M_p$ at $e^h U$ and $U$, with $h=D^{-2}$, then divide by $h$. This counts each prime $p\le U$ with its full coefficient $\psi(p)p^{iv}\log p$; the boundary costs at most $O((hU+1)\log(2U))$ by counting integers. By (1) the resulting sharp prime sum through $U$, divided by $U$, is uniformly

$$ \ll D^4X^{\sigma-1}\log(2m(2+2T))+D^6 X^{-1/2}+D^{-1}=o(1). $$

Consequently partial summation gives $o(\sqrt X)$ for the $p^{-1/2}$-weighted prime-log sum through $Y$; the discarded $p\le X/D^2$ cost $O(\sqrt X/D)$ by Chebyshev. Divide by $S$. The same Gram proof now excludes $\lfloor C^2\rfloor+1$ distinct twists with multiplier peaks of normalized modulus $\ge1/C$.

Outside that peak list, apply the [multiplier reduction](hybrid-height-weil-list.md#two-reductions-to-one-counting-problem): The signed prime cost on a stated unit input is at most $2S(1/C+\eta)+o(\sqrt X)$ by integrating over its Fourier probability measure. Prime powers through $Y$ cost $O(D)$, larger shifts vanish on compact tests, and the cited block tail for shifts above $Y$ costs $o(1)$. Since Gamma is bounded below and $4A/C<1$, small fixed $\eta,\nu$ suffice. This proves the restricted floor, not a converse from a peak to an admissible bad input.

**Next decision.** For an all-height real endpoint list, (2) and $h_d\le1+o(1)$ already rule out failure when $\log(2+|y|)>(A-1+\epsilon)\log q$ for fixed $\epsilon>0$. In the intervening range, keep the Gamma contribution: A failing pair would require the real part of the average of its two normalized product means to be at least $2/A-1+\sum_{k=i,j}\log(2+|y_k|)/(A\log c_{d_k})-o(1)$. Can this **one-sided**, height-dependent threshold be excluded on the remaining pairs? At $|v|=q^b$ for fixed $b>0$, the first term of (1) at $U=X$ only gives order $X^{\sigma-1/2}$, not $o(1)$ with the cited $7/8$ strip. Neither a single discriminant's sign nor an unrestricted Weil floor follows from the bounded list.
