# A fixed-third price at depth 39/20

**Decision.** The [six-pair refit](priced-deletion-33.md) cannot reach positive failure surplus at exactly $39/20$ by splitting its last replacement fraction at $27/5$. More generally, even replacing **every slab law** by any probability law on $0\le u\le1$, adding negative slabs back to $-12.48$, and splitting the positive tail into 81 independently refittable slabs, does not work on either of the specified meshes if the third field is kept fixed. But if negative slabs can go arbitrarily far left, **no finite set of sampled $t$ frequencies can rule out positive surplus**, even with $B$ kept fixed. That last fact does not give a law satisfying the continuous $t$ cap.

## Setup and bounds

Use the accepted seed at `c6f94db30246183a4793d89638d1191a4c73ce32`, [`delete-33-unfolded-seed.txt`](deletion-laws/delete-33-unfolded-seed.txt), SHA-256 `2cd7c50f9e286a845f103c80f90d778ef4879945384e5a9f6bd86b2d85783875`. Put $X=2u^2-1$, $T(X)=4X^3-3X$, and $(A,B,U)=(\mathbb E X,\mathbb E T(X),\mathbb E u)$; write $M=\int z_+e^{-z}U(z)\,dz$. Since $B(z)$ is unchanged on the whole line, the [exact-depth $3t$ cap and second-reply completion](priced-deletion-33.md#preserve-the-input-to-the-three-site-problem-not-both-first-fields) need no new estimate. At $t$ the required cap is $|V_A(\xi)|\le1$ for every real $\xi$, in the jump convention

$$ V_A(\xi)=\frac{\sum_j e^{(-1/2+i\xi)z_j}\Delta A_j}{C_t(1/2+i\xi)},\qquad C_t=\frac{\cosh(39/20)}{6\cos(\pi/12)}. $$

The modulus is also the modulus of the normalized Fourier field with denominator $1/2-i\xi$; the phase for each recorded cut uses the displayed convention.

| Family | Certified upper bound on $M-8/9$ under the $t$ cap |
|:---|---:|
| Six named pairs, one arbitrary fraction in $[0,1]$ each | $<-2.6734\cdot10^{-6}$ |
| Same pairs, independently split the last fraction at $27/5$ | $<-2.6688\cdot10^{-6}$ |
| Arbitrary fixed-$B$ laws, 586 slabs below | $<-6.29\cdot10^{-7}$ |
| Arbitrary fixed-$B$ laws, 868 slabs (halve every negative slab of the 586) | $<-1.22\cdot10^{-7}$ |

For the first two rows, the fractions are independent, not the fractions of the nearby-depth witness. The pair weights are reconstructed rationally from $B$ and checked. The cap cuts add an allowance to the seed surplus and leave a residual linear coefficient $r_j$ for each fraction. We add $\max(0,\operatorname{upper}(r_j))$ for each one, so rounded dual weights need not give exact stationarity.

For the last two rows retain every seed knot. Add left knots $-4.48-j/10$ for $1\le j\le80$, with $B=0$ on each added slab. As in the seed, $A=B=0$ on the ray left of the first knot. Add right knots $4.4+j/5$ for $1\le j\le80$, with the terminal seed $B$ on each slab. The last slab runs to infinity. No atom grid, bound on the change of $A$, or positivity of the change of $A$ is imposed by the certificate. The three-site completion is not being used as a necessary bound on the new laws; we use only $B$ invariance and necessary cuts of the $t$ cap.

## Price the law on each slab

For a cut $(\lambda,\xi,p)$, $\lambda\ge0$, use $\operatorname{Re}(\overline p V_A(\xi))\le|p|$. Sum the cuts, writing the resulting left side as $\sum_I d_I A_I$ where, for $I=[l,r)$,

$$ d_I=\sum_{(\lambda,\xi,p)}\lambda\operatorname{Re}\frac{\overline p\,(e^{(-1/2+i\xi)l}-e^{(-1/2+i\xi)r})}{C_t(1/2+i\xi)}. $$

Use zero for the exponential at infinity. If $w_I=\int_I z_+e^{-z}\,dz$, then

$$ M-8/9\le\sum\lambda|p|-8/9+\sum_I \sup_{\mathbb E[T(X)]=B_I}(w_I U_I-d_I A_I). $$

For $w_I=0$ take $-f(-B_I)\le A_I\le f(B_I)$, where $f(b)=\cos(\arccos(b)/3)$. The top inverse branch $f$ is the inverse of the increasing convex part of $T$ on $[1/2,1]$. Thus it is concave and $X\le f(T(X))$; Jensen gives the upper bound and symmetry gives the lower bound. Both endpoints are attainable with one atom.

On every other slab independently nominate a real $\beta$ and certify a constant $h$ such that

$$ w_Iu-d_I(2u^2-1)-\beta(32u^6-48u^4+18u^2-1-B_I)\le h\qquad(0\le u\le1). $$

The multiplier term averages to zero. The checker bounds the entire sextic by subdividing its Bernstein coefficients using de Casteljau's rule, then sums the certified upper bounds using 128-bit Sage balls. Float evaluations are used only to propose $\beta$ and a ceiling for the polynomial; failure of any covering bound aborts or widens that ceiling. The certificate does not need to establish an LP optimum.

## Search, replay, and next decision

The tangent-cut LP used SciPy 1.18.1 / HiGHS IPM with moment changes scaled by $10^6$. On negative slabs it used the two inverse-branch bounds above and on positive slabs it used the upper hull of fixed-$B$ pairs on 65 uniform atom sites plus each slab's seed sites. It started with seed directions and the four axis directions on a $0.25$ frequency grid to 95, and added directions at sampled local peaks. On the 586-slab run, its objective surplus at iterations 0, 1, 2 was approximately $1.5321\cdot10^{-4}$, $2.4218\cdot10^{-6}$, $-1.7103\cdot10^{-6}$; the sampled moduli reached 1.656, 1.487, 1.415 respectively. For the last solve the maximum linear-cut row violation reported by HiGHS was $2.33\cdot10^{-10}$ in scaled coordinates. None of these laws is a witness. For its certificate we retained 116 positive multipliers above $10^{-10}$, rounded each cut entry to 14 significant decimal digits, and paid for the entire continuum of atoms. Reusing these cuts on the 868-slab mesh would increase the negative-slab price by more than $8.23\cdot10^{-6}$, with the positive price unchanged. We instead reoptimized there, with the same dictionary, spacing $0.22$ to 125, and seed peak cuts. The initial solve reported surplus $-1.8363\cdot10^{-6}$, max sampled modulus $2.757$, and max scaled row violation $3.71\cdot10^{-11}$. Repricing its 154 retained multipliers as above proves the last row. The serialized cut tables for [586](deletion-laws/delete-33-fixed-third-left.duals) and [868](deletion-laws/delete-33-fixed-third-halved.duals) slabs suffice independently of SciPy or the LP outputs. The narrower cuts are embedded in their checker.

Replay from the repository root with SageMath 10.9 and assertions enabled:

```sh
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-split-tail-deletion-33.py
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-fixed-third-left-deletion-33.py
```

The 586- and 868-slab cut prices enclose approximately $-6.2983784\cdot10^{-7}$ and $-1.2262972\cdot10^{-7}$, respectively. Neither is claimed to be the optimal surplus.

## Why finite cuts cannot settle unbounded left support

Start with the seed and change just the positive tail to the single atom $u=\sqrt{(1+f(B_{\rm tail}))/2}$. Its third moment is exactly $B_{\rm tail}$ by the inverse identity. The checker gives $M-8/9>.0010795$; this baseline is **not** claimed to satisfy the $t$ cap.

Let $S$ be any finite set of real test frequencies. Discard repeated absolute frequencies since $V_A(-\xi)=\overline{V_A(\xi)}$, and use real and imaginary coordinates at the positive frequencies, with only a real coordinate at zero if present. On any fixed bounded negative interval the coordinate functions $1$ (when needed), $\cos(\xi z)$ and $\sin(\xi z)$ are linearly independent: equivalently, the exponentials at distinct signed frequencies are independent, as seen by differentiating at one point and using a Vandermonde matrix. Measuring $V_A$ at these frequencies is equivalent to integrating these functions against $e^{-z/2}A(z)$, followed by invertible scalar or complex multiplications at each frequency. This equivalence follows from the slab integral formula, whose denominator is $1/2-i\xi$ rather than $1/2+i\xi$.

If there are $d$ real coordinates, choose $d$ distinct points at which the evaluation columns span $\mathbb R^d$ (otherwise a nonzero functional annihilates all columns). Sufficiently short disjoint slabs around them give invertible integrated columns by continuity, after dividing each by its length. Translating **only these added slabs** left by $L$ multiplies their joint response by $e^{L/2}$ and applies a block rotation by $-\xi L$ at each frequency. Solving the invertible linear system to cancel the baseline at all sites in $S$ therefore requires slab values $A_j=O(e^{-L/2})$, uniformly in $L$ for this fixed $S$. For sufficiently large $L$ the slabs are all left of the first seed knot and $|A_j|\le\sqrt3/2$. Realize each $A_j$ by mixing the two atoms $X=\pm\sqrt3/2$, both of which have $T(X)=0$; the rest of the left ray retains $X=0$. This preserves $B$ exactly and cannot change $M$. The resulting law has $V_A=0$ at every site in $S$ and the same positive surplus. There is no control of the moduli between the sites or on the tails of the frequency line.

## A continuous test that never sees the added left slabs

Write $G_A(\xi)=\int_{\mathbb R}e^{(-1/2+i\xi)z}A(z)\,dz$; the cap says $\|G_A\|_\infty\le C_t$. For real $f\in L^1\cap L^2(0,\infty)$, extend $f$ by zero to the negative half-line. Fourier inversion and Plancherel give

$$\left|\int_0^\infty e^{-z/2}A(z)(f*f)(z)\,dz\right|\le C_t\|f\|_2^2.$$

Indeed the multiplier in frequency is $\widehat f(-\xi)^2$, whose absolute integral divided by $2\pi$ equals $\|f\|_2^2$. This is the quadratic form of the positive-side Hankel operator with kernel $e^{-(s+r)/2}A(s+r)$. The test holds for all the slab laws here since their weighted $A$ is integrable. It is unaffected by any changes to negative slabs. The simplest normalized choice $f(s)=e^{-s/2}$ gives $|\int_0^\infty z e^{-z}A(z)\,dz|\le C_t$. The checker gives values near $0.588278$ on the seed and $0.592081$ on the upper-branch tail modification, below $C_t\approx0.618660$ in both cases: this one test does not exclude the latter. This observation is not a sufficient extension theorem for admissible left laws.

**Next decision.** With a fixed left cutoff, the slab prices can be refined further. For unbounded left support, price a family of the continuous tests above on admissible positive-side laws before deciding whether to move search effort to a genuine continuous Fourier completion or to release $B$ and spend the $3t$ completion slack. Neither the unrestricted comparison at $39/20$ nor the arithmetic lower bound is decided.

## The whole positive-side test passes, but shifting it changes the answer

Keep the seed for $0\le z<4.4$. On the infinite terminal slab mix its law with the upper-branch atom above in proportion $\eta\in[0,1]$ of the atom. This preserves the entire positive-side $B$. At $c=39/20$:

* Even at $\eta=1$, **every** unshifted positive-side Hankel test passes: The operator norm is less than $.617782<C_t$. Thus this entire test family cannot reject the positive profile with surplus $>.0010795$. By convexity and the seed cap, the same holds for every mixture (with norm below $C_t$, not necessarily below $.617782$).
* A single **shifted** test forces $\eta<.121$, for any measurable negative profile with $|A|\le1$ and integrable $e^{-z/2}A$. It imposes no left cutoff, mesh, or fixed negative $B$. In particular, moving negative boundaries arbitrarily far left cannot repair the full replacement, even though it can cancel any finite menu of frequency samples. But positive surplus begins just above $\eta_*=.00301807074\ldots$; the cut does not exclude every mixture with positive surplus.

Here are the norm and sign arguments. For $l\le0$ let $H_l$ on $L^2(0,\infty)$ have kernel $e^{-(l+s+r)/2}A(l+s+r)$. The same Fourier proof as above inserts a unit phase $e^{\pm i l\xi}$, so each normalized form $|\langle f,H_l f\rangle|/\|f\|^2\le C_t$ is necessary. Use real tests $f_y(s)=e^{-s/2}\sum_i y_iL_i(s)$ with ordinary Laguerre polynomials, so $\|f_y\|^2=\sum y_i^2$. To integrate a jump at $x\ge l$, put $t=x-l$ and $c_k=\sum_{i+j=k}y_i y_j$. Its coefficient before dividing by the norm squared is

$$e^{-l/2-t}\sum_k c_k(2L_k(t)-L_{k-1}(t)-L_{k+1}(t)),\qquad L_{-1}=0.$$

Indeed $L_i*L_j=L_{i+j}-L_{i+j+1}$ by Laplace transformation, and $\int_t^\infty e^{-v}L_k(v)\,dv=e^{-t}(L_k(t)-L_{k-1}(t))$. Both identities include index zero.

For $l=0$, $\|H_0\|_{\rm HS}^2=\int_0^\infty z e^{-z} A(z)^2\,dz$. This compact self-adjoint operator has a negative eigenvalue at most the normalized form for $y=(1,6,6,6)$, and a positive eigenvalue at least the form for $y=(1)$. The former form is below $-.05050$, the latter above $.59208$. For the extremal eigenvalue in absolute value subtract the squared bound for the *opposite* sign from the squared Hilbert-Schmidt budget. Taking the weaker subtraction still gives the asserted norm bound, without needing an infinite matrix truncation error.

For $l=-3/5$ the checker gives an integer 32-term test. On $[0,-l]$, exact Bernstein coefficients of $\sum y_iL_i(s)$ all have the same sign, so $f_y*f_y\ge0$ there. Replacing $A$ by $-1$ on $[l,0)$ therefore gives a **lower** bound on the actual shifted form, independent of the negative-side laws. Values below $l$ never enter. The resulting bound is affine in $\eta$, has positive slope, and crosses $C_t$ before $.121$. This excludes a portion of the fixed-positive-interior family for the unfolded cap, not arbitrary positive-side refits or other $t$ realizations. The quoted surplus threshold uses the actual change in $U$, not a first-moment proxy. At mean equality this floor still falls short of $C_t$ by more than $.00049$.

Replay both decisions with `PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-shifted-hankel-deletion-33.py`. To improve the exclusion, price a shifted test at the **least** terminal replacement that pays the mean deficit, not at full replacement. The negative-side contribution must be minimized with its sign; an eigenvalue on a chosen negative continuation alone does not certify that minimum.
