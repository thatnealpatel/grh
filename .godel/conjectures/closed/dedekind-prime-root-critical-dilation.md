---
evidence_revision: a954fef4e3a0db9c2124fbeb457b881886b18b47
outcome: established
---

# A rational-prime root-count comparison for Dedekind zeta

Fix one monic irreducible nonconstant polynomial $f$ in
$\mathbb Z[T]$, and let $K=\mathbb Q[T]/(f)$. This includes
linear $f$. A good prime is a rational prime not dividing
$\operatorname{disc}(f)$; $N_f(p)$ counts distinct roots in
$\mathbb F_p$. For an integer $m\ge2$ let
$h_m=\mathbf{1}_{[0,\log 2]}^{*m}$ in the log variable. Set

$$B_m(X)=\sum_{p\ {\rm good}}N_f(p)\log p\,
 h_m(\log(p/X))-X,\qquad
 S_m(X)=\sum_{p\ {\rm good}}\log p\,h_m(\log(p^2/X)).$$

**Proposition to test:** For each such fixed $f$, all
nontrivial zeros of $\zeta_K$ have real part $1/2$ if and
only if there exist an integer $m\ge2$ and $A\ge1$ with

$$\sqrt 2\,B_m(X)-B_m(2X)\le S_m(X)
\qquad\text{for every real }X\ge A.$$

The order is fixed before $X$ varies. Neither $K/\mathbb Q$
Galois, Artin holomorphy, a real-axis zero-free premise,
nor uniformity in $f$ is assumed.

**Source and payoff:** This is an operator extension of the
[critical prime-square allowance](../closed/critical-dilation-prime-square-allowance.md)
at the evidence revision and its
[real-character precursor](../closed/real-character-prime-spline-dilation-comparison.md)
at `25e564b06ce948bd41fbc69aa73f1df306a7f043`. Neither
landing asserts the extension. It would encode Dedekind
zero location using one polynomial's rational-prime root
counts, including ordinary RH when $f$ is linear.

**Discriminating test:** Derive both transforms from the
Dedekind Euler factors on rational primes, tracking the
square coefficient by the Frobenius cycle counts, including
degree-two primes. Check the coefficient on good split and
inert primes in a quadratic example, and the centering in
the linear case. Separate the finite excluded primes,
including index primes, from all exponents at least three.
Extract the square-scale term with fixed-field Chebotarev
and partial summation, and test its cancellation and the
central-zero cancellation against the allowance. Derive
the fixed-order spline contour shift with the pole at one
and account for trivial and archimedean terms. Test whether
the noncentral zero budget contracts below the allowance
for one fixed order. For the converse, transform the
nonnegative tail directly, keeping the centering integral
separate from the entire finite-prime-sum correction. Test
the pole cancellation at one, all open-half-plane zero
residues, and the real-abscissa Landau step.

## Adjudication

**Yes.** The unsigned squares provide the margin, but they are not the squares that must be removed from the Euler product. The latter have a field-dependent mean. Critical dilation removes that mean; no estimate uniform in the field or in the spline order is needed.

### Isolating the observable

Write $n=\deg f$ and $d_{\mathfrak p}$ for the residue degree over $p$. In $-Y=-\zeta_K'/\zeta_K$, the coefficient of $p^{-js}$ is $c_j(p)\log p$, where

$$c_j(p)=\sum_{\mathfrak p\mid p,\ d_{\mathfrak p}\mid j} d_{\mathfrak p}\le n.$$

This follows by logarithmically differentiating the local factors $(1-p^{-d_{\mathfrak p}s})^{-1}$. The bound follows from the degree formula, including at ramified primes. At a good prime the discriminant-index formula excludes both an index divisor and ramification in $K$. Dedekind factorization identifies these degrees with the degrees of the distinct factors of $f\bmod p$. In the splitting field $L$, good primes are unramified: The distinct residue roots all lift over an unramified local extension by Hensel's lemma. Frobenius $g_p$ permutes the roots in cycles of the factor degrees. Thus $c_1=N_f(p)$, while

$$c_2=\#\operatorname{Fix}(g_p^2)=N_f(p)+2\#\{\mathfrak p\mid p:d_{\mathfrak p}=2\}.$$

In particular these are **prime ideal powers**, not arbitrary ideals of norm $p^2$. For an independent check, for $T^2-5$ at $p=3,11$ the distinct root counts over $(\mathbb F_p,\mathbb F_{p^2})$ are $(0,2),(2,2)$; for $T^3-2$ at $5$ they are $(1,3)$. These counts can be reproduced by enumerating $x+y\sqrt d$ over $\mathbb F_p$, taking $d=2$ in all three cases. They agree with the first two coefficients of $uZ'_p/Z_p$ for $Z_p=\prod_{\mathfrak p\mid p}(1-u^{d_{\mathfrak p}})^{-1}$. For $T^2-5$, both $2$ (index) and $5$ (ramification) are bad. For linear $f$, all primes are good and both coefficients are one.

Let $\Phi(s)=\int_0^{\log 2}e^{st}dt=(2^s-1)/s$ with its removable value at zero, $k=\Phi(1/2)$, and $D(s)=\sqrt2-2^s$. The transform of the spline is $\Phi(s)^m$. At each of the finitely many bad primes the interval $X\le p^j\le 2^m X$ contains at most $1+m\log 2/\log p$ choices of $j$, so all omitted bad terms cost $O_{f,m}(1)$ in the spline sum. The good $j\ge3$ cost $O_{f,m}(X^{1/3}\log^2(2X))$ for $X\ge1$, since $p\le(2^m X)^{1/3}$, $j\ll_m\log(2X)$, and $h_m$ is bounded.

By the unconditional Chebotarev prime number theorem in the fixed Galois extension $L/\mathbb Q$, weighted by $\log p$ via partial summation, $\sum_{p\le y,\ {\rm good}} c_2(p)\log p=\mu y+o_f(y)$, where $\mu$ is the group average of $\#\operatorname{Fix}(g^2)$. Ordinary PNT gives coefficient one instead for the allowance. With $T=\sqrt X$, integrate these two asymptotics against $v\mapsto h_m(2\log v)$ at scale $p=Tv$. This weight has bounded variation on its fixed support $[1,2^{m/2}]$, where the scaled counting errors are uniformly $o(T)$. Its integral in $dv$ is $\frac12\int h_m(t)e^{t/2}dt=k^m/2$. The discarded good square sum and $S_m(X)$ are consequently $\mu T k^m/2+o_{f,m}(T)$ and $T k^m/2+o_{f,m}(T)$, respectively.

### From zero location to one fixed order

Use the classical continuation and functional equation of Dedekind zeta, its simple pole at $1$, and the order-one entire function obtained by multiplying the completed zeta by $s(s-1)$. Its zeros are exactly the nontrivial zeros; let $w_\rho$ denote multiplicity at a distinct zero. Suppose they lie on the line. Fourier inversion on $\Re s=2$ gives the full prime-power spline sum as the integral of $-Y(s)X^s\Phi(s)^m\,ds/(2\pi i)$. The Euler series is absolute, $\Phi(s)^m$ is integrable for $m\ge2$, and $h_m$ is continuous even at knots.

Shift to $\Re s=1/4$. To justify the shift, the real part of the completed entire function's Hadamard logarithmic derivative at $2+it$ gives $\sum_\rho w_\rho/(1+(t-\Im\rho)^2)\ll_K\log(3+|t|)$: Each real part of $(2+it-\rho)^{-1}$ dominates a constant times the weight, the real parts of $1/\rho$ are absolutely summable by order one and bounded real parts, and the gamma and Euler derivatives at $2+it$ satisfy the stated bound by Stirling and absolute convergence. Subtract the product derivative there from the one at $\sigma+it$, $1/4\le\sigma\le2$. Differences from zeros at ordinate distance greater than one are bounded by the same summable weights. On the new vertical each of the $O_K(\log(3+|t|))$ nearby zeros is at distance at least $1/4$. For the horizontal edges choose heights tending to both infinities in successive unit intervals, deleting intervals of radius $c_K/\log(3+|t|)$ around nearby ordinates; the local count leaves room for small $c_K$. Removing the elementary and gamma derivatives therefore bounds $Y$ by $O_K(\log(3+|t|))$ on the new vertical and $O_K(\log^2(3+|t|))$ on these edges. The kernel is $O_m((1+|t|)^{-m})$ throughout the strip. The edges vanish for each $X$; the vertical costs $O_{K,m}(X^{1/4})$.

No archimedean pole or trivial zero is crossed. The pole of zeta contributes $X\Phi(1)^m=X$, independent of the field's zeta residue. The full spline sum is thus

$$X-\sum_\rho w_\rho X^\rho\Phi(\rho)^m+O_{K,m}(X^{1/4}).$$

The sum is absolute by the inverse-square zero sum. After subtracting $X$ and the omitted Euler terms, the constant contribution to $B_m(X)/(T k^m)$ is $-w_{1/2}-\mu/2$ (zero multiplicity if absent). Both constants disappear under dilation. In fact, putting $z_\rho=\Phi(\rho)/k$ and $\gamma=\Im\rho$, one obtains

$$\frac{\sqrt2 B_m(X)-B_m(2X)}{T k^m}
=-\sum_{\gamma\ne0}w_\rho D(\rho)z_\rho^m X^{i\gamma}+o_{f,m}(1).$$

Strict triangle inequality for the nonconstant phase $e^{i\gamma t}$ against $e^{t/2}dt/k$ gives $|z_\rho|<1$ for every noncentral zero. The absolute budget is dominated termwise by $2\sqrt2\,w_\rho|z_\rho|^2$, summable by the same inverse-square bound. Hence one can first choose $m\ge2$ with budget $<1/8$ by dominated convergence. For this order alone, take $A$ large enough that the normalized error is $<1/8$ in modulus and $S_m(X)/(T k^m)>3/8$ for every real $X\ge A$. This proves the comparison.

### From the centered tail to zero location

Fix an order and threshold from the comparison. Put $P=B_m+X$ (that is, $P(X)=B_m(X)+X$), $H=S_m-\sqrt2 B_m+B_m(2\,\cdot)$, and $Q(u)=\sum_{p\ {\rm good}}(\log p)p^{-u}$. Let $R$ be the discarded Euler series (all bad terms and the good $j\ge2$ terms of $-Y$). The series for the observed primes is $-Y-R$. Both $Q(2s)$ and $R(s)$ converge normally on $\Re s>1/2$: For good prime powers use $n\sum_p(\log p)p^{-2\sigma}/(1-2^{-\sigma})$ on $\Re s\ge\sigma>1/2$; the finite bad Euler tails converge already on $\Re s>0$.

For $U=P,S_m$ put $I_U(a,s)=\int_0^a U(X)X^{-s-1}dX$. These integrals are entire: On bounded intervals only finitely many primes occur, and the splines vanish near zero. The Mellin transform of a full $p^j$ spline is $p^{-js}\Phi(s)^m$ by $t=\log(p^j/X)$. In the dilated tail change variables to $2X$, so its endpoint becomes $2A$. Termwise integration for $\Re s>1$ gives

$$\begin{aligned}
F_A(s)&=\int_A^\infty H(X)X^{-s-1}dX\\
 &=\Phi(s)^m[Q(2s)+D(s)(Y(s)+R(s))]
   +E_A(s)+D(1)\frac{A^{1-s}}{s-1},\\
E_A(s)&=-I_{S_m}(A,s)+\sqrt2 I_P(A,s)-2^s I_P(2A,s).
\end{aligned}$$

Only $E_A$ is the entire endpoint correction. The slack near zero equals $D(1)X$, not zero. The last term comes from integrating this linear centering contribution on the **tail**. Its residue $D(1)$ cancels the residue $-D(1)\Phi(1)^m$ from $Y$ at $1$. This cancellation also holds for linear $f$, where $Y=\zeta'/\zeta$; it would fail with a different coefficient of $X$. The continued transform has precisely the zero poles of zeta in $\Re s>1/2$, with residues $w_\rho D(\rho)\Phi(\rho)^m$. Neither factor vanishes there since $|2^s|>\sqrt2$. At a real zero the residue is strictly negative.

Let $b\le1$ be the abscissa of convergence of the nonnegative tail, possibly $-\infty$. The integral is holomorphic on $\Re s>b$ and equals the continuation on $\Re s>\max(b,1/2)$. Suppose $b>1/2$. If regular at $b$, choose $\epsilon>0$ so small that the continuation has a disk of regularity of radius $4\epsilon$ about $b$ in this half-plane of meromorphic continuation. At $u=b+\epsilon$ its Taylor coefficients in $u-s$ are $\int_A^\infty H(X)X^{-u-1}(\log X)^j dX/j!$, by domination using convergence at $b+\epsilon/2$. All are nonnegative since $A\ge1$. At $s=b-\epsilon$ the Taylor sum is finite, and monotone convergence identifies it with the defining integral, contradicting the abscissa. If instead $b$ is a pole, its negative residue makes $F_A(u)\to-\infty$ as real $u\downarrow b$, impossible for a nonnegative integral inside convergence. Thus $b\le1/2$. Holomorphy now excludes every zero pole strictly to the right, and the functional equation excludes the reflected zeros strictly to the left.

This proves the equivalence without selecting a rightmost zero, treating a boundary pole as an interior pole, or using Artin holomorphy. It gives a criterion for ordinary RH in degree one, not a proof of the comparison for that field or any other.
