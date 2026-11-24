---
evidence_revision: 25e564b06ce948bd41fbc69aa73f1df306a7f043
---

# A prime-square allowance at the critical dilation

Fix any primitive nonprincipal Dirichlet character $\chi$
of conductor $q$, real or nonreal. For an integer $m\ge2$
let $h_m=\mathbf{1}_{[0,\log 2]}^{*m}$ under ordinary real
convolution. For $X>0$ define

$$W_m(X)=\sum_p\Re\chi(p)\log p\,h_m(\log(p/X)),\qquad
S_m(X)=\sum_{p\nmid q}\log p\,h_m(\log(p^2/X)).$$

**Proposition to test:** All nontrivial zeros of $L(s,\chi)$
lie on $\Re s=1/2$ if and only if there exist one integer
$m\ge2$ and one $X_0\ge1$ such that

$$\sqrt2\,W_m(X)-W_m(2X)\le S_m(X)\qquad (X\ge X_0).$$

The order and threshold may depend on $\chi$. The order is
fixed over all real $X\ge X_0$. There is no chosen phase,
real-axis nonvanishing premise, or conductor uniformity.
The allowance counts genuine prime squares with $\log p$,
not $\log(p^2)$.

**Source and payoff:** The operator proposes this as a
single-comparison replacement for the real-character
[family of comparisons](../closed/real-character-prime-spline-dilation-comparison.md)
at the evidence revision, built on the
[fixed-character sign criterion](../closed/real-character-prime-spline-eventual-sign.md)
at `d3675071daa1e1afbff4107024f1a9943855a43b`. Bob's
[fixed-strip estimate (1)](../../bob/fixed-strip-endpoints.md#the-product-mean-at-the-original-endpoint-weight)
at `bbca37033019090f6f40e6223b5054d382c9d789` is a magnitude
bound with a different weight and premise. None of these
sources asserts the proposed critical-dilation criterion.
The payoff would be a characterization for complex as well
as real characters, not an independent proof of the
comparison or an equivalence with a prime-only comparison.

**Discriminating test:** Use the holomorphic average of the
logarithmic derivatives for $\chi$ and $\overline\chi$.
Derive the fixed-order explicit formula, keeping
multiplicity at shared and real zeros. Audit the square
mean of $\Re(\chi(p)^2)$ by fixed-modulus prime arithmetic
and the separate positive mean of $S_m$. Test whether the
critical factor removes all constant $\sqrt X$ terms and
whether summable kernel contraction beats that allowance
for a fixed order, even at small nonzero ordinates.
Conversely, carry $S_m$ and the finite endpoint corrections
through the Mellin transform of the nonnegative tail.
Locate its singularities, test the residue sign at a real
abscissa above $1/2$, and check all possible multiplier
cancellations and the reflection for a nonreal character.
