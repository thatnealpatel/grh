# A pole test for the p. 520 window over $\mathbb Q(\sqrt{-5})$

**Result (ordinary mathematics).** Fix $0<\alpha<1/2$. With the quotient Haar measure specified in the manuscript, the two sides of (12.5.1.1)–(12.5.1.3) cannot agree on all radial tests supported above norm one over $F=\mathbb Q(\sqrt{-5})$. They disagree on translates of any nonnegative bump as below, at arbitrarily large translations. This is an obstruction to the *combined* evaluations on p. 520. It does not identify the value of either cutoff trace.

The point of translating the test is to distinguish a normalization error from the omission of zeros. Under a Laplace average in the translation parameter, the finite local sum detects the **order** of the pole of $\zeta_F$, which is one, not its residue. The positive polar moment instead detects the **volume** of $C_F^1$. Zeros in the stated window contribute to neither coefficient.

## Measure and tests

Pages refer to the [pinned edition](../sources/masullo/README.md). Source readings use layout extraction and machine reading of rendered pages, not an independent visual certification. In Theorem 12.5.1.1 the finite coefficient is $\log(q_v)/\mu_v(\mathcal O_v^\times)$, the complex coefficient is $1/(2\pi)$, and $M(\varphi)(c)=\int_{C_F}\varphi(g)c(g)\,d\bar\mu(g)$, with no volume divisor. The proof on p. 520 uses the global Haar $\bar\mu$. With counting measure on $F^\times$ and $dt/t$ on the norm quotient, (A.3.2.1), pp. 559–560, gives

$$V=\bar\mu_1(C_F^1)=\frac{2^{r_1}(2\pi)^{r_2}h_FR_F}{\sqrt{|d_F|}\,w_F}=\frac{2\pi\cdot2}{\sqrt{20}\cdot2}=\frac{\pi}{\sqrt5}\ne1.$$

Here $d_F=-20$, the units are $\{\pm1\}$, the rank-zero regulator is one, and the [class number calculation](isotypic-exhaustiveness-q-sqrt-minus-five.md#the-missing-valuations-and-the-target-character) gives $h_F=2$. Remark 9.2.0.1, p. 403, and (D.2.1.6), p. 794, distinguish this Haar from the canonical $\bar\mu/V$.

Fix a nonzero $b\ge0$ in $C_c^\infty((0,\log 2))$. Write $B(z)=\int b(u)e^{zu}\,du$. For $R\ge0$ put $\varphi_R(g)=b(\log|g|_F-R)$. This is the pullback of a smooth compactly supported function on the Lie quotient $C_F/C_F^1$ with compact kernel, so it belongs to $D(C_F)$. It vanishes on a neighborhood of $C_F^1$ and is invariant under every finite unit group. For each $R$, choose $T>2e^R$ and include in $S$ the archimedean place, the ramified places, and every place of norm $\le T$, closing under places over the same rational prime. Inverting the prime over $2$ kills the class group, so this meets the $S$ conditions on p. 520 for the trivial character. No uniform choice of $S$ is used or needed in the asserted scalar identity.

## The window has lower exponential growth than the polar term

Haar integration over the compact norm fibre kills the Mellin transform on every nontrivial compact character. On the trivial compact character it gives exactly

$$M(\varphi_R)(|\cdot|_F^z)=V e^{zR}B(z).$$

Only the trivial-character Hecke zeros survive. In the window these are the zeros $\rho$ of the finite Dedekind zeta $\zeta_F$, with unchanged orders, since the archimedean factor is holomorphic and nonzero there. For $|\Re z|\le\alpha$, integration by parts gives $|B(z)|\le C_n(1+|\Im z|)^{-n}$ for each $n$. Thus the entire window sum is $O(e^{\alpha R})$, including multiplicities. This bound also works for any order-bounded multiplicities on the closed window.

For the summability in that estimate, use Lemma B.1.1.2, p. 590, which bounds the **finite** Hecke $L$-function polynomially on fixed vertical strips at large height. At $2+it$ the Euler product gives $|\zeta_F(2+it)|\ge\prod_v(1+q_v^{-2})^{-1}>0$ (finite places). For $|t|>5$ the disk of radius $4$ about that point is pole-free. Jensen's inequality bounds the number of zeros in the concentric disk of radius $3$, counted by order, by $O(\log(2+|t|))$, using the strip bound on the outer disk and the lower bound at the center. The inner disk covers $0\le\Re\rho\le1$, $|\Im\rho-t|\le1$. Bounded heights give finitely many zeros by meromorphicity. Summing over unit height bands against the decay of $B$ proves the estimate without any conjecture about the zeros.

## The finite local sum detects the order of the pole

Write $L(R)$ for the displayed local side. All local restrictions vanish near the identity; identity-supported principal-value corrections are zero. At a finite place, only the shells $|g|_v=q_v^k$, $k\ge1$, contribute. On such a shell $|1-g|_v=q_v^k$, and its multiplicative mass is $\mu_v(\mathcal O_v^\times)$ even at ramified places. Thus by (B.4.4.5), p. 620, the finite contribution is exactly

$$L_f(R)=\sum_{v\text{ finite}}\sum_{k\ge1}(\log q_v)q_v^{-k/2} b(k\log q_v-R).$$

This sum is finite for each $R$. At the one complex place put $x=\log|g|_v=2\log|g|_{\rm Euc}$. In $(x,\theta)$ the multiplicative Haar is $dx\,d\theta$ by Definitions A.3.1.2 and A.3.2.2. In the off-identity local density we read the archimedean denominator on p. 519 as the normalized local modulus, as in (B.4.4.16); the subscript is absent in (12.5.1.1). The numerator is $e^{x/2}$ and the denominator is $|1-e^{x/2}e^{i\theta}|_{\rm Euc}^2$, bounded below by $(e^{x/2}-1)^2$. On the support $x\in R+\operatorname{supp}b$, this gives $L_\infty(R)=O(e^{-R/2})$ as $R\to\infty$, and a bounded integral on bounded $R$ intervals. The estimate, unlike an exact evaluation of this term, is insensitive to a fixed complex-place Haar multiplier. Even reading the denominator as an unsquared Euclidean modulus gives $O(1)$ instead, still negligible in the average below.

For $\delta>0$ apply the same linear functional to both sides:

$$\mathcal A_\delta H=\delta\int_0^\infty e^{-(1/2+\delta)R}H(R)\,dR.$$

Put $a=1/2+\delta$. Since $y=k\log q_v\ge\log 2>\sup\operatorname{supp} b$, the substitution $u=y-R$ gives $\int_0^\infty e^{-aR}b(y-R)\,dR=e^{-ay}B(a)$ with no endpoint error. Tonelli's theorem and the absolutely convergent logarithmic derivative of the Euler product give

$$\mathcal A_\delta L_f=\delta B(a)\sum_{v,k}(\log q_v)q_v^{-k(1+\delta)}=\delta B(a)\left(-\frac{\zeta_F'}{\zeta_F}\right)(1+\delta)\longrightarrow B(1/2).$$

Here only the simple pole at one is needed (Proposition 3.2.1.3 and (3.2.1.7), pp. 123–124); its residue cancels in the logarithmic derivative. In particular this does not use a prime ideal theorem or the unrestricted explicit formula. The complex place contributes zero in the limit.

On the printed global side $G(R)$, the positive polar term gives $\mathcal A_\delta[V e^{R/2}B(1/2)]=V B(1/2)$ exactly. The negative polar term and the window sum give $O(\delta)$ by their respective $O(e^{-R/2})$ and $O(e^{\alpha R})$ bounds. Hence

$$\lim_{\delta\downarrow0}\mathcal A_\delta[G-L]=(V-1)B(1/2)\ne0.$$

If the two sides agreed for all sufficiently large $R$, the difference, bounded on every bounded interval by the estimates above, would have average tending to zero. This proves the claimed failure on admissible tests.

**Consequence for the trace comparison.** The [measure comparison](trace-scalar.md#compare-the-measures-on-local-and-global-tests) does not permit setting $V=1$. With the local coefficients held fixed, a common multiplier on the printed global terms is forced to be $1/V$ by this test. This agrees with the factors in the unrestricted (B.4.4.16), p. 623. Alternatively one could retain raw global Haar and multiply the whole local side by $V$. Either change removes this particular discrepancy; neither proves that the normalized local terms minus the polar terms evaluate the same global diagonal as the restricted zero sum. That remains the operator comparison to establish. There is no conclusion here about GRH.

## Lean handoff: Refute the scalar identity before counting zeros

The paper proof above bounds an independently defined zero sum. A shorter Lean target is the negation of *eventual agreement with convergence*: For a fixed bump and any threshold, some later translate fails the proposed `HasSum`. This is the convention used by `RationalRadialStripTrace` in `Proofs/Theorems/RationalRadialStripTrace.lean`. It rules out an identity with an unordered complex sum; it does not give convergence separately or cover a sum defined only by symmetric truncations.

Suppose agreement starts at $R_0$. After proving radial Mellin translation, write each term at $R_0+t$ as $a_i e^{z_i t}$, with $a_i$ the entire multiplicity-weighted term at $R_0$ and $\Re z_i\le\alpha$. The `HasSum` at $R_0$ gives `hs.summable.norm` in $\mathbb C$. For $t\ge0$, `tsum_of_norm_bounded` gives the bound $e^{\alpha t}\sum_i|a_i|$ for the norm of the window sum. No identification or counting of the individual zeros is needed for this implication. The index family and its multiplicities must be independent of the translation, even though the auxiliary finite set of places need not be.

If independent convergence is wanted, the project already has an alternative to the sharper finite-$L$ Jensen estimate above. `exists_completedHeckeEulerProduct_one_gaussianContinuation_zeroCount` in `IdeleClassGaussianZeroCount.lean` bounds the divisor sum of the entire pole-cleared trivial-character numerator on the radius-five disk about $2+it$ by $C(1+|t|)$. Integer-height disks cover the window. Cubic vertical decay from `compactLogMellin_vertical_decay` suffices against this weaker count: Each disjoint unit-height band costs at most a constant times $(1+|t|)^{-2}$ after weighting. Summation by height and order comparison with the chosen window index remain; the disk estimate itself does not.

For the local comparison put $Z(t)=\zeta_F(1+t)$ on the positive real axis and $S(t)=\sum_{v}\sum_{k\ge1}(\log q_v)q_v^{-k(1+t)}$, where the sum runs over finite places and positive powers. The finite-shell Laplace calculation above and the window bound imply $tS(t)\to V$ **under the agreement hypothesis**: The polar term survives, the error is lower order, and $B(1/2+t)\to B(1/2)>0$. Mathlib's `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` gives $tZ(t)\to c\ne0$. If $Z'=-SZ$ for $t>0$, then $(1/Z)'=S/Z\to V/c$. Apply `HasDerivAt.lhopital_zero_nhdsGT` to $(1/Z)/t$: Its limit is both $V/c$ and $1/c$, so $V=1$. This does **not** differentiate the residue asymptotic or require a continuation across one.

The useful missing identification to prove first is `finiteHeckeEulerProduct (K := K) (fun _ ↦ 1) (σ : ℂ) = NumberField.dedekindZeta K σ` for **real** $\sigma>1$. The product on the left already has `finiteHeckeEulerProduct_logDeriv`. To connect the ideal-count Dirichlet series on the right, expand finite products using unique ideal factorization (`Ideal.finprod_heightOneSpectrum_factorization`) and multiplicativity of `Ideal.absNorm`, exhaust the nonzero integral ideals, and regroup by norm. Then restrict the product derivative to the real ray. The finite Euler factorization for the *nontrivial* ideal-class character is not this identification.

In parallel, specialize `measure_ideleClassNormOne_univ_of_logSplit` to the raw quotient measure. The discriminant and the two-class classification are in `IdealClassSmallRepresentative.lean`, `IdealClassTwoClasses.lean`, and `IdealClassPrimeTwo.lean`. Expose the signature, evaluate the rank-zero regulator by the empty determinant, and use `qSqrtNegFive_span_absNorm_eq_coordinates` on units to obtain the torsion order. The remaining links back to p. 520 include admissibility and Mellin translation for the chosen bump, the off-identity shell and complex-place estimates, and the Laplace interchange. These are proof obligations, not conclusions of the abstract summability or calculus lemmas.

## A full-divisor test at width one

There is also a test with no moving support, zero count, or Laplace limit. Take a nonzero smooth $F\ge0$ compactly supported in $(0,\log 2)$ and put $g(x)=e^{-x/2}F(x)$. For $\alpha=1$ the open window contains the entire closed critical strip. `Masullo.hasSum_trivialHeckeStrip_iff` (`Lemmas.TrivialHeckeStripSum`) transports an unordered weighted sum from the zeros of the entire numerator $H$ of `exists_completedHecke_one_explicitFormula` to the full Hecke strip index, provided the weight vanishes on characters nontrivial on norm-one classes. It preserves the full multiplicity. Do **not** shift the index: Apply the shift in the weight $W(\chi)=M(\varphi)(\chi|\cdot|^{-1/2})$. The owning Lean build, statement review, and axiom-check session is `01a20674-e76e-733c-b30b-d54d5b2cd736`.

The remaining comparison is ordinary mathematics here. In the trivial-character explicit formula $g(0)=0$, all prime samples vanish, and the single complex Gamma contribution is $-J$, where

$$J=\int_0^\infty \frac{e^{-x/2}F(x)}{1-e^{-x}}\,dx>0.$$

Thus the two polar moments minus the full zero sum, computed with Lebesgue log measure, equal $J$. The raw idelic Mellin transforms multiply this entire difference by $V$. On the local side the finite terms vanish. At the complex place write $r=e^{x/2}>1$: The normalized angular mean of $r/|1-r e^{i\theta}|^2$ is $r/(r^2-1)=e^{-x/2}/(1-e^{-x})$. Hence the sole local contribution is $+J$, contradicting $VJ=J$ for the printed raw measure. Dividing the global side by $V$ passes this test, not the general trace comparison.

This fixed test is now formalized end to end. `Theorems.QSqrtNegFiveStripTrace` proves `Masullo.not_ideleClassStripTrace_qSqrtNegFive` at width one and hence `Masullo.not_ideleClassTraceFormula_qSqrtNegFive`. It uses `Lemmas.RadialClassTest` for global admissibility, `Theorems.ShortBumpFiniteTrace` for the actual finite kernels, `Theorems.ShortBumpExplicitFormula` for the absolutely summable contour divisor, and `Theorems.QSqrtNegFiveResidue` for the raw Haar factor. Uniqueness of the same unordered sum forces $(V-1)J=0$, impossible for this field and test. The conclusion concerns the project's multiplicity-weighted, raw-measure statement of (12.5.1.3), not a volume-normalized replacement, the operator trace, or GRH. Owning integration, signature, and axiom-check session: `01a20674-e76e-733c-b30b-d54d5b2cd736`.
