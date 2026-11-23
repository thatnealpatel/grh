---
evidence_revision: c1d9906c831ff0c9380c9bacd83d5b66bcd67c51
outcome: refuted
---

# Prime-two periodization does not compute the fixed-band localized trace

**Claim tested.** Set $L=\log 2$, $J=[0,L/2]$, and $Y=1/4$. Let $Q$ be the [real log level projection](../../../Proofs/Lemmas/RealLogLevel.lean) at $\alpha=r=0$, and fix a smooth compactly supported output window $p$ equal to one on $J$. For every smooth compact log probe $\varphi$, does convolution by its periodization on $\mathbb R/L\mathbb Z$, localized to the image of $J$, have the same trace as $M_p C_\varphi Q M_{1_J}$ on $L^2(\mathbb R,dx)$? Use inherited length measure on the circle, the trivial compact type, and the same probe on both sides.

**Refuted.** Take $\varepsilon=1/100$ and a smooth bump $0\le\varphi\le1$ supported in $[L-\varepsilon,L+\varepsilon]$ with $\varphi(L)=1$. The smooth periodic convolution kernel has constant diagonal $\sum_{n\in\mathbb Z}\varphi(nL)=1$. Its localized trace is $|J|$ by the absolutely convergent Fourier series. In contrast,

$$
\big|\operatorname{Tr}(M_p C_\varphi Q M_{1_J})\big|
\le 2\varepsilon e^{\varepsilon/2}|J| < 0.021|J|.
$$

**Paper proof of the bound.** The [Lean-checked evaluation estimate](../../../Proofs/Lemmas/RealLogBandEvaluation.lean) bounds $|h(x)|$ by $2\sqrt Y e^{x/2}\|h\|_2$ on admissible profiles. Their finite linear combinations are still admissible profiles. Hence an $L^2$-Cauchy sequence from their span converges uniformly on compact intervals, giving each element of $\operatorname{ran}Q$ a continuous representative with the same bound. For any orthonormal basis $(e_i)$ of this range, Parseval for evaluation and Cauchy–Schwarz give

$$
\sum_i |e_i(x-s)\overline{e_i(x)}|\le 4Y e^{x-s/2}.
$$

The [fixed-annulus trace result](../../../Proofs/Theorems/FixedAnnulusTraceDensity.lean) applies to $B=M_p C_\varphi Q$. By trace cyclicity, compute $\operatorname{Tr}(B M_{1_J})$ as $\operatorname{Tr}(M_{1_J} B)$ in the range basis completed by a basis of $\ker Q$. The latter contributes zero. The remaining diagonal sum integrates $\varphi(s)\sum_i e_i(x-s)\overline{e_i(x)}$ over $x\in J$ and $s$ in the probe support. There $4Y e^{x-s/2}\le e^{\varepsilon/2}$, justifying termwise integration and giving the bound since the support has length at most $2\varepsilon$. This computes the full localized trace, not a finite-cell compression.

Unlike the [Boolean-shell counterexample](common-lift-boolean-shell-orbital-comb.md), this test retains the input projection at fixed bandwidth and uses the first winding itself. The interval comparison is a paper proof, not a Lean theorem. It rules out this same-probe cyclic identification, not a different lift, a transformed probe, or the [global trace claim](../open/rational-normalized-global-geometric-trace.md).
