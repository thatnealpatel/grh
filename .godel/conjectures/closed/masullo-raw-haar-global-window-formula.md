---
evidence_revision: a684299f2b54e602be826969b35b7c1f30742700
outcome: refuted
---

# The printed number-field trace formula with raw global Haar

For every number field, (12.5.1.1–3) asserts equality of the displayed local distributions with the two raw global Mellin polar terms minus the interior-window Hecke zero sum on tests vanishing on the norm-one group. Take any fixed strip half-width $0<\alpha<1/2$ in the p. 520 argument.

**Refuted as printed:** For $F=\mathbb Q(\sqrt{-5})$, the positive polar term has coefficient $V=\mu^1(C_F^1)=\pi/\sqrt5$ by (A.3.2.1), while the finite local side detects the simple pole of $\zeta_F$ with coefficient one.

Take $0\ne b\ge0$ smooth with compact support in $(0,\log 2)$, $B(z)=\int b(x)e^{zx}\,dx$, and $\varphi_R(g)=b(\log|g|_F-R)$ for $R\ge0$. Each test is admissible; the finite set of places may grow with $R$. Average each side against $\delta e^{-(1/2+\delta)R}\,dR$. The finite shells give $B(1/2+\delta)\delta(-\zeta_F'/\zeta_F)(1+\delta)\to B(1/2)$. The complex place contributes zero in the limit. On the global side only the trivial compact character survives. Smoothness and zero counting bound the strip sum by $O(e^{\alpha R})$, so only the positive polar term survives the average, giving $VB(1/2)$. Since $B(1/2)>0$, some admissible translates disagree, even arbitrarily far out.

This is a [paper argument with the measure, shell integral, and growth estimates](../../obligations/trace-window-q-sqrt-minus-five.md), not a Lean counterexample or numerical zero search. Dividing the printed global terms by $V$ removes this mismatch; it does not prove the resulting identity. The [normalized rational comparison](../open/rational-normalized-global-geometric-trace.md) is a different claim.
