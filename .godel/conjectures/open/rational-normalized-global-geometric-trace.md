---
evidence_revision: a684299f2b54e602be826969b35b7c1f30742700
---

# The whole rational geometric trace equals the normalized local expression

Over $\mathbb Q$ in the trivial compact isotype, the target is the following for arbitrarily small positive strip half-widths $\alpha$ and a common admissible Sobolev degree: For every $f\in C_c^\infty((0,\infty))$ with $\int f=0$, the **whole** half-twisted geometric trace (band limit first at fixed position cutoff, then position exhaustion) equals the normalized real and finite local terms of (12.5.1.1–2) minus the sum $M_f(1/2)+M_f(-1/2)$, where $M_f(z)=\int e^{zx}f(x)\,dx$. The minus sign applies to both polar terms.

This is the geometric comparison, not the [evaluation of the ordered trace by interior zeros](../closed/rational-radial-ordered-inner-trace.md). One needs both evaluations for the **same operator and widths**. Together with the full explicit formula they would yield the test agreement in [`Masullo.riemannHypothesis_of_strip_test_agreement`](../../../Proofs/Props/ZetaTestSumComparison.lean). Lean checks that implication, not its premise. The [raw-Haar field counterexample](../closed/masullo-raw-haar-global-window-formula.md) does not settle this question: The rational norm-one volume is one.

**A substitution that fails:** Fix a common good width, even degree $s\ge4$, and $f=b'$ with $0\ne b\ge0$ smooth and compactly supported in $(0,\log 2)$. All finite-place scalar samples vanish. With $J_f$ the normalized real-place term, the [joint local projection calculation](../../obligations/trace-joint-local-q.md) gives $J_f-M_f(-1/2)$ in its own cutoff order. The claimed whole trace differs from that value by
$$
-M_f(1/2)=\tfrac12\int e^{x/2}b(x)\,dx>0,
$$
by integration by parts. This refutes substituting that projection for the whole global trace. It does **not** refute the stated identity: Vanishing finite-place scalar samples do not imply vanishing global orbital traces.

**Remaining test:** Retain the right theta projection at fixed position cutoff. For the strongly convergent weighted band levels $P_n\to P$ and convolution $A=A_f$, the [fixed-cutoff comparison](../../obligations/trace-hardy-diagonal-q.md#removing-the-order-defect-in-the-weighted-rational-isotype) gives $M_\rho PA P_n\to M_\rho PAP=M_\rho AP$ in trace norm. The whole scalar order defect vanishes under subsequent position exhaustion; that does not evaluate the trace of an individual shell. Identify the actual global $S$ component and orbital terms at these cutoffs, and justify comparison with the separately ordered local limit at the **same** width. On this bump their net correction to the local value must be exactly $\tfrac12 M_b(1/2)$. Agreement would calibrate one bump at one width. A mismatch would rule out that width and degree together, not all arbitrarily small widths at a common degree. The [global handoff](../../obligations/trace-to-zeros.md) records the missing geometric identification.
