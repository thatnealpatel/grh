# Nuclear operators, trace definitions, and Schwartz–Bruhat tests

**Finding:** The rational additive Schwartz–Bruhat space is implemented. A general nuclear-operator trace for the manuscript's weighted Hilbert spaces is not. There is enough in the pinned Mathlib to check a useful intermediate statement without defining a new operator ideal: For an operator with an explicitly summable rank-one presentation, its Hilbert-basis diagonal sums to the trace of that presentation.

**Scope:** Source inventory at `8cd15730fbc809dcacdf8660885329d3ae1981a2`, Lean 4.36.0, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The [Hilbert trace proposition](../../../Proofs/Props/HilbertRankOneTrace.lean) and [fixed-annulus theorem](../../../Proofs/Theorems/RationalFixedAnnulusTrace.lean) are in `Proofs`; this note records the source comparison. Manuscript locators below are from the [digest-matched edition](../../sources/masullo/README.md), by layout extraction, with an additional OCR check of the rendered statement on p. 697. No full project rebuild or new visual passage review is claimed.

## Which trace?

- **Nuclear trace:** In Lemma C.3.1.2 and Proposition C.3.2.1, pp. 694–695, a presentation uses summable coefficients, equicontinuous functionals, and vectors in a bounded Banach disc. The trace is the sum of the coefficients times the pairings of the corresponding functionals and vectors. The approximation property ensures independence of the presentation. Lemma C.3.2.2 compares traces on two spaces given a continuous injection and a *nuclear lift* through it. Nuclearity of the ambient operator or a description of the test space does not exhibit that lift.
- **Hilbert-space trace:** Definition C.3.4.2, p. 697, uses the diagonal sum of $T$ in an orthonormal basis; the trace norm is the diagonal sum of $|T|=(T^*T)^{1/2}$. Do **not** import Lemma C.3.4.1(2) as stated: It claims that the sum of the absolute values of the diagonal entries of $T$ is basis-independent. For $T=\operatorname{diag}(1,-1)$ on $\mathbb C^2$, those entries are $1,-1$ in the coordinate basis and $0,0$ in the basis $(e_1\pm e_2)/\sqrt2$. The absolute sums are 2 and 0. The trace is 0 and the trace norm is 2 in both bases. This refutes that clause, not absolute convergence or basis independence of the trace itself.
- **Algebraic trace in Lean:** [`FiniteCompletionIntegralTrace`](../../../Proofs/Lemmas/FiniteCompletionIntegralTrace.lean) uses `Algebra.trace` for multiplication in finite algebras. Mathlib's `LinearAlgebra/Trace.lean` defines `LinearMap.trace` to be zero when no finite basis exists. Even a rank-one orthogonal projection on an infinite-dimensional Hilbert space would be assigned zero by that definition, whereas its analytic trace is one. `Analysis/InnerProductSpace/Trace.lean` uses a finite orthonormal basis for `trace_eq_sum_inner`; `SingularValues.lean` there concerns finite-dimensional maps. I found no analytic trace-class or locally convex nuclear-map API in `Proofs` or the pinned Mathlib. Compactness alone is insufficient.

## A checked Hilbert-space bridge

Run `lake build Props.HilbertRankOneTrace` from the repository root. `Masullo.OperatorTrace.hasSum_diagonal` takes vectors $u_n,v_n$ in a complex Hilbert space and a continuous linear $T$ with

$$T x=\sum_n\langle v_n,x\rangle u_n,\qquad \sum_n\|u_n\|\|v_n\|<\infty.$$

It proves summability of the scalar pairings and, for **any** Hilbert basis $b$, the unordered sum identity

$$\sum_i\langle b_i,T b_i\rangle=\sum_n\langle v_n,u_n\rangle.$$

Lean's inner product is linear in the second slot. The absolute sum over $i$ for one rank-one term is bounded by $\|u_n\|\|v_n\|$ by Cauchy–Schwarz on the basis coordinates; this licenses exchanging the two sums. Fixing a presentation shows independence of the basis, and fixing a basis shows that two such presentations of the same $T$ have the same value. This tests the trace definition in infinite dimension, not just for matrices. It does not construct a presentation for an adelic operator or give a trace on a general locally convex space.

## Which Schwartz–Bruhat space?

The manuscript defines $\mathcal S(G)$ for locally compact abelian groups by a locally convex inductive limit (§2.1.1.3, p. 62, and Appendix D). The project's concrete construction is for the **additive rational adeles**. At positive level $M$, the finite support lies in $M^{-1}\widehat{\mathbb Z}$ and the finite translation invariance group contains $M\widehat{\mathbb Z}$. Their quotient gives $M^2$ cells, each carrying an ordinary real Schwartz profile. The profiles need not be compactly supported in the real variable.

- [`rationalAdeleStageCoordinates`](../../../Proofs/Props/RationalAdeleStageCoordinates.lean) gives the fixed-stage coordinates. [`RationalAdeleSchwartzLF`](../../../Proofs/Props/RationalAdeleSchwartzLF.lean) gives the union along factorial levels its locally convex topology, with closed stage embeddings and a stagewise continuity criterion.
- [`rationalAdeleLF_bounded_iff`](../../../Proofs/Props/RationalAdeleSchwartzBounded.lean) identifies bounded families with bounded profile families in one stage. [`rationalAdeleLFFourierEquiv`](../../../Proofs/Theorems/RationalAdeleLFFourierInversion.lean) makes the normalized adelic Fourier transform a continuous linear self-equivalence. Neither theorem asserts nuclearity of the space. The [general number-field adele stages](../../../Proofs/Lemmas/AdeleFiniteStage.lean) are not an analogous Schwartz LF construction.
- The convolution tests in the [Chapter 12 comparison](../../obligations/trace-geometric.md) are instead compact Bruhat-smooth functions on the **multiplicative idele-class group**, vanishing on the norm-one subgroup. The additive Schwartz inputs generate theta vectors; they are not replacements for those convolution tests.

## What this buys for the manuscript

The [fixed-annulus argument](../../obligations/trace-polar-free-q.md) gives an explicit, rapidly convergent Fourier presentation of $M_p A_\phi Q_Y$ in the rational real model. Here $p$ is a smooth compact log-position cutoff, $A_\phi$ is convolution, and $Q_Y$ is the actual local level projection. The argument factors through smooth profiles on a fixed compact interval. It is project mathematics, not a Lean application of the check above. For the proposed cutoff equal to one near norm zero, even the claimed flat range can fail.

**Fixed-annulus Hilbert trace, now checked:** The [concrete Fourier presentation and verification instructions](fixed-annulus.md) identify the projected operator on every input and sum its diagonal in every Hilbert basis. Periodizing the convolution test rather than its outputs separates the kernel into explicit input and output modes without commuting the projection. The smooth-space nuclear lift above remains informal. What remains for the geometric comparison is the actual global level, not another definition of trace. The [spectral audit](../../obligations/trace-spectral.md), [fixed-band Gram calculation](../rational-theta-gram/handoff.md), and [trace assembly record](../../obligations/trace-assembly.json) isolate those separate issues. The [rational radial explicit formula](../../../Proofs/Theorems/RationalIdeleRadialExplicitFormula.lean) is a scalar identity, not the missing common operator evaluation.
