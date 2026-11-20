# Proof frontier

This is a working map of the trace-to-zeros argument, not a complete inventory of the paper. Paragraphs and page numbers are navigation into the [pinned edition](sources/masullo/README.md); follow the handoffs for the evidence and its limitations. No endpoint listed here has an accepted Lean declaration.

## Toward the trace identity (Theorem 12.5.1.1, pp. 519–520)

The [final scalar comparison](obligations/trace-assembly.json) has a visual reading. It needs both evaluations of the **same** diagonal, on the same tests, with the same measure and limit. The algebra does not certify those inputs.

- **Geometric evaluation:** First justify the integrated kernel decomposition and the orbital tail for the two-sided test class; separately identify the normalized $S$-local cutoff asymptotic with the global $S$ contribution, including the two Mellin corrections. The [geometric handoff](obligations/trace-geometric.md) distinguishes these from the vanishing of the omitted linear local terms. Its [sharp cutoff estimate](obligations/trace-geometric.md#independent-lower-cutoff-estimate-for-the-sharp-logarithmic-integrals) bounds the summed lower-endpoint error by $O((\lambda'/\lambda'')^{1/4})$ under the volume interface of (12.4.1.24). Separate divergence of the two parameters to infinity does not suffice. Next, check the radially extended domain (the extracted equations name a norm-one domain) and keep the smooth radial profiles in the local integrals. Test whether averaging sharp bands controls the lower endpoint uniformly before comparing the remaining smooth errors or identifying the local and global kernels.
- **Finite-place support subproblem:** Prepare norm multiplicativity on ideles and descent through the principal quotient by inspecting the pinned Mathlib source. The [single-place norm draft](obligations/single-place-norm.md) awaits the worker; multiplicativity and descent themselves do not depend on its elaboration. This only supplies a premise of the support argument, not of the two-sided orbital trace evaluation.
- **Spectral evaluation:** The [spectral handoff](obligations/trace-spectral.md) identifies a closed-strip versus interior-strip mismatch and a diagonal theorem stated with the singleton kernels. Check whether the proof of Theorem 12.1.1.3 applies with the Definition 10.4.3.7 kernels and the correct measures. Separately justify excluding or accounting for boundary zeros. This branch does not need the geometric comparison.

## From trace to zeros (Chapters 1, 13, and 14)

Neither a trace on a restricted test class nor the empty [divisor heading](obligations/divisor-heading.json) supplies a divisor theorem. The [trace-to-zeros handoff](obligations/trace-to-zeros.md) distinguishes the two trace statements and two proposed routes. An independent task is to check if differencing the §1.4 holomorphic test family at a fixed parameter permits uniform Archimedean bounds **without** changing what one can recover about the logarithmic derivative. Alternatively, specify the inputs a positivity route would need and test them on the Chapter 13 test class. Neither task needs to assume that the trace has been proved.

## External gates

- **Visual source review:** No new visual reading from the attempted routes. Reopen only with image-capable Yah and working credentials; first run one fresh p. 514 control. This gate does not prevent provisional extracted-text work or labeled project reasoning.
- **Lean checking:** No designated proof worker was configured. Reopen when `GRH_PROOF_WORKER` is provisioned. Use the [exact-revision check](../cmd/godel/README.md#checking-a-proof-candidate), not local Lean. Independently reviewed drafts can meanwhile be kept outside `Proofs` and labeled unelaborated.
