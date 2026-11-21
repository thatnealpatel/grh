# The compact-test Laplace estimate

**Status: Lean endpoints in [`Lemmas.CompactTestLaplace`](../../Proofs/Lemmas/CompactTestLaplace.lean).** This project lemma implements step 1 of the [cutoff repair](trace-divisor-cutoff.md) for Chapter 13. The manuscript interface is the provisional reading of (13.3.1.2)–(13.3.1.3), p. 522. The estimate is independent of the moment condition and does not supply equality of the full and capped distributions.

For a smooth complex test supported compactly in $(0,\infty)$, integration by parts gives $T_w(g')=-wT_w(g)$. The boundary at zero vanishes by support and the boundary at infinity vanishes by compactness. Applying the identity to $f'$ as well as $f$ bounds $(1+|w|^2)|T_w(f)|$ by the sum of the weighted $L^1$ norms of $f$ and $f''$. The derivative identity itself only needs $C^1$ regularity, compact support, and $g(0)=0$. No division by $w$ is used.

The public declarations are `Masullo.positiveLaplaceTest` and
`Masullo.norm_positiveLaplaceTest_mul_weight_le`. An independent Yah reviewer
confirmed that their types give the positive-sign transform on $(0,\infty)$
and the stated estimate for smooth compact tests with topological support in
that half-line. The estimate includes $w=0$ when $0\le a$, with no moment
condition. The comparison of full and capped distributions is a separate
premise. The pinned text locators refer to provisional extraction, not new
visual evidence.

The initial local build exposed a real-module instance mismatch for the
derivative of the real embedding into $\mathbb C$. The proof uses the
equivalent slope-limit characterization to bridge those instances without
changing either endpoint.

The estimate uses two separate integrals for the majorant. Each is finite by continuity and compact support, so their sum equals the single integral used in the [cutoff interface](trace-divisor-cutoff.md#implementation-order-at-the-pinned-mathlib-revision). Dividing by $1+|w_i|^2$ and multiplying by $|d_i|$ gives the precise majorant for `Summable.of_norm_bounded` on any index type. No uniform estimate in a **family** of tests is proved here. The [integral majorant](trace-divisor-cutoff-integral.md) is now in Lean. The [profile specialization](trace-divisor-cutoff-profiles.md) instantiates it uniformly for the smooth test family. The scalar transform limit must still be checked before assembling the mass-corrected series limit.
