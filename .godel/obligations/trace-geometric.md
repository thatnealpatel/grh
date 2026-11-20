# Trace formula: Geometric input to the final comparison

**Status: Navigation, project reasoning, and open obligations, not a new visual source packet or a Lean result.** The [existing visual reading](trace-assembly.json) verifies what the author does in the last paragraph of Theorem 12.5.1.1, not the cited evaluations. The leads below come from `pdftotext -layout` of the [pinned edition](../sources/masullo/README.md), after matching its SHA-256. Page locators below are PDF ordinals. Check the formulas and page boundaries in the rendered pages before promoting any of these leads to source evidence.

## Which tests should the comparison use?

- PDF pp. 419–420, §9.3.1: Check the meaning of $D(G)$ (the extraction points to complex-valued smooth compactly supported tests in the sense of Bruhat, not arbitrary Schwartz-Bruhat functions).
- PDF pp. 519–520, Theorem 12.5.1.1: The theorem line uses $\varphi\in D(C_F)$ with $\varphi(C_F^1)=0$. The section introduction instead mentions $\varphi(1)=0$ and the smooth-cutoff limit. The proof chooses finite $S$ containing the Archimedean places and the places where $F$ or the character is ramified, with $\operatorname{Pic}(\mathcal O_{F,S})=1$. It uses $|\operatorname{supp}\varphi|_F\subset(1/T,T)$ with $T<N(\mathfrak p_v)$ for finite $v\notin S$, and invariance under the image of the product of local units outside $S$. Check these restrictions as proof setup, not additional assumptions silently inserted in the theorem statement.
- On the same pages, check the Mellin argument $c|\cdot|_F^{-1/2}$ and the indexing by Hecke zeros **in the interior** of the relative strip $\sigma(c)\in 1/2+I$ for $I=[-\alpha,\alpha]$, weighted by the order of the zero $N(c)$. This is not the critical-line sum with clipped multiplicities appearing on p. 522.

## What has to be shown before the scalar step applies?

The author uses (11.3.1.4), Theorem 11.3.2.1, and Theorem 12.4.1.1 to pass to the weighted local side minus the two Mellin terms. Check the following obligations in that order:

1. **Global-to-local decomposition.** Around (11.3.1.4) on p. 494 the extraction shows a definition of partial kernels by successive differences of strata indicators. A kernel decomposition does not on its own justify integrating the smoothed diagonal term by term, including the $S$ piece. Locate the equality with the common global integral and its measure and limit. Check §12.3 on p. 514, which appears to have a heading and an “Include section” footnote rather than a derivation; this is not a claim of absence elsewhere.
2. **Tail outside $S$.** On pp. 494–495, the support argument preceding Theorem 11.3.2.1 is eventual and uses tests supported above norm one. The theorem itself appears to give an orbital trace for a test supported above norm one, with a local sum involving $\sum_{k\in\mathbb Z}\varphi(\pi_v^k)$. This is not literally the vanishing assertion invoked on p. 520 for a test allowed on both sides of norm one. A possible argument of ours is to use the two-sided annulus to kill all nonzero powers at each $v\notin S$, and norm-one vanishing for $k=0$. This only kills that local sum if the norm and indexing agree. It does not extend the orbital trace evaluation to the two-sided class. Check whether test splitting, inversion, or a separately justified extension covers the below-one part, and how the place bounds apply to each rational prime in the claimed tail.
3. **Normalized local asymptotic versus global value.** The extraction of (12.4.1.1)–(12.4.1.3) on p. 514 shows an integral over $J_{F,S}$ of an $S$-local Paley-Wiener kernel, divided by a norm-one volume. Its right side has the finite-place terms over $S_f$ and the correction $\varphi(1)\log(\lambda\lambda')+o(1)$. Even with $\varphi(1)=0$, this is an asymptotic about a particular local kernel. Find the identification with the $k_S$ contribution to the global diagonal, including normalization and cutoffs, the two subtracted Mellin values, and the extension of the finite-place sum from $S_f$ to all finite places. The nearby cutoff footnote is relevant; do not treat it as a proved limit argument.

Independently, the spectral evaluation (12.5.1.4) still needs to be derived for the **same** smoothed diagonal, test, normalization, and strip. The paper cites Definition 10.4.3.7 and Theorem 10.4.2.8 there. The final algebra from the two evaluations remains conditional. None of these steps supplies a divisor theorem; the [divisor heading record](divisor-heading.json) still applies.

## Narrowing the bridge: Project reasoning, not a source reading

The finite-place extension and the kernel comparison are separate. Assume the normalized single-place map $i_v:F_v^\times\to C_F$ has $|i_v(a)|_F=|a|_v=q_v^{-\operatorname{ord}_v(a)}$, where $q_v=N(\mathfrak p_v)$. Take $T>1$, $q_v>T$ outside $S$, $|\operatorname{supp}\varphi|_F\subset (T^{-1},T)$, and $\varphi|_{C_F^1}=0$. For any $a\in F_v^\times$ at $v\notin S$:

- If $\operatorname{ord}_v(a)>0$, then $|i_v(a)|_F\le q_v^{-1}<T^{-1}$.
- If $\operatorname{ord}_v(a)<0$, then $|i_v(a)|_F\ge q_v>T$.
- If $\operatorname{ord}_v(a)=0$, then $i_v(a)\in C_F^1$.

Thus the whole local restriction $\varphi\circ i_v$ is zero, not just its values on uniformizer powers. If each omitted term is a linear local functional of that restriction, it is zero, so extending the finite-place sum from $S_f$ to all finite places adds only zero terms. This also kills the discrete sum in obligation 2 if the arguments are the indicated uniformizer powers; it does **not** show that the two-sided orbital trace is computed by that sum. Matching the normalizations, local functional, and hypotheses to the text and Mathlib remains to be done.

Write $P_S$ for the limit of the normalized local Paley-Wiener diagonal on p. 514 (if established for the needed cutoffs) and $D_S$ for the global $k_S$ diagonal contribution used on p. 520. Under the support argument above, and if the cited local asymptotic applies, $P_S=L_{\mathrm{loc}}$: The logarithmic term vanishes since $1\in C_F^1$. The target comparison is then

$$D_S+M(\varphi)(|\cdot|_F^{1/2})+M(\varphi)(|\cdot|_F^{-1/2})=P_S.$$

This isolates what the argument still needs. Vanishing on the norm-one subgroup removes the logarithmic term, not the Mellin corrections. Neither the normalization nor the cutoff identification, nor this comparison itself, has been proved here.

### Mathlib entry point (source inspected, not elaborated)

At the pinned Mathlib revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`:

- `NumberTheory/NumberField/AdeleRing.lean` defines `NumberField.IdeleClassGroup.ofAdicCompletion` as the single-place unit map followed by the principal quotient. `NumberField.AdeleRing.norm_apply_of_isUnit` expands the *adelic* norm on units into local factors, and `NumberField.AdeleRing.norm_algebraMap_eq_one_of_ne_zero` gives its value on principal ideles when the base ring is the ring of integers. These declarations do not themselves supply the descended norm used in the support argument.
- `NumberTheory/NumberField/Completion/FinitePlace.lean` gives `NumberField.FinitePlace.norm_def` on the adic completion in terms of its valuation, normalized using the ideal's absolute norm. Its use of `WithZeroMulInt.toNNReal_neg_apply` in `FinitePlace.two_le_norm_of_one_lt_norm` shows how to expose an integer exponent. The bound by 2 in that lemma is too weak here: Keep the actual ideal norm $q_v$ for the comparison with $T$.

**First worker target.** An [independently source-reviewed draft](single-place-norm.md) is ready for elaboration once the designated worker is available. For a number field `K`, `v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)`, and `u : (v.adicCompletion K)ˣ`, prove that the adelic norm of the underlying adele of `IdeleGroup.ofAdicCompletion (𝓞 K) K v u` equals the local norm `‖(u : v.adicCompletion K)‖`.

Use `AdeleRing.norm_apply_of_isUnit` with the embedded unit's `isUnit`. The infinite component is 1. For the finite factor, unfold `AdeleRing.ofAdicCompletion` and `IsDedekindDomain.FiniteAdeleRing.ofAdicCompletion` to the restricted product's `mulSingleMonoidHom`. The component at `v` is `↑u`, and all others are 1. Apply `finprod_eq_single` with precisely the off-place equality, not a separate nontriviality assumption at `v`: The result must also hold when `‖↑u‖ = 1`.

**Quotient target.** Define a multiplicative map from `IdeleGroup (𝓞 K) K` to `ℝ` with value the norm of the underlying adele. Prove multiplicativity on units, not from an assumed `NormedRing` structure on adeles. In `AdeleRing.norm_apply_of_isUnit`, distribute the finite Archimedean product using local `norm_mul`, powers, and `Finset.prod_mul_distrib`. Distribute the other product with `finprod_mul_distrib`, using `NumberField.FiniteAdeleRing.hasFiniteMulSupport_norm` for each unit's finite component (the image of the idele under `Units.map` of the second projection). For the identity, all factors are 1. For the principal-subgroup inclusion in the kernel, write an element of the subgroup as `IdeleGroup.unitEmbedding` of `x : Kˣ` and use `AdeleRing.norm_algebraMap_eq_one_of_ne_zero x.ne_zero`. `QuotientGroup.lift` then gives the class-group map; `QuotientGroup.lift_mk'` reduces its value at `IdeleClassGroup.ofAdicCompletion` to the first worker target. The kernel is the norm-one subgroup for this construction. No continuity or Haar normalization is needed for this algebraic support step, and neither is obtained by quotient descent here.

This is a source-inspected proof plan for the project's finite-place support argument, not a checked Lean result or a justification of the analytic bridge.

## Review attempts and next check

The nested visual reader received renders for pp. 419–420, 494–495, 514, and 519–520 from the digest-matched edition but did not establish visual access. A separate single-page control on p. 514 through the in-session native reviewer also failed before giving a successful terminal reading. Both routes reported `unrecognized_model` and expired OAuth. No new `verified`, `ambiguous`, or `absent` source packet resulted. No designated proof-worker transport was configured for these runs, and no Lean was run.

A later readiness check for different image transports found Codex's image-attachment CLI logged out and Pi's `exe-dev-anthropic` image-model credential invalid. No image request was sent through either transport, and the unchanged native reviewer was not retried. The PDF digest was rechecked against the pin; it does not certify any reading of the page.

Reopen visual review after a non-Claude Yah reviewer has confirmed native image input and working credentials. Start with p. 514 only and a fresh page challenge, then obtain independent readings for the p. 514 and p. 520 comparison before recording visual source evidence. Do not try another image batch on the strength of the navigation alone. While visual review is blocked, extracted text can support provisional comparisons with page and equation locators, not verified readings. An independent mathematical next step is the multiplicativity and principal-quotient descent above; Lean checking still requires the designated worker transport.
