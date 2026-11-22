# Diagonal finite trace phases over a number field

## Manuscript and repair

Pin: *The Music of the Primes*, SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The reading for this branch is from Appendix A Markdown and `pdftotext
-layout` of the pin; it is provisional as a reading of the printed glyphs.
The [earlier rendered rational sign check](theta-inversion-q.md#rendered-sign-check-a-translated-box-breaks-the-printed-theta-identity)
records firsthand rendered evidence for the signs of the rational local
characters, their product, and the conjugated Fourier kernel. It is not a
new rendered check of the general-field displays here.

- Example A.3.1.5, p. 557, takes the positive real standard character
  and the real trace in the complex standard character. Example A.3.1.6,
  p. 557, also takes a **positive** character: the class in
  $\mathbb Q_p/\mathbb Z_p$ maps to the $p$-primary subgroup of
  $\mathbb Q/\mathbb Z$, then to $e^{2\pi i t}$. Example A.3.1.8,
  p. 558, takes their product as printed. Over $\mathbb Q$, the
  diagonal $1/3$ then gives $e^{4\pi i/3}$, not $1$. The centered-ball
  calculation in Example A.3.1.7, pp. 557–558, does not detect the sign.
- Example A.3.1.9, (A.3.1.7), p. 558, specifies trace pullback.
  Example A.3.1.10, p. 558, specifies the local trace pullback to the
  standard positive $\mathbb Q_p$ character. Neither definition itself
  establishes the correctly signed diagonal compatibility needed for
  the global pairing. Keep the positive local definitions, but use the
  product of their **conjugates** for the finite part of the global
  character. Keep the Archimedean phase positive. On the diagonal,
  this last phase is $e^{2\pi i\operatorname{Tr}_{K/\mathbb Q}(x)}$:
  the real embeddings contribute their values and each complex pair
  contributes twice the real part. The Lean endpoint states this phase
  directly by the rational trace; it does not construct the separate
  Archimedean local factors.
- The Fourier integral conjugates the character, as in (2.2.4.32),
  p. 92. Consequently its **finite** factor is the product of the
  positive local trace phases. Theorem 2.2.3.2, (2.2.3.2), p. 82,
  is the intended theta application, not a proof of this repair. The
  calculation does not use the printed translated-ball formula
  (A.3.1.5) or assume the theta identity.

## Lean argument and scope

Write $K_v$ for the actual `HeightOneSpectrum.adicCompletion` at the
finite place $v$, $p(v)$ for its rational prime, and $x_v$ for the image
of $x\in K$ under `algebraMap K K_v`. For every number field and every
$x\in K$, define

$$
a_v(x)=\operatorname{padicStdAddChar}_{p(v)}\bigl(
    \operatorname{Tr}_{K_v/\mathbb Q_{p(v)}}(x_v)\bigr).
$$

1. [Finite support and regrouping](../../Proofs/Lemmas/FiniteCompletionDiagonalSupport.lean):
   `finiteCompletionDiagonalPhase_hasFiniteMulSupport` proves that
   $a_v(x)=1$ outside a finite set. The actual diagonal finite adele
   is integral outside a finite set, localization sends the integral
   trace to the completion-field trace there, and the standard
   character is one on $\mathbb Z_{p(v)}$.
   `finiteCompletionBasePrime_eq_iff` identifies the fiber of $p(v)$
   with the places dividing $(p)$. The regrouping lemma reindexes the
   product on explicit finite support, then fills each fiber with
   omitted factors that are exactly $1$.
2. [Trace comparison](../../Proofs/Lemmas/FiniteCompletionDiagonalTrace.lean):
   `finiteCompletion_sum_trace_overPrime` compares the sum of
   completion-field traces over $p$ to the image of the global trace
   in $\mathbb Q_p$. On $\mathcal O_K$, this follows by localizing the
   integral trace identity for the product of completion integers and
   the global integral trace. A common nonzero integer denominator and
   linearity then give the result for every $x\in K$.
   `finiteCompletionDiagonalPhase_eq_overPrime` identifies the
   transported fixed-$p$ scalar action with the canonical scalar
   action at the place by equality of their algebra maps. Thus the
   comparison uses the same local traces as the definition of $a_v$.
3. [Substantive endpoints](../../Proofs/Theorems/NumberFieldDiagonalPhase.lean):
   `finiteCompletionDiagonalPhase_prod_overPrime` uses the additive
   character law to identify the fiber product with the positive
   `rationalPadicPhase p (Algebra.trace ℚ K x)`. Use the union of the
   image of finite support and the denominator primes of the rational
   trace as the finite outer index. The existing rational finite phase
   identity now gives `finiteCompletionDiagonalPhase_finprod`,
   $\prod_v a_v(x)=e^{2\pi i\operatorname{Tr}_{K/\mathbb Q}(x)}$.
   Conjugation commutes with the product using the proved finite support.
   `numberFieldDiagonal_phase_eq_one` gives
   $e^{2\pi i\operatorname{Tr}_{K/\mathbb Q}(x)}\prod_v\overline{a_v(x)}=1$;
   `numberFieldDiagonal_fourier_finite_phase` gives
   $\overline{\prod_v\overline{a_v(x)}}=\prod_v a_v(x)$.
   By `inner_archimedeanEuclideanEmbedding_traceFrequency`, the positive
   finite product on $xy$ is the positive shift phase in
   `archimedeanIdeal_poisson` at $a=e(x)$ and frequency $T(e(y))$. For a
   translated box one still needs a diagonal representative and the
   equality of its phases with those of the local translation centers
   on the dual support.

This proves diagonal phase compatibility only, independently of any
finite-box approximation theorem. It proves neither an off-diagonal
continuous global character nor the full diagonal annihilator, Fourier
formula, theta inversion, or GRH. A next use is to substitute the positive
finite phase for the conjugate of the corrected finite character on a
diagonal product $xy$, for $x,y\in K$, in the finite-box Fourier
formula. The identification of the finite frequency support with the
actual fractional-ideal trace dual, and comparison of the Haar and
lattice factors in the shifted Poisson formula, are separate obligations.
A testable next comparison is for a box with nonzero scaled local
integer lattices $I_v=c_v\mathcal{O}_{K_v}$, equal to $\mathcal{O}_{K_v}$
away from finitely many $v$, and fractional ideal
$I=\{x\in K: x_v\in I_v\text{ for every }v\}$. For every $y\in K$, prove
$$
y\in I^\vee \quad\Longleftrightarrow\quad
\forall v\ \forall b\in I_v,\quad
\operatorname{padicStdAddChar}_{p(v)}
\bigl(\operatorname{Tr}_{K_v/\mathbb Q_{p(v)}}(b\,y_v)\bigr)=1.
$$
This needs the actual completed lattice $I_v$ at each place. The
codifferent annihilator for the completion integers and the global
fractional-ideal trace dual supply local and global inputs, not this
identification for an arbitrary box.

## Local checks and integration replay

Writer session `01a20447-557d-705c-895c-7a7e44094b93`, agent `vnbRfBv`.
Assigned base `61c21936385cf7c570fdb3666c92dc06aa5fe4c3`; comparison with
requested base `aca6533d21b24a10276e26e59845e83e83f43a64` is empty on
`Proofs` and the Lake pins. Lean `v4.36.0`, Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Exact Lean file SHA-256s:

| Module | SHA-256 |
|---|---|
| `Lemmas.FiniteCompletionDiagonalSupport` | `28cceb552fe0c537ad6a4113aafaa1e9a041999bd917e6bc50350b4545426a12` |
| `Lemmas.FiniteCompletionDiagonalTrace` | `d47964d93acb4a3691606780da2dc1b637e626b3c7135eeb78dd1aebbba64bc0` |
| `Theorems.NumberFieldDiagonalPhase` | `4c634a764caf57980289d30a850f5ee85137d02a7c3b40f5d92aa7b80f66f8f7` |

`lake --wfail build +Theorems.NumberFieldDiagonalPhase` and
`lake --wfail build Proofs` passed. Joint import of every module under
`Proofs/` via `lake env lean --stdin` passed. All three modules passed
separate `lake env leanchecker -v <module>` replays. Imported `#check`
and `#print axioms` for all ten declarations below succeeded: the
support and three global identities quantify over every `[Field K]`
`[NumberField K]` and `x : K`; the fixed-prime product adds `p : Nat.Primes`,
and the trace sum takes `p : ℕ` and `[Fact p.Prime]`. Every listed
endpoint reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The Lean audit from `internal/worker/worker.go` also passed for all constants
in these three modules: transitive axioms lie in that same list, no module
introduces an axiom, and each listed endpoint is safe and originates in an
audited project module.

Independent read-only Yah statement review: same session, child
`phase-review` (`FpeVzga`, output `6d4494c1e519670426ddef68aa0ce6e2fb73ab17`).
The reviewer verified the three file hashes above and approved the seven
substantive signatures: cofinite support, canonical prime fiber, fixed-$p$
trace sum and phase product, and all three global identities. The review
independently derived the positive finite product and the conjugation rule,
checked the actual completion maps, ramified fibers and positive residue
orientation, and did not rely on the translated-ball formula or theta
inversion. Its source reading was also provisional as to rendered glyphs.
The built signatures agree with this scope. The support domain is the height-one
spectrum of $\mathcal O_K$; `conj` prints as `starRingEnd ℂ`; the fiber
`Fintype` and transported algebra are instantiated inside the declarations,
not added hypotheses on the callers.

From the exact integration workspace, run the project audit and compare
its built signatures with the reviewed scope before adoption:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.FiniteCompletionDiagonalSupport Lemmas.FiniteCompletionDiagonalTrace \
  Theorems.NumberFieldDiagonalPhase -- \
  Masullo.finiteCompletionDiagonalPhase_apply \
  Masullo.finiteCompletionDiagonalPhase_hasFiniteMulSupport \
  Masullo.finiteCompletionBasePrime_eq_iff \
  Masullo.finprod_finiteCompletionDiagonalPhase_group \
  Masullo.finiteCompletion_sum_trace_overPrime \
  Masullo.finiteCompletionDiagonalPhase_eq_overPrime \
  Masullo.finiteCompletionDiagonalPhase_prod_overPrime \
  Masullo.finiteCompletionDiagonalPhase_finprod \
  Masullo.numberFieldDiagonal_phase_eq_one \
  Masullo.numberFieldDiagonal_fourier_finite_phase
```
