# Finite-adele trace character: Exact-candidate check

Lean candidate `7026d477e8ee7fa5462a1b9d033c92557a51dffb`, base
`83e360130cbd779f6d5ed1ca21f0d19613b91a0d`, was adopted in owning Yah
session `01a204b9-9c06-7958-9ac8-47b71f2e2360` (events 116–117).
The three prior checked candidates `d7c16e8d1b1db501d25000af3e285d9eca1dbd19`,
`e3179515b76f4ce24360eee73c881951f4127e93`, and
`d462ef17124c21390e8f30feec752f8ad0ac3b98` had stale adoptions. The
target moved, respectively, through a Blitz prompt edit, a Companion
prompt edit, and a manuscript reading note. The patch against the
respective base, proof tree, pins, and fresh Lean reports matched
across all four candidates. Cache seeding reused `lib` and `ir` only
for unchanged Lean inputs. Each restack was checked again; none was
adopted on the strength of its predecessor's check.

`Theorems.FiniteAdeleTraceCharacter` defines the eight new declarations
below. No changed Lean file contained placeholders or new axioms. The
owning integration workspace passed these Lake targets:

```sh
lake build --wfail +Theorems.FiniteAdeleTraceCharacter \
  +Theorems.FiniteBoxFourier +Theorems.AdeleRestrictedProductHaar
```

The pinned inputs were Lean `v4.36.0` and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The owning Yah then ran
`lake env lean -DwarningAsError=true` on a fresh joint import of
`Theorems.FiniteAdeleTraceCharacter`, `Theorems.FiniteBoxFourier`, and
`Theorems.AdeleRestrictedProductHaar`. Replay by importing them in that
order and using `#check @` and `#print axioms` on all eight declarations
below, plus `Masullo.finiteBoxLocalFourier` and
`Masullo.exists_adeleRestrictedProductHaar`. All ten axiom sets were
exactly `[propext, Classical.choice, Quot.sound]`.

## Independent statement and source review

Yah reviewer `TjkTwAg` (owning session event 74) checked the seven
public endpoints against the exact obligation and the pinned definitions.
The final built signatures for those endpoints matched the reviewed
signatures verbatim. The local character definition was additionally
checked in the joint import and against the pointwise trace formula.
The reviewer confirmed the actual cofinite restricted product, no fixed
stage restriction, compatibility of the local scalar action and trace
with the diagonal embedding, and the absence of an exact conductor
claim. The diagonal identity is for every field element, including zero.
The reviewer did not attest the candidate's elaboration; the independent
review and the owning checks serve separate purposes.

Provisional source review: Pinned PDF p. 558, Examples A.3.1.9–10 and
(A.3.1.7), gives the trace pullback; Examples A.3.1.5–6 and A.3.1.8,
pp. 557–558, give the positive local phases and their product. Those
signs do not give a diagonal-trivial character, already at $1/3$ over
$\mathbb Q$. The module retains the positive Archimedean phase and
conjugates the positive finite factors. This makes the conjugated
Fourier kernel in (2.2.4.32), p. 92, use the positive finite phases.
The printed finite factor there also uses the frequency rather than
the integration variable, which `finiteBoxLocalFourier` repairs by
restricting the measure to the box. The reviewer compared Markdown
and numbered layout and checked PDF vector extraction for the bars,
not the rendered page. See the [branch handoff](single-place-norm.md#continuous-finite-adele-trace-character)
for the remaining global integral obligation.

## Built signatures of the new declarations

```text
@Masullo.finiteCompletionTraceAddChar_apply : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (v : HeightOneSpectrum (𝓞 K)) (x : HeightOneSpectrum.adicCompletion K v),
  (Masullo.finiteCompletionTraceAddChar v) x =
    (Masullo.padicStdAddChar ↑(Masullo.finiteCompletionBasePrime v))
      ((Algebra.trace ℚ_[↑(Masullo.finiteCompletionBasePrime v)] (HeightOneSpectrum.adicCompletion K v)) x)
@Masullo.numberFieldFiniteAdeleAddChar : {K : Type u_1} →
  [inst : Field K] → [inst_1 : NumberField K] → AddChar (FiniteAdeleRing (𝓞 K) K) ℂ
@Masullo.numberFieldFiniteAdeleAddChar_eq_prod : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (a : FiniteAdeleRing (𝓞 K) K) (S : Finset (HeightOneSpectrum (𝓞 K))),
  (∀ v ∉ S, a v ∈ HeightOneSpectrum.adicCompletionIntegers K v) →
    Masullo.numberFieldFiniteAdeleAddChar a = ∏ v ∈ S, (starRingEnd ℂ) ((Masullo.finiteCompletionTraceAddChar v) (a v))
@Masullo.continuous_numberFieldFiniteAdeleAddChar : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K],
  Continuous ⇑Masullo.numberFieldFiniteAdeleAddChar
@Masullo.conj_numberFieldFiniteAdeleAddChar_eq_prod : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (a : FiniteAdeleRing (𝓞 K) K) (S : Finset (HeightOneSpectrum (𝓞 K))),
  (∀ v ∉ S, a v ∈ HeightOneSpectrum.adicCompletionIntegers K v) →
    (starRingEnd ℂ) (Masullo.numberFieldFiniteAdeleAddChar a) = ∏ v ∈ S, (Masullo.finiteCompletionTraceAddChar v) (a v)
@Masullo.norm_numberFieldFiniteAdeleAddChar : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (a : FiniteAdeleRing (𝓞 K) K), ‖Masullo.numberFieldFiniteAdeleAddChar a‖ = 1
@Masullo.numberFieldFiniteAdeleAddChar_diagonal : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] (x : K),
  Complex.exp (2 * ↑Real.pi * Complex.I * ↑((Algebra.trace ℚ K) x)) *
      Masullo.numberFieldFiniteAdeleAddChar ((algebraMap K (FiniteAdeleRing (𝓞 K) K)) x) =
    1
@Masullo.finiteCompletionTraceAddChar : {K : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] → (v : HeightOneSpectrum (𝓞 K)) → AddChar (HeightOneSpectrum.adicCompletion K v) ℂ
```
