# A base-normalized common lift cannot implement the rational prime-two action

**Objective.** Test the passage from the projected global operator to an
orbital operator before using any scalar trace identity toward RH or GRH.
The [cut-output obstruction](trace-cut-orbital-q.md) excludes postprocessing
on all representatives, but leaves upstream lifts and chosen sections open.
This test eliminates one upstream lift, even if its quotient kernel depends
on the cutoff and even at an arbitrarily small positive Fourier band.

## The lift and why it cannot work

Write $J=\mathbb A_{\mathbb Q}^\times$, $H=\mathbb Q^\times$, and $D_0,D_2$
for the stages where all finite places, respectively all finite places other
than $2$, must be units. The positive logarithmic section $\sigma(u)$ has
finite coordinates $1$ and lies in $D_0$. The specified lift uses a
nonnegative indentation $w$, with full $H$-sum and restricted
$H\cap D_0$-sum both $1$ at every $x\in D_0$. It lifts a common quotient
kernel by the two-leg coefficient $\sum_{h\in H}w(h^{-1}x)w(h^{-1}y)$,
and integrates the negative input shell over $D_2\setminus D_0$.

Subtract the two actual sums at each base point $x$. Nonnegativity forces
$w(h^{-1}x)=0$ for $h\notin D_0$. Every idele off $D_0$ can be written
in this form by bringing it into the base by a principal idele; hence
$w=0$ off $D_0$. At a base output and an off-base input, each term then
vanishes on at least one leg. The pair weight is zero
pointwise, independent of both the quotient kernel and the input. Lean
uses `Masullo.rationalIdeleFiniteStage_indentation_pair_weight_hasSum_zero`
for this step. These normalizations are not vacuous: As a mathematical
example, take the indicator of the clopen fundamental window with positive
real component and all finite components units. At a base point the unique
normalizing principal element is one of $\pm1$.

Our original band-mode construction starts with an even Schwartz $g$ whose
Fourier transform is supported in band $B/p$ and vanishes at zero, and
normalizes $g(0)=-1$. Poisson summation gives $\Theta g(t)=1$ for sufficiently
small $t>0$, and Schwartz decay gives $\Theta g(t)\to0$ as $t\to\infty$.
The difference $b=g-g(p\,\cdot)$ lies in band $B$ and has both zero moments
removed. Its theta sum telescopes in the orbit index; absolute summability
from the two-moment log bounds upgrades the two-sided window limit to an
actual `HasSum`. `Masullo.exists_rationalThetaBand_logPeriod_hasSum_one`
proves that one such $b$ works for every log position at each fixed $p>1$.
The $p=2$ periodization is identically $1$. The nonnegative above-one bump
of `Theorems.RationalOrbitalPrimeTwo`, positive at $2$ and supported in
$[5/3,7/3]$, has strictly positive integral against $t^{-a}\,d^\times t$
for every real $a$. The corresponding log convolution on the constant
periodic mode is therefore nonzero at every point, also at $a=1/2$.

`Masullo.rationalBasePrimeTwoShell_misses_band_constant` brings the two
conclusions together in [the theorem module](../../Proofs/Theorems/RationalBasePrimeTwoShell.lean).
It compares pointwise operator outputs, not a trace, and does not assume
that any particular quotient kernel exists. If the specified lift were to
implement this orbital action on band representatives, it would have to
agree on the constant mode, regardless of the choice of the cutoff kernel
or of the input used in the lift. Zero cannot equal that nonzero output.

## Source interface and limits

Source: *The Music of the Primes*, pinned PDF SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Locators here are printed pages of that PDF. The fresh readings are
text/layout-based and provisional as visual readings.

- Proposition 12.2.2.2, p. 508, (12.2.2.1–2), supplies the common
  quotient-kernel two-leg lift for counting Haar, in a diagonal unfolding
  argument. It does not identify the projected orbital operator. Proposition
  12.2.2.4, pp. 512–514, simultaneously normalizes the full and base
  orbit sums for its increasing exhaustion with base fundamental domain.
  Its ambient setup is not literally the rational clopen-window model.
  These two normalizations are required of a repair using that same weight
  to implement both unfoldings as written, not of all possible lifts.
- Chapter 11, §11.3.2, pp. 494–496, instead has a decreasing unit chain.
  The two section factors of (11.3.2.2) are not this indentation. On the
  invariant finite-unit window the signed input difference for the
  localized step $S'=\{\infty,2\}$ is $-1_{D_2\setminus D_0}$, with
  an additional right mask in (11.3.2.4). This is the block tested here,
  not a global equality between the two chapter constructions. Retaining
  the later original right cutoff already kills that block in (11.3.2.3);
  changing it cannot restore the zero mixed weight of the specified lift.
- Theorem 7.4.2.1, p. 367, and its kernel (7.4.0.2), p. 366, start with
  convolution on the orbital subquotient. In log coordinates with twist
  $a$ this uses the test multiplied by $\exp(-ay)$ before periodization.
  The claim of (11.3.2.5), p. 496, is a limiting trace calculation, not a
  finite-cutoff operator comparison. The nonzero output on an actual band
  mode is our control for any repair that proposes to identify these
  operators on this test. It is not a consequence of the claimed trace.
- The support choice in Theorem 12.5.1.1, p. 520, requires $T>7/3$ for
  this bump, and residue norms outside $S$ must exceed $T$. Thus $2\in S$
  is mandatory in that scalar calculation. This test does not contradict
  a required omitted-prime scalar there. Neither the projected trace
  identity nor RH or GRH is settled. A different lift, with no simultaneous
  full/base normalization for the same weight, is not excluded; it would
  still owe both a valid common-diagonal comparison and the orbital
  identification where consumed.

**Review and checks.** Independent Yah `base-shell-source-review`
(`ELQFIVa`), same owner session, checked the exact endpoint statement
(source SHA-256 `7ca249cc686fdba75e7a39296da86cae79ac6ab73915c1c49aa0b63f3b589c37`),
the helper at writer output `c7b9d1d6d89979f3e8ea5dda80115215f8e05b3e`,
and the passage dependencies and scope above. Owner session
`01a205f3-b1d1-7885-8c36-002f23511cea` records the exact integrated
candidate, scoped build, signatures and axioms, and adoption if successful.

**Runnable successor.** For the scalar route, the remaining lower-edge
check in [the Chapter 12 real-prime comparison](trace-real-prime-q.md#lean-checked-sharp-limit-without-a-support-gap)
is independent of the eliminated lift. On this branch, do not test another
kernel in the same lift. Any proposed new transfer should first specify
which kernel or diagonal it actually represents and why its inputs and
order of limits give the identification that the consuming trace needs.
