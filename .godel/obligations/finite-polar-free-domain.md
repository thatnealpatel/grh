# The finite factor in the Chapter 5 polar-free space

**Status:** The pointwise tensor inclusion in (5.3.4.1), p. 259, fails
with the multiplicative Schwartz space of Remark 2.1.2.1, p. 63. The
obstruction is on a single pure tensor over $\mathbb Q$, with
$S=\{\infty,3\}$. It precedes any question about tensor topology.
This is a source audit and an informal calculation, not a Lean result.

## Printed membership, and a failed additive extension

In the [pinned edition](../sources/masullo/README.md), §2.1.1.3, p. 62,
defines $\mathcal S(\mathbb Z)$ by $a_k=O(|k|^{-N})$ as $|k|\to\infty$
for every integer $N\ge0$. Remark 2.1.2.1, p. 63, expressly includes
this space in $\mathcal S(F_v^\times)$ via $\mathcal O_{F_v}^\times$-invariance
on the uniformizer powers. It distinguishes this space from the
strictly smaller $C_c^\infty(F_v^\times)$. In contrast, §2.1.2.1, p. 63,
and Example 2.1.2.5, p. 64, identify additive Schwartz–Bruhat tests
with locally constant, compactly supported functions.

Let $U=\mathbb Z_3^\times$, and put $g(3^ku)=3^{-k}$ for $k\ge0$ and
$g(3^ku)=0$ for $k<0$, for $u\in U$. This is well-defined on the
punctured field by the unique valuation index $k$. For each $N\ge0$,
$(1+|k|)^N|g(3^k)|$ tends to zero at both ends of $\mathbb Z$ because
exponential decay dominates any fixed power of $k$ on the positive
end, and the negative end is zero. Thus $g\in\mathcal S(\mathbb Q_3^\times)$
by the printed criterion. The weight is polynomial in $k$, not in
$|3^k|_3^{-1}=3^k$. Its multiplicative support is not compact: Its
valuation image is all of $\mathbb Z_{\ge0}$. The proof of Lemma
5.3.4.3 on p. 262, just before (5.3.4.7), explicitly uses the full
$\mathcal S(\pi_v^{\mathbb Z})$ factor, so replacing the finite space
by compact-away tests is a repair, not a reading of Chapter 5's symbol.

On the additive side, every neighborhood of zero contains $3^k$ and
$3^{k+1}$ for some $k\ge0$, with distinct $g$-values. No assignment
at zero makes $g$ locally constant there. The extension by zero is
continuous and supported in the compact set $\mathbb Z_3$, so it is
local constancy, not continuity or additive compact support, that
fails. By contrast, $h=\mathbf1_U$ is supported on one compact open
shell, and extends by zero to the locally constant additive test
$\mathbf1_{\mathbb Z_3}-\mathbf1_{3\mathbb Z_3}$.

## The real slice tests the displayed inclusion

Equation (A.1.5.1), p. 543, makes $\mathbf A_{\mathbb Q,S}$ the product
$\mathbb R\times\mathbb Q_3$. Fix any nonzero $b\in C_c^\infty((1,2))$,
extended by zero to $\mathbb R$. All its derivatives vanish at zero,
so it belongs to the real factor in (5.3.4.1) by the pullback in
Definition 5.3.4.1, p. 259, and the flatness criterion (5.3.3.10),
p. 252. The flatness display and the coordinate-vanishing conditions
use $p$ real and $q$ complex coordinates, although an intervening
space in the prose is misprinted with $\mathbb C^p$. The self-inclusion
printed in the introductory sentence of Definition 5.3.4.1 does not
affect the test: The sentence specifies the preimage of the real flat
subspace, and the proof of Lemma 5.3.4.2(1) on p. 260 uses that
subspace inside the ordinary additive space.

The left side of (5.3.4.1) contains the elementary tensor $b\otimes g$.
If an additive Schwartz–Bruhat function agreed with its product
values on $\mathbb R^\times\times\mathbb Q_3^\times$, evaluate it at
$t_0\in(1,2)$ with $b(t_0)\ne0$. By the additive kernel isomorphism
(2.1.4.1), p. 71, each real slice of such a function is a finite linear
combination of additive finite tests, hence locally constant. Here
the slice would equal $b(t_0)g$ off zero, which cannot be locally
constant at zero. This rules out the canonical inclusion even before
completion, and even if a value on the zero fiber may be chosen
freely. The control $b\otimes h$ does give an additive test under the
same kernel isomorphism.

## Scope of the repair and use in Lemma 5.3.4.2

The same obstruction works at any finite completion: Use a
uniformizer $\pi_v$, residue size $q_v$, and the sequence $q_v^{-k}$
for $k\ge0$, zero otherwise. More generally, a unit-invariant rapidly
decreasing valuation sequence has an additive Schwartz–Bruhat
extension exactly when it is finitely supported in $k$. Compact
additive support bounds $k$ below, and local constancy at zero forces
an eventually constant positive tail. Decay forces that constant to
be zero. Conversely a finite union of shells is compact open and
away from zero. Without imposing unit invariance, the finite tests
whose **zero extension** is additive Schwartz–Bruhat are exactly
$C_c^\infty(F_v^\times)$: Such an extension vanishes on a neighborhood
of zero, and conversely compact support in the punctured field leaves
such a neighborhood. This also gives the whole intersection of the
two finite test spaces under restriction: A multiplicative Schwartz
test decays along $\pi_v^k$ (evaluate the unit-group factor at $1$
in the decomposition on p. 262), whereas an additive extension is
constant there for large $k$. That value must be zero, forcing the
extension to vanish near zero. This identifies the pointwise repair,
not its tensor topology.

On p. 260, the proof of Lemma 5.3.4.2(1) explicitly uses the claimed
closed inclusion $\mathcal S(F_v^\times)\subset\mathcal S(F_v)$ to
establish closedness and stability of the tensor subspace. The finest
locally convex topology cannot supply a pointwise inclusion where
none exists. Part (2) states forward entireness, but its proof starts
with **additive** factors and assumes product entireness. It infers
local vanishing from this assumption, then invokes continuity and
density on pp. 260–261. That does not
supply the forward local calculation on the printed space, and
product entireness alone is not a local residue criterion. The proof
of (3), p. 261, explicitly treats the finite $f_v$ as locally constant
and compactly supported. That is consistent with the smaller test
space, not with the full space in Remark 2.1.2.1.

The [independently reviewed finite residue audit](finite-local-zeta-residue.md)
supplies the forward finite-local input on the repaired domain: The
compact-away shell sum has only finitely many terms (and thus is
entire on each local character component). Its pp. 130, 141, and 560
source checks are inherited from that note, not repeated here. This
audit does not establish entireness on a repaired completed tensor
space, justify the Archimedean input or passage to the completion,
or settle character descent. It is a counterexample to the printed
inclusion, not a counterexample to repaired entireness. The
[diagonal-unit check](#diagonal-unit-cancellation-on-every-quotient-character-component)
separately tests the reverse inference on the actual quotient.

**Independent review:** Yah session `01a201f3-2ac7-70b6-a2de-5c20cb1c1598`,
agent `UduQBuX` (`finite-factor-review`). The reviewer checked the source
pin, used Markdown and layout to locate the passages, and independently
inspected raster glyph crops for the decisive notation, with raster OCR
for surrounding prose. For the printed-domain route, the reviewer
confirmed the rapid-sequence definition, its unit-invariant embedding,
the real flatness criterion, and the full finite factor in (5.3.4.1).
For the additive-extension route, the reviewer confirmed the product
and additive slice definitions, and separately checked the two-point
obstruction and the compact-away control. The reviewer also confirmed
the uses of the inclusion in Lemma 5.3.4.2 and the full valuation
factor immediately before (5.3.4.7), but did not redo the residue audit
or review the topology of the replacement.

## Diagonal-unit cancellation on every quotient character component

**Result:** The reverse inference in the proof of Lemma 5.3.4.2(2),
p. 260, fails for an additive pure tensor over $\mathbb Q$ with
$S=\{\infty,3\}$. Its $S$-local zeta transform is entire on the whole
quotient character space, although its finite test takes value one
at zero and its finite zeta factor has a pole. This is a mathematical
check of the printed inference, not a Lean theorem or a counterexample
to forward entireness on the repaired domain.

**Printed route and hypotheses.** Use the [inherited rendered reading
of the proof](#scope-of-the-repair-and-use-in-lemma-5-3-4-2): The proof
starts with additive Schwartz–Bruhat factors, assumes $Z_S$ entire
on $\Omega(J_{F,S})$, and infers local vanishing, in particular
$f_v(0)=0$ at finite $v$. The statement of part (2) starts instead
with a polar-free test. With $B=\mathbb Z_3$, choose nonzero
nonnegative $b\in C_c^\infty((1,2))$ and extend by zero. Put
$$
f(t,y)=(b(t)-b(3t))\mathbf1_B(y),\qquad
h(t,y)=b(t)\mathbf1_{B\setminus3B}(y).
$$
The real difference is a nonzero Schwartz test (the two supports
are disjoint) and is flat at zero. Both finite indicators are compact
open in the additive field. Thus $f$ is in the additive pure-tensor
domain of the reverse inference by (2.1.4.1), p. 71, and the additive
test conventions on pp. 63–64 in the [domain audit](#the-real-slice-tests-the-displayed-inclusion).
It is not asserted to be in the antecedent of the forward statement.

**Defining route on the quotient.** The [shared-norm audit](hecke-right-line-majorant.md#checked-shared-norm-and-the-printed-s-local-mismatch)
verifies the quotient and product norm in (3.1.2.1) and the following
clause, p. 120, with the product (A.1.5.1) and outside-$S$ integrality
in §A.1.5.1, p. 543. Here the numerator is
$G=\mathbb R^\times\times\mathbb Q_3^\times$, the diagonal units are
$\pm3^{\mathbb Z}$, and $N(t,y)=|t||y|_3$. For every continuous
quasi-character $c$ of $J_{\mathbb Q,S}$ its pullback to $G$ satisfies
$c(3,3)=1$. More explicitly, writing $y=3^k u$ with $u\in B^\times$,
the quotient identifies with $\mathbb R_{>0}\times B^\times$ by
$(t,y)\mapsto (3^{-k}|t|,\operatorname{sgn}(t)u)$, with inverse on
classes given by $(r,u)\mapsto[(r,u)]$. With the [inherited character
convention](complex-gaussian-angular.md#rendered-readings) from
(3.1.1.1)–(2), p. 119, these coordinates put every component in the form
$c=\xi N^s$ for a fixed unitary character $\xi$ of $B^\times$.

Equation (3.3.1.1), p. 129, integrates the test times the pulled-back
character on $G$, not directly on $J_{\mathbb Q,S}$: Inherit the
[integral reading](isotypic-inverse-range-q-sqrt-minus-five.md#character-domain-and-constants)
and the [product Haar reading](isotypic-fourier-gluing-q-sqrt-minus-five.md#evidence-and-limits)
of (A.3.4.2), p. 561. On $\Re s>0$ all terms converge absolutely:
The real supports are compact in $\mathbb R^\times$, and the finite
absolute mass on $B\setminus\{0\}$ is a geometric shell sum. Apply
$(t',y')=(3t,3y)$ to the integral of $b(3t)\mathbf1_B(y)c(t,y)$.
The indicator becomes $\mathbf1_{3B}(y')$, multiplicative Haar is
invariant, and $c(t'/3,y'/3)=c(t',y')$. Therefore
$$
Z_S(f,c)=Z_S(h,c)\qquad(\Re s>0)
$$
on **every** component, with no normalization factor. The substitution
uses only diagonal-unit invariance and applies to any such unit and
integrable translated test on its common convergence domain. The
right-hand test has compact support in $G$: $\log N$ is bounded on it,
so differentiation of $e^{s\log N}$ under the integral gives an
entire continuation component by component. In this example the
continuation is zero on $\xi\ne1$ by the $B^\times$ Haar average,
and nonzero on the trivial component.

**Pole control and verdict.** In (3.3.1.7), p. 130, with unit mass one
from (A.3.2.2), p. 560, the local finite factor of $f$ on the trivial
norm line is
$$
\sum_{k\ge0}3^{-ks}=(1-3^{-s})^{-1}\qquad(\Re s>0).
$$
Inherit those readings and the shell-tail calculation from the
[finite residue audit](finite-local-zeta-residue.md#defining-integral-and-reflected-control).
This factor has a simple pole at $s=0$, and $\mathbf1_B(0)=1$.
Writing $M_b(s)=\int b(t)|t|^s\,d^\times t$, the real factor of $f$
on that line is $(1-3^{-s})M_b(s)$, with $M_b(0)>0$. This cancels the
pole rather than making its finite residue vanish. The same calculation
works with $3$ replaced by any rational prime $p$ and $S=\{\infty,p\}$.
Holomorphy does not detect whether the **given** tensor has zero finite
slice, even when the entire transform is not identically zero. The
**different** representative $h$ is flat and compact-away, so the example
does not obstruct finding such a lift.
Nor does it test passage to a completed tensor space.

**Evidence:** Independent review by `GJphKCD` (`reverse-inference-review`,
transcript Yah `01a2052f-36ab-7cb0-9c82-1c22ab09a1ae`), against
`c1211d2341543aa63bc58bdd4fee81206e2411ac`. The reviewer separately
checked the printed inference and witness membership, the applicability
of the inherited quotient and integral readings, and the defining
calculation at $3$ (including absolute convergence, the change of
variables, and the nonzero continuation). The source readings above are
inherited from accepted rendered audits, not a new visual check. The
quotient coordinates, absolute convergence, substitution, and comparison
of orders are ordinary mathematics. The accepted [exact-stage Lean
pairing](#checked-entire-pairing-on-the-exact-rational-idele-stage)
already handles the compact-away representative for its stage and
Hecke-character hypotheses; it is not a formalization of this
original additive test or all characters of the printed quotient.

## Residues characterize a compact-away lift

**Result (ordinary mathematics, not Lean).** Let $F=\mathbb Q$,
$S=\{\infty,3\}$, $B=\mathbb Z_3$, and
$f(t,y)=a(t)\mathbf1_B(y)$ with arbitrary complex-valued
$a\in C_c^\infty(\mathbb R_{>0})$, extended by zero. With $L=\log 3$,
$g(x)=a(e^x)$, and $P(x)=\sum_{k\in\mathbb Z}g(x+kL)$, one has
$$
 \operatorname{Res}_{s=2\pi i n/L} Z_S(f,N^s)=\widehat P(-n),
 \qquad
 \widehat P(m)=\frac1L\int_0^L P(x)e^{-2\pi i mx/L}\,dx.
$$
Entireness on all quotient character components is equivalent to $P=0$,
and to the existence of a compactly supported smooth Bruhat test on
$\mathbb R^\times\times\mathbb Q_3^\times$ with the **same** $Z_S$
transform on all components. A lift can be taken as a pure tensor with
finite factor $\mathbf1_{B^\times}$. This is a project criterion, not the
reverse inference about the *given* test in Lemma 5.3.4.2(2), p. 260.

**Inherited source inputs and applicability.** The additive test
conventions on pp. 63–64 and (2.1.4.1), p. 71, used in the
[diagonal-unit check](#diagonal-unit-cancellation-on-every-quotient-character-component),
admit $f$: The real extension is smooth and zero near zero, and $B$
is compact open. We are not assuming the finite polar-free antecedent
of the forward statement. Use the same quotient and norm from
(3.1.2.1), p. 120, and (A.1.5.1) and §A.1.5.1, p. 543, and the
component convention (3.1.1.1)–(2), p. 119, as in that check. In the
coordinates $(3^{-k}|t|,\operatorname{sgn}(t)u)$ for $y=3^ku$,
$c=\xi N^s$, with $\xi$ a unitary character of $B^\times$ and
$N=|t||y|_3$.

- (3.3.1.1), p. 129, uses the [integral upstairs, without division by
  the diagonal units](isotypic-inverse-range-q-sqrt-minus-five.md#character-domain-and-constants).
  (A.3.4.2), p. 561, uses the [product of the local Haar
  measures over $S$](isotypic-fourier-gluing-q-sqrt-minus-five.md#evidence-and-limits).
- (3.3.1.7), p. 130, [pairs the local test with the local character,
  not its inverse](complex-gaussian-angular.md#rendered-readings).
  (A.3.2.2), p. 560, gives [mass one on the finite
  units](finite-local-zeta-residue.md#defining-integral-and-reflected-control)
  and [raw real Haar $dt/|t|$](trace-real-prime-q.md#source-and-domain).
  Here only $t>0$ contributes, so the real log measure is $dx$, without
  an additional sign or normalizing factor.

**Defining calculation.** On $\Re s>0$, the real support is compact
away from zero, and the absolute finite shell sum is geometric.
Fubini and $y=3^ku$, $k\ge0$, give
$$
 Z_S(f,\xi N^s)= M_a(s)\frac{\int_{B^\times}\xi(u)\,d^\times u}{1-e^{-Ls}},
 \qquad M_a(s)=\int_{\mathbb R}g(x)e^{sx}\,dx .
$$
The unit integral is zero for $\xi\ne1$ by Haar invariance and one
otherwise. Thus the nontrivial components continue by zero, and only
the trivial component requires pole removal. The numerator $M_a$
is entire by compact log support. The denominator has simple zeros
at $s_n=2\pi i n/L$, with derivative $Le^{-Ls_n}=L$. Consequently
its quotient with numerator $M_a$ has residue $M_a(s_n)/L$ (zero at
a removable singularity). Locally the sum for $P$ is finite, and on
$[0,L]$ only finitely many translates can contribute. Unfolding gives
$$
 \int_0^L P(x)e^{s_n x}\,dx
 =\sum_k\int_{kL}^{(k+1)L} g(u)e^{s_n u}\,du=M_a(s_n),
$$
since $e^{-s_n k L}=1$. The positive exponent gives the index $-n$;
the derivative $L$ is exactly the normalization of the circle
coefficient. As all possible poles are simple, entireness is equivalent
to the vanishing of every coefficient, hence to $P=0$ by Fourier
uniqueness on the circle.

**Lift and converse.** Restrict the [compact-log difference
calculation](trace-orbital-q.md#which-quotient-is-closed) to
$C_c^\infty(\mathbb R)$ at period $L$; neither its Hilbert range nor
its provisional global source interface is used here. If $P=0$, then
$q(x)=\sum_{k\ge0}g(x+kL)=-\sum_{k<0}g(x+kL)$ is smooth and compactly
supported, using the first sum at the right end and the second at the
left. It satisfies $g(x)=q(x)-q(x+L)$. Taking $b(t)=q(\log t)$ on the
positive ray, we have $a(t)=b(t)-b(3t)$. The [accepted diagonal-unit
substitution](#diagonal-unit-cancellation-on-every-quotient-character-component)
in the $b(3t)\mathbf1_B(y)$ term replaces it by
$b(t)\mathbf1_{3B}(y)$ under each pulled-back character on $\Re s>0$.
It preserves Haar and the character, with no scalar. Hence
$b(t)\mathbf1_{B^\times}(y)$ is the required representative. Conversely,
any compact-away Bruhat representative with the same transform on the
common convergence half-plane gives entire continuation, since $\log N$
is bounded on its compact multiplicative support. Equality here is of
transforms, not of tests. In particular, the finite factor of $f$ is
still one at zero and still has its simple poles on the trivial norm
line. The criterion and proof also work for any single rational prime
$p$ with $S=\{\infty,p\}$, $B=\mathbb Z_p$, and $L=\log p$; its finite
unit mass is likewise one. No completed-space, noncompact real-test,
or many-place assertion is made.

**Evidence.** Independent reviewer `BZZyWIK` (`compact-away-review`,
transcript Yah `01a20538-8b62-74f7-af92-08af3ae701a6`) checked
`440cba4511f9a646194d7d1eb732e8983a4a2c0e`. The reviewer confirmed
admissibility for the additive route on p. 260, the applicability
of the inherited quotient, character, integral, and Haar readings
listed above, and separately checked absolute convergence, the unit
average, the signed and scaled residue formula, the removal criterion,
and both directions of the compact-away lift claim. These are
mathematical and source-applicability checks, not new renderings or
Lean elaboration.

**Checked Fourier coefficient bridge (Lean).**
[`Masullo.fourierCoeffOn_logPeriodization_neg`](../../Proofs/Lemmas/CompactLogMellinPeriodization.lean)
proves the normalized coefficient identity on $[0,L]$ for every $L>0$,
every continuous compactly supported $g:\mathbb R\to\mathbb C$, and
every $n\in\mathbb Z$. The left side uses the accepted
`Masullo.logPeriodization L g` in the physical log coordinate; the right
side is `compactLogMellin g (2 * π * n * I / L) / L`. The proof applies
`Real.fourierCoeff_tsum_comp_add` at $-n$ to $u\mapsto g(Lu)$, proves
finite support of the restricted translates on every compact, and
checks both the interval and whole-line changes of variables. Thus
$L=\log 3$ needs no separate summability or smoothness premise. This is a
Lean result for the repair, not a derivation of the adelic residue or of
the printed reverse inference. The source applicability is inherited
from the evidence above, not a new manuscript reading.

**Lean evidence.** `compact-log-coeff-review` (`xptOGce`, transcript Yah
`01a20558-d9d5-7ebe-a54d-daf0713a0cf0`) independently checked the fixed
statement against accepted source `022676f32fb32118354a025cb57b7c48d5dac9cf`
and the pinned Mathlib definitions, including the domain, sign, and
normalization. This was exact-source review, not elaboration. The same
owning Yah transcript records the candidate build, joint-import
signature and axiom check, and specialization at $L=\log 3$.

**Checked Fourier uniqueness (Lean).**
[`Masullo.logPeriodization_eq_zero_of_compactLogMellin_samples_eq_zero`](../../Proofs/Lemmas/CompactLogMellinPeriodization.lean)
proves pointwise vanishing of `logPeriodization L g` if every sample
`compactLogMellin g (2 * π * n * I / L)` is zero, for all $L>0$ and
continuous compactly supported $g:\mathbb R\to\mathbb C$. The proof
reuses the coefficient bridge's compact-translate summability and
Fourier rescaling for $u\mapsto g(Lu)$. It reindexes $n\mapsto -n$ to
get a zero Fourier sample sequence, applies Mathlib's unit-period
Poisson formula at $x/L$, and transports the result back to $x$.
The owning check includes $L=\log 3$ with the same hypotheses, not
smoothness or a Schwartz condition. It proves the Fourier implication
in the repair only, not the adelic residue identity, pole removal, the
existence of the lift, or the printed reverse inference. The manuscript
conventions are inherited from the evidence above.

**Uniqueness evidence.** `compact-log-uniqueness-review` (`RlpbOpt`,
transcript Yah `01a20562-2211-7f0f-b01c-f419a5877c37`) independently
checked the statement, sign, physical coordinate, and applicability of
the reduction against `c6ba655a2bd4172c960654957aa0f0f4a2f8ad26` and
pinned Mathlib, without elaborating. The same owning transcript records
the integrated candidate, warning-free build, joint-import signatures
and axioms, and $\log 3$ specialization.

**Checked compact-log difference primitive (Lean).**
[`Masullo.logDifferencePrimitive_spec`](../../Proofs/Lemmas/CompactLogMellinPeriodization.lean)
uses the canonical `logDifferencePrimitive L g x = ∑' k : ℕ, g (x + k * L)`.
For every real $L>0$ and continuous, compactly supported
$g:\mathbb R\to\mathbb C$ of pointwise zero `logPeriodization L g`, it proves
that the primitive is continuous, compactly supported, and satisfies
$g(x)=q(x)-q(x+L)$ at every real $x$. The proof factors out the Fourier
argument's compact-local finiteness, now in the physical log coordinate.
The shift removes exactly $k=0$. For compact support, the nonnegative
sum vanishes beyond the right end of the support interval; the strictly
negative leg of the full periodization vanishes beyond its left end,
so zero periodization forces the primitive to vanish there too. The
owning check composes the theorem with Fourier uniqueness at $L=\log 3$
from vanishing Mellin samples, without a smoothness or Schwartz premise.
This is a project repair; source applicability is inherited from the
reviewed construction above, not a new manuscript reading.

**Primitive evidence.** `compact-log-primitive-review` (`ckBZSur`,
transcript Yah `01a2056a-a55a-7561-9441-27136d96d4f0`) independently
checked the exact statements and the scope of the reductions against
`809ffb4ce75dbd4ea4a10af93a48cdb6bf7438c8` and pinned Mathlib, without
elaboration. The same owning transcript records the integrated candidate,
warning-free build, fresh joint-import signature and axiom checks, and
the $\log 3$ composition.

**Next bounded check (formalization only).** Prove smoothness of the
same primitive for smooth compactly supported $g$. The private
`logDifferencePrimitive_eqOn_finset` already identifies $q$ with a
finite sum on each compact interval, under $L>0$ and compact support
alone. In the same module, reuse this equality on a neighborhood of
each point and check the smoothness of the translated finite sum and
its transfer to $q$. Neither zero periodization nor the stronger
`LogWeightedSchwartz` hypotheses of `logPeriodization_smooth` are
needed for that step. This is the smoothness argument in the
[compact-log difference calculation](trace-orbital-q.md#which-quotient-is-closed),
with no new numbered manuscript dependency. Transport to the positive
ray, assembly of the adelic lift, and the residue and pole-removal
identifications remain separate Lean obligations.

## The finite-only repair is not projectively continuous

**Result:** For $F=\mathbb Q$ and $S=\{\infty,3\}$, set
$E=\mathcal S_{00}(\mathbb R)$ with its induced Schwartz topology,
$H=C_c^\infty(\mathbb Q_3^\times)$ with its usual locally convex LF
topology, and $D=\mathcal S(\mathbb R\times\mathbb Q_3)$ with its
additive Schwartz–Bruhat topology. The pointwise zero-extension map
$T:E\otimes_\pi H\to D$ is defined on the algebraic tensor product but
is **not continuous**. This is a second obstruction, not a restatement
of the failure of pointwise extension on the original finite factor.

**Printed source, checked on the pinned rendered pages:** (A.1.5.1),
p. 543, identifies the $S$-adeles with the finite product, here
$\mathbb R\times\mathbb Q_3$. (5.3.4.1), p. 259, uses $\otimes_\pi$,
and the proof of Lemma 5.3.4.2(1), p. 260, uses completeness of that
projective tensor product to argue closedness.
The criterion surrounding (C.2.3.14), p. 679, requires joint continuity
of the bilinear map, not merely separate continuity. In contrast,
(2.1.4.1), p. 71, uses $\otimes_\iota$; Proposition 2.1.4.1(1)–(2)
identifies the additive target with this tensor and gives its strict
LF topology. Its proof on pp. 71–72 gives the finite-dimensional
finite-factor stages tensored with the real Schwartz space. Proposition
2.1.2.4 and Example 2.1.2.5, p. 64, give the additive compact support
and congruence stages. Example 2.1.1.3, p. 60, gives the Schwartz
seminorms; (5.3.3.10), p. 252, and Definition 5.3.4.1, p. 259,
give the closed real subspace via flatness at zero in this model.
In particular every smooth bump supported in $(1,2)$ is in $E$.
Remark 2.1.3.3, p. 69, already distinguishes the two topologies for
the full additive finite-adelic factor; it does not test this repair.

**Additive LF test:** For $r,s\ge0$, use the additive stage with
support in $3^{-r}\mathbb Z_3$ in the finite variable and invariance under
$3^s\mathbb Z_3$. Its real Schwartz coordinates are indexed by the
finite quotient $3^{-r}\mathbb Z_3/3^s\mathbb Z_3$. These stages are
cofinal: Finite tests have compact support and a common open
congruence subgroup of local constancy. Fix $t_0\in(1,2)$ and set
$$
q(\Phi)=\sup_{n\ge1}\left|\partial_x^n\Phi(t_0,3^{-n})\right|.
$$
On the $(r,s)$ stage only $1\le n\le r$ can contribute, and each
contributing term evaluates a derivative at $t_0$ of one Schwartz
coordinate. Thus $q$ is finite and is a continuous seminorm on each
stage (zero for $r=0$). It is continuous on $D$ by the **locally
convex** inductive-limit topology.

**Projective test:** For the bilinear map $B(b,h)(x,y)=b(x)\widetilde h(y)$,
where $\widetilde h$ is zero extension, take arbitrary zero neighborhoods
$U\subset E$ and $V\subset H$. A basic neighborhood contained in $U$
uses finitely many Schwartz seminorms, with real derivative orders at
most $m$. Choose $n>m$ and $h_n=\mathbf1_{3^{-n}\mathbb Z_3^\times}$,
a locally constant test on one compact open shell away from zero.
Continuity of scalar multiplication lets us choose $a\ne0$ with
$a h_n\in V$. For $\chi\in C_c^\infty((1,2))$ equal to $1$ near $t_0$,
let
$$
b_\lambda(x)=c\lambda^{-m}\chi(x)e^{i\lambda(x-t_0)},\qquad \lambda\ge1.
$$
The weights are bounded on the fixed compact support, and the product
rule bounds each tested weighted derivative independently of $\lambda$
by a constant times $c$. Fix $c>0$ small enough for $b_\lambda\in U$
for every $\lambda\ge1$. Since $\chi$ is identically $1$ near $t_0$,
we have $|b_\lambda^{(n)}(t_0)|=c\lambda^{n-m}$. The shell contains
exactly the $n$th sample among the $3^{-j}$, giving
$$
q(B(b_\lambda,a h_n))=|a|c\lambda^{n-m}\longrightarrow\infty.
$$
No product of zero neighborhoods maps into $\{q<1\}$. Thus $B$ is
not jointly continuous at zero, and (C.2.3.14), p. 679, rules out
continuity of $T$. The same proof works with the real factor unchanged
and any non-Archimedean local field in place of $\mathbb Q_3$, using
powers of a uniformizer. No feature of the residue size is used.

**Control and scope:** On the single fixed shell line $\mathbb C h_1$,
the map is jointly continuous into one additive stage, and $q$ there
reduces to $|a|\,|b'(t_0)|$. For the usual LF topology of $H$, take
finite-dimensional stages supported in $-r\le v_3(y)\le r$ and invariant
under $1+3^j\mathbb Z_3$ for $j\ge1$. Their zero extensions land in the
additive $(r,r+j)$ stage: For $y$ in the annulus and
$\delta\in3^{r+j}\mathbb Z_3$, $\delta/y\in3^j\mathbb Z_3$, so
$y+\delta=y(1+\delta/y)$ preserves both the annulus and the function;
the complement is preserved too. On each such fixed stage $B$ is
jointly continuous by its finite coordinates. On the full domain $B$
is separately continuous: With the finite factor fixed it has
finitely many Schwartz coordinates, and with the real factor fixed
it is continuous on every LF stage of $H$. It follows that
$E\otimes_\iota H\to D$ is continuous by the criterion at (C.2.3.22),
p. 682. This is a topology repair, not a reading of (5.3.4.1). The
test rules out the continuous inclusion
needed for the projective-completeness argument in Lemma 5.3.4.2(1),
even after repairing the finite factor. A continuous extension from
the projective completion would restrict to the same impossible map.
The test does not decide whether the repaired image is closed by
another argument or prove entireness or character descent. The
finite-local input remains the one in the
[accepted residue audit](finite-local-zeta-residue.md).

**Independent review:** Yah session `01a20200-e0f8-7ec2-acfd-a61b86a31e58`,
agent `gENGQlD` (`tensor-topology-review`). The reviewer matched the
source pin and independently inspected raster glyphs and prose at the
cited loci. For the projective route, the reviewer confirmed the
uncompleted $\otimes_\pi$ in (5.3.4.1), the real flatness condition,
the joint-continuity requirement on p. 679, and the completeness use
on p. 260, and checked the arbitrary-neighborhood oscillatory test.
For the additive route, the reviewer confirmed the finite product,
finite support and congruence stages, and $\otimes_\iota$/strict LF
identification on pp. 71–72, and checked finiteness and LF continuity
of $q$, the fixed shell line, and the separate-continuity repair.
No decisive source reading remains provisional. This is reviewed
mathematics, not Lean. The reviewer did not test closedness, entireness,
or descent. The earlier printed-domain audit and finite residue audit
are inherited, not redone.

## The repaired uncompleted tensor has closed image

**Result:** Set $E=\mathcal S_{00}(\mathbb R)$,
$H=C_c^\infty(\mathbb Q_p^\times)$, and
$D=\mathcal S(\mathbb R\times\mathbb Q_p)$ with the additive
Schwartz–Bruhat LF topology, for any prime $p$. For the continuous
zero-extension map $T:E\otimes_\iota H\to D$ of the preceding repair,
$$
\operatorname{im}T=\{\Phi\in D:\ \Phi(x,0)=0\ \text{for every }x,\quad
\partial_x^j\Phi(0,y)=0\ \text{for every }y,\ j\ge0\}.
$$
This is a closed subspace. In particular it gives the closed-image
part of the repaired Lemma 5.3.4.2(1), pp. 259–260, for $F=\mathbb Q$
and $S=\{\infty,3\}$. The tensor is algebraic, with the inductive
tensor topology, not a completion.

**Source interface:** Inherit the rendered readings and independent
review in [the preceding audit](#the-finite-only-repair-is-not-projectively-continuous):
The product model (A.1.5.1), p. 543, the real flatness criterion
(5.3.3.10), p. 252, and Definition 5.3.4.1, p. 259, and the
additive kernel isomorphism and finite-factor LF stages (2.1.4.1) and Proposition
2.1.4.1, pp. 71–72. The substitution of $H$ and $\otimes_\iota$
for the factors in (5.3.4.1), p. 259, is a repair. No new rendered
reading was needed, and projective completeness plays no role.

**Arbitrary-stage check:** Write $K=p^{-r}\mathbb Z_p$ and
$U=p^s\mathbb Z_p$ for any support and invariance stage containing
$\Phi$, with $r,s\ge0$. The profile on $c\in K/U$ is
$b_c(x)=\Phi(x,y_c)$ for any representative $y_c$. The value condition
sets $b_{U}=0$ as a Schwartz function, so the entire coset containing
zero disappears. For each other $c$ the derivative conditions set
$b_c^{(j)}(0)=0$ for every $j$. The coset $c$ is compact open and
avoids zero, so its indicator is the zero extension of a member of
$H$. Therefore $\Phi=\sum_{c\ne U}b_c\otimes\mathbf1_c$ as pointwise
profiles. Conversely any such pure product with factors in $E,H$
has both vanishings, and so does a finite sum. A finite additive
locally constant test with compact support is the zero extension
of an element of $H$ exactly when it vanishes at zero: Local
constancy then kills a neighborhood of zero. In the other direction,
a compact subset of the punctured field is also compact in the
field, so its complement is a neighborhood of zero.

**Actual LF topology:** On each stage the evaluation $\Phi\mapsto
\Phi(\cdot,y)$ is a projection to one Schwartz coordinate, or zero
if $y\notin K$. Scalar evaluation of its derivative of order $j$ at
zero is continuous by the Schwartz seminorm of order $(0,j)$.
The locally convex inductive-limit universal property gives
continuity on $D$. The zero-slice condition can use a single
Schwartz-valued kernel, or all scalar evaluations at $x$; their
common zero sets coincide. Intersecting with the derivative kernels
proves closedness. No common stage for a convergent unbounded family
is needed.

**Lean scope and identification:**
[`Props.PadicSchwartzFlatImage`](../../Proofs/Props/PadicSchwartzFlatImage.lean)
checks `mem_padicSchwartzFlatAwaySpan_iff` and
`isClosed_padicSchwartzFlatAwaySpan` for every prime $p$. The domain
model is a compactly supported locally constant map from $\mathbb Q_p$
to the real Schwartz space. To identify its underlying space with
$D$, cover the support by finitely many balls on which the profile is
constant and nonzero. The nonzero set is closed by local constancy,
so equals the compact support. Refining those balls to the smallest
of their radii gives uniform congruence invariance on the support
and its complement. The support is bounded and fits in some $K$.
Conversely every finite-stage tuple defines such a map. The Lean
reverse implication directly uses the accepted decomposition
`padicTest_eq_sum_closedBalls` on the Schwartz-valued map with zero
value at zero; its representatives' balls avoid zero by the strict
radius bound. The span of the pure products is the algebraic tensor
image, not a closure.

The Lean topology is generated by the seminorms whose pullbacks
along $b\mapsto (y\mapsto h(y)b)$ are continuous for every fixed
additive finite test $h$, **including tests nonzero at zero**.
This is the same admissibility condition as continuity on the
finite quotient stages: Each fixed $h$ lands in one such stage,
with coordinates $h(y_c)b$. Conversely each stage assembly is the
finite sum of the fixed-cell-indicator assemblies composed with
coordinate projections. A seminorm continuous on the fixed-test
maps is continuous after this assembly: Subadditivity bounds it
by the sum of the finitely many continuous coordinate seminorms.
This proves the identification with the actual LF topology in
ordinary mathematics, not as a separate Lean isomorphism. Lean
proves that profile evaluations are continuous for its defining
seminorm topology and uses continuous Schwartz jet evaluations to
close the common kernel.

**Independent statement and interface review:** Agent `WnTMCcH`
(`closed-image-review`), transcript Yah
`01a2049a-ad23-711a-8761-d1f96d5892b8`, checked the finite stage,
compact-away decomposition, derivative conditions, and closedness
via the LF universal property. The reviewer checked the two
stage-to-fixed-test implications and the applicability of the
inherited source readings, not the manuscript pixels anew.

## Checked negative-log decay of flat real tests

[`Lemmas.RealSchwartzFlatTail`](../../Proofs/Lemmas/RealSchwartzFlatTail.lean)
checks `exists_realSchwartz_negLog_tail_bound`: For each
$b\in\mathcal S(\mathbb R,\mathbb C)$ with $b^{(j)}(0)=0$ for every
$j\in\mathbb N$, and each natural $N\ge1$, there is a single $C_N\ge0$
for both signs such that $\|b(\pm e^t)\|\le C_N e^{Nt}$ for all $t\le0$.
There is no support gap at zero. The preceding closed-image theorem
supplies exactly these jet hypotheses for each real profile of the
repaired image, including at $p=3$; it did not provide the estimate.

The reusable `exists_twoRay_pow_bound_of_vanishing_jets` needs only
$C^{n+1}$ regularity on $\mathbb R$ and vanishing jets through order $n$
for a function into any real normed space. Apply the pinned Mathlib
Taylor remainder bound on $[0,1]$ to $f(x)$ and $f(-x)$ separately.
The interval is uniquely differentiable, so the within derivatives at
zero equal the corresponding ordinary derivatives. Reflection only
multiplies the $j$-th jet at zero by $(-1)^j$. Thus both degree-$n$
Taylor polynomials are zero. Take the maximum of zero and the two
remainder constants, giving order $x^{n+1}$ on both rays. Substituting
$x=e^t\in[0,1]$ and $n=N-1$ gives the log estimate. Independent Yah
reviewer `ietJPWl` (transcript `01a204a9-beaa-7ad6-9e5b-b1e2c7292079`)
checked both statements, the Taylor reduction, and applicability to
the preceding jet and signed-log interfaces.

**Source and scope:** This is a local input to the repaired forward
claim of Lemma 5.3.4.2(2), pp. 259–261, not the printed proof or a
proof of entireness. The real jet condition comes from the inherited
rendered reading of (5.3.3.10), p. 252, and Definition 5.3.4.1,
p. 259, in the [domain audit](#the-finite-only-repair-is-not-projectively-continuous).
The [angular audit](complex-gaussian-angular.md#rendered-readings)
verifies the bilinear integrand of (3.3.1.7), p. 130, and the direction
of local restriction in §3.1.2.2, p. 121. The
[real-prime audit](trace-real-prime-q.md#source-and-domain) verifies
full real Haar $dx/|x|$ on both signs in A.3.2.2(1), p. 560, and the
usual real absolute value in (A.2.2.2), p. 546. The checked
[signed-log pushforward](single-place-norm.md#checked-signed-real-log-haar)
has $t=\log|x|$ and mass one per sign. The checked
[real restriction](hecke-right-line-majorant.md#real-archimedean-restriction-parity-and-radial-frequency)
uses that same $t$; its manuscript mapping of the real split in
(3.1.2.3), p. 121, remains provisional. No pixels were reread here.

This closed-image and tail check does not prove tensor entireness,
character descent, or anything about the completed tensor, and it does
not rehabilitate the printed finite factor or projective map.

## Checked entireness of the raw real log-Mellin pairing

[`Lemmas.RealSchwartzFlatMellin`](../../Proofs/Lemmas/RealSchwartzFlatMellin.lean)
checks the real log-coordinate input to the repaired forward direction
of Lemma 5.3.4.2(2), pp. 259–261. Let $b\in\mathcal S(\mathbb R,\mathbb C)$
with $b^{(j)}(0)=0$ for every $j\in\mathbb N$, and set
$f_\epsilon(t)=b(e^t)+(-1)^\epsilon b(-e^t)$.
The Lean statements use any $\epsilon\in\mathbb N$, so include both
parities without an extra bound on the index.

* `exists_realSchwartzParityLog_mellin_bound`: At each $z\in\mathbb C$,
  some $C_z\ge0$ bounds $\|f_\epsilon(t)e^{zt}\|$ by $C_z e^{-3|t|}$
  for all $t\in\mathbb R$.
* `hasDerivAt_realSchwartzParityLog_mellin`: The integrand and its
  product with $t$ are absolutely integrable against Lebesgue measure
  for every $z$. The first log moment is the complex derivative of
  $z\mapsto\int_{\mathbb R} f_\epsilon(t)e^{zt}\,dt$ at $z$.
* `differentiable_realSchwartzParityLog_mellin`: This raw integral is
  complex differentiable on all of $\mathbb C$.

Choose one natural $K$ with $|\Re z|+3\le(K:\mathbb R)$. The previous
negative tail bounds each ray for $t\le0$ by $A e^{Kt}$. At each
$y=\pm e^t$, the order-$(K,0)$ Schwartz seminorm $B$ bounds
$\|y\|^K\|b(y)\|$, so for $t\ge0$ each ray is bounded by $B e^{-Kt}$.
The parity coefficient has norm one, and $\|e^{zt}\|=e^{(\Re z)t}$.
Thus $2\max(A,B)$ works across both half-lines. The folded profile is
continuous, so `hasDerivAt_logMellin_of_decay` applies at $r=1$. No
support gap, a priori convergence strip, or decay premise is assumed.
Independent statement and reduction review: Yah transcript
`01a204b4-d84a-7569-a9f4-8dde8fe945d6`, agent `tycBfXz`, against
`56a97650d2239fe3b5aaff0a1a0dee08975e82e0`. The review checked the
hypotheses, signs, split estimates, differentiation interface, and
applicability of the inherited source readings.

**Manuscript scope:** Inherit the rendered jet condition, (5.3.3.10),
p. 252, and Definition 5.3.4.1, p. 259, from the
[domain audit](#the-finite-only-repair-is-not-projectively-continuous);
the raw bilinear pairing (3.3.1.7), p. 130, and restriction by insertion
in §3.1.2.2, p. 121, from the
[angular audit](complex-gaussian-angular.md#rendered-readings); and
full real Haar A.3.2.2(1), p. 560, and the usual rational real norm
(A.2.2.2), p. 546, from the
[real-prime audit](trace-real-prime-q.md#source-and-domain). The
[checked restriction](hecke-right-line-majorant.md#real-archimedean-restriction-parity-and-radial-frequency)
and [signed Haar](single-place-norm.md#checked-signed-real-log-haar)
use the same $t=\log|y|$; $z=s+i\tau$ is the raw exponent, not the
argument of a Gamma factor or a normalized pairing. The manuscript
mapping of the real split (3.1.2.3), p. 121, is provisional and is not
needed for the estimate or for using the checked coordinate identities.
No pages were reread for this proof.

## Checked raw flat Schwartz pairing on real completion units

[`Masullo.realCompletionSchwartzMellinPair`](../../Proofs/Theorems/RealCompletionSchwartzMellin.lean)
transports the real log pairing to the actual units $F_v^\times$ of
any real place of a number field, with their Borel measurable structure.
For a unitary Mathlib Hecke character $\chi$ and a complex Schwartz
profile $b$ with every jet at zero equal to zero, the statement supplies
$\epsilon\le 1$ and $\tau\in\mathbb R$ satisfying the local character
identity on all units, before quantifying over $s\in\mathbb C$. It
proves absolute integrability and the value equality
$$
\int_{F_v^\times} b(y)\,\chi(j_v(u))\,|y|^s\,d^\times u
 = \int_{\mathbb R}
  [b(e^t)+(-1)^\epsilon b(-e^t)]e^{(s+i\tau)t}\,dt.
$$
Here $y=\operatorname{extensionEmbeddingOfIsReal}(hv)(u.\mathrm{val})$.
The Lean norm is $\|u.\mathrm{val}\|^{v.\mathrm{mult}}=|y|$ by the real
isometry and `hv.mult_eq_one`. The measure is full `realCompletionHaar`,
with no restriction to the positive sign or division by two. There is
no support gap, convergence half-plane, or Gamma normalization.

At the same $z=s+i\tau$, the half-sum and half-difference of the
integrable parity-zero and parity-one integrands give integrability
of each ray. This is stronger than integrability after cancellation
between signs. `realCompletionHaar_map_logSign` pushes the measure to
Lebesgue times counting measure, with mass one on each sign. The
checked restriction and `positive_cpow_add_radial` apply at $|y|>0$ in
that same coordinate $t=\log|y|$. Fubini sums the two integrals without
a scalar. The result thus identifies the raw pairing with the
[already-entire log integral](#checked-entireness-of-the-raw-real-log-mellin-pairing)
translated by the fixed $i\tau$.

**Evidence:** Independent statement and reduction review, including
normalization and source applicability: Yah
`01a204bf-f419-7ee0-957f-3990373a8b6f`, agent `pfjAZjT`, against
`83e360130cbd779f6d5ed1ca21f0d19613b91a0d`. Inherit the rendered jet
condition (5.3.3.10), p. 252, and Definition 5.3.4.1, p. 259, from the
[domain audit](#the-finite-only-repair-is-not-projectively-continuous);
(3.3.1.7), p. 130, and insertion in §3.1.2.2, p. 121, from the
[angular audit](complex-gaussian-angular.md#rendered-readings); and
A.3.2.2(1), p. 560, from the
[real-prime audit](trace-real-prime-q.md#source-and-domain). The
provisional manuscript mapping of (3.1.2.3), p. 121, is not a premise.
No pages were reread. This supplies one local input to the repaired
forward direction of Lemma 5.3.4.2(2), pp. 259–261, not a proof on its
printed tensor domain.

## Checked compact-away finite pairing on rational completion units

[`Masullo.rationalFiniteCompactMellinPair`](../../Proofs/Theorems/RationalFiniteCompactMellin.lean)
replaces the [informal finite shell argument](finite-local-zeta-residue.md#what-is-checked-in-lean-and-what-chapter-5-can-use)
for this rational case. At any finite place $v$ of $\mathbb Q$, take a
continuous compactly supported $b:F_v^\times\to\mathbb C$, with the Borel
structure on the actual completion units, and a fixed Mathlib Hecke
character $\chi$. Lean supplies integers $L\le U$ such that the entire
topological support of $b$ is in the union of the shells from $L$ to $U$.
These bounds are chosen before $s$. For every $s\in\mathbb C$ the raw
integrand is absolutely integrable against `rationalLocalMultiplicativeHaar`,
and its integral is
$$
\sum_{k=L}^{U}\exp(-ks\log p)
  \int_{\operatorname{shell}(k)} b(u)\chi(j_v(u))\,d^\times u.
$$
Lean also proves complex differentiability on all of $\mathbb C$.
Here `χ.restrict v u.val` evaluates the actual single-place insertion
`IdeleClassGroup.ofAdicCompletion` on $u$, and $p$ is the prime of $v$.

The continuous coordinate $-\log\|u\|/\log p$ equals $k$ on shell $k$.
Its compact image on the support gives both bounds, even though the
ambient field norm tends to zero along shells with $k\to+\infty$.
The support is compact *in the units*. Continuity of the restricted
character and the norm power on units gives compact-support
integrability on Haar, without requiring unitarity. The finite disjoint
union and the log-norm identity pull out only the exponential, not the
character or the test. Locally constant tests are included by continuity;
there is no radiality, unramifiedness, or half-plane hypothesis. The
shells have mass one in the accepted normalization, but no coefficient
is replaced by a shell mass.

**Evidence and scope:** Independent statement and applicability review:
Yah `01a204cc-c59d-7f4e-b2ac-7073aab9a2d7`, agent `VtkshAk`, at
`6ad2f07c6fa0a979abf3ecd63fa4077a47c71283`. Inherit the rendered reading
of (5.3.4.1) and Lemma 5.3.4.2(2), pp. 259–261, from the
[domain audit](#scope-of-the-repair-and-use-in-lemma-5342); the pairing
(3.3.1.7), p. 130, and insertion §3.1.2.2, p. 121, from the
[real Haar handoff](#checked-raw-flat-schwartz-pairing-on-real-completion-units);
and the normalized finite norm and measure, §3.1.2.1, p. 120, and
A.3.2.2, p. 560, from the
[finite normalization audit](finite-gaussian-tamagawa.md#source-and-the-two-readings-of-l_v).
No pages were reread. Compact-away support is a repair, not the printed
finite test space. This proves local entireness, not tensor entireness,
character descent, or passage to a completion.

## Checked singleton Archimedean factor of the rational stage integral

[`Masullo.rationalArchimedeanEval_measurePreserving` and
`Masullo.rationalArchimedeanSchwartzMellinPair`](../../Proofs/Theorems/RationalArchimedeanSchwartzMellin.lean)
use the Borel structures on the actual rational completion units. Write
$w$ for the unique real place and $e(x)=x_w$. Lean proves
$$
e_*\operatorname{Measure.pi}(v\mapsto\mathrm{archimedeanCompletionHaar}(v))
  =\mathrm{realCompletionHaar}(w).
$$
This measure endpoint needs no test, character, stage, or probability
hypothesis. The target is full signed Haar, not its positive half or
half of the full measure.

For a unitary Mathlib Hecke character $\chi$ and a complex Schwartz
profile $b$ with all jets zero at zero, set the infinite test to
$b\circ\iota_w\circ e$, with $\iota_w$ the real embedding on units.
The grouped infinite density of
[`ideleFiniteStage_zetaIntegral`](hecke-right-line-majorant.md#checked-grouped-zeta-integrals-on-each-stage)
is pointwise the pullback of
$b(\iota_w(u))\chi(j_w(u))\|u\|_w^s$. Both products over infinite places
collapse to $w$: The character insertion is unchanged, and the local
norm has multiplicity one by `Rat.isReal_infinitePlace.mult_eq_one`.
The real isometry identifies that completion norm with $|\iota_w(u)|$.
For every $s\in\mathbb C$, Lean transports absolute integrability and
equality of the integral with the
[real completion pairing](#checked-raw-flat-schwartz-pairing-on-real-completion-units),
so the inherited signed-log value applies with the same fixed parity
and radial frequency. There is no scalar and no half-plane condition.

**Evidence and scope:** Independent statement and applicability review
against `2c5c54646c2d084a150179022e8454ea1b3ce6f6`: Yah
`01a204d9-06bb-77e4-a5a1-bb61f1fb154f`, agent `nIukxDJ`. The reviewer
checked the singleton measure and density reductions and the stage
interfaces. The owner separately elaborated the dependent local
applications with the actual Borel instance families. The repaired
scope and jet condition are inherited from the
[domain audit](#scope-of-the-repair-and-use-in-lemma-5342) and
[real pairing handoff](#checked-raw-flat-schwartz-pairing-on-real-completion-units):
(5.3.3.10), p. 252, and Definition 5.3.4.1 and Lemma 5.3.4.2(2),
pp. 259–261. Inherit the rendered raw density (3.2.2.1), p. 124,
from the [global sign audit](global-mellin-sign-q.md#what-the-source-prints);
the bilinear local pairing (3.3.1.7), p. 130, and insertion §3.1.2.2,
p. 121, from the [angular audit](complex-gaussian-angular.md#rendered-readings);
and the signed Haar and restricted-product normalizations in
(A.3.2.2) and (A.3.2.5), p. 560, from the
[real prime audit](trace-real-prime-q.md#source-and-domain) and
[relative 1-line audit](idele-relative-one-line-q.md#source-checked-on-rendered-pages).
No pages were reread. The manuscript mapping of the grouped factor
to (3.4.1.2), p. 143, remains provisional and is not a Lean premise.
This is a check on the compact-away repair, not on the printed finite
test space or its completion.

**Previous check:** A scratch probe on the then-accepted source supplied
stage integrability using these local inputs and off-stage unit masses.
It neither landed a stage theorem nor checked differentiation. The
following endpoint supersedes that probe.

## Checked entire pairing on the exact rational idele stage

[`Masullo.rationalIdeleFiniteStage_schwartzMellin`](../../Proofs/Theorems/RationalIdeleFiniteStageSchwartzMellin.lean)
uses the actual rational idele group with the indicated Borel
structures. Let $S$ be the finite set of test exceptions, $U_S$ the
range of `ideleFiniteStageEmbedding ℚ S`, and $\mu$ a measure with
exact comap `ideleFiniteStageProduct ℚ μa μf S`. Here $\mu_a$ is the
family `archimedeanCompletionHaar` and $\mu_f$ is the family
`rationalLocalMultiplicativeHaar`. Fix a unitary Hecke character $\chi$
unramified outside $S$, a complex real Schwartz profile $b$ with
all jets zero at zero, and continuous compactly supported $f_v$ on
$F_v^\times$ for $v\in S$. No assumption on $f_v$ off $S$ is needed:
`ideleZetaTest` uses the integer-ring indicator there. On $U_S$ the
inactive coordinates already lie in the integer-unit groups.

Write $g_s$ for `ideleZetaTest` times $\chi$ evaluated on the idele
class times the idelic norm to $s$. For every $s\in\mathbb C$, Lean
proves `IntegrableOn` for $g_s$ on $U_S$ and the identity

$$
 T_S(s)=\int_{U_S} g_s\,d\mu=R(s)\prod_{v\in S}L_v(s).
$$

Here $R$ is the full signed real completion integral, and $L_v$ is the
raw finite integral of $f_v(u)\chi(j_v(u))\|u\|_v^s$ on the full
completion units against $\mu_f(v)$. Neither is divided by a Gamma or
Euler factor. There is no scalar. Lean proves `Differentiable ℂ T_S`,
with no restriction on $s$ and no nonvanishing hypothesis. The finite
product includes the case $S=\varnothing$ with the empty product one.

**Reduction checked in Lean:** At `E = S`, the active `ideleFiniteTest`
is exactly $f_v$. `rationalFiniteCompactMellinPair` handles its integral
and complex differentiability. `rationalArchimedeanSchwartzMellinPair`
identifies the grouped infinite integral and supplies its integrability.
The off-stage mass required by `ideleFiniteStage_zetaIntegral` is
supplied directly by `rationalLocalMultiplicativeHaar_unitMass` in the
actual Borel instance families; no bridge or extra mass assumption is
needed. The real pairing is the checked signed-log integral with
profile $b(e^t)+(-1)^\epsilon b(-e^t)$ evaluated at $s+i\tau$ for
one fixed $\epsilon,\tau$ for the character. Translation and the finite
product rule give entireness without differentiating under the upstairs
integral.

**Evidence and scope:** Independent exact-source statement and reduction
review against `3b8584b048a2c6a5fa82a87612add28a89e02e02`: Yah
`01a204e7-042d-7c33-aeda-4beeb570780b`, agent `wUandyg`. The reviewer
checked the actual stage, density, local interfaces, and applicability
of the inherited source readings, and flagged the equality of the
unit-mass inclusions as an elaboration question. The owner resolved
that question by applying the theorem with the direct argument above
in the matching Borel context, not by changing its hypothesis.

This is a forward step for the compact-away **repair** of Lemma
5.3.4.2(2), pp. 259–261, not the printed finite test space. Inherit the
rendered readings of the lemma and flatness (5.3.3.10), p. 252, the
raw density (3.2.2.1), p. 124, the local pairing (3.3.1.7), p. 130, and
insertion §3.1.2.2, p. 121, and the signed and product Haar conventions
(A.3.2.2), (A.3.2.5), p. 560, through the
[singleton real handoff](#checked-singleton-archimedean-factor-of-the-rational-stage-integral).
The [finite normalization audit](finite-gaussian-tamagawa.md#source-and-the-two-readings-of-l_v)
verifies the finite norm (§3.1.2.1, p. 120), the unit condition (after
(3.1.2.6), p. 121), and the product norm (A.1.3.3), p. 541. No pages
were reread. The provisional manuscript mapping of the grouped
factor to (3.4.1.2), p. 143, is not a premise.

**Successor:** The comparison to the global integral on the same measure
is checked below.

## Checked stage-to-global pairing above one

[`Masullo.rationalIdeleZetaIntegral_schwartzMellin`](../../Proofs/Theorems/RationalIdeleZetaIntegralSchwartzMellin.lean)
uses the **same** rational tensor, unitary character unramified off $S$,
and Borel structures as the exact-stage theorem. The real Schwartz
profile has all jets zero at zero; the finite profiles are continuous
and compactly supported on the full local multiplicative groups for
$v\in S$. No regularity is assumed of the supplied profiles off $S$.
Let $\mu$ be one upstairs measure whose comap on **every** stage
$U\supseteq S$ is `ideleFiniteStageProduct ℚ μa μf U` for the same
actual local Haar families as above. For $\Re s>1$, Lean proves that
$g_s$ is absolutely integrable upstairs and that

$$
\int g_s\,d\mu = T_S(s)\operatorname{finiteHeckeEulerProduct}(z,s),
\qquad z_v = \begin{cases}0 & v\in S, \\
\operatorname{finiteHeckeCoefficient}(\chi)_v & v\notin S.\end{cases}
$$

Here $T_S$ is the **integral of $g_s$ over the range of the exact stage
embedding**, against the same $\mu$. There is no scalar, additional Haar
hypothesis on $\mu$, or nonvanishing premise on the retained factors.
The theorem includes $S=\varnothing$. Existence with the required
comaps follows from the [general restricted-product Haar construction](hecke-right-line-majorant.md#checked-restricted-product-haar-for-number-fields)
and rational unit masses; the theorem itself takes the comaps as a
hypothesis and does not name the calibrated `rationalIdeleHaar`.

**Checked reduction:** Apply `ideleZetaIntegral_rightHalfPlane` at
`E = T = S`. `rationalLocalMultiplicativeHaar_unitMass` and the actual
local Haar instances supply the measure premises.
`rationalArchimedeanSchwartzMellinPair` supplies grouped integrability
and the signed real value. On $S$, `ideleFiniteTest` is the supplied
profile, so `rationalFiniteCompactMellinPair` supplies integrability.
`Finset.prod_coe_sort` aligns the active product with the stage theorem,
which evaluates $T_S$ using precisely these raw local factors. This is
a product comparison, not a support reduction: Off $S$ the global test
requires integral values, whereas the stage requires integral values
and inverses. In particular the upstream omitted integrals run over
the full completion units with the ball indicator, not over just the
integral-unit subgroup.

**Manuscript scope:** Inherit the rendered readings of Lemma
5.3.4.2(2), pp. 259–261, the density (3.2.2.1), p. 124, and the local
and product Haar conventions (A.3.2.2), (A.3.2.5), p. 560, via the
[singleton real handoff](#checked-singleton-archimedean-factor-of-the-rational-stage-integral).
Inherit the finite norm and unit condition, pp. 120–121, and product
norm (A.1.3.3), p. 541, from the
[finite normalization audit](finite-gaussian-tamagawa.md#source-and-the-two-readings-of-l_v).
The [admissible-set audit](weil-admissible-set.md#source-and-admissibility)
verifies that (3.4.1.6), p. 143, excludes $S_0$, not the actual stage
set. The theorem checks the compact-away **repair** with the tail off
$S$, not that printed formula, continuation of the upstairs Lebesgue
integral, tensor assembly, descent to the manuscript test quotient, or
extension to the completed test space. No pages were reread. The
provisional mapping to (3.4.1.2), p. 143, is not a premise.

**Evidence:** Independent statement and interface review against
`6f1d672bc14e2f53d6fc17f45019bf1b61e64e8b`: Yah
`01a204f0-cbfc-7476-bcfc-a7055bca25e0`, agent `PKAAzTC`. The reviewer
checked the proposed binders, accepted dependencies, and inherited
readings' applicability, and built and inspected the dependency
signatures. The owner elaborated their applications in the actual Borel
context and aligned the products in the new theorem, not in the old
stage theorem. The owning candidate build, signature, axiom check, and
adoption are recorded in the same Yah session.

**Measure premise discharged:** The [generic-coordinate comparison below](#checked-generic-stage-comap-for-the-named-rational-haar) supplies the required comaps for `rationalIdeleHaar`.

## Checked generic stage comap for the named rational Haar

[`Masullo.comap_rationalIdeleHaar_ideleFiniteStage`](../../Proofs/Theorems/RationalIdeleRestrictedProductHaar.lean)
proves, for **every** finite set $U$ of rational finite places, including
$\varnothing$,

```
rationalIdeleHaar.comap (ideleFiniteStageEmbedding ℚ U) =
  ideleFiniteStageProduct ℚ μa μf U
```

The families are `archimedeanCompletionHaar` and
`rationalLocalMultiplicativeHaar` in the same local and upstairs Borel
structures as the preceding zeta theorem. There is no sign, scale, or
cofinality hypothesis on $U$. This is the **generic** stage embedding,
not the rational-specific embedding with an explicit $\mathbb R^\times$
factor. Joint import checks the direct application to the hypothesis of
`rationalIdeleZetaIntegral_schwartzMellin` with the named upstairs measure,
for arbitrary $S$ and at $S=\varnothing$.

**Discriminating check:** Let $B$ be the preimage of $[1,e]$ under the
sole signed real coordinate on the grouped Archimedean units. The
coordinate is an open embedding with image containing $[1,e]$, so $B$
is compact with nonempty interior. The upstairs carrier of
`ideleCalibrationBox ℚ B` is `ideleUnitRectangle ℚ B`: It requires
integrality at every finite place for the idele and its inverse, just
as `rationalIdeleWindowUnitStrip` does. In the box direction the
interval gives positivity; in the reverse direction the window already
requires positivity. On these finite units,
`ideleNorm_eq_abs_rationalIdeleReal` therefore identifies the norm with
the signed real value, proving equality of the two carriers.

The Archimedean box mass is one by measure-preserving evaluation at
the singleton place and the real completion pushforward of $dt/|t|$,
compared to `realMultiplicativeHaar_unitStrip`. The
restricted-product construction with empty exceptional set uses the
unit mass at every finite place and gives the same box upstairs mass
one. `rationalIdeleHaar_unitStrip` and Haar uniqueness on the common
positive compact strip identify the two upstairs measures. The
positive strip fixes the scalar only; the comap retains both signs.

**Source and scope:** Inherit the rendered readings of (A.3.2.2) and
(A.3.2.5), p. 560, via the
[singleton real handoff](#checked-singleton-archimedean-factor-of-the-rational-stage-integral).
The p. 556 stage prescription and the §A.3.3.1, p. 561, strip mapping
remain [layout readings](theta-inversion-q.md#checked-finite-stage-product-of-local-haar-measures),
not Lean premises. No pages were reread. This closes the measure premise
for the compact-away repair of Lemma 5.3.4.2(2), pp. 259–261, above one;
it does not check the printed identity, upstairs continuation, test
quotient descent, or completed tensor space.

**Evidence:** Independent exact-source statement and reduction review
against `0914c44c01168b68a96cf877d2a09fdfb0c4ebec`: Yah
`01a204fc-7fb8-7209-b88b-9ecd5eadc4c5`, agent `RyLXPwH`. The reviewer
checked applicability of the inherited readings, both carrier
inclusions, the normalizations, and compatibility with the zeta
hypothesis; elaboration was checked by the owner. The integrated
warnings-as-errors build, fresh joint import, signature, axiom report,
and adoption are recorded in the same owning Yah session.
