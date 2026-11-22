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
inclusion, not a counterexample to repaired entireness.

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

**Next bounded check:** Over $\mathbb Q$, identify the grouped
Archimedean density and its integral in `ideleFiniteStage_zetaIntegral`
with the actual single-real-place flat-Schwartz pairing. Its measure
is `Measure.pi μa` on the product of completion units; use the singleton
infinite-place evaluation with $\mu_a(v)$ equal to `realCompletionHaar`
at the unique real place. The grouping has a product of the same
local character evaluations and a norm with real multiplicity one.
Check the evaluation pushforward and the density transport, with no
extra scalar. This supplies the real integrability premise for one
repaired pure tensor on a stage with all its finite exceptions and
ramification active. Taking the exception set equal to the stage
makes each active finite input exactly the compact-away endpoint
above. The [stage Fubini formula](hecke-right-line-majorant.md#checked-grouped-zeta-integrals-on-each-stage)
is already checked, with an exact stage comap hypothesis. A global
upstairs support reduction, algebraic tensor assembly, and the
completion and character-descent questions are separate.

For this bridge, the [real Haar handoff](#checked-raw-flat-schwartz-pairing-on-real-completion-units)
records the inherited source for jets, insertion, and mass on both
signs. The [global sign audit](global-mellin-sign-q.md#what-the-source-prints)
verifies the raw bilinear density in (3.2.2.1), p. 124; the
[relative 1-line audit](idele-relative-one-line-q.md#source-checked-on-rendered-pages)
verifies the rational local normalization and restricted product
in (A.3.2.2) and (A.3.2.5), p. 560. The grouped-factor mapping of
(3.4.1.2), p. 143, in the stage note is provisional and is not a
premise of the singleton evaluation check.

