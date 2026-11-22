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

**Next bounded check:** In the same $(\mathbb Q,\{\infty,3\})$ model,
test whether the repaired canonical map with the printed projective
tensor topology is continuous into the additive LF space of (2.1.4.1).
Use disjoint shells $3^{-n}\mathbb Z_3^\times$ and an LF seminorm
that measures increasing real derivative orders on their sampled
slices. Only finitely many samples occur in any fixed additive stage.
Apply the joint-continuity criterion in (C.2.3.14), p. 679. This would
decide whether replacing the finite factor alone suffices for the
claimed topological inclusion, separately from entireness and descent.
