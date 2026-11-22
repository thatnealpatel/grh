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

**Next bounded check:** In this same local model, test whether the
image of $E\otimes_\iota H$ is exactly the common kernel in $D$ of
$\Phi(x,0)$ for every $x$ and $\partial_x^j\Phi(0,y)$ for every $j\ge0$
and $y$. Use the finite quotient stage containing $\Phi$ to turn this
into coordinate conditions, including vanishing on the zero coset.
This would decide closedness of the repaired image independently of
projective completeness. Archimedean forward entireness, passage to a
completed repaired tensor, and character descent are separate.
