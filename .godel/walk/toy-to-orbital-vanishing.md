# The toy calculation previews, but does not prove, orbital vanishing

**Printed passage.** Masullo, *The Music of the Primes*, §1.2.8,
printed p. 17, claim beginning “This vanishing illustrates the origin
of the vanishing of”, including its display and the closing phrase
“for all but finitely many prime numbers p.” The display says that
$\int_{C_F} k_{p,\varphi}(x,x)\,d\bar\mu(x)=0$ for those rational
primes. This is a preview about the adelic orbital kernels of §1.2.2,
printed p. 15, not another assertion about the smooth circle. The
paragraph and display were checked in a rendered pixel crop of PDF
page 17, separately from chapter Markdown, text extraction, and OCR.
The PDF ordinal agrees with the printed page; the verified SHA-256 is
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.

**What the analogy checks.** In the introductory setup of §1.2.1–2
(pp. 13–15), fix a norm-one isotype, twist $1/2$, base $I=[-a,a]$ with
$a>0$, degree $s=0$, and a compactly supported test $\varphi$ strictly
above norm one. If the norms on the support lie in $(1,B]$, then for
$p>B$ and every $v\mid p$ the residue norm satisfies $q_v\ge p>B$.
The norms of the single-place uniformizer powers are $q_v^{-m}$,
$m\in\mathbb Z$, and none lies in $(1,B]$. Thus all the proposed
local lattice samples vanish, including if one integrates the test
against the character over the norm-one fibres at those norms. The
half twist does not change the support. This is the reviewer's check
of the support argument previewed by Masullo and developed in §11.3.1
(pp. 494–495), conditional as a computation of the orbital integral.

The [finite-place support audit](../obligations/finite-place-support.md)
records the distinct project lemma
`Masullo.exists_finitePlaceRestriction_eq_zero_of_hasCompactSupport`.
Its signature at `55ca1bff1a728a317b177b4575150dc55417431b` assumes
compact support and vanishing on the norm-one subgroup and concludes
vanishing of the entire single-place restriction outside a finite
set of places. It does not state an identity or vanishing for the
averaged diagonal of an orbital kernel. The preceding
[toy vanishing passage](toy-trace-support-vanishing.md) likewise
checks scalar samples, not the adelic comparison.

**Open step.** For each rational prime outside a sufficiently large
finite set, identify the Haar integral of the averaged diagonal of
that same shell kernel on $C_F$ with the applicable periodic sampling
expression, accounting for all places over the prime. In Masullo's
route this requires identifying the actual lifted shell with the
orbital quotient trace and justifying cutoff removal and passage to
the averaged diagonal at the introductory degree $s=0$. Theorem
11.3.2.1 (printed pp. 495–496) concerns an indented Paley–Wiener-level
calculation at $s>1$; its displayed (11.3.2.1) has a single-place
right side, whereas (11.3.2.5) uses the zero sum for the product over
places above $p$. Neither the toy trace nor a vanishing scalar sum
supplies the identification at the introductory scope. These later
source comparisons use the chapter Markdown and PDF text extraction,
not rendered pages, and are provisional. No new Lean claim is made.
