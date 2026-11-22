# The product arrow in the introductory orbital sequence

**Printed passage.** Masullo, *The Music of the Primes*, §1.2.11,
printed p. 20, from “Now take S saturated” through “both linearly and
topologically.” Saturation means including every place above a rational
prime once any one is included. The top row of the diagram goes from
the polar-free theta isotype to the full S-local theta isotype, then to
the Archimedean orbital quotient times the primed product of the
$p$-primary quotients. Masullo claims exactness both linearly and
topologically **on the left and in the middle**. No right-hand
surjectivity is asserted. The displayed top arrows have no formulas.
The saturation wording, spaces, arrows, and exactness qualification
were spot-checked directly in rendered pixels of PDF p. 20, separately
from the chapter Markdown and PDF text extraction. The PDF matches the
[pinned SHA-256](../sources/masullo/README.md)
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The stack-support rows and their interpretation are separate passages.

**The left arrow.** Write $H$ for the full isotype and $D$ for the
projected image of the all-place polar-free tests. The inclusion must
first be defined on those tests and then be a topological embedding
with closed image in the intrinsic topology of $H$. The accepted
[finite-factor audit](../obligations/finite-polar-free-domain.md)
finds that the larger multiplicative Schwartz space denoted
$\mathcal S(F_v^\times)$ in the cited setup does not in general include
into the additive test space by zero extension. Below, use the
compact-away finite test factors as an explicit repair, not as a
verification of the printed definition. Proposition 5.3.4.4,
pp. 263–264, identifies polar-free representatives by an entire
Mellin transform on the chosen isotype. Proposition 5.4.1.4 and
Theorem 5.4.1.1 compare the left and middle spaces with a common
Mellin-pair model. Those claims, in a common well-defined topology,
would give the intended strict inclusion. They do not identify the
kernel of the product arrow.

**A check on the natural componentwise interpretation.** For the
finite coordinates take the quotient maps $H\to H/P_\ell H$ of
(7.3.1.5), where $P_\ell$ is the principal-value product above
$\ell$. For the Archimedean coordinate one could take the introductory
quotient by the Archimedean-flat image, or, using (7.3.4.3), follow
the full finite-place product $P$ by the projection $PH\to PH/D$.
Neither reading of these component maps recovers $D$ as the joint
kernel. Here is a test of that interpretation, not a specification
of Masullo's unlabelled arrow.

Take $F=\mathbb Q$, $S=\{\infty,p,q\}$ for distinct primes $p,q$, and
the trivial norm-one isotype. Normalize finite unit masses to one,
and put $E_\ell(s)=1-\ell^{-s}$. The finite unit ball has Mellin
transform $1/E_\ell$, and on these unit-invariant tests $P_\ell$
is the uniformizer difference, with Mellin multiplier $E_\ell$.
Choose a smooth compactly supported log-norm bump with Mellin
transform $B(s)$ and $B(0)\ne0$. Convolution on the log line with
the indicator of $[-\log\ell,0]$ gives a smooth compactly supported
log-norm test with transform $B(s)E_\ell(s)/s$. Pull it back to
$\mathbb R^\times$ by the log absolute value and normalize by the
real unit mass. It extends to a flat real Schwartz test $a_\ell$.

Apply $P_p$ to the theta class of $a_q\otimes 1_{\mathbb Z_p}\otimes
1_{\mathbb Z_q}$, and $P_q$ to the analogous class using $a_p$.
Both have Mellin transform $B(s)/s$ on the trivial component, so
Lemma 5.1.2.2(2), p. 225, identifies them as one class $h$. It is in
both $P_pH$ and $P_qH$. The displayed representative for $h$ is
Archimedean-flat, and $Ph$ also has compact-away factors at both
finite places. Thus either proposed Archimedean coordinate kills
$h$. But $h\notin D$, since $B(s)/s$ has a pole and tests in the
repaired polar-free space give entire Mellin transforms. Dividing
out the two prime ranges separately can therefore lose information
at their common zero $s=0$, even though $S$ is saturated and no
ramified factors are involved.

**Disposition.** Chapter 8 repeats the row in (8.4.0.6), p. 390,
and cites Propositions 5.3.4.4 and 5.3.4.5 for exactness. The cited
entire-transform criterion and finite-pole removal do not specify a
joint residual map that accounts for the pole orders at coincident
points. The precise missing argument is to define that map into the
stated targets, show its kernel is exactly the polar-free image,
and identify the quotient topology with the induced topology on
its actual image. The later Chapter 5, 7, and 8 readings used here
are provisional, from chapter Markdown. The exactness assertion is
Masullo's; the componentwise test is the reviewer's. The printed
claim remains open, and no Lean declaration is used.
