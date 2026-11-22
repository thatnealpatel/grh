# Cutting the lifted geometric kernel and expanding the shell operator

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.2,
printed p. 27, the first bullet after “The idea is the following.”
Masullo proposes multiplying the lifted geometric kernel by successive
indicator differences. He prints
$(\alpha_{k+1}-\alpha_k)K_{\mathrm{geom},I,\varphi}$, names it
$k_{S_{p_k},\varphi}(x,y)$, and proposes writing it as a limit of finite
rank kernels by acting on Schauder basis elements. The adjacent trace
and remnant bullets are separate passages. Chapter Markdown and layout
extraction located the text. OCR of the rendered crop checked the prose,
and direct inspection of the formula and name in the rendered pixels
checked the sign and indices, using the [digest-verified edition](../sources/masullo/README.md).

**What the cut specifies.** The display suppresses the argument of
$\alpha_k$. The second named variable $y$ is meant, following Masullo's
explanation on p. 24 immediately after (1.3.1.12). For the explicit
coordinate unit loci $D_k$ of p. 26, the [successive-difference check](primary-divisorial-successive-difference.md)
gives $\alpha_{k+1}-\alpha_k=-1_{D_k\setminus D_{k+1}}$. This cuts a
chosen idèle kernel, with a minus sign. On the first-primes indexing
of p. 26 the newly tested fiber is over $p_{k+1}$, even though the
term's name uses $p_k$. Neither observation identifies an operator on
an orbital quotient. In particular, the mask can distinguish principal
translates of the same idèle class. The earlier [theta cut audit](primary-divisorial-theta-range.md)
also rules out an unrestricted coordinate-cut-to-PV rule on theta
representatives, but does not rule out every transport of the actual
lifted kernel using a prescribed section.

**Missing comparison.** One needs the integral action of the actual
signed $y$-cut, with a specified lift, Haar input measure, and any
level and position cutoffs, on the space on which the basis is used.
For an action on the successive quotient, changing a representative
by the next principal-value range must not change the resulting
class. With a specified system of lifts instead, one still needs to
identify its reconstructed operator with the one given by the cut
kernel. For a continuous operator $T$ already identified on a space
with a Schauder basis, composing with the partial-sum maps gives
pointwise convergence of finite-rank operators. That does not identify
$T$ or supply a limit of kernel representatives in a topology that
controls the later smoothed diagonal. A trace-class estimate for the
identified endomorphism and comparison with the regularized Haar
diagonal would be one route to the latter use.

**Later route and its scope.** Equation (11.3.1.4), p. 494, repeats the
cut and says the basis lifts are taken with Paley–Wiener restrictions
and the half-norm twist. The proof of Theorem 11.3.2.1, pp. 495–496,
asserts that its cutoff operator is the limit of the series in
(11.2.2.12), using the method of Theorem 10.3.2.1. These readings are
from extraction and chapter Markdown; they are provisional here. The
latter application needs a comparison on the same spaces: The theorem
on p. 495 assumes $s>1$, whereas (11.2.2.12) is presented for an
untwisted singleton-base quotient with $s\ge2[F:\mathbf Q]$. Neither
supplies the introductory $s=0$ comparison as printed. Moreover, the
accepted [fixed-shell audit](../obligations/trace-orbital-q.md#the-right-cutoff-erases-a-fixed-shell-in-the-literal-chain)
independently inspected the Chapter 11 mask displays in rendered pages.
At the common source variable, the additional literal mask
$\alpha_{k_1}$ in (11.3.2.3) annihilates the fixed signed shell once
$k_1\ge k+1$. The outside-$S'$ mask in (11.3.2.4) does not have that
property. This is an obstruction to the stated cutoff comparison,
not a refutation of the existence of an expansion for the kernel in
the first bullet. An exhaustion based outside $S'$ would be a change
of masks and would still need an operator comparison and limit proof.

**Disposition.** The cut construction and the proposed basis method
are Masullo's. The signed-mask reading and the separation between a
pointwise operator expansion and kernel or diagonal convergence are
the reviewer's. The basis construction on the relevant levels and
identification and convergence of the finite-rank kernels remain open.
No Lean declaration is claimed for this passage.
