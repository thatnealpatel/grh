# Localizing an orbital kernel before taking its trace

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.3,
printed p. 27, from “Observe that the orbital kernels” through
“using the Shell Structure” and footnote 5. Masullo says only loci
inside $(\mathrm{GL}_1(\mathbf A_{F,S'})\times U^{S'})\times
\mathrm{GL}_1(\mathbf A_F)$ need be sampled for the orbital trace
contributions, for $S'$ large enough. Here
$U^{S'}=\prod_{v\notin S'}\mathcal O_v^\times$. The proposed next
step is to compute the action on $S'$-local theta functions. The
paragraph gives no localization criterion or action calculation;
footnote 5 reads “Finish!” Section 1.3.4 is a separate passage.
Chapter Markdown and PDF layout extraction located the text.
Raster OCR checked the prose and footnote, and inspection of the
rendered formula pixels checked the grouping and the $S'$ indices
in the [digest-verified edition](../sources/masullo/README.md).

**Uniform localization is an extra step.** For the coordinate
strata, a shell specifies unit membership at previously tested
places and its failure somewhere in the new fiber. It places no
unit condition at later primes. For example, over $\mathbb Q$
take the first shell at $2$ and the norm section $\tau(t)$ with
finite components one. The second input on the principal skewer
$(\tau(t),2\ell\tau(t))$ is in that shell whenever $\ell>2$ is a
prime, but it is nonunit at $\ell$. The diagonal rational $2\ell$
is itself a uniformizer at $2$. No one finite $S'$ contains the
nonunit places of all these candidate inputs. This example tests
the inference from the shell and the uniformizer condition, not
the nonzero support of Masullo's actual lifted kernel.

The opening proof paragraph of Theorem 11.3.2.1, p. 495, asserts
vanishing unless the principal multiplier is a uniformizer at a
new place, then asserts that the resulting locus is contained in
the $S'$-local product. Rendered-crop OCR checked these phrases;
Chapter Markdown and layout extraction supplied the symbols. The
stated theorem assumes $s>1$, not the introductory $s=0$. The
[fixed-shell audit](../obligations/trace-orbital-q.md#the-right-cutoff-erases-a-fixed-shell-in-the-literal-chain)
also shows that the subsequent same-chain right multiplier in
(11.3.2.3) kills the fixed signed shell. It cannot approximate an
outside-$S'$ unit mask on that shell by the suggested reasoning.

**Missing trace and action comparisons.** For the actual lift and
averaging used in the introductory trace, let $A_k(x,\xi)$ be the
smoothened signed shell value at $(x,\xi x)$. To discard the
outside-$S'$ part, show that its skewered Haar integral is zero,
for example by proving that the contributing second inputs are
units outside a common finite $S'$ for almost every $x$. A bound
on $\int_D\sum_\xi|A_k(x,\xi)|\,d\mu(x)$ would justify convergence
of the integrals as $S'$ exhausts the finite places and the
outside-unit masks increase to one. It would not imply exactness
at a finite $S'$. The [conditional diagonal split](skewered-mass-piece-sum.md)
explains the distinction. One still needs to identify the Haar
integral action of the localized signed shell with the operator
on the proposed $S'$-local theta or Paley–Wiener level, including
its lifts or quotient compatibility, and justify passage to the
same averaged diagonal after removing cutoffs. Convergence of
ordinary theta tests alone does not identify this operator.

The localization and computation program are Masullo's. The
uniformizer example is the rational witness from the fixed-shell
audit applied to the localization inference. The distinction
between convergence under an integrable bound and exact localization
is the reviewer's application of the conditional split. The printed
preview remains open; no Lean declaration is claimed for it.
