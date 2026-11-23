# Polar multiplicities and the geometric coefficient functionals

**Printed passage.** Masullo, *The Music of the Primes*, §1.7.1,
printed p. 35, fourth bullet, paragraph beginning “This Theorem has
nothing to do with the zeros of the Hecke L-function” and ending
“the paper.” Masullo says the results around Theorem 1.7.1.1 help
choose normed topologies, for example Sobolev degree at least
$2[F:\mathbf Q]$, to make the coefficient functionals of orbital
Schauder bases continuous for the trace calculation. The claim
concerns poles of local Euler factors, not zeros of the Hecke
$L$-function. It is a preview of a use, not a statement specifying
a normed quotient or an operator. The separate sentence on function
fields is not covered. Chapter Markdown and layout extraction located
the paragraph. OCR checked the rendered text, and direct inspection
of rendered pixel crops spot-checked the distinction from Hecke zeros,
the degree bound, the Schauder wording, and the next sentence, using
the [digest-verified edition](../sources/masullo/README.md).

**What the degree bound gives.** Fix one rational prime $p$ and a
unitary character. Each unramified place above $p$ supplies a simple
pole of its local factor at a zero of its reciprocal, on the zero
line. Ramified factors are one. The pole order $N$ of the product
above $p$ at any one point is at most the number of places above $p$,
hence at most $[F:\mathbf Q]$. This does not use prime-logarithm
independence: The relevant residue-size logarithms are integer
multiples of $\log p$. The [separation result for distinct residue
characteristics](finite-local-polar-multiplicities.md) is pairwise;
it does not bound a product over many rational primes by
$[F:\mathbf Q]$. For the trivial character, all finite factors have
a pole at zero.

At the zero line and degree $s\ge 2[F:\mathbf Q]$, all Mellin jets
of orders $0\le m<N$ pass the ambient boundedness test $2m+1<s$.
The accepted Lean `Masullo.boundaryLogJet_exists_smooth_extension_iff`
(`Proofs/Props/BoundaryLogJet.lean`, revision
`231909b11e1ee1f770dc248731645774dd5d3fbb`) assumes $s\ge0$ and
$|\Re z|=\alpha$, including $\alpha=0$. It characterizes extension
of the jet on weighted smooth compact log profiles to an ambient
continuous linear functional in the $L^2(dx)$ coordinate. It does
not identify a Hecke multiplicity, a coefficient on an orbital
subquotient, a basis, or a trace. The same ambient test does not
impose this degree bound for jets at interior points of a strip.

**What the trace still needs.** Theorem 11.2.0.2 (pp. 485–486),
Theorem 11.2.2.1 (pp. 490–491), and Remark 11.2.2.2 (p. 491) are
later interfaces for this claim. Their locators and statements here
are provisional readings from extraction. For the single-prime
zero-line step, identify the required coefficient functionals with
these jets, check the action of the actual principal-value product
by the matching Mellin multiplier on the completed isotype, and
show that the jets annihilate its range and separate the intended
Hausdorff quotient. Boundedness and annihilation pass to the closure;
identification of a joint kernel of continuous jets does not prove
that the actual operator range is already closed. The accepted
[one-prime rational audit](../obligations/trace-orbital-q.md#which-quotient-is-closed)
gives an ordinary countercheck in the trivial radial isotype: On
polynomially weighted $L^2$ the extended difference is injective but
not bounded below, so its range is not closed even at the indicated
degree. Replacing the range by its closure repairs that issue in
this example, not the printed quotient in general.

Even with continuous and separating coefficients, a Markushevich
system does not give Schauder convergence in the topology of the
shell action. One needs estimates for the biorthogonal vectors and
trace-norm summability of (11.2.2.12), and a comparison transporting
that expansion to the actual signed, half-norm-twisted Paley–Wiener
shell operators used in the geometric diagonal. The untwisted
zero-line estimate with $s\ge 2[F:\mathbf Q]$ does not supply that
comparison at positive width and introductory degree zero. A
comparison combining different primes must either keep the primary
contributions separate or control extra orders at shared poles.
See the [cutoff trace audit](orbital-cutoff-trace-limit.md).

**Disposition: Open.** The proposed use of the coefficients and the
trace construction are Masullo's. The single-prime count, application
of the ambient jet threshold, and distinctions between the actual
range, its closure, a basis expansion, and a cutoff trace comparison
are the reviewer's scope analysis, using the accepted results and
audits above. No Lean declaration establishes or refutes the printed
trace-topology claim.
