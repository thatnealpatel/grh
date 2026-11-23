# Both trace evaluations at the same positive width

**Status: Open.** Masullo, *The Music of the Primes*, printed p. 32,
§1.4.9, preview from “This can all be done within” through “too.”
This paragraph follows the proposed reduction to a Connes-style local
calculation and ends before §1.4.10. Masullo says that the preceding
calculation can be done within $W_{[-a,a]}^{s,2}(C_F)$ for any fixed real
$a>0$, and that the spectral side can be computed in that same space.
Here $a$ is the strip half-width, not the later half-norm twist. The
paragraph fixes neither a new degree range nor a new test class. It
does not assert uniform convergence as $a\downarrow0$, or cover $a=0$.

Chapter Markdown and PDF layout extraction located the paragraph.
Raster OCR checked the prose, and direct inspection of rendered crops
from the [digest-verified PDF](../sources/masullo/README.md) checked
both strip expressions and $a>0$. Rendered crops also checked the
later degree conditions cited below. The proof comparisons use the
chapter transcriptions and the linked audits.

**Missing comparison.** Even at the introductory degree $s=0$, with
twist $1/2$, one norm-one isotype, and a Bruhat test supported strictly
above norm one, fix the requested positive width. At that width one
must construct the actual geometric cutoff kernel, justify integration
and removal of the cutoffs on the signed shell split, and identify
its averaged Haar diagonal with the normalized local limit (including
the polar Mellin subtractions in the trivial isotype). Then identify
that *same* diagonal with the negative of the spectral cutoff trace
limit for convolution after the actual orthogonal spectral projection.
The quotient trace must have full interior zero orders and justified
boundary weights, including when a shifted zero lies on an edge.
Varying the width in a scalar local expression does not supply these
operator identifications, and working only at widths without edge
zeros does not prove the statement at every fixed positive width.

Definition 10.4.3.7, p. 473, requires $s\ge3$. Theorem 11.3.2.1, p. 495,
allows an arbitrary width parameter but requires $s>1$; it does not
extend the [orbital cutoff comparison](orbital-cutoff-trace-limit.md)
to degree zero. Theorem 10.4.2.8, p. 463, prints $s\ge0$, but cites
Theorem 10.3.2.1, p. 453, with $s>1$ for the quotient trace. Even a
valid local asymptotic, without the [residual comparison](local-residual-diagonal-comparison.md),
would not compute the trace of this operator. The [reading of p. 520](../obligations/trace-assembly.json)
checks how Masullo combines the two values, not that both have been
obtained at the claimed degree and width. The construction and trace
argument are Masullo's; the scope comparison is the reviewer's. No
Lean declaration is invoked for this same-space claim.
