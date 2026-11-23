# Shifted Mellin jets and the strip restriction

**Status: Open for the spectral inference.** Masullo, *The Music of the
Primes*, printed p. 31, §1.4.8, claim from “The spectral side takes the
form as above” through the parenthesis ending “for $s>0$).” This is the
reason given for the preceding [degree-zero sum](degree-zero-narrow-strip-spectral-trace.md)
and [positive-degree edge terms](positive-degree-edge-spectral-trace.md).
It says that evaluation at $z=\rho-1/2$ and its distributional derivatives,
continuous on $\mathcal S_{\mathrm E}(C_F)$, cannot extend continuously to
$W_I^{s,2}(C_F)$ unless $z\in\mathbf C_{[-a,a]}$. It gives the **same
closed-strip subscript** in the degree-zero display and the positive-degree
parenthesis. “Unless” is a necessary condition, not an assertion that
all these jets extend at every point of the closed strip. There is no
order-dependent boundary criterion in this sentence. The following
Deligne analogy is not part of this finding.

Chapter Markdown and layout extraction located the passage. Raster OCR
checked its prose, and direct inspection of pixel crops rendered from the
[digest-verified PDF](../sources/masullo/README.md) checked both pairs of
square brackets and the derivative order. The inverse weight and its
endpoint powers in (9.2.2.40–41), p. 417, were also checked in rendered
crops. The cross-reference to the strip definition (B.5.3.1), p. 632, is
from layout extraction.

## What the weighted norm gives

Fix a norm-one isotype and choose a unitary base character for its Mellin
parameter, using the log-norm coordinate $x=\log|g|_F$. Up to a positive
Haar constant, the squared norm has density
$w(x)=e^{2a|x|}(1+x^2)^{s/2}$ relative to $dx$. The functional of order $m$
pairs the profile with $x^m e^{zx}$, up to the distributional sign
convention. The squared modulus of its kernel divided by $\sqrt{w(x)}$
is

$$
 |x|^{2m}e^{2\operatorname{Re}(z)x-2a|x|}(1+x^2)^{-s/2}.
$$

Cauchy–Schwarz gives boundedness if this is integrable. Conversely, even
on smooth compact log profiles in the fixed isotype, a bounded functional
would have an $L^2$ representing vector after multiplying profiles by the
square root of the weight. These weighted tests are dense on each bounded
log interval, so that vector must agree locally with the divided kernel,
up to conjugation. The displayed density therefore gives the ambient
criterion: All fixed orders work in the open strip; no order works
outside the closed strip; at either edge the matching tail behaves like
$|x|^{2m-s}$, so precisely $2m+1<s$ works. In particular, degree zero
allows only the interior, and even edge evaluation requires $s>1$.
This sharpens the printed necessary condition rather than contradicting
it. It is a check in the positive weighted norm, not a claim about the
[separate interior-line topology](../obligations/boundary-point-evaluation.md)
of Definition 9.2.2.3.

Masullo gives the spectral explanation; the reciprocal-weight test and
scope comparison above are the project audit. The accepted Lean
`Masullo.interiorLogJet_toLp` identifies an interior jet with the bilinear
integral on weighted log profiles sent into $L^2(dx)$, assuming $s\ge0$
and $|\operatorname{Re}z|<a$. The accepted
`Masullo.boundaryLogJet_exists_smooth_extension_iff` characterizes existence
of a continuous complex-linear map on that $L^2(dx)$ coordinate agreeing
on weighted smooth compact profiles, assuming $s\ge0$ and
$|\operatorname{Re}z|=a$. These are ambient log-model statements, not a
classification of the dual of the idelic theta quotient. Neither statement
assumes that $z+1/2$ is a Hecke zero or computes a trace.

## What the spectral explanation still needs

On each actual fixed-isotype Hilbert quotient at twist $1/2$, prove that
the surviving jets, of orders below the corresponding zero orders,
annihilate the closure of the twisted two-mode theta image. Prove also
that the common ambient kernel of those jets is **no larger than that
closure**, as required for totality in Theorem 10.2.2.1 (p. 446). Ambient
continuity by itself gives neither direction. Even totality would not
justify a spectral trace sum: The trace-class, multiplicity, and cutoff
comparisons in the two preceding findings are separate requirements.
