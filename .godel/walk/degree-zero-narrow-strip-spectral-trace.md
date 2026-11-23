# Degree-zero spectral trace on the same narrow strip

**Status: Open.** Masullo, *The Music of the Primes*, printed p. 31,
§1.4.8, claim from “Because then, once the geometric side is computed”
through “$N(\rho)$ is the multiplicity of the zero.” This finding does not
cover the next paragraph on positive Sobolev degrees.

The chapter Markdown and layout extraction located the passage. Raster
OCR checked its prose; direct inspection of rendered crops of the
[digest-verified PDF](../sources/masullo/README.md) checked $s=0$, the
shift $\rho-1/2$, the factor $N(\rho)$, and the square brackets in
$\mathbf C_{[-a,a]}$. Masullo says that one can continue from the intrinsic
geometric calculation to the spectral calculation in the *same* space
$W_I^{s,2}(C_F)$. In degree zero he prints

$$\sum_{\rho,I} N(\rho) M(\varphi)(\rho-1/2),$$

where $\rho$ runs over zeros of $L(z,\chi)$ whose shifts belong to the
indicated strip. The paragraph does not specify a new test class or state
an endpoint exclusion. The following sentence starts a separate claim about
edge contributions in positive degree. The intended interior-only reading
at degree zero must not be confused with what the bracketed display alone
states. Theorem 12.5.1.1, (12.5.1.3), p. 519, explicitly specifies the
interior in the extracted statement. Working at widths with no zeros on the
edges avoids this distinction at those widths, not at every requested width.

## What the spectral evaluation needs

Even granting the [preceding geometric calculation](intrinsic-narrow-strip-geometric-trace.md),
a separate evaluation is needed. Fix the norm half-twist and one compact
isotype. For the common Chapter 12 tests in $D(C_F)$ vanishing on $C_F^1$,
show that the interior zero jets are continuous and separate the actual
degree-zero theta quotient, prove trace class for its convolution, and
derive the sum with full interior zero orders and justified boundary
weights. The cited quotient trace formula, Theorem 10.3.2.1, pp. 453–455,
assumes $s>1$, as checked on a rendered crop. Its (10.3.2.3–4) includes
Sobolev-capped boundary terms under that hypothesis, on the provisional
extraction reading. Theorem 10.4.2.8, p. 463, prints $s\ge0$, also checked
on a rendered crop, but cites that
higher-degree formula to evaluate its limit. This citation does not extend
the formula to $s=0$.

The limit needed in (10.4.2.20) is for $M_r A(\varphi)P^{\rm spec}_{1/2}$,
where $r$ is the exhausting position cutoff and $P^{\rm spec}_{1/2}$ is the
orthogonal spectral projection, with convolution *after* projection. The
[spectral audit](../obligations/trace-spectral.md) explains why a
trace-norm sum that lifts quotient outputs into the spectral subspace instead
controls $P^{\rm spec}_{1/2}A(\varphi)$, not the geometric-output block of the
required operator. For the expansion with convolution after the lifts, the
audit also identifies an unsupported uniform bound on biorthogonal lifts
and a squared-norm estimate that does not give trace-norm summability.
Prove the cutoff trace limit in the required order (for
example, by trace class of the uncut operator and strong cutoff convergence),
and identify it with the integrated Haar diagonal subtracted in the same
geometric calculation. Equality of quotient traces alone does not give this
cutoff and kernel comparison. The operator and proof comparisons beyond the
rendered degree hypotheses are based on the layout extraction.

The proposed spectral inference and its use of the quotient trace are
Masullo’s. The degree, endpoint, and operator-order comparisons are project
audits, not a disproof of the trace formula. The project’s separate
[positive-width jet trace](../obligations/trace-spectral-strip-q.md) and
[theta closure identification](../obligations/trace-theta-density-q.md) give
a repair over $\mathbb Q$, in the trivial compact isotype, at even degrees
$s=2r$ with integer $r\ge1$, and on a common full-measure set of half-widths
in $(0,1/2)$. They do not supply the degree-zero statement, the arbitrary
isotype or width, or the common geometric diagonal. No Lean statement is
invoked for this passage.
