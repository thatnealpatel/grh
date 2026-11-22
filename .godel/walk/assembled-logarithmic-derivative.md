# The assembled logarithmic derivative has the wrong pole sign

**Printed passage.** Masullo, *The Music of the Primes*, printed
p. 29, claim in §1.4.5, “Putting everything together,” from the
heading through “Everything else follows from this.” For a fixed
$a>0$ and $I=[-a,a]$, the display asserts

$$
A(s)+\frac{L'_f(s+1/2,\chi)}{L_f(s+1/2,\chi)}
=\delta\left(\frac1{s+1/2}+\frac1{s-1/2}\right)-S(s),
$$

where $A$ is holomorphic on $\operatorname{Int}K$, $S$ is holomorphic
on $\Re s>a$, and $\delta$ is one for trivial restriction to $C_F^1$
and zero otherwise. The text calls this the main consequence of the
Trace Formula. The continuation argument beginning on p. 30 is a
separate passage.

Chapter Markdown and PDF layout extraction located the passage in the
[digest-verified edition][edition]. Raster OCR checked the prose;
direct rendered-pixel inspection checked the positive sign before
the logarithmic derivative, both pole denominators and their plus
sign, the minus sign before the right holomorphic term, the domain
$\Re s>a$, and the citation “§5.1.” The extraction of Chapter 5 places
§5.1 on pp. 221–229, on the topology of adelic theta and idelic zeta
spaces; no assembly of the p. 29 cutoff limits was identified there.
The source of that cross-reference is unresolved, not silently
replaced by the nearby argument in Chapter 1.

## Rational residue check

The identity is false as printed on its claimed domain. Take
$F=\mathbb Q$, $\chi=1$, $a=1/4$, and $K$ the closed disc centered
at $1$ of radius $5/8$. The disc lies in $\Re s>a$, its interior
meets $\Re s>1$ in an open set, and $1/2\in\operatorname{Int}K$.
Thus it meets the conditions for $K$ in §1.4.3. Here $\delta=1$
and $L_f$ is the Riemann zeta function. The simple pole at $u=1$
gives $\zeta(u)=g(u)/(u-1)$ near $1$, with $g$ holomorphic and
$g(1)=1$. Taking the logarithmic derivative gives
$g'(u)/g(u)-1/(u-1)$ off the pole. After the shift $u=s+1/2$,
the residue at $s=1/2$ on the left is $-1$, and on the right it
is $+1$. This contradicts the meromorphic equality even if it is
read only off the displayed poles in $\operatorname{Int}K$.
Even an equality asserted initially only on the overlap with
$\Re s>1$ would give the same contradiction by the meromorphic
identity theorem on this disc, if both printed holomorphy domains
for the remainders are retained.

This is the reviewer's analytic check of Masullo's assertion. An
independent Yah reader (`pole-sign-reader`, output
`f92e650abbad2827e993b9b414717dc44ba5a909`) checked the rendered
signs, the admissibility of the disc, the residue contradiction,
and the supporting declarations against GRH revision
`b066a806e08fdcc782c1dd91fcdd7c0207b9bec1`. The Mathlib pin at that
revision is `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. In that pin,
`riemannZeta_residue_one` gives the punctured limit of
$(u-1)\zeta(u)$ equal to one, and `analyticOn_riemannZeta` gives
analyticity off $1$. Removable singularity and the elementary
logarithmic differentiation above give the residue check; neither
Lean signature states the off-pole equality in §1.4.5 or its
refutation. A fresh joint Lean import of the two Mathlib statements
confirmed their signatures and only `propext`, `Classical.choice`,
and `Quot.sound` as axioms. No new Lean theorem is added.

## What remains missing after correcting the sign

The [finite-place audit][finite] checks that with ramified coefficients
set to zero, the scalar cutoff limit on the right half-plane is the
**negative** logarithmic derivative. Reversing that sign in the
assembly agrees with the rational pole residue, but cannot justify
the limit. The
[Archimedean subsection][infinity] and [zero-sum subsection][zeros]
claim separate holomorphic limits of the unsubtracted tests, which
fail in the rational controls there. Opposite divergences could
cancel in a joint calculation; the separate-limit argument does
not establish such a cancellation or the resulting holomorphic
function. A replacement needs a fixed-test identity on the same
character convention and strip for all cutoff tests, a common
norm-one normalization or a proof of cancellation, and a locally
uniform, summably controlled limiting remainder. It needs
a domain containing the right-half-plane overlap and reaching the
claimed region, not merely one Montel subsequence on an isolated
compact set.

The existing [fixed-parameter rational repair][repair] subtracts an
exponential at a fixed parameter. On the common right half-plane
it gives a **plus** between the shifted zeta logarithmic derivative
and the two rational pole terms after rearrangement, consistent with
the residue cancellation, but the repaired strip result is
conditional on a rational, strip-restricted fixed-test trace identity.
`Masullo.rationalIdeleRadial_explicit_formula` at accepted revision
`9330ec2f38fe508354301080f8110dc70989458a` instead compares the
normalized scalar local terms, two polar moments, and the full-order
sum over the nontrivial zeta zeros for any smooth compact rational
radial log profile. It is not that strip-restricted premise, an
operator trace comparison, or a limit for the original test family.
No conclusion about RH, GRH, or the later continuation is asserted.

[edition]: ../sources/masullo/README.md
[finite]: finite-prime-cutoff-sign.md
[infinity]: archimedean-montel-subsequence.md
[zeros]: unsubtracted-zero-sum-limit.md
[repair]: ../obligations/trace-to-zeros.md#fixed-parameter-subtraction-over-the-rationals
