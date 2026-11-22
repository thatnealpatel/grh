# The finite-place cutoff limit has the opposite sign

**Printed passage.** Masullo, *The Music of the Primes*, printed p. 29,
claim in §1.4.4, “The logarithmic derivative of $L_f(s,\chi)$,” from
“Now note” through the last display. The cutoff profiles are supported in
$(1,\infty)$, so their samples at $q_v^{-m}$ vanish for $m>0$. The
remaining positive-sign prime-power sum is said to converge uniformly on
compact subsets of $\Re s>1$ to the ordinary logarithmic derivative
$L'_f(s+1/2,\chi)/L_f(s+1/2,\chi)$. The section uses $z$ for the profile
parameter and $s$ for that same parameter in the target.

Chapter Markdown and PDF layout extraction located the passage. Raster
OCR checked its prose. Direct inspection of pixel crops from the
[digest-verified PDF][source] checked the sign of the first term, the
plus between the two terms, their $q_v^{\pm m}$ samples, and the absence
of a minus sign before the target quotient. The reciprocal factor and
the exclusion of $S_\chi$ were checked in the rendered (3.2.1.7),
Definition 3.2.1.4, pp. 123–124. The leading minus sign in the rendered
Dirichlet series (B.6.1.12), p. 638, agrees with that definition.

## Checked scope

The support observation is correct. The limit as printed is false
already for $F=\mathbb Q$, $\chi=1$. At a real parameter $z_*>1$ in an
admissible $K$, take nonnegative additive mollifiers of mass one and
the cutoffs of §1.4.2. Each sum is nonnegative. The Euler product gives
$\zeta'(z_*+1/2)/\zeta(z_*+1/2)<0$: It is minus the absolutely
convergent sum of strictly positive prime-power weights. So the sums
cannot approach the printed value, even at this one point.

For the corrected finite calculation over a number field, take a
unitary $\chi$ and set $c_v=\chi_v(\pi_v)$ at each unramified place
and $c_v=0$ at each ramified place. The latter convention is not the
literal evaluation at an arbitrary uniformizer in the p. 29 sum.
It is required by (3.2.1.7) and by the unit average in the
[characterwise local comparison](characterwise-trace-formula.md).
For $u=z+1/2$ the limit is

$$
\sum_{v,\,m\ge1}(\log q_v)c_v^m q_v^{-mu}
=-\frac{L'_f(u,\chi)}{L_f(u,\chi)}.
$$

Indeed, writing $w=c_vq_v^{-u}$, the logarithmic derivative of
$(1-w)^{-1}$ is $w'/(1-w)=-(\log q_v)w/(1-w)$.

For compact-uniform convergence, let $E$ be a nonempty compact set in
$\Re z>1$, $\sigma=\min_E\Re z$, and $M=\max_E\Re z$. For additive
mollifiers supported in $[-\varepsilon,\varepsilon]$ with
$\varepsilon<1/2$, the integrand at $t=q_v^m\ge2$ only samples
arguments $t-b\ge t/2$. Thus the mollified cutoff profile at $t$ is
bounded in modulus by $2^M t^{-\sigma}$ because the mollifier is
nonnegative of mass one and $0\le h\le1$. At each fixed $t$ it
converges uniformly on $E$ to $t^{-z}$, by uniform continuity in
$(z,b)$ for the mollifier samples there and $h(t)\to1$. Multiplying
by the finite weights gives the joint summable majorant
$2^M(\log q_v)q_v^{-m(\sigma+1/2)}$; control the tail by this
majorant and take the limit on the remaining finite set. No uniform
Archimedean or spectral estimate is needed for this finite-place step.

## Accepted evidence

At exact revision `de778015788ba5c3a3f199393d2fdb5b835478c1`,
[`Masullo.finiteHeckeCharacterEulerProduct_logDeriv`][product] proves
nonvanishing, differentiability, and a joint `HasSum` to the negative
logarithmic derivative of the product of inverse local polynomials,
for actual unitary Hecke characters and $\Re u>1$. Ramified factors
are one and their coefficients zero. It does not identify Mathlib's
`χ.LSeries` with that product. The [majorant declaration][majorant],
`Masullo.finiteHecke_right_line_majorant`, proves summability and the
coefficient bound for any family $|c_v|\le1$ and $\Re u\ge a>1$.
These are unchanged from `756b8cd07027d5a4eb88c74abb657e9e8d00a912`
and `861ddae46e7a84e194d99880844c5fc1e4c05f3a`, respectively.

**Independent review.** Fresh Yah reviewer `BrjdoZs` (output
`4296b6e2d3aec262eeadc5b2e5a53c8ee3f078bb`) checked the rendered
passage, the sign counterexample, the ramified-place convention, and
the two declaration signatures at the exact revision cited above.
The reviewer independently derived a summable tail bound by grouping
prime powers by integer norm. This was a source and signature review,
not a new kernel check.

The cutoff family and support observation are Masullo's. The
counterexample and uniform cutoff estimate are the reviewer's analytic
arguments using the accepted Euler-product results, not new Lean
limit theorems. The repair does not supply a consistent character lift,
a limiting trace identity, or a zero-location conclusion.

[source]: ../sources/masullo/README.md
[product]: ../../Proofs/Theorems/FiniteHeckeCharacterEulerProduct.lean
[majorant]: ../../Proofs/Theorems/FiniteHeckeRightLine.lean
