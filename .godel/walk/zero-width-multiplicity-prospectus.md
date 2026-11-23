# The zero-width multiplicity prospectus

**Printed passage.** Masullo, *The Music of the Primes*, §1.7.3,
printed p. 37, preview from “As mentioned in the last bullet point”
through “The takeaways are as follows:”. The opening sentence says
that the extremal case $a=0$ in (1.8.2.2) leads to information on
zero multiplicities. The introductory block then reserves the work
for a sequel and says that the details were not worked out beyond
expectations to test against the literature. This block states no
multiplicity bound, degree hypothesis, or argument. Coverage stops
before the first bullet. The degree threshold in the preceding
[letter paragraph][prior] is not restated here.

Chapter Markdown and PDF layout extraction located the passage.
Raster OCR checked the prose, and direct inspection of pixel crops
from the [digest-verified PDF][source] checked $a=0$, the equation
number, the express deferral, and the lead-in to the bullets. The
reading of (1.8.2.2), p. 44, and the distinction between width and
theta twist use the accepted [singleton audit][singleton], not a
new inspection of those later pages.

**Disposition: Open.** The proposed method is Masullo's; the scope
comparison here is the reviewer's. In (1.8.2.2), $a=0$ means the
base is $I=\{0\}$, not that the theta twist is zero. The project Lean
result `Masullo.boundaryLogJet_exists_smooth_extension_iff` at
`b3c013c0f661e3ed459db26e8f7a2cfeb4acbd29` concerns continuous extension
of the order-$j$ Mellin pairing from smooth compact profiles, embedded
with the weight root in ambient $L^2(dx)$. For nonnegative degree $b$
and $|\Re z|$ equal to the half-width, the criterion is $2j+1<b$.
It therefore also applies when the half-width is zero. It neither
identifies the actual theta quotient nor bounds zero orders.

First one needs descent and totality of the allowed jets for the
actual half-twisted singleton quotient, as in the scoped obligation
at Theorem 10.2.1.1, p. 440. Even a capped identification only sees
jets below both the zero order and the degree cutoff. For a full
order bound, an additional comparison must rule out orders above
the proposed bound, rather than count the visible jets. At fixed
half-twist the singleton sees only the critical line; any claim
about zeros off that line needs a separate argument or their prior
exclusion. Expectation 1.7.1, p. 38, is the later place to check the
precise noncentral bounds, their character normalization, and their
hypotheses. Neither that expectation nor the intervening trace
obstruction is resolved by this preview.

[prior]: zero-width-trace-preview.md
[source]: ../sources/masullo/README.md
[singleton]: connes-singleton-spectral-interpretation.md
