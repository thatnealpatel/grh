# The claimed obstruction at width zero

**Printed passage.** Masullo, *The Music of the Primes*, §1.7.3,
printed p. 37, claim in the first bullet's opening paragraph from
“For $a=0$, no trace formula” through “as we now explain.” Masullo
says no trace formula can be proved at width $a=0$ for any $b\ge 0$,
refers to (1.8.2.2) for the parameters, and says that Theorem 1.7.1.1
already contains the obstruction. Coverage stops before “Let $F$ be
a number field,” which begins the primary pole-order definitions.

The chapter Markdown located the passage. Raster OCR of p. 37 in the
[digest-verified PDF][source] checked the prose. Direct inspection of
rendered pixel crops checked $a=0$, the inclusive $b\ge 0$ (OCR read
it as strict), (1.8.2.2), and the citation to Theorem 1.7.1.1.
The identifications of the parameters and the scope of the cited
polar theorem use the accepted [singleton][singleton] and
[finite-pole][poles] audits, not a fresh reading of those pages.

**Disposition: Open.** Masullo proposes an obstruction to his
zero-width trace method. Width zero leaves the singleton base $I=\{0\}$;
it does not turn off the half-norm twist of the theta image. Theorem
1.7.1.1, printed p. 35, concerns shared poles of finite local Euler
factors, not operators or traces. Its first part bounds the number
of common poles for one pair of distinct residue characteristics;
its specified exceptional-point statements use algebraicity with
Schanuel as printed, or finite order. They do not establish a failure
of a cutoff comparison for each finite $b$.

The reviewer's comparison is that a common pole whose order grows
without bound would eventually exceed any fixed ambient jet cutoff.
The project Lean lemma `Masullo.boundaryLogJet_exists_smooth_extension_iff`
at `b98dbff3caa84fbffa7a33abbcd0f2fef16b77c6` assumes nonnegative degree
and $|\operatorname{Re} z|$ equal to the half-width, including width
zero. It tests continuous complex-linear extension from weighted
smooth compact log profiles to ambient $L^2(dx)$ by $2j+1<b$ for
jet order $j$. It says nothing about which jets the geometric
comparison actually requires, or a trace of the theta quotient.

For the claimed obstruction, identify a necessary step in the
actual zero-width geometric cutoff calculation and show that it
fails at each finite degree, for example by showing that a functional
required after subtraction and passage to the limit is unbounded in
that topology. Growth of pole orders in finite products does not
show that the corresponding high jets survive the subtractions and
are required by the limit. The second bullet's paragraph beginning
“And indeed, we find it” attributes the obstruction to the repeated
pole, but defers the explanation. This review does not rule out
other width-zero trace identities and makes no claim about full
zero orders.

[source]: ../sources/masullo/README.md
[singleton]: connes-singleton-spectral-interpretation.md
[poles]: finite-local-polar-multiplicities.md
