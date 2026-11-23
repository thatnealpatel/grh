# Zero-width trace and multiplicity preview

**Printed passage.** Masullo, *The Music of the Primes*, §1.7.2,
third bullet, printed pp. 36–37, preview from “The degenerate case
$a=0$” to “No need now.” Masullo says that the zero-width case no
longer gives a trace formula, but appears to give information on zero
multiplicities at degree $b\ge 2m_\chi$. Here $m_\chi$ is the supremum,
over rational primes $p$, of the maximum pole order of the product
of the finite Euler factors above $p$. The paragraph gives
$b\ge 2[F:\mathbf Q]$ as sufficient for that degree threshold.
It reports a phone remark by Brian concerning the trace formula and
reserves the proposed multiplicity conclusions for sequel work. No
particular multiplicity bound on global zeros is stated here.
Coverage stops before §1.7.3.

Chapter Markdown and PDF layout extraction located the paragraph.
Raster OCR checked the prose across the page break. Direct inspection
of thresholded pixel crops from the [digest-verified PDF][source]
checked the three greater-than-or-equal signs, which OCR read as
strict inequalities.

**Checked scope.** The degree threshold concerns one rational prime
at a time. At an unramified finite place the inverse local Euler
polynomial has simple poles; at a ramified place the factor is one.
Thus the product above $p$ has order at most the number of places
above $p$, which is at most $[F:\mathbf Q]$. This is the local count
in the earlier [polar coefficient review][polar]. It does not bound
orders in an exhausting product over many primes. For instance, for
the trivial character every finite factor contributes at zero.

Here $a=0$ denotes the width in (1.8.2.2), not the exponent used to
twist the theta image. The project Lean statement
`Masullo.boundaryLogJet_exists_smooth_extension_iff`, at
`32da3abff99858e9838a64f34ef22d9f35095cc2`, characterizes bounded
extension of the ambient log-line order-$j$ Mellin pairing from
smooth compact profiles by $2j+1<b$, also at zero width. Thus, if
$b\ge 2m_\chi$, the orders below any one primary pole order pass
this ambient test. This application is the reviewer's comparison,
not a result on the actual orbital or spectral quotient. A truncated
zero block on a singleton spectral line would not give an upper
bound on the full zero order. See the [singleton comparison][singleton].

**Disposition: Open.** The trace obstruction and proposed sequel
argument are Masullo's. To show why the zero-width method fails at
any finite degree, identify the actual geometric cutoff operator and
show which step of its diagonal comparison fails when primary pole
orders accumulate at a common point. Unbounded orders in the finite
products alone do not show failure of that operator limit, much less
exclude all trace identities at width zero. To extract the promised
multiplicity information, an additional argument must bound full
Hecke zero orders from primary pole orders rather than bound only the
number of ambient continuous jets. The later paragraph beginning
“And indeed, we find it,” p. 37, assigns the obstruction to an
infinitely repeated pole but defers the explanation to a conversation.
Expectation 1.7.1, p. 38, states the proposed bounds separately.
Neither passage is advanced over by this review.

[source]: ../sources/masullo/README.md
[polar]: polar-coefficient-continuity.md
[singleton]: connes-singleton-spectral-interpretation.md
