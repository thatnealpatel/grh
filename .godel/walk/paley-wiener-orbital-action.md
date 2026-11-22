# Acting on the Paley–Wiener levels after inversion

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.4,
printed p. 27, with footnote 6. Masullo proposes truncating the orbital
kernels on the source and acting on Paley–Wiener levels after inverting
both source and target of the global geometric kernel. He invokes
Tate’s Riemann–Roch theorem for the inversion and the toy example for
the orbital traces. Footnote 6 reads “Finish!” The passage does not
specify the projector for each shell or prove a trace identity. Chapter
Markdown and layout extraction located the passage in the
[digest-verified PDF](../sources/masullo/README.md), and OCR of the
rendered p. 27 corroborated the prose and footnote. This reading is
provisional as a direct visual check.

**Inversion is not invariance of a finite level.** Under the hypotheses
of Tate’s identity, the zero-mode terms of (2.2.3.2), p. 82, drop out
on tests with both moments zero. On half-norm-weighted theta tests,
pullback by inversion then exchanges the test with its Fourier
transform. In particular, the constraint on the Fourier transform
becomes a *spatial* support constraint on the transformed test, and
pullback takes a norm-one isotype to its inverse. One must transport
the source projector and the cutoff, not silently reuse the same
finite level. The [rational reflection audit](../obligations/trace-orbital-q.md#half-twisted-reflection-of-the-rational-theta-projector)
identifies the checked Lean counterpart: `rationalThetaLogReflection_freq_image`
compares closures of the Fourier- and spatial-support images in the
rational even two-moment log-line model. It is not a theorem about
all isotypes, lifted orbital kernels, or invariance of a finite-level
projector. The [theta inversion audit](../obligations/theta-inversion-q.md#rendered-sign-check-a-translated-box-breaks-the-printed-theta-identity)
also records the issue with using the combined printed rational Fourier
conventions in the theta identity as they stand.

**Missing comparison.** Theorems 11.2.1.2 and 11.2.1.4, pp. 488–489,
treat the *whole* projected operator at fixed position cutoff. The
[operator-order audit](../obligations/trace-hardy-diagonal-q.md#the-fixed-cutoff-limit-retains-a-right-projection)
explains why in the ambient composition the strong limit of the right
level projector leaves a terminal geometric projector. These theorems
do not give a limit for a signed cut of the lifted kernel. In the proof
of Theorem 11.3.2.1, pp. 495–496, Masullo invokes (2.2.3.2) to transport
the basis and claims convergence to the finite-rank series (11.2.2.12).
Rendered-page OCR checks the hypothesis $s>1$ and the proof’s invocation
of inversion, the level, and the series. The operator formulas and
level identifications here are read from Chapter Markdown and layout
extraction. The series is presented in an untwisted, singleton-base
setting with $s\ge 2[F:\mathbb Q]$. Neither this series nor the orbital
theorem supplies the introductory $s=0$ comparison. In addition, the
[literal same-chain source multiplier](../obligations/trace-orbital-q.md#the-right-cutoff-erases-a-fixed-shell-in-the-literal-chain)
eventually erases the fixed signed shell, and an idèle position mask
is not by itself an orthogonal Paley–Wiener projector.

For the actual signed shell and specified Haar-compatible lift, identify
the inverted and source-cut integral operator with the expansion on
the transported half-twisted orbital level, at degree zero and a
positive-width symmetric base. Show that the chosen source and position
cutoffs can be removed in a sense that recovers the averaged diagonal
of **that shell**, with its original Haar normalization. Only after
this identification can the scalar Mellin–Poisson step evaluate the
shell contribution. The plan is Masullo’s; the limitations on the
reflection and cutoff steps use the accepted audits cited above. The
preview remains open, and no new Lean declaration is claimed.
