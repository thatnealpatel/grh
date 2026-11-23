# The letter's edge-multiplicity rule and the common trace

**Status: Open.** Masullo, *The Music of the Primes*, printed p. 36,
§1.7.2, third bullet, the paragraph beginning “The entire paper itself”
and ending “altogether.” Masullo says that the geometric ingredients
are prepared in the locally convex spaces, then transferred to coarser
normed completions. After the intrinsic geometric calculation, he says,
one can compute the spectral side in the same completion. The topology
selects the continuous zero evaluations and derivative evaluations
according to whether their support is in the interior, on an edge, or
outside the closed strip. On the edges he says “only multiplicity up
to the smallest integer less than or equal to” $|b-1|/2$. The next
paragraph, beginning “The takeaway,” is separate.

Chapter Markdown and PDF layout extraction located the passage in the
[digest-verified edition][edition]. Raster OCR checked the paragraph;
direct inspection of the formula crop from the rendered page checked
“smallest integer less than or equal to,” the absolute value, and the
following closed-strip brackets. Later proof comparisons use extraction
and the source checks identified in the linked audits.

## A jet-order bound is not a multiplicity

There is no smallest integer below a given real number. Even if the
search is restricted to nonnegative integers, the smallest such integer
here is always zero. Reading “smallest” as “largest” is a repair, and
still leaves a distinction between the last admitted derivative order
and the number of admitted jets. These issues are separate from the
[unsquared modulus][display] in the preceding (1.7.2.2). The following
comparison uses the intended squared-modulus Hardy–Sobolev norm in
(1.8.2.2), p. 44, and (9.2.2.34), p. 417.

On the matching end of the ambient weighted log line, the squared
reciprocal-weight density for the order-$m$ jet has the asymptotic
order $|x|^{2m-b}$. Boundedness there needs $2m+1<b$, including a
strict inequality at equality degrees. For example, at $b=3$,
interpreting the repaired floor as an inclusive order cap would admit
$m=1$, which is unbounded in that model. At $b=2$, interpreting the
floor as a count instead gives zero, although the order-zero jet is
bounded. At an edge zero of order $N$, the ambient model gives at
most $\min(N,\lceil(b-1)/2\rceil)$ candidate jets for $b\ge0$. This
counts orders starting at zero; it does not compute a trace weight.

The comparison uses `Masullo.boundaryLogJet_exists_smooth_extension_iff`
in [BoundaryLogJet.lean][lean] at accepted evidence revision
`f8ee555e7d4062f5427ebee62de485f619910d74`. It assumes $s\ge0$ and
$|\Re z|=\alpha$, and characterizes extension of the pairing on
weighted smooth compact log profiles to a continuous complex-linear
functional on $L^2(dx)$ by $2m+1<s$. This is not a theorem identifying
the full idelic theta quotient or the edge contribution to its trace.
The [positive-degree edge audit][edge] compares the model threshold
with the later *count* in (10.2.2.5), p. 446, and (10.3.2.4), p. 454,
which can include an unbounded equality jet in a sufficiently long
zero block. Neither the model calculation nor this paragraph shows
that a particular half-twisted strip has a zero on an edge.

## The same diagonal must have both evaluations

Fix a half-twist, a positive symmetric strip, a norm-one isotype, and
common trace tests. At a width with edge zeros, show that the admitted
jets annihilate the actual twisted theta closure and, together with
all interior jets, separate the quotient. Derive the trace-class
quotient convolution and the boundary coefficients. A higher-degree
result in Theorem 10.3.2.1, pp. 453–455, would not by itself cover the
introductory range $0\le b\le1$. Then identify the cutoff spectral
trace in Theorem 10.4.2.8, pp. 463–464, with the spectral term in the
same normalized smoothed Haar diagonal as the intrinsic geometric
evaluation. Track the shift, jet orders, and order of projection and
convolution in the cutoff calculation. Theorem 12.5.1.1, pp. 519–520,
prints an interior-only sum, which supplies no boundary comparison at
a width with admitted edge jets. The [same-width audit][same] and the
[geometry-first audit][geometry] record the separate geometric
requirements, including the orbital tail and normalized local
residual. Computing both sides in one ambient space does not identify
their cutoff diagonals.

The ordering and selection mechanism are Masullo's. The distinction
between the printed wording, bounded ambient jets, and spectral
multiplicity is the reviewer's source comparison using the existing
model check. No new Lean result, trace evaluation, or counterexample
to a trace formula is claimed.

[edition]: ../sources/masullo/README.md
[display]: first-hardy-sobolev-display.md
[lean]: ../../Proofs/Props/BoundaryLogJet.lean
[edge]: positive-degree-edge-spectral-trace.md
[same]: same-width-trace-comparison.md
[geometry]: geometric-first-preview.md
