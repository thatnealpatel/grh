# The cutoff orbital trace still needs a diagonal limit

**Printed passage.** Masullo, *The Music of the Primes*, §1.4.9,
printed p. 32, preview beginning “As the cutoff tends to” and
ending “are all zero!” Masullo says to evaluate the limiting
orbital trace by summing diagonal entries on Jordan blocks and
applying Poisson summation. He asserts vanishing for all but
finitely many prime residue characteristics. The paragraph itself
prints no trace formula or cutoff regime. The chapter Markdown
and PDF layout extraction located it, raster OCR checked the prose,
and direct inspection of rendered crops checked the limit symbol,
the block and Poisson wording, and the finite-tail quantifier. The
[pinned edition](../sources/masullo/README.md) was verified against
SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The next paragraph, on reduction to Connes' S-local computation,
is a separate passage.

**What the scalar calculation gives.** Conditionally on the claimed
jet coordinates and convolution action, the product rule makes the
order-$N$ matrix at each Euler zero triangular, with the Mellin
multiplier on each of its $N$ diagonal entries. This determines a
finite block, not the trace of the cutoff operator or the limit of
its trace. Masullo's later (11.3.2.5), p. 496, sums over the zeros
of the reciprocal Euler product above $p$, with multiplicities and
the factor $|g|_F^{-1/2}$ in the Mellin weight. Theorem 7.4.2.1(2),
p. 367, gives the corresponding untwisted formula on the intrinsic
orbital theta quotient. Substituting the half-norm-weighted test
matches the scalar weights, not the two operator realizations.

After disintegration of a fixed-character Mellin integral by norm,
Poisson summation samples character-weighted integrals over norm
fibres, not automatically point values at uniformizer powers. Each
unramified place $v\mid p$ supplies a lattice with sampled norms
$q_v^{\mathbf Z}$; summing the lattices counts coinciding zeros with
their multiplicities. For a fixed test with compact norm support in
$(1,B]$, $p>B$ ensures $q_v\ge p>B$ for every $v\mid p$, so all those
fibres miss the support. Ramified factors supply no Euler zeros.
Thus the scalar sum has the finite-tail property even without the
point-sample formula. See the earlier [finite-tail reading] and the
[orbital audit]. The scalar reasoning does not say an operator is
zero or identify any trace with a geometric diagonal.

**Missing comparison.** After identifying the actual truncated
signed shell with the cutoff basis operator, one needs a trace
limit that both gives the multiplicity-weighted Mellin sum and
recovers the Haar integral of the averaged diagonal of that same
lifted shell. Fixed-cutoff trace class does not give uniform control
as the cutoffs are removed. Theorem 11.3.2.1, pp. 495–496, invokes
the Paley–Wiener level and the regime $\Lambda\to\infty$ with
$\varepsilon\Lambda=o(1)$; its displayed right side (11.3.2.1) is
single-place, whereas (11.3.2.5) is $p$-primary. The statement
assumes $s>1$, not the introductory $s=0$ case at positive width
and twist $1/2$. These later statement and formula readings are
provisional from the chapter Markdown and layout extraction.
Separately, the [rendered mask check] shows that the extra right
mask in (11.3.2.3) is eventually zero on a fixed shell in the
literal chain. Replacing it by the outside-$S'$ unit mask in
(11.3.2.4) is not justified by that cutoff limit. This does not rule
out a different comparison for the actual shell.

**Disposition.** The block trace and Poisson route is Masullo's.
The conditional block and scalar checks, and the distinction between
operator trace, scalar sum, and averaged Haar integral, are the
reviewer's, using the accepted [fixed-cutoff reading], [global
Mellin reading], and [finite-tail reading]. The preview remains
open. No Lean result identifies the cutoff limit or proves vanishing
of the geometric orbital trace here.

[fixed-cutoff reading]: truncated-orbital-trace-class.md
[global Mellin reading]: global-orbital-mellin-trace.md
[finite-tail reading]: orbital-trace-finite-tail.md
[orbital audit]: ../obligations/trace-orbital-q.md
[rendered mask check]: ../obligations/trace-orbital-q.md#the-right-cutoff-erases-a-fixed-shell-in-the-literal-chain
