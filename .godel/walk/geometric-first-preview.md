# Geometry first: The intrinsic projection and the printed kernel

**Printed passage.** Masullo, *The Music of the Primes*, §1.7.2,
printed pp. 35–36, third bullet, opening paragraph from “The Geometric
Side of the Trace Formula drives everything” through “The zeros play
no role here.” Masullo says that the geometric calculation dictates
which normed topologies to use, that the spectral side is computed
only afterward, and, more broadly, that zeros are never used as input
or in a construction. This review stops before “The relevant
topologies” and (1.7.2.2); it does not check that formula or any
subsequent claims about completion or multiplicities.

Chapter Markdown and layout extraction located the passage in the
[digest-verified edition](../sources/masullo/README.md). Raster OCR
checked the paragraph over the page break. Direct pixel crops checked
its opening, the “never used as an input” continuation, the final
sentence, and the start of the next paragraph. For the comparison
below, extraction located the Chapter 10 definitions and raster OCR
and pixel crops spot-checked the closure, orthogonal projector,
zero enumeration, and kernel subtraction. That is a source check,
not a verification of the kernel theorem. A rendered crop of p. 519
also checked the operator order in the opening of §12.5. The
independent [source packet for p. 520](../obligations/trace-assembly.json)
checks the final comparison, not its analytic premises.

**Two levels of dependence.** Definition 10.1.1.1(1), p. 434,
(10.1.1.3), defines the closed twisted two-zero-moment adelic theta
subspace by taking its closure in a specified Hardy–Sobolev space.
Definition 10.4.1.1, p. 456, defines complementary orthogonal
projections from this closure. Neither definition asks for the
locations or orders of Hecke zeros. This is independence of the
*definitions*, not a proof that geometric estimates alone justify
using the space in the trace formula.

In contrast, Theorem 10.4.3.5(2)–(3), pp. 472–473, presents a spectral
kernel construction using finite-rank sums indexed by Hecke zeros
and their admitted jet orders, and Definition 10.4.3.7(2), p. 473,
(10.4.3.50), writes the geometric kernel as the convolution kernel
minus the spectral kernel. Thus “never ... to make any construction”
is not an accurate literal account of the explicit kernels. Chapter
10 already gives a spectral calculation; p. 520 compares the two
values of the smoothed geometric diagonal and cites that earlier
work for the zero sum. This does not show that the zeros select the
norms, or that the analytic argument is circular. Local reciprocal
Euler-factor zeros in the orbital calculation are distinct from
the global Hecke zeros in these spectral kernels.

**Open comparison.** Even at a degree admitted by Definition
10.4.3.7 ($s\ge3$), fix twist $1/2$, a positive symmetric strip,
one norm-one isotype, and a Bruhat test supported strictly above
norm one. Obtain the Haar diagonal for the cutoff convolution
*after* the intrinsic orthogonal theta projection, and show that
its smoothing, lift, and cutoff limit give the very diagonal used
for the signed shell and $S$-local evaluations in Chapter 12,
without taking the spectral expansion as an input to that geometric
evaluation. The opening of §12.5 names projection *after*
convolution, whereas the general-strip kernel construction in
§10.4.3.2 uses convolution *after* projection. The bridge must fix
the order or justify equality for the actual cutoff diagonals and
limits. Equality of operators in the Hilbert space alone does not
identify a diagonal: An almost-everywhere kernel representative
need not determine its restriction to the diagonal. The geometric
route also needs the orbital tail limit and identification of the
actual $S$ residual with the normalized local limit, with the two
polar Mellin corrections in the trivial isotype. The [geometric
input audit](../obligations/trace-geometric.md) separates these
steps, and the [same-width review](same-width-trace-comparison.md)
records the additional scope issues in extending the comparison
to degree zero. The separate spectral evaluation must use that
same diagonal in the same normalization.

**Disposition and attribution.** Open as a claim about the proposed
trace calculation, not a theorem about permissible topologies.
The construction and methodological claim are Masullo's. The
distinction between the intrinsic projection and its explicit
kernel, and the identification of the missing analytic comparison,
are the reviewer's source analysis. No Lean result is invoked for
this passage.
