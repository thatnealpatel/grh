# Support vanishing in the toy trace calculation remains open

**Printed passage.** Masullo, *The Music of the Primes*, §1.2.8,
printed p. 17, claim beginning “In particular, if the support of”.
For $\gamma>1$ and $\varphi\in C_c^\infty(\mathbb R_{>0})$, Masullo says
that $\operatorname{supp}\varphi\subset(1,\gamma)$ implies
$\operatorname{Tr} A(\varphi)=0$ on
$\mathcal S(\mathbb R_{>0}/\gamma^{\mathbb Z})$. Here $A(\varphi)$ is
convolution for inverse left scaling with Haar measure $dt/t$. The
rendered sentence was checked as a raster pixel crop of PDF page 17,
separately from the chapter Markdown and raster OCR. The printed page
agrees with the PDF ordinal, and the PDF SHA-256 was verified as
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.

**Scalar step.** For $k\le0$ one has $\gamma^k\le1$, and for $k\ge1$
one has $\gamma^k\ge\gamma$. Thus every lattice sample vanishes. The
[accepted normalization audit](toy-poisson-normalization.md) at
`110c36e6908673da5c0202f59a05237f597c7d2d` gives the corrected scalar
identity
$$
\sum_{m\in\mathbb Z}M(\varphi)(2\pi im/\log\gamma)
  =(\log\gamma)\sum_{k\in\mathbb Z}\varphi(\gamma^k)=0.
$$
The missing factor on p. 17 cannot affect this zero. Masullo draws the
support consequence from the preceding trace and Poisson formulas.
The endpoint and normalization checks above are the reviewer's. The
Lean input `Masullo.schwartz_scaled_poisson` at
`9b447a5ce120c101fb0fd341378d877f2bb469c9` is an additive real-lattice
identity for a complex Schwartz function and positive spacing. It
neither defines nor computes this operator trace.

**Open operator step.** The exact premise needed is that the nuclear
trace of $A(\varphi)$ on the smooth quotient, with the stated Haar
normalization, equals the absolutely convergent sum on the left.
A direct route uses the Fourier rank-one expansion on the log circle
of length $L=\log\gamma$: The character $u\mapsto e^{2\pi imu/L}$
has multiplier $M(\varphi)(-2\pi im/L)$ under inverse scaling.
To obtain the trace, justify the nuclear expansion in the smooth
Fréchet topology and its trace by summing the normalized coefficient
pairings. Rapid decay justifies reindexing the scalar sum, without
requiring the printed per-mode sign or a separate transpose trace
identity. The operator-to-sum identification is not checked by the
accepted scalar evidence. This finding does not assert that
$A(\varphi)$ is the zero operator, and it does not review the next
paragraph's analogy with the prime-indexed adelic diagonal integrals.
