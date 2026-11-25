---
evidence_revision: 7f7e24f7e1dc4cddb20aab6d4343b8b1f460ca82
---

# Do selected Gaussian singleton cutoffs converge rapidly in trace norm?

Use the exact weight-four Gaussian block of the
[corrected singleton kernel card](gaussian-singleton-corrected-kernel-series.md):
$G=C_{\mathbb Q(i)}$, $a=1/2$, $I=\{0\}$, $s=4$,
$w=(1+\log^2|\cdot|_F)^2$, and $\varphi=b_0\eta$ with its
fixed prescribed positive-log bump. Write $A=A(\varphi)$,
$P=P_a^{\mathrm{spec}}$, and $Z(t)=L(1/2+it,\bar\eta)$ for
the completed function. Here $\mu$ is quotient Haar.

**Claim:** There is one sequence $R_j\in[j+1/4,j+3/4]$ for
all sufficiently large integers $j$ such that the truncation
$T_{R_j}$ of the full quotient biorthogonal coordinate sum
for $PA$ to all $|t|\le R_j$ and all their allowed jets has
$\|PA-T_{R_j}\|_{\mathcal S_1}=O_A(j^{-A})$ for every
$A>0$. The associated corrected output-first Haar kernels
then converge in $L^2(w(x)w(y)^{-1}\,d\mu(x)d\mu(y))$.
These are the original coordinate sums at the selected
heights, not orthogonal compressions or new observables.

**Source and payoff:** The antecedent card uses the
single-character rectangles of (10.4.3.14), PDF pp. 466–467,
and the coordinate density of (10.4.3.21), p. 469. Proving
this would identify the actual kernel along selected cutoffs
in a stronger operator topology, not settle all prefixes or
supply any diagonal trace or global limit-order equivalence.

**Discriminating test:** In the positive log Fourier $H^2$
quotient, verify the full biorthogonal family and coordinate
normalization by the [capped jet totality](../../obligations/trace-theta-totality-qi.md)
and local interpolation at the actual zeros. Use the
[inherited zero count](../../obligations/trace-spectral-singleton-qi.md)
to seek a polynomial-width interval free of absolute zero
heights in every stated window. Test whether cutoffs flat at
every zero give exactly the original smoothed coordinate sum,
including both components at a double jet. Bound each
successive multiplier difference in $H^2$ through derivative
order two, and its quotient rank by the capped annular jet
count. Test summability with rapid tail and identification of
the limit with $PA$; verify the lift and
[Haar normalization](../../obligations/trace-spectral-singleton-kernel-qi.md).
Use a close pair or a double jet as a control for a split or
nonflat cutoff, not as a counterexample on the actual data.
