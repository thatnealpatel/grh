# Prime-logarithm independence and the choice of trace topology

**Printed passage.** Masullo, *The Music of the Primes*, §1.7.1,
printed pp. 34–35, fourth bullet, from “The ℚ-linear independence”
through the introductory “in an essential manner throughout:”. Masullo
says that independence of the logarithms of the primes, with no
analogue of comparable strength in positive characteristic, pervades
the choice of normed completions for the trace calculation. The “How?”
paragraph presents the polar-multiplicity theorem that follows as an
example and a consequence of an earlier result. Neither the theorem's
numbered statements nor the subsequent paragraph about how it is used
are part of this review.

**Source check.** Chapter Markdown and layout extraction located the
passage. Raster OCR checked the prose. Direct inspection of rendered
pixel crops from the [digest-verified PDF](../sources/masullo/README.md)
spot-checked “ℚ-linear independence,” “with comparable strength,” the
page break within the sentence on normed topologies, and the “How?”
transition. The later source locators below are provisional readings
from extraction.

**Arithmetic scope.** For distinct rational primes $p,r$ and residue
sizes $q_v=p^f$, $q_w=r^g$, unique factorization makes
$\log q_v/\log q_w$ irrational. At an unramified finite place, the pole
set of the local factor is a translate of
$(2\pi i/\log q_v)\mathbf Z$. Two common poles would give a nonzero
common period by subtraction. This is the reasoning in Theorem
7.1.3.2(1), p. 324, behind the example announced as Theorem 1.7.1.1(1),
p. 35. It allows one common pole and gives no lower bound on distances
between the two pole sets. For an untwisted curve over $\mathbf F_q$,
all residue sizes are powers of $q$ and the local pole sets all contain
$(2\pi i/\log q)\mathbf Z$. This is the relevant loss of period
independence, not an impossibility theorem about function-field traces.

**What still needs to be shown.** The paragraph on p. 35 beginning
“This Theorem has nothing to do with the zeros” supplies the claimed
link from polar multiplicity to continuity of the geometric
coefficient functionals. The arithmetic observation by itself neither
identifies those functionals on the actual normed subquotients nor
bounds them there. For the specific finite $p$-primary step in
Theorems 11.2.0.2 and 11.2.2.1 (pp. 485–486 and 490–491), and Remark
11.2.2.2 (p. 491), the bound by $[F:\mathbf Q]$ for one primary
product is just a count of places over a **single** prime, each with
at most a simple pole. It does not require independence across primes.
If the requisite functionals are jets of orders $m<N$ for this
product and $N\le [F:\mathbf Q]$, then $s\ge 2[F:\mathbf Q]$ yields
$2m+1<s$, the ambient continuity threshold on the Mellin 0-line.
To use this argument in the trace, identify the required
coefficient functionals with such bounded jets on the actual
completed orbital subquotients, including the orders needed in
cutoff comparisons and treatment of exceptional cross-prime
coincidences. Basis and trace convergence are further steps.

**Disposition and provenance.** Open as a claim about what determines
the topology of the trace calculation. The proposed role of the
arithmetic and the pole-lattice argument are Masullo's. The
single-prime versus cross-prime distinction and the separation of
ambient continuity from quotient and trace conclusions are the
reviewer's scope analysis. At inspected revision
`231909b11e1ee1f770dc248731645774dd5d3fbb`, the existing Lean declaration
`Masullo.boundaryLogJet_exists_smooth_extension_iff` in
`Proofs/Props/BoundaryLogJet.lean` has hypotheses $s\ge 0$ and
$|\Re z|=\alpha$ and states the threshold for bounded extension from
weighted smooth compact tests in the ambient weighted log-line
model. It includes width zero. It does not identify any Hecke
Euler-factor multiplicity, idelic quotient, or geometric trace.
