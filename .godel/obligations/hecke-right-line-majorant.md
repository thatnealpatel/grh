# An absolute majorant for the Hecke right line

**Status:** Open Lean obligation. This can run independently of the
trace comparison and without a meromorphic Hecke L-function interface.

## Source and needed estimate

In the [pinned text](../sources/masullo/README.md), (3.2.1.1), p. 122,
gives the unramified finite Euler factor. Lemma 3.2.1.1, (3.2.1.2),
p. 123, gives absolute, compact-uniform product convergence and refers
to comparison with the rational zeta product. In (B.4.2.5)–(7),
p. 615, Masullo uses absolute and uniform convergence on the right
line and expands the local logarithmic derivatives as geometric
series. The interchange in (B.4.2.8)–(9) integrates the expansion
against the Mellin test. The needed dominating bound is for the
**differentiated** coefficients, with the extra $\log q_v$, summed over
**both** $v$ and $m$. Neither a local geometric series alone nor
compact-uniform convergence of the undifferentiated product on its own
supplies the majorant over the entire vertical line. The locators and
scope above are from text extraction, not a rendered-page review.

Prove the following project result in Lean first. For an arbitrary
number field $K$, let $v$ range over `HeightOneSpectrum (𝓞 K)`, put
$q_v=v.\mathrm{asIdeal}.\mathrm{absNorm}$, and index $m=k+1$ with
$k\in\mathbb N$. For every real $a>1$, prove `Summable` on the product
index for the nonnegative real function

$$
c_a(v,k)=(\log q_v)\,(q_v^{a(k+1)})^{-1}.
$$

For any scalar family $z_v\in\mathbb C$ with $|z_v|\le1$ and any
$\Re s\ge a$, verify that the norm of
$(\log q_v)z_v^{k+1}\exp(-(k+1)s\log q_v)$ is at most $c_a(v,k)$.
This covers unitary coefficients in (B.4.2.7) and deletion of places
by setting $z_v=0$; it does not construct the Hecke character or identify
a logarithmic derivative of a global L-function. The same majorant
works with conjugated coefficients on the **same** right line. Given
an integrable vertical weight $W$, domination by $c_a(v,k)\|W(t)\|$
would then give summability of the $L^1$ norms and interchange with
the two-index sum. The checked rational example of that consumer is
`vonMangoldt_right_line_integrals` in
[`Lemmas.ZetaRightLine`](../../Proofs/Lemmas/ZetaRightLine.lean).
Do not import that lemma as a general Hecke identity.

## First runnable proof

Use pinned Mathlib's `NumberField.HeightOneSpectrum.one_lt_absNorm`
from `NumberTheory.NumberField.Completion.FinitePlace` for $q_v\ge2$.
For each $v$, a geometric sum bounds $\sum_k c_a(v,k)$ by
$(1-2^{-a})^{-1}(\log q_v)q_v^{-a}$. It remains to sum over $v$.
Use `NumberField.Ideal.tendsto_norm_le_div_atTop₀` from
`NumberTheory.NumberField.Ideal.Asymptotics`: The number of nonzero
integral ideals with norm at most $B$ is $O(B)$. Map each place to its
nonzero integral prime ideal. The map is injective by
`HeightOneSpectrum.asIdeal_injective`, and the ideal count bounds the
cardinality of the places in each dyadic shell $2^j\le q_v<2^{j+1}$
by $C\,2^{j+1}$. Bounded fibers are finite by
`Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le`.
Thus the sum of $(\log q_v)q_v^{-a}$ on shell $j$ is bounded by a
constant times $(j+1)2^{-(a-1)j}$. A geometric comparison completes
summability, without identifying distinct ideals of equal norm.

Start a theorem in `Proofs/Theorems/` stating the product-index
summability and the uniform pointwise bound, and keep the count-to-sum
machinery in `Proofs/Lemmas/`. Check the theorem locally against the
pinned Mathlib and obtain independent statement review before the full
candidate audit. The lookup above checks interfaces, not elaboration.
Only after this result is checked should the integrated version import
it. The contour identity, its analytic continuation and growth
premises, the ramified Fourier calibration, and the global trace all
remain separate obligations.
