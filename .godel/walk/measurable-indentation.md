# Measurable indentations and fundamental-domain indicators

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.1,
printed p. 22, claim in the paragraph beginning “Functions such as”
after (1.3.1.2). It names the preceding cutoff a continuous indentation,
then allows a measurable cutoff with a μ_G-null discontinuity set
instead. It retains condition (2), compact intersection of the closed
support with π⁻¹(π(K)) for each compact K ⊂ G, and requires the Haar
orbit integral (1.3.1.1) to be 1 at every x ∈ G. It announces using
the relaxed notion for indicators of fundamental domains “when these
exist.” The counting-measure hypothesis for discrete H comes in the
following setup, not in this paragraph.

The [pinned PDF][source] was verified against SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The paragraph and its context were read in chapter Markdown and layout
extraction. The term “indentations,” the references to (2) and
(1.3.1.1), the null-discontinuity clause, and the qualification about
fundamental-domain indicators were spot-checked in rendered pixel
crops. The subsequent two-variable setup is outside this finding.

**Existence versus the choice of indicator.** The relaxed existence
claim follows from the [continuous indentation existence][continuous]
claim on pp. 21–22: A continuous cutoff is measurable and has no
discontinuity points. The relaxation does not assert that the cutoff
must be discontinuous. This implication is classical and conditional
on the earlier existence input, not a further construction.

For a Borel exact transversal D for H acting on G, the function
h ↦ 1_D(h⁻¹x) is the indicator of a singleton in H, for each x.
Its orbit integral is 1 with counting measure on discrete H, is the
singleton mass for any other normalization, and is 0 for nondiscrete
H. In a locally compact nondiscrete group a compact neighborhood has
infinitely many distinct points, so finite Haar mass on that
neighborhood forces every singleton to have mass zero. For the
indicator, the closed support is the closure of D and the
discontinuity set is precisely the boundary of D. Thus in the
counting-measure case, one still needs compactness of the intersection
of that closure with π⁻¹(π(K)) for all compact K, and μ_G-null boundary
of the specific D used. Exact orbit representation alone supplies
neither of these two conditions. For example, a Borel transversal for
ℝ/ℤ can take the rational representatives in [0,1) and the irrational
ones in [1,2), giving positive-measure boundary despite boundedness.

**Why compactness needs a separate check.** For G = ℝ² and H = ℤ²,
let f(x) = x/(1−x) on [0,1) and take
D = {(x,y) : 0 ≤ x < 1, f(x) ≤ y < f(x)+1}. The first coordinate
chooses x modulo ℤ, and the interval of width one then chooses y
modulo ℤ. This Borel transversal is homeomorphic to [0,1)² by
vertical shear, has nonempty interior, and has null boundary (two
graphs and a vertical segment). Even the intersections of its
closure with nontrivial lattice translates are null: The x = 1
edge is absent since f diverges, so horizontal displacement makes
the closures disjoint, and nonzero vertical integer displacement
allows only boundary overlap. Boundary images in the quotient are
null as well, by splitting into countably many translates of the
unit square. But π([0,1]²) is the entire quotient and the closure of
D is unbounded. Thus (2) fails even with a null boundary and the
unit orbit sum. This example tests an unrestricted reading of the
indicator remark, not the relaxed existence claim or any particular
idelic domain.

**Forward scope.** Remark 12.2.1.4, printed p. 507, appears to define
fundamental domains by covering, disjointness, and null closure
overlaps, with connectedness and nonempty interior. That reading is
provisional from chapter Markdown, not a rendered-page check. In
applying that terminology to p. 22, the precise question is whether
it supplies the ambient null boundary and compact closed-support
intersections, or whether those must be checked for each chosen
representative set. No inference from a quotient-measure overlap
condition to ambient null boundary is needed for the example above.
The two-variable setup and any claims about concrete idelic domains
are separate passages.

**Formal scope: Open.** The indicator requirements and the example
are the reviewer's classical checks. Masullo supplies the terminology
and announces the use, but does not give the missing support and
boundary checks in this paragraph. No Lean endpoint is used here; in
particular, the smooth real-log lattice cutoff described in the
[continuous audit][continuous] does not verify a measurable
fundamental-domain indicator. This note does not close any formal
claim.

[source]: ../sources/masullo/README.md
[continuous]: continuous-indentation.md
