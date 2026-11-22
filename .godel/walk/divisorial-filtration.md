# The ordinary divisorial filtration of the idèles

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.2,
printed pp. 25–26, from the definition (1.3.2.2) through the first
two displays on p. 26. Before defining the “primary” version, the
manuscript sets ρ_T = ∏_{v ∈ T} ρ_v for a finite set T of finite
places disjoint from S. It says an increasing chain with a single
new place per step defines a “stratification” by clopen subsets.
The next page calls each 1-locus a stratum and describes its
successive difference by requiring nonzero valuation at the newly
added place. The rightmost set in the first p. 26 display quantifies
already over GL₁(A_F)_{T_k}, not the ambient GL₁(A_F).

Chapter Markdown and PDF layout extraction supplied the reading.
Raster OCR from the digest-verified [pinned PDF][source] confirmed
the surrounding prose on both pages. Direct inspection of rendered
pixel crops confirmed the product and its index in (1.3.2.2),
the subscript on the rightmost ambient group, and the newly added
place in the successive-difference condition. Coverage stops before
“At last, we will term the primary divisorial stratification.”

**Checked scope.** Use the [corrected coordinate multiplier][local]
ρ_v(g) = 1_{O_{F_v}×}(g_v), and take each T_k disjoint from S as
required for (1.3.2.2). Write X = GL₁(A_F) and
D_T = {g ∈ X : g_v ∈ O_{F_v}× for every v ∈ T}. A finite product
of indicators is the indicator of the intersection, so ρ_T = 1_{D_T}
and D_T is clopen. For the empty set the product is one and D_T = X.
The description of D_{T_k} by the unit tests must use X as the
ambient set; the printed self-reference is not that description.

If T_{k+1} = T_k ∪ {w} with w outside T_k, then D_{T_{k+1}} ⊂ D_{T_k}.
Their difference is clopen and consists of g passing the tests at
T_k for which g_w is a nonunit. The local multiplicative group is
partitioned by its uniformizer shells, and the unit group is the
shell with exponent zero. This gives the printed union of the
nonzero shells at w. The terminology and formulas are Masullo's;
these checks are the reviewer's elementary indicator and valuation
calculations on the repaired input.

**Limit of the claim.** The D_{T_k} are a decreasing filtration,
not disjoint strata. The adjacent differences are disjoint and
cover D_{T_0} minus the residual intersection R = ⋂_k D_{T_k}:
For a point of D_{T_0} outside R, the first failing test determines
its piece. An exhaustive partition of X also uses R and, for
T_0 nonempty, X minus D_{T_0}. The identity idèle belongs to R even
if the chain exhausts the places outside S. In the idelic
restricted-product topology R is itself clopen: It is closed by
intersection, and at each of its points a basic neighborhood can
impose unit membership outside a finite set and at every tested
place inside that set. No exhaustion or disjointness claim for the
printed family is inferred from the word “stratification.” No Lean
endpoint was proposed or checked. This does not check primary
strata, norm pullback, quotient descent, or a diagonal integral.

Independent Yah reviewer nQZahNE (output
`408ab7638d8ea489c59651644b87f2cceff73859`) separately verified the
pin, inspected both rendered pages, and checked the repaired
finite-coordinate statement, the successive differences, and the
need for residual pieces if an exhaustive partition is required.

[source]: ../sources/masullo/README.md
[local]: single-place-divisorial-multiplier.md
