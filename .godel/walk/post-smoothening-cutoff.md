# Truncating an already smoothened lift

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.1,
printed p. 24, application paragraph beginning “Part (3) teaches
us.” It describes multiplying lifted kernels *after smoothening*
by an invariant function pulled back from G/H along π. It previews
truncation in the first variable using mollified indicators of
relatively compact sets. This review stops before “Part (4)
teaches us.”

The [pinned PDF][source] matched SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Chapter Markdown and PDF layout extraction gave the paragraph.
Rendered pixel crops confirm “after smoothening,” “an invariant,”
the quotient pullback, and “relatively compact subsets in the
x-variable”; crop OCR separately confirms the mollification wording.

**What item (3) supplies.** Write Q = G/H and Ψ(v) = w · (v ∘ (π × π)).
For a supplied bounded continuous ρ on Q, set v(q₁,q₂) = ρ(q₁)ũ(q₁,q₂).
Substituting into Masullo's definition gives Ψ(v)(x,y) =
ρ(π(x))Ψ(ũ)(x,y) wherever the already smoothened quotient kernel ũ
is defined. This is the same
scalar calculation as [item (3)][multiplier], (1.3.1.10), not an
interchange of limits. The restriction to C_c(Q × Q) in the printed
item does not literally include ρ(q₁) when Q is noncompact and ρ is
nonzero. Compact support in the second coordinate is not needed for
this calculation; boundedness suffices to preserve local integrability
when the input is locally integrable. The pullback ρ ∘ π is invariant
under H-translations in the first variable. Multiplying an already
defined *ambient* smoothening is also pointwise, but item (3) does not
identify that ambient smoothening with Ψ(ũ) on the [skewers][skewers].

**Open use.** The paragraph does not specify the domains or construct
the cutoffs. To use (1.3.1.10) for a concrete truncation, say where the
cutoff is made and show that the ambient multiplier factors through π.
A compactly supported cutoff constructed on Q has the needed descent
by definition. In the norm-cutoff application, Definition 9.3.3.1,
p. 427 (read provisionally from chapter Markdown and layout extraction),
specifies a profile of the proper quotient norm, supported on a bounded
norm band away from zero. Pulling such a profile back to the ideles
preserves invariance, not compactness of support. In fact, if H is
infinite and closed discrete, the support of any nonzero H-invariant
function on G contains a translate of H, so cannot be relatively compact.
Mollification of an arbitrary ambient indicator does not supply descent.

If a later use truncates *before* averaging and identifies the result
on a diagonal or skewer with a product formed *after* averaging, it
needs a separate value comparison there. For a continuous multiplier m
and shrinking normalized boxes, the error from replacing m inside the
average by its value at the center is bounded by its oscillation on the
box times the normalized average of the absolute kernel. Boundedness of
these absolute averages suffices, but does not follow from convergence
of the signed means. The factorization and error-bound distinctions
are the reviewer's; neither a cutoff limit nor a Lean endpoint was
checked here.

[source]: ../sources/masullo/README.md
[multiplier]: lifted-quotient-multiplier.md
[skewers]: skewered-smoothening-use.md
