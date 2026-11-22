# One finite stage for the global theta isotype

**Printed claim.** Masullo, *The Music of the Primes*, §1.3.2,
printed p. 25, paragraph beginning “Recall that there exists,”
equation (1.3.2.1), and the following attribution. For fixed $F$
and $\chi$, a single $S$ is to work for every element of the global
norm-one $\chi|_{C_F^1}$ theta isotype with source
$\mathcal S_0(\mathbf A_F)$. Each element is to be the homogeneous
theta image of a test $f_S\otimes\bigotimes_{v\notin S}1_{\mathcal O_{F_v}}$
with $f_S$ in the full $S$-local Schwartz–Bruhat space. The text
requires $S$ to contain the ramified places of $F$, the Archimedean
places, and the places where $\chi$ is ramified, and to satisfy
$\operatorname{Pic}(\mathcal O_{F,S})=1$. The same $S$ is chosen
before the theta function; finite-stage membership with $S$ depending
on the function would not give the common tensor factor.

Chapter Markdown and PDF layout extraction supplied the text.
Rendered pixel crops of the [pinned edition](../sources/masullo/README.md)
were checked separately for the hypotheses, the restricted tensor
display, and the attribution. The verified SHA-256 is
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The passage literally says “finite set of finite places” and then
requires all Archimedean places. The intended reading is a finite
set of places, including the Archimedean ones. On that reading,
the arithmetic choice is independent of the theta function: Enlarge
the ramification and Archimedean set by the finite primes supporting
ideal representatives of generators of the finite ideal class group.
Localization then kills that group. This choice does not prove
that one stage supplies all the representatives.

**Dependency and disposition.** The reference to the end of Chapter 5
is misplaced. The Fifth Structure Theorem is **Theorem 6.2.1.1(2),
p. 295**, in Chapter 6. The theorem heading and the surjectivity
line were checked in rendered crops. It states surjectivity of
insertion on the **full** homogeneous theta quotients under the
class-group and unramifiedness hypotheses. Its proof is provisionally
read from the chapter Markdown as reducing global surjectivity to
surjectivity at every finite enlargement (pp. 296–297); that
argument has not been verified here. The exact missing input for
(1.3.2.1) is surjectivity of the induced insertion at one such $S$,
with insertion on test representatives given by tensoring with the
outside-$S$ unit-ball indicators.

Conditional on this input, view a theta function from the smaller
source as an element of the full isotype. Lift its class by the
surjective insertion, then choose a Schwartz–Bruhat representative
of the local class and apply the displayed tensor insertion followed
by the global homogeneous theta map. This is the reviewer's
application of Masullo's stated theorem, not a verification of its
proof. The display does not require the inserted test itself to be
in $\mathcal S_0$, nor assert an isomorphism of the restricted
quotient topologies. For a use that needs zero moments on the
inserted test, one must also compare the moment kernels, as in the
[conditional quotient argument](orbital-subquotient-comparison.md#conditional-quotient-argument).
No Lean endpoint is used. The finding is open at the printed general
scope, and does not cover the subsequent use of the common factor.
