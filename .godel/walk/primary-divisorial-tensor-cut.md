# The primary unit cut on a supplied tensor

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.2,
printed p. 26, from “The primary divisorial stratification ...
adapts itself nicely” through the unnumbered tensor equality.
Masullo cites (11.3.1.1), defines $\alpha_k$ as the indicator of the
$k$th primary locus, and multiplies the displayed test by it. The
left side uses the integer-ring tensor indexed by $v\notin S$.
On the right, he retains $f_S$, puts the integer-ring indicators
at $v\in S-P_k$, and puts the unit-group indicators at $v\in P_k$.
The cited equation on printed p. 492 gives the same input shape
as (1.3.2.1), with $f_S$ a local Schwartz–Bruhat test. Coverage
here stops before the ensuing assertion about the zeta function.

Chapter Markdown and PDF layout extraction located both passages.
The PDF matched the [edition pin][source]. Raster OCR recovered
the p. 26 lead-in and indicator sentence. Direct inspection of
rendered crops checked the indicator subscript and the tensor
indices, in particular the slash on the left and its absence in
the middle index on the right. A rendered crop of p. 492 also
confirmed the outside-$S$ index of the cited input.

**Checked scope.** Let $D_k$ be the explicit coordinate locus:
All components at places in $P_k$ are integer units. For a supplied
test in the displayed input form, apply Masullo's p. 25 local
indicator identity to each tested coordinate outside $S$. If
$P_k\cap S=\varnothing$, the result of multiplying by $1_{D_k}$
on idèles is the restriction of the Schwartz–Bruhat tensor

$$
f_S\otimes\bigotimes_{v\notin S\cup P_k}1_{\mathcal O_{F_v}}
   \otimes\bigotimes_{v\in P_k}1_{\mathcal O_{F_v}^{\times}}.
$$

The [local tensor check][tensor] supplies the pointwise calculation:
At a tested coordinate, the intersection of the integer ring and
its units is the units, and at every untouched coordinate the old
factor is unchanged. The printed $S-P_k$ is not the required
complement of $S\cup P_k$. Even for disjoint sets it repeats
coordinates already in $f_S$ and omits the untested coordinates
outside $S$.

The disjointness condition for the products in (1.3.2.2) is not
ensured for the literal first-$k$ rational-prime fibers at p. 26.
For a coordinate cut with overlap, the correct local factor is
$f_S$ times the product of the unit indicators at $P_k\cap S$;
only $P_k\setminus S$ contributes a new outside-$S$ unit factor.
Thus retaining $f_S$ also requires disjointness or a support
condition making the in-$S$ cut redundant. In the disjoint case
the [norm-preimage comparison][norm] gives the same product on
the supplied test, not the same indicator on all idèles.

This checks a corrected pointwise formula on a supplied test, not
the tensor equality as printed. It needs no fixed-stage theorem
supplying representatives for a whole theta isotype. It does not
prove preservation of the two zero moments, descent independent
of the representative, or an assertion about a zeta function or
a trace. The finite-factor calculation is the reviewer's
application of Masullo's local mechanism. There is no Lean
statement for this check.

[source]: ../sources/masullo/README.md
[tensor]: stratification-tensor-compatibility.md
[norm]: primary-divisorial-norm-preimage.md
