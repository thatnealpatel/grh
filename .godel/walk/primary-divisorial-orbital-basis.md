# The successive principal-value quotient and its orbital basis

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.2,
printed p. 27, from “But now the subquotient” through “Orbital
Schauder basis!” Write $H$ for the norm-one character isotype of
the global theta quotient on the two-zero-moment test space
$\mathcal S_0(\mathbf A_F)$. The display is
$\mathrm{PV}_{P_k}H/\mathrm{PV}_{P_{k+1}}H$. Masullo calls this a
copy of $\mathscr E_{S_p}(\chi|_{C_F^1})$ with its own orbital
Schauder basis. The printed target uses $p$ without a $k$ index;
the preceding product identity makes $p=p_{k+1}$ the natural
reading. The lead-in, display indices, and conclusion were
spot-checked in rendered pixel crops of the
[pinned PDF](../sources/masullo/README.md), SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Chapter Markdown, PDF text extraction, and raster OCR were used
separately. The next list, on chopping kernels and computing
traces, is not covered here.

**The comparison map.** Set $A=\mathrm{PV}_{P_k}$ and
$B=\mathrm{PV}_{S_{p_{k+1}}}$ using one consistent convention. The
new set of places is exactly $P_{k+1}\setminus P_k$, so the
commuting products give $\mathrm{PV}_{P_{k+1}}H=ABH$. The target
of the printed comparison is $H/BH$ by (7.4.0.2), p. 366. The
natural map $H/BH\to AH/ABH$ sends $[h]$ to $[Ah]$. It is a
continuous surjection with kernel $(BH+\ker A)/BH$. If $A$ is a
topological embedding on $H$, it is a linear topological
isomorphism in the indicated direction: The continuous inverse
on $AH$ takes $ABH$ to $BH$ and descends to the quotient. Both
maps respect the translation action when the factors commute
with translations. Closedness of $BH$ then also makes $ABH$
closed in $AH$. This comparison concerns principal-value images;
it neither identifies them with images of all coordinate cuts
nor uses the false unrestricted cut containment from the
[preceding passage](primary-divisorial-theta-range.md).

**What is missing.** The embedding must be in the intrinsic
global theta topology, not on adelic tests before taking the
quotient. For the later unit-averaged operators, Lemma 5.3.1.5,
p. 242, states a closed embedding on the full theta quotient for
each finite product. Together with Lemma 5.5.2.1, p. 280, on
descent of the moments, this would restrict to the closed
norm-one isotype in the joint kernel, with its intrinsic
quotient topology. The [closed-embedding gap](global-orbital-submodule.md)
remains: Openness on the whole test space does not imply relative
openness on the principal-value range, and a fixed-stage
intertwining identity does not put the whole global image in
that stage. The literal introductory uniformizer differences
agree with the later unit-averaged factors when the isotype is
unramified at all relevant places, not merely when the tested
fiber is contained in $S$. Without agreement one needs a
comparison for the actual operators in the passage. In
particular, the averaged factor at a ramified place is the
identity, not the literal difference.

**The basis is a separate input.** The intermediate quotient
in (7.5.0.4), p. 375, and its comparison diagrams are Masullo's
later analogue of this step. One route to a basis for $H/BH$ is
the topological comparison in Theorem 7.5.0.1, pp. 374–378, with
the quotient of the exponentially decaying Schwartz isotype by
the matching periodic difference product. This needs the
preimage of the model's difference range under the theta
embedding to equal $BH$, surjectivity modulo that range, and
continuity of the inverse in the stated topologies. Separation
by the relevant jets on the actual quotient does not follow
just from their topological freeness. Transport of the
[local basis](local-orbital-schauder-basis.md) also needs the
correct zero-moment quotient and a checked range comparison.

Theorem 4.6.1.5, p. 212, is a proposed source of the model
basis. The actual log-norm shifts above one rational prime are
$\log q_v=f_v\log p$, so they are commensurable. The printed
statement defines $b_k=\log|\gamma_k|_G$ but then imposes
commensurability on $\log b_k$ and uses $\log b_k$ in the
frequency denominator. Commensurability of $\log q_v$ is not
verification of the stated double-log condition. The basis
argument must use the actual shifts and the correct jet
multiplicities at shared frequencies. Chapter 11 repeats the
basis claim at (11.3.1.3), p. 494, but then uses
Paley-Wiener-restricted spaces, and §11.2.2, pp. 489–491,
discusses biorthogonal systems on Sobolev quotients. Neither
is a proof of Schauder convergence on this intrinsic quotient.
The later readings here are provisional, from chapter Markdown
and PDF text extraction, not direct rendered-page inspection.

**Disposition.** The quotient identification and orbital basis
assertion are Masullo's. The quotient map and its conditional
transport argument are the reviewer's. The claimed intrinsic
topological identification and Schauder basis remain open. No
Lean declaration is claimed for either.
