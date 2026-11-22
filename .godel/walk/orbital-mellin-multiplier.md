# Mellin multiplier of the finite-place principal-value product

**Printed passage.** Masullo, *The Music of the Primes*, §1.2.9,
printed p. 18, claim beginning “Here comes the main observation”
and its display. The Mellin transform is said to turn $\mathrm{PV}_{S_p}$
into multiplication by the finite product of entire reciprocal Euler
factors $\prod_{v\in S_p}L_v(\chi_v|\cdot|_v^s)^{-1}$. The preceding
definition uses the literal uniformizer differences $1-T_{\pi_v}$,
where $T_a f(x)=f(a^{-1}x)$, and does not require unramifiedness at
$v\mid p$. The statement and display were checked in a crop rendered
from p. 18 of the pinned PDF (SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`),
separately from the chapter Markdown, PDF text extraction, and raster OCR.
The subsequent analogy and basis assertion are separate passages.

**Actual multiplier.** Write $c=\chi|\cdot|^s$. In the half-plane of
absolute convergence, the transform integrates $f(x)c(x)$ against
multiplicative Haar. The substitution $x=ay$ gives
$Z(T_af,c)=c(a)Z(f,c)$; the same calculation applies to $Z_S$ at a
finite stage containing the support of $a$. The identity persists after
meromorphic continuation and descent to the theta quotient where those
are available. Thus the literal product multiplies by
$\prod_{v\in S_p}(1-\chi_v(\pi_v)q_v^{-s})$. Each factor is entire in
$s$, but equals the reciprocal Euler factor at that place only in
the unramified case. At a ramified place the reciprocal Euler factor
is $1$, not $1-c_v(\pi_v)$. The two-zero-moment restriction does not
remove this discrepancy.

For example, take $F=\mathbf Q$, $p=3$, and the [odd quadratic
idele-class character of conductor 3](../obligations/global-mellin-sign-q.md#an-odd-character-and-an-absolutely-convergent-witness).
Its component at $3$ has $\chi_3(3)=1$ and is nontrivial on units.
Use the tensor test with real factor $x e^{-\pi x^2}$, $3$-factor
$\chi_3^{-1}\mathbf 1_{\mathbf Z_3^\times}$, and unit-ball indicators at
all other finite places. The test vanishes at zero and its additive
integral is zero by oddness of the real factor, so its Fourier value at
zero vanishes too. At $c=\chi|\cdot|^2$, its Mellin transform is
positive: The archimedean and $3$-integrals are positive, and each
remaining unit-ball integral is $(1-\chi_\ell(\ell)\ell^{-2})^{-1}$,
whose product converges absolutely to a positive number. The test
has the indicated norm-one isotype: The real signs and the local
units act by the quadratic character, and every rational idele class
of norm one has a representative with real component of absolute
value one and all finite components units, by clearing valuations.
The literal difference gives the multiplier $1-3^{-2}=8/9$ at this
point, whereas the printed reciprocal Euler factor is $1$.

**Scope of the later formula.** With $U_v$ the normalized local unit
average, Masullo's later factor $1-T_{\pi_v}U_v$ multiplies by
$1-c_v(\pi_v)\int c_v(u)\,du$, with the integral over local units.
That integral is one for the trivial unit character and zero otherwise,
so the later product gives precisely the stated Euler factors. For the
literal product the uniform sufficient hypothesis is unramifiedness
at every $v\mid p$. Alternatively, replacing the literal factors by
the later ones repairs the multiplier on arbitrary isotypes, but is
not the same operator there. See the [operator audit](global-orbital-submodule.md)
for the rendered definitions on pp. 241–242. This calculation neither
proves a closed-range result nor identifies the topology or basis of
an orbital quotient.

**Provenance and disposition.** The formulas and operators are
Masullo's. The translation and averaging calculations and the use of
the conductor-three example to test this multiplier are the reviewer's.
Lemma 5.1.3.1(1)–(2), p. 227, states the Mellin translation identity;
Proposition 5.3.4.5(1), p. 264, gives (5.3.4.12) for the later
$S$-local operator. Those readings, and the finite Euler factor
convention at (3.2.1.1) and (3.2.1.7), pp. 122 and 124, are
provisional, from chapter Markdown and PDF text extraction.
The accepted Lean declarations `Masullo.finiteHecke_localPolynomial_eval_uniformizer`
and `Masullo.finiteHeckeEulerFactor_eq_one_of_ramified` in
`Proofs/Theorems/FiniteHeckeCharacterEulerProduct.lean` at
`2001482d42d23f06788f7c2309567ac1e57b1cf8` concern local polynomials
and the unit Euler factor, not a Mellin intertwining statement on a
theta quotient. The printed general claim remains open in the formal
ledger; neither the corrected operator formula nor the unramified
specialization is recorded as establishing it.
