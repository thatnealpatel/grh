# The finite local polar multiplicities in Theorem 1.7.1.1

**Printed passage.** Masullo, *The Music of the Primes*, §1.7.1,
printed p. 35, Theorem 1.7.1.1, from its heading through part (3).
For a continuous unitary Hecke character χ of a number field F, it
asserts:

1. Two finite local Euler factors at distinct residue characteristics
   have at most one common pole.
2. If χ = χ₀|·|_F^{s₀} with χ₀ algebraic, then, assuming Schanuel's
   conjecture, the only possible pole shared by infinitely many finite
   local factors is s = −i Im(s₀).
3. For finite-order χ, the at-most-one assertion is unconditional,
   with s = 0 the specified point.

Coverage stops before the paragraph about Sobolev topologies and
coefficient functionals. Chapter Markdown and PDF layout extraction
located the theorem and its Chapter 7 source. Raster OCR checked the
prose, and direct inspection of rendered pixel crops from the
[digest-verified PDF][source] spot-checked the heading, common-pole
wording, Schanuel condition, shift, infinite-place-count wording,
and unconditional clause on p. 35, as well as the source theorem
heading on p. 324 and the Six Exponentials citation on p. 325. The
detailed Chapter 7 proof locators below follow the extraction.

**Local calculation and provenance.** At a ramified finite place the
factor is one. At an unramified place v, for uniformizer π_v and
residue size q_v, it is the meromorphic reciprocal of
`1 − χ_v(π_v) exp(−s log q_v)`. The denominator has nonzero derivative
`log q_v` at every zero, so the poles are simple and are exactly the
solutions of `exp(s log q_v) = χ_v(π_v)`. Unitarity puts them on the
imaginary axis. The following track the arguments in Masullo's
Theorem 7.1.3.2, pp. 324–325:

- **Part (1):** The source theorem's part (1) treats the two places
  in an S-local stage at which χ is unramified. Enlarge the stage to
  include both given places, the ramified places, and the infinite
  places. By Masullo's subtraction argument, the difference of two
  common poles would be a common period in `(2πi/log q_v)ℤ` and
  `(2πi/log q_w)ℤ`. This difference is zero: Distinct underlying
  rational primes make `log q_v` and `log q_w` linearly independent
  over ℚ by unique prime factorization. The unit factor takes care
  of the ramified branch in the overview. This gives no lower bound
  on distances between distinct poles.
- **Part (2):** The two-finite-place step of source part (3.b) uses
  `exp((s+s₀) log q_v) = χ₀,v(π_v)`, an algebraic value at an
  unramified v. The norm twist is trivial on local units, so χ₀ is
  also unramified there. The value is algebraic because some power of
  the prime ideal is ray-principal and the algebraic infinity type
  makes the value on that power algebraic. The sign follows from
  `|π_v|_v = 1/q_v`. If `s ≠ −i Im(s₀)` then `s+s₀` has nonzero
  imaginary part, so
  `1, s+s₀` are ℚ-linearly independent. At two distinct residue
  characteristics the Four Exponentials consequence of Schanuel
  would make at least one of the two residue sizes and the two
  displayed character values transcendental. All four are
  algebraic. Infinitely many places supply two distinct residue
  characteristics, since there are at most `[F:ℚ]` places above any
  one rational prime. The assertion need not show that the candidate
  point is a pole at infinitely many places.
- **Part (3):** In the two-finite-place step of source part (3.a),
  a common exponent N kills the two finite-order character values.
  So `exp(Ns log q_v) = exp(Ns log q_w) = 1`, and the same
  common-period argument gives `Ns = 0`, hence `s = 0`.
  For existence at zero, finite-order class field theory gives the
  finite abelian extension cut out by χ. At its completely split
  finite places the unramified local value is one, regardless of
  the reciprocity sign convention, and Chebotarev supplies infinitely
  many such places. Compare the paragraph continuing Remark 7.1.3.1
  at the top of p. 324; existence does not follow from clearing N.

**Why the infinite-place-count claim does not need Schanuel.** For
part (2) as stated on p. 35, the reviewer can instead take *three*
places above distinct rational primes and use the unconditional Six
Exponentials Theorem cited by Masullo in his proof of part (3.b) on
p. 325. Use the two independent exponents `1, s+s₀` and the three
independent logarithms `log q_v`. All six exponentials would be
algebraic, a contradiction. Thus off the exceptional point, poles
can occur above at most two rational primes. This is an application
of Masullo's three-finite-place argument to the overview, not a
proof of the stronger two-place exclusion without Schanuel or of
any bound for a product that includes Archimedean factors. No
statement here concerns zeros of the completed L-function.

**Formal disposition: Open.** At accepted revision
`3809bb9a96263828effac6b53ee3cad23cf0cc54`, the checked normalizations
`Masullo.finiteHecke_localPolynomial_eval_uniformizer` and
`Masullo.finiteHeckeEulerFactor_eq_one_of_ramified` in
`Proofs/Theorems/FiniteHeckeCharacterEulerProduct.lean` identify the
pointwise denominator at an unramified place and the unit factor at
a ramified place. See the [ordinary-import audit][lean-audit]. These
statements do not identify meromorphic poles with simple denominator
zeros or formalize their common periods. In particular, the inverse
in the pointwise complex-valued definition is totalized at zero;
the value of that inverse at a denominator zero is not evidence of
a pole. No matching Lean endpoint for the paired meromorphic pole
claim or the two infinite-occurrence claims was found. A formal
proof would need the reciprocal-pole bridge, the prime-power period
argument on actual finite places, and the finite-order or algebraic
local-value and transcendence inputs as appropriate. The calculations
above are ordinary mathematical evidence, not a formal resolution.

Independent Yah reviewer `wZiKdKl` (output
`a5df416ef0412470bff27cc0cb81f41d0046906c`) separately checked the
rendered-source signs, the two- and three-place arguments, and the
scope of the nearby Lean signatures at the cited accepted revision.
The independent review found no matching Lean endpoint and did not
run a new Lean build.

[source]: ../sources/masullo/README.md
[lean-audit]: ../formalize/finite-hecke-half-plane.md
