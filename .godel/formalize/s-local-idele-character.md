# S-local descent and the trivial unitary base point

**Assignment** `43b86bfe3419289dc9b5f874c3cc975b3d16defbe19648c05ed3ad4bb7e55999`,
Walk record revision `422b22889832db04e8b2f15939301a25be0a82146ce5d953037bf5d9060a1248`.
The request named `main` at `dae367901690c1ac4732af839634d7979e12488b`;
the reconciled writer base is `8d6df0da8aaf7cc4fb066dd20b7270a231cb7eb9`.
The difference adds `.godel/walk/divisorial-filtration.md`, not character evidence.
The accompanying receipt identifies the defining files and endpoints.

## Reading

The source is Alessandro Maria Masullo, *The Music of the Primes*, pinned by
[the edition record](../sources/masullo/README.md), SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The writer checked the PDF's SHA-256 and read rendered pages (including
magnified text-terminal renderings of key displays; text extraction used to
locate passages). Printed pages equal one-based PDF ordinals below.

- **p. 12, chapter 1, §1.1.4 second bullet**: for an arbitrary continuous
  unitary character χ of \(C_F\), if χ is unramified outside a finite \(S\)
  containing the infinite places, \(\chi_S\) is the unique continuous
  character of \(J_{F,S}\) whose composition with the unnumbered quotient
  display equals the restriction of χ. The next sentence uses 1 as unitary
  base point of the component of χ when \(\chi|_{C_F^1}=1\), rather than the
  imaginary norm twist representing χ. The bullet itself is not a proof.
- **pp. 98–99, §2.3 opening and first paragraphs**: the group in the middle
  is \(C_{F,S}\). It embeds openly and injectively in \(C_F\), and the image
  in it of \(\Gamma=\{1\}\times\prod_{v\notin S}\mathcal O_{F_v}^{\times}\)
  is the compact closed kernel of the quotient to \(J_{F,S}\). This passage
  discusses norm-one characters. Its hypothesis on \(\mathrm{Pic}(\mathcal
  O_{F,S})\) is for the isomorphism \(C_{F,S}\simeq C_F\) and that converse
  extension, not forward descent from a supplied χ.
- **p. 543, Appendix A.1.5.1**, (A.1.5.1)–(A.1.5.3) and the intervening
  definition: \(\mathrm{GL}_1(\mathbf A_{F,S})\) is the product of the
  multiplicative *field* groups at the places in \(S\), and the definition
  of \(\mathcal O_{F,S}\) requires integrality outside \(S\). A unit of this
  subring requires that condition for both the element and its inverse.
  **p. 544, A.1.5.3**, (A.1.5.7) includes the outside integral-unit product
  in \(C_{F,S}\); **p. 120, §3.1.2**, (3.1.2.1) omits it in \(J_{F,S}\).
  Both groups divide by the diagonally embedded \(S\)-units in the relevant
  ambient group. Product topologies precede quotient topologies.
- **p. 121, §3.1.2.3**, (3.1.2.6) defines unramifiedness by triviality of
  each outside local unit restriction; (3.1.2.7)–(3.1.2.8) insert ones at
  the outside places into a global idele; (3.1.2.9) denotes the resulting
  global-to-local operation. The insertion is on *representatives*: an
  inserted diagonal \(S\)-unit need not be globally principal. The values
  of a character satisfying (3.1.2.6) must be shown invariant under the
  local quotient relation.
- **pp. 118–119, §3.1.1**: the topology on \(\Omega(G)\) is compact-open,
  with values in \(\mathbb C^\times\). Display (3.1.1.1) restricts to the
  compact norm-one subgroup, with discrete dual, and the following display
  for a real-positive module identifies the fibres as
  \(\{\chi|\cdot|^s:s\in\mathbb C\}\). The component notation below those
  displays places the trivial norm-one character in the fibre of 1. The
  statement here concerns this particular fibre for the actual idelic norm,
  not the discretely modulated case or a choice of base point in all fibres.

## Argument and scope

`Theorems.SLocalIdeleCharacter` takes `S` to be the finite-place portion of
\(S\) and includes all `InfinitePlace K` automatically. Write \(B\) for
the active product and \(U\) for the product of outside integral units.
The accepted `IdeleFiniteStage` identifies \(B\times U\), up to
reassociation, with an open subgroup of the actual ideles. By
`range_ideleFiniteStageEmbedding`, the intersection of its image with
the diagonals of \(K^\times\) consists exactly of the diagonals of
\(\mathcal O_{K,S}^{\times}\): at every outside place the element and its
inverse must both be integral. The new `mem_ideleStagePrincipal_iff`
expresses this criterion on stage elements. Let \(N\) be the principal
relation so obtained, and let \(M=p(N)\) for active projection \(p\).
Thus \(C_{F,S}=(B\times U)/N\) and \(J_{F,S}=B/M\).

The open embedding passes to the former quotient since \(N\) is the
preimage of the principal relation. The projection factors to an open
continuous surjection of quotients: its composite with the stage quotient
is the open surjection obtained from the product projection and the
local quotient; the stage quotient is itself open and surjective. If
\([x]\) is in the kernel, its active components equal \(p(n)\) for some
\(n\in N\), so \([x]=[x/n]\) is represented with only outside components.
Conversely, every outside element maps to 1. The outside product is compact
by `compactSpace_finiteCompletionIntegralUnits` and product compactness;
its image is closed by the Hausdorff property of the actual class group
(`t2Space_ideleClassGroup`) and the open embedding of the stage classes.

The accepted `ideleFiniteStage_character_factor` identifies the character
evaluation on any stage element with just the product of its active local
values when the character is unramified at each outside place. The key
continuity step there kills the full outside product, not just elements
with finite support. Consequently insertion of ones leaves a stage
character evaluation unchanged. For \(b=p(n)\) with \(n\in N\), the
value at the insertion of \(b\) is the value of the global character at
the principal element \(n\), namely 1. So the insertion evaluation gives
an invariant continuous homomorphism on \(B/M\), using the quotient
continuity criterion. It has the specified pullback, is unique by
surjectivity, and preserves unitarity. The construction works also for a
quasi-character not assumed unitary. No assumed extension to the whole
idele class group is used beyond the original χ supplied in the bullet.

`Theorems.IdeleClassCharacterComponent` transfers the compact-open topology
from the \(\mathbb C^\times\)-valued realization to mathlib's
`HeckeCharacter` (continuous multiplicative maps to \(\mathbb C\) from a
group, hence everywhere nonzero). The coefficient inclusion is an
embedding, so is its compact-open postcomposition; it is surjective on
these homomorphisms by lifting values to units. Compactness of the actual
norm-one group (`compactHausdorff_ideleClassNormOne`) forces unit modulus
there: the values of powers of any element are bounded, and the same
holds for its inverse. Restriction into its discrete Pontryagin dual is
continuous by precomposition and compact-open evaluation on that compact
group. A connected component containing 1 therefore lies in the fibre
over the trivial restriction.

The accepted `ideleClassLogNorm_section` gives a continuous homomorphic
section of the actual log norm. If χ kills the norm-one group, dividing
an idele class by the section at its log norm does not change χ, so χ
is reconstructed from its section restriction. For a continuous
multiplicative one-parameter function \(h\), continuity and additivity of
\(\log|h|\) give \(\log|h(t)|=a t\). Dividing out \(e^{at}\) gives a unitary
one-parameter function, to which `existsUnique_unitary_oneParameterCharacter`
applies. Hence \(h(t)=\exp(st)\), with uniqueness also seen from the
derivative at zero. This identifies the fibre with all complex norm
powers, with unique exponent. They form a connected set through 1 by
joint continuity of the exponential formula inducing a continuous map
for the compact-open topology. This proves the reverse component
inclusion. Evaluating the modulus at log norm 1 shows that unitarity is
equivalent to \(\Re(s)=0\); the reverse implication is immediate for all
classes. The resulting `ideleClass_trivial_basePoint` gives membership of
1 in the component of χ and the unique imaginary exponent of the original
unitary χ. The value of 1 has unit modulus, so this is the printed choice
of unitary base point.

This covers the assigned descent and component claims. It does not prove
all the surrounding statements: no converse global extension, continuity
as a family on the whole unramified character locus, surjectivity or local
analytic isomorphism of (3.1.2.9), complex manifold structure, or θ-function
claim is asserted. These are not needed to define the descended continuous
characters or to choose 1 as the unitary base point.

## Replay

Run from the exact candidate workspace with the pinned `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`:

```sh
lake build --wfail +Theorems.SLocalIdeleCharacter +Theorems.IdeleClassCharacterComponent
receipt=.godel/formalize/43b86bfe3419289dc9b5f874c3cc975b3d16defbe19648c05ed3ad4bb7e55999-422b22889832db04e8b2f15939301a25be0a82146ce5d953037bf5d9060a1248.json
check=$(mktemp --suffix=.lean)
{
  printf '%s\n' 'import Theorems.SLocalIdeleCharacter' 'import Theorems.IdeleClassCharacterComponent'
  jq -r '.evidence[].declarations[] | "#check @\(.)\n#print axioms \(.)"' "$receipt"
} > "$check"
lake env lean "$check"
```

The following ordinary-import client uses the constructed descent to
evaluate on representatives, proves equality for competitors with the same
pullback, and uses the base-point theorem on actual classes. Save the
block to a fresh `.lean` file and run `lake env lean` on it.

```lean
import Theorems.SLocalIdeleCharacter
import Theorems.IdeleClassCharacterComponent

open IsDedekindDomain NumberField Topology Masullo

variable {K : Type*} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (χ : HeckeCharacter (𝓞 K) K) (hS : ∀ v ∉ S, χ.IsUnramifiedAt v)

-- Descend an actual idelic character, evaluate on arbitrary local representatives,
-- and use the quotient projection to evaluate on arbitrary stage classes.
example (b : SLocalIdeles K S) (x : IdeleFiniteStage K S) :
    ∃ ψ : SLocalIdeleClasses K S →ₜ* ℂ,
      ψ (QuotientGroup.mk b) =
        χ (QuotientGroup.mk (ideleFiniteStageEmbedding K S (ideleStageInsert K S b))) ∧
      ψ (QuotientGroup.mk (ideleStageProject K S x)) =
        χ (QuotientGroup.mk (ideleFiniteStageEmbedding K S x)) := by
  refine ⟨sLocalCharacter K S χ hS, sLocalCharacter_mk K S χ hS b, ?_⟩
  rw [← ideleStageToLocal_mk, sLocalCharacter_pullback, ideleStageToClass_mk]

example (hχ : ∀ c, ‖χ c‖ = 1) (y : SLocalIdeleClasses K S) :
    ∃ ψ : SLocalIdeleClasses K S →ₜ* ℂ,
      (∀ z, ψ (ideleStageToLocal K S z) = χ (ideleStageToClass K S z)) ∧
      ‖ψ y‖ = 1 := by
  exact ⟨sLocalCharacter K S χ hS, sLocalCharacter_pullback K S χ hS,
    sLocalCharacter_unitary K S χ hS hχ y⟩

example (ψ : SLocalIdeleClasses K S →ₜ* ℂ)
    (hp : ∀ z, ψ (ideleStageToLocal K S z) = χ (ideleStageToClass K S z)) :
    ψ = sLocalCharacter K S χ hS := by
  obtain ⟨ψ₀, _, huniq⟩ := sLocalCharacter_existsUnique K S χ hS
  exact (huniq ψ hp).trans (huniq _ (sLocalCharacter_pullback K S χ hS)).symm

example (z : IdeleStageClasses K S) (hz : ideleStageToLocal K S z = 1) :
    ∃ w : OutsideSUnits K S,
      (QuotientGroup.mk (ideleStageOutside K S w) : IdeleStageClasses K S) = z ∧
      χ (ideleStageToClass K S z) = 1 := by
  have hk : z ∈ (ideleStageToLocal K S).toMonoidHom.ker := hz
  rw [ker_ideleStageToLocal] at hk
  obtain ⟨w, hw⟩ := hk
  exact ⟨w, hw, character_eq_one_on_ideleStageToLocal_kernel K S χ hS z hz⟩

-- Use the printed unitary base point and obtain the value of the original
-- character on *all* actual classes from its (unique) imaginary exponent.
example (hu : ∀ c, ‖χ c‖ = 1) (h₁ : ∀ c : ideleClassNormOne (K := K), χ c = 1)
    (c : IdeleClassGroup (𝓞 K) K) :
    (1 : HeckeCharacter (𝓞 K) K) ∈ connectedComponent χ ∧
      ∃ t : ℝ, χ c = (ideleClassNorm c : ℂ) ^ ((t : ℂ) * Complex.I) := by
  obtain ⟨hcomp, t, ht, _⟩ := ideleClass_trivial_basePoint χ hu h₁
  refine ⟨hcomp, t, ?_⟩
  rw [ht, ideleClassNormPower_apply]

-- Recover equality of two genuine unit-valued quasi-characters from the
-- complex-valued model, using its verified compact-open homeomorphism.
example (a b : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ)
    (h : ∀ c, (a c : ℂ) = (b c : ℂ)) : a = b := by
  apply ideleClassQuasiCharacterHomeomorph.injective
  ext c
  rw [ideleClassQuasiCharacterHomeomorph_apply, ideleClassQuasiCharacterHomeomorph_apply, h]
```
