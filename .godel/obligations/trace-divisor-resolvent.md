# Subtracted resolvents determine the noncentral weights

**Status: Lean residue endpoint.** [`Masullo.subtractedResolvent_weight_eq_zero`](../../Proofs/Lemmas/SubtractedResolvent.lean) proves the residue step of the [Chapter 13 uniqueness repair](trace-divisor-uniqueness.md#a-one-sided-moment-uniqueness-lemma). This is a project argument, not a proof supplied in the manuscript. The provisional text interface is the zero-moment condition (13.3.1.2) and capped sum (13.3.1.3), p. 522 of the [pinned edition](../sources/masullo/README.md). The lemma takes local agreement of the subtracted series as a hypothesis. It does not identify the capped trace with the full-zero distribution.

## Interface

Use an injective countable family $w_i$ with no finite accumulation: At each $z$ a positive distance separates $z$ from all $w_i\ne z$. The anchor $z_0$ must have a uniform positive gap from the family. The summability hypothesis is $\sum_i |d_i|/(1+|w_i|)^2<\infty$. If the sum of the subtracted terms agrees near a point outside $\{w_i\}\cup\{0\}$ with a function analytic off zero, then $d_i=0$ whenever $w_i\ne0$. Nothing here detects the weight at zero.

## Proof and checks

On a small ball with a gap from the active poles, each denominator grows at least linearly with $1+|w_i|$. The two factors thus give a summable uniform majorant. Mathlib's holomorphic sum theorem gives analyticity on the ball. Analytic uniqueness propagates the local agreement on the connected complement of the countable excluded set. At $w_i\ne0$, set $d_i$ temporarily to zero to obtain a remainder analytic there. In the identity off the poles, multiply by $z-w_i$ and take the continuous limit along the dense complement. At the center the left side is zero, and the right side is $d_i$. The original series is never evaluated at its pole.

Independent Yah review confirmed the draft's sign, pole hypotheses, and noncentral conclusion, and checked how the half-plane identity supplies local agreement. The Lean implementation keeps the reviewed statement unchanged. Release checks are `lake --wfail build Proofs`, `lake env leanchecker Lemmas.SubtractedResolvent`, and `#check` and `#print axioms` for the endpoint.

## Assembled conditional uniqueness

[`Masullo.weight_eq_zero_of_zero_mass_annihilation`](../../Proofs/Props/ZeroMassUniqueness.lean) composes the [cutoff series endpoint](trace-divisor-cutoff.md#lean-endpoint) and the residue theorem. It requires an injective countable pole family with the stated separation, a bound $\Re w_i\le a$ with $a\ge0$, weighted summability, and annihilation on all compactly supported smooth positive-log tests of mass zero. It concludes $d_i=0$ for $w_i\ne0$.

The proof chooses $z_0=a+1$. The real-part bound gives a uniform anchor gap of at least $z_0-a$. The inequality $1+t^2\le(1+t)^2$ supplies the residue theorem's summability. The cutoff theorem gives a single coefficient $c$ for the whole open half-plane $\Re z>a$. There, both denominators are nonzero, so each reciprocal difference can be rewritten as $d_i(z_0-z)/((z-w_i)(z_0-w_i))$ **inside** the sum. Agreement with $G(z)=(z^{-1}-z_0^{-1})c$ on this open set gives the required neighborhood identity at $z_0$. The two unsubtracted series need not converge.

Independent Yah statement review confirmed the subtraction sign, anchor and half-plane bounds, and noncentral conclusion. The public documentation distinguishes the aggregated weights and complex test premise from the manuscript. The transform is the existing public `positiveLaplaceTest` in `Lemmas.CompactTestLaplace`, reexported by the cutoff modules, and the summability conversion is explicit in the proof.

Audit the assembled endpoint with `lake --wfail build Proofs`, `lake env leanchecker Props.ZeroMassUniqueness`, and `#check` and `#print axioms` for `Masullo.weight_eq_zero_of_zero_mass_annihilation`. The [zeta-family geometry](trace-divisor-uniqueness.md#checked-separation-of-the-shifted-zeta-zeros) is now in Lean. Weighted summability and the full-versus-capped comparison are still separate obligations. The real-place normalization still needs image-capable review.
