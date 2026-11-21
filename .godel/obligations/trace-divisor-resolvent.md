# Subtracted resolvents determine the noncentral weights

**Status: Lean residue endpoint.** [`Masullo.subtractedResolvent_weight_eq_zero`](../../Proofs/Lemmas/SubtractedResolvent.lean) proves the residue step of the [Chapter 13 uniqueness repair](trace-divisor-uniqueness.md#a-one-sided-moment-uniqueness-lemma). This is a project argument, not a proof supplied in the manuscript. The provisional text interface is the zero-moment condition (13.3.1.2) and capped sum (13.3.1.3), p. 522 of the [pinned edition](../sources/masullo/README.md). The lemma takes local agreement of the subtracted series as a hypothesis. It does not identify the capped trace with the full-zero distribution.

## Interface

Use an injective countable family $w_i$ with no finite accumulation: At each $z$ a positive distance separates $z$ from all $w_i\ne z$. The anchor $z_0$ must have a uniform positive gap from the family. The summability hypothesis is $\sum_i |d_i|/(1+|w_i|)^2<\infty$. If the sum of the subtracted terms agrees near a point outside $\{w_i\}\cup\{0\}$ with a function analytic off zero, then $d_i=0$ whenever $w_i\ne0$. Nothing here detects the weight at zero.

## Proof and checks

On a small ball with a gap from the active poles, each denominator grows at least linearly with $1+|w_i|$. The two factors thus give a summable uniform majorant. Mathlib's holomorphic sum theorem gives analyticity on the ball. Analytic uniqueness propagates the local agreement on the connected complement of the countable excluded set. At $w_i\ne0$, set $d_i$ temporarily to zero to obtain a remainder analytic there. In the identity off the poles, multiply by $z-w_i$ and take the continuous limit along the dense complement. At the center the left side is zero, and the right side is $d_i$. The original series is never evaluated at its pole.

Independent Yah review confirmed the draft's sign, pole hypotheses, and noncentral conclusion, and checked how the half-plane identity supplies local agreement. The Lean implementation keeps the reviewed statement unchanged. Release checks are `lake --wfail build Proofs`, `lake env leanchecker Lemmas.SubtractedResolvent`, and `#check` and `#print axioms` for the endpoint.

## Next runnable step: Assemble the conditional uniqueness proposition

Compose with the [checked cutoff series endpoint](trace-divisor-cutoff.md#lean-endpoint-and-next-check), keeping test-class annihilation explicit. Use the open half-plane $\Re z>a$ and take $G(z)=(z^{-1}-z_0^{-1})c$ with the single coefficient returned by the cutoff theorem. The real anchor $z_0>a\ge0$ is itself outside the excluded set, and $z_0-a>0$ bounds the anchor gap below. Summability with denominator $1+|w_i|^2$ implies the residue lemma's weighted summability by $1+t^2\le (1+t)^2$ for $t\ge0$.

Before taking the sum, rewrite each reciprocal difference as the single fraction $d_i(z_0-z)/((z-w_i)(z_0-w_i))$, using the half-plane inequalities to show that both denominators are nonzero. The two unsubtracted reciprocal series need not converge. The eventual equality at the anchor follows from the identity throughout the open half-plane. This assembly is not yet in Lean. The full-versus-capped comparison and the zeta-family inputs remain separate obligations, and the real-place normalization still needs image-capable review.
