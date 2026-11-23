# The first Hardy–Sobolev display omits the square

**Printed passage.** Masullo, *The Music of the Primes*, p. 36,
§1.7.2, third bullet, equation (1.7.2.2) and its surrounding
paragraph, from “The relevant topologies” through the definition
of an ℝ₊-modulated group. The text calls the displayed quantities
norms inducing subspace topologies. For the idèle class group
G = C_F, a > 0, and b ≥ 0, the display takes the square root
of the integral of **|f(g)|**, not its square, against the positive
weight

$$
w(g) = \max(|g|_G^{2a}, |g|_G^{-2a})
       (1 + |\log |g|_G|^2)^{b/2}
$$

times Haar measure. Chapter Markdown and PDF layout extraction
located the passage in the [digest-verified edition](../sources/masullo/README.md).
Direct inspection of rendered pixel crops checked the unsquared
modulus and the outside exponent 1/2 on p. 36, and the squared
modulus in the counterpart (1.8.2.2) on p. 44. Printed page numbers
are the corresponding one-based PDF ordinals.

**Literal obstruction.** Write N(f) for the displayed expression.
Take a nonzero smooth compactly supported bump in the log-norm
coordinate, pulled back along the idelic module. This is a radial
Schwartz–Bruhat test: It factors through the quotient by the compact
norm-one subgroup, and every real twist is still smooth and compactly
supported on that quotient. The idelic module is proper and surjective,
so the pullback has compact support and is nonzero on a nonempty open
set. Haar measure is positive on nonempty open sets and finite on
compacts, and the weight is continuous and strictly positive. Therefore
0 < N(f) < ∞. The displayed expression satisfies N(4f) = 2N(f),
not the norm requirement N(4f) = 4N(f). Its square is the weighted
L¹ norm, which induces the same topology as the distance
(f,h) ↦ N(f−h) on continuous tests where finite. Thus the defect
is not failure to describe *any* normable topology. Neither this
observation nor an outside monotone reparametrization supplies the
weighted L² norm.

**Comparison, not a proof of the repair's later uses.** The
squared-modulus formula on printed p. 44, §1.8.2.3, (1.8.2.2), is
also the form of the [p. 11 display](../formalize/radial-hardy-sobolev-completion.md)
with symmetric endpoints. The same comparison with the general
compact-interval formula (9.2.2.34), Lemma 9.2.2.10(2), p. 417, uses
I = [−a,a] and s = b, with canonical Haar there. A rendered crop
of (9.2.2.34) also confirms the squared modulus. Changing Haar by a
fixed positive scalar does not change the induced topology. This
comparison identifies the apparent intended correction; it does not
verify the passage's subsequent Mellin regularity or trace claims.

**Argument and Lean scope.** The displays are Masullo's; the scaling
obstruction and topology distinction are the reviewer's. Fresh
independent Yah reviewer `norm-display-reader` (output revision
`f093cf6fda27bdc9a142ecf1ccdf86bb0650756d`) checked the pinned
renders of both numbered equations, the homogeneity argument, and
the exact comparison signature. At accepted GRH revision
`dc858f7dd104d89538391e1cccbeed427becacdc`,
`Masullo.logSobolevToLp_positiveIntegral` in
[RadialHardySobolevCompletion](../../Proofs/Theorems/RadialHardySobolevCompletion.lean)
identifies the norm of the weighted L² image of a closed-interval
log profile with the square root of a *squared*-modulus integral.
It takes ordered real endpoints, real degree, the identity module
on ℝ₊, and normalized dt/t. It is comparison evidence for the
corrected radial formula, not a statement about the unsquared
expression, an arbitrary C_F, or the geometric trace. No new Lean
endpoint is claimed.
