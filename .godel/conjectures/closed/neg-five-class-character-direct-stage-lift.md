---
evidence_revision: b3ef7d2334043e14616016e40d44222923cc6a04
outcome: established
---

# Direct lift of the common divided pair at the class-character stage

Let $F=\mathbb Q(\sqrt{-5})$, let $\chi$ be its nontrivial
ideal-class character, and fix
$S''=S_\infty\cup\{\mathfrak p_2,\mathfrak p_5\}$. Use the
corrected two-ended $AS$ topology, the trace-dual Fourier
transform, and Masullo's measures. Let $\Lambda$ be the
manuscript's entire completed Hecke factor, and put
$D(s)=(1+2^{-s})(1-5^{-s})L(s,\chi_{-4})L(s,\chi_5)$.

**Proposed implication:** For every $\Phi\in AS(\mathbb C)$
with $\Phi=\Lambda V$ for some $V\in\mathcal O(\mathbb C)$,
the holomorphically extended pair
$(\Phi(s)/D(s),\Phi(s)/D(1-s))$ on $\Re s>0$ and $\Re s<1$,
respectively, is $U_{S'',\chi}([f])$ for one class of the full
local isotypic Schwartz quotient. Its actual insertion
satisfies $(L\circ\overline\pi_{S''})([f])=\Phi$ exactly. No
reflection symmetry of $\Phi$ or moment condition on $f$ is
assumed.

**Source and payoff:** The
[accepted divisor comparison](../closed/neg-five-class-character-divisor-orders.md)
identifies the scalar jet conditions and explicitly leaves
local pair membership open. This is a proposed direct use
for (6.3.2.3), p. 304, via (6.3.2.10)–(13), pp. 305–306,
at this stage alone, distinct from closedness and from the
pre-existing archimedean realization.

**Discriminating test:** Check the hypotheses of the
interior-strip division estimate for each actual quotient,
transporting the left estimate by holomorphic reflection.
Compute the local forward-over-reflected ratio on the
Gaussian tensored with the two retained balls. Compare with
the continued ratio $D(1-s)/D(s)$, tracking the two retained
unit masses and the direction of the trace-dual Fourier
factor. Extend through shared zeros without dividing by
$\Phi$. Check a non-symmetric target off the central line
against a wrong ratio. Apply the full local image criterion
and the exact insertion only if these conditions hold;
contrast with independent numerators satisfying only jets.

## Proof for the stated character and stage

All obligation references below are to `isotypic-…-q-sqrt-minus-five.md`
at the evidence revision. The divisor comparison there (lines 77–82)
settles orders, not the two-leg condition. The norm-one idèle with
components $\sqrt2,\varpi_2,1$ has character $-1$, whereas the section
$t\mapsto(\sqrt t,1,1)$ has trivial character. Inverting the nonprincipal
prime over $2$ kills the class group. Thus (6.3.2.10) uses the full
quotient (5.2.2.4), with no moment condition, polar factor, or shift;
the dual variable is $1-s$ and $\chi^{-1}=\chi$.

**Division on both domains.** Write $D=UD_f$, where
$U(s)=(1+2^{-s})(1-5^{-s})$. Put $G(s)=2\pi(2\pi)^{-s}\Gamma(s)$
and $E(s)=20^{1/2-s}$. The landed identities are
$2\pi\Lambda=GD_f$ and $\Lambda(s)=E(s)\Lambda(1-s)$. Consequently
for the *same* $V$ in the premise the divided pair is
$$
 P_+(s)=\frac{V(s)G(s)}{2\pi U(s)},\qquad
 P_-(s)=\frac{V(s)E(s)G(1-s)}{2\pi U(1-s)}.
$$
The first expression is holomorphic on $H_+=\{\Re s>0\}$, the second
on $H_-=\{\Re s<1\}$: Neither Euler denominator vanishes in its
respective domain. These identities include cancellation to full order.

For growth, use `forward-division`, lines 69–134. Its hypothesis on
$h$ is $h\in AS(H_+)$ with $h/D$ holomorphic there. For this $D$,
bounded partial sums of each periodic nonprincipal character give
$L(s,\psi)=O_{a,b}(1+|\Im s|)$ on $0<a\le\Re s\le b$ by summation
by parts. At every $A>1$ the Euler products give
$|D(A+it)|\ge (1-2^{-A})(1-5^{-A})/\zeta(A)^2$. These are the
polynomial disk bound and nonzero anchor needed by the interior-circle
estimate. For an interior strip $I$ it gives
$p_{I,n}(h/D)\le C p_{J,n+K}(h)$ with $J$ still interior, where
$p_{I,n}$ uses the weight $(1+|t|)^n$. Take first $h(w)=\Phi(w)$,
then $h(w)=\Phi(1-w)$ on $H_+$. The latter quotient is $P_-(1-w)$,
not $\Phi(1-s)/D(1-s)$ in the original left variable $s$. Both
numerators have all the required seminorms by whole-plane membership.
Reflection takes $[a,b]$ to $[1-b,1-a]$ and preserves $|t|$. Thus
both legs belong to their stated spaces with the corrected two-ended
topology; Cauchy on wider interior strips gives the derivative bounds.
No growth assumption on $V$ has been made.

**Which ratio?** In `fourier-gluing`, lines 82–106 and 307–359,
the different $(2\sqrt{-5})$ gives $(q,d,a)=(2,2,-1),(5,1,1)$,
where $a=\chi_v(\varpi_v)$. A ball has Mellin transform
$u_v/(1-aq^{-s})$, with $u_v=q^{-d/2}$ by (A.3.2.2). Its Fourier
transform is $q^{-d/2}1_{\varpi_v^{-d}O_v}$. Relative to the ball
at the dual parameter, the first shell at $-d$ and the Fourier mass
supply $q^{-d/2}(a^{-1}q^{-(1-s)})^{-d}$. Their product over the two
places is $E(s)$. Hence the Gaussian $g(z)=e^{-2\pi|z|^2}$ tensored
with the balls has legs $uG(s)/U(s)$ and $uE(s)G(1-s)/U(1-s)$,
where $u=u_2u_5=(1/2)(1/\sqrt5)$. Neither vanishes in the overlap.
By (3.3.1.2), forward equals $\rho$ times reflected, so
$$
 \rho(s)=E(s)^{-1}\frac{G(s)U(1-s)}{G(1-s)U(s)}.
$$
The global identity $G(s)D_f(s)=E(s)G(1-s)D_f(1-s)$ gives
$D(1-s)=\rho(s)D(s)$ throughout the overlap. More directly, the two
explicit expressions for $P_\pm$ give $P_+=\rho P_-$ there, even at
shared zeros. This never cancels $\Phi$ or assumes its symmetry.

**Realization and normalization.** Formula (5.4.1.3) is equality of
the full image with the pairs just tested, not merely closedness.
Indeed, dividing the two legs by $u/U(s)$ and $uE(s)/U(1-s)$
respectively preserves their strip bounds (each multiplier and its
inverse is bounded on each corresponding interior strip). The pair
now satisfies the archimedean criterion with ratio $G(s)/G(1-s)$.
Take its one Schwartz representative and tensor it with the two balls,
as in `local-closed-range`, lines 91–133. This gives one $[f]$ with
both original legs. On $\Re s>1$ counting Weil unfolds the actual
inserted integral to $Z_{S''}(f,c_s)D(s)=\Phi(s)$: Every omitted
unit mass is one, and both retained masses are inside $Z_{S''}$.
Every omitted ball is Fourier-fixed. Thus continuation yields exactly
$\Phi$, with no quotient-volume scalar (`fourier-gluing`, lines
277–345; `glued-closed-range`, lines 109–129).

**Off-center check.** Dilate the Gaussian to $g_4(z)=g(2z)$, keeping
the same balls. Substitution in the complex Mellin integral multiplies
the forward leg by $4^{-s}$. Its Fourier transform is
$4^{-1}g(z/2)$, so the dual leg also gains $4^{-1}4^{1-s}=4^{-s}$.
The common target is $\Phi_4=2\pi u\,4^{-s}\Lambda(s)$, not symmetric
under the completed reflection of $\Lambda$. It is entire and in
$AS(\mathbb C)$: On bounded strips with $\Re s\ge1/2$ use Stirling
and the polynomial bounds for $D_f$ above. Use the completed
reflection on the other side; $4^{-s}$ and $E$ are bounded on each
bounded-width strip. At $s=3/4$ the fourth powers of the correct
scale and the incorrectly substituted $4^{-(1-s)}$ are $1/64$ and
$1/4$. The conductor check is also rational there: Removing each
geometric denominator, the fourth powers of the combined leading
shell coefficients are $1/400$ forward and $1/8000$ reflected.
Their ratio is $20$, not $1/20$ as using $E$ in $\rho$ would give.
The local legs are nonzero. So is the target: At this real argument
the mod-$4$ blocks are positive by monotonic decrease of $x^{-s}$,
and each mod-$5$ block with signs $+,-,-,+$ is positive by strict
convexity. These are convention checks, not the proof for every $V$.

Independent numerators $\Phi_4|_{H_+}$ and $2\Phi_4|_{H_-}$ meet all
scalar jet conditions but their divided legs fail the relation at
$3/4$. They do not restrict one entire numerator. Conversely, at
this stage actual insertion gives one entire $AS$ numerator, a tail
times a holomorphic leg on each half-plane. The landed order identities
on this cover then imply its divisibility by $\Lambda$ everywhere.
The inclusion alone also follows by transitive insertion of the two
balls into the pre-existing archimedean lift (for a unit-normalized
archimedean test first scale by $u^{-1}$; `inverse-range`, lines
194–203). The direct calculation identifies the actual divided pair;
it neither relies on closedness for surjectivity nor extends the
result to arbitrary stages.
