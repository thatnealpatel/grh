---
evidence_revision: a684299f2b54e602be826969b35b7c1f30742700
outcome: established
---

# Zero orders of the two stage multipliers for the nontrivial class character

Let $\Lambda(s,\chi)$ be Masullo’s entire completed Hecke factor for the nontrivial ideal-class character of $F=\mathbb Q(\sqrt{-5})$. At $S''=S_\infty\cup\{\mathfrak p_2,\mathfrak p_5\}$, put $D_f(s)=L(s,\chi_{-4})L(s,\chi_5)$ and $D_{S''}(s)=(1+2^{-s})(1-5^{-s})D_f(s)$. The claim is equality of the full zero orders (order zero at a nonzero value):

$$
\operatorname{ord}_s\Lambda(\cdot,\chi)=
\begin{cases}
\operatorname{ord}_s D_{S''} & \text{on }\Re s>0,\\
\operatorname{ord}_s [D_{S''}(1-\cdot)] & \text{on }\Re s<1.
\end{cases}
$$

Both equalities must hold on the overlap. The two extra Euler factors have no zeros on the forward open half-plane, but they belong in the stage multiplier, not in the completed global factor.

The [completed-product audit](../../obligations/isotypic-inverse-range-q-sqrt-minus-five.md#verified-completed-product-and-divisibility) identifies the complex gamma factor by continuation. Lean checks the [finite Hecke product comparison](../../obligations/isotypic-euler-factorization-q-sqrt-minus-five.md#checked-all-prime-grouped-identity) on $\Re s>1$. The [glued closed-range calculation](../../obligations/isotypic-glued-closed-range-q-sqrt-minus-five.md) identifies both stage multipliers in reviewed mathematics. These are inputs, not a Lean proof of the two order equalities.

**Next discriminating test:** Write the quotient of $\Lambda$ by the forward multiplier, then by the reflected multiplier using the functional equation for this self-dual character. Track the gamma, conductor, and finite factors in the same normalization. Check for a holomorphic, nowhere-zero extension on each stated half-plane, explicitly at $s=1$ on the forward side and $s=0$ on the reflected side. A residual zero or pole in either domain would give an order mismatch. Success identifies the scalar vanishing conditions in the proposed range of (6.3.2.3), p. 304; it does not prove that the divided pair satisfies the local gluing relation.

## Proof at the pinned stage

Write $U(w)=(1+2^{-w})(1-5^{-w})$. The omitted-ball shell sum is
$u_v/(1-a_v q_v^{-w})$, with $a_v=\chi_v(\varpi_v)$. The prime of norm
$2$ is nonprincipal (no $a^2+5b^2=2$ in integers), so $a_2=-1$; the
prime of norm $5$ is $(\sqrt{-5})$, so $a_5=1$. Retaining these places
removes their inverse Euler factors from the tail, hence the multiplier
is $D_{S''}(w)=U(w)D_f(w)$. Every omitted $u_v$ is one and every omitted
ball is Fourier-fixed since both places of the different are retained.
Thus the reflected multiplier is the same tail at $w=1-s$ for
$\chi^{-1}=\chi$, with no conjugation of $s$ and no conductor scalar.
See `isotypic-fourier-gluing-q-sqrt-minus-five.md`, lines 82–106 and
307–364, in the pinned obligations.

The pinned completed-product audit, lines 41–79, gives the entire
$\Lambda(s)=(2\pi)^{-s}\Gamma(s)D_f(s)=(G(s)/(2\pi))D_f(s)$ by
continuation. To obtain its reflection, complete the two primitive
Dirichlet factors separately with $(q/\pi)^{(s+a)/2}\Gamma((s+a)/2)$.
The conductor-parity pairs $(q,a)$ are $(4,1)$ and $(5,0)$; the Gauss
sums are $2i$ and $2\cos(2\pi/5)-2\cos(4\pi/5)=\sqrt5$, respectively.
Both root numbers $\tau/(i^a\sqrt q)$ are one. The product of the two
Dirichlet completions is therefore invariant under $s\mapsto1-s$.
By duplication, $\Gamma((s+1)/2)\Gamma(s/2)=2^{1-s}\sqrt\pi\,\Gamma(s)$,
so that product is $4\,20^{s/2}\Lambda(s)$, not $\Lambda(s)$. It follows
that $\Lambda(s)=E(s)\Lambda(1-s)$ with $E(s)=20^{1/2-s}$. The sign of
the exponent also follows from the two retained Fourier shell ratios:
$(-1)^2 2^{1-2s}\,5^{1/2-s}=E(s)$. The retained masses $1/2$ and
$1/\sqrt5$ occur in the local integral, not in the tail.

The meromorphic product identities are
$$
\Lambda(s)=Q_+(s)D_{S''}(s)=Q_-(s)D_{S''}(1-s),\qquad
Q_+(s)=\frac{G(s)}{2\pi U(s)},\quad
Q_-(s)=E(s)\frac{G(1-s)}{2\pi U(1-s)}.
$$
These are identities by continuation, including at shared zeros. For
$\Re w>0$, $|2^{-w}|,|5^{-w}|<1$, and $\Gamma(w)$ has neither a pole nor
a zero. Taking $w=s$ and $w=1-s$ shows that each $Q$ is a holomorphic
unit on its entire stated domain. Since $G(1)=1$ and $U(1)=6/5$,
$Q_+(1)=5/(12\pi)$ and $Q_-(0)=5\sqrt{20}/(12\pi)$. A unit preserves
the first nonzero Taylor order, including the sum of the orders of any
common Dirichlet zeros. On the overlap both divisors thus equal that of
$\Lambda$; the units need not be the same.

The *excluded* endpoints illustrate why the domains matter. Both
nonprincipal Dirichlet factors are nonzero at $1$, so $\Lambda(1)$
and $\Lambda(0)=\sqrt{20}\,\Lambda(1)$ are nonzero. At $w=0$ the simple
Gamma pole gives $D_f$ a simple zero; $U(w)\sim 2w\log 5$ supplies a
second zero. Thus the forward multiplier at $0$ and the reflected one
at $1$ have order two, not zero. This is not a counterexample on either
claimed domain. The endpoint cancellation is already noted in the
Fourier audit, lines 167–186.

This proves the scalar jet comparison requested by the glued closed-range
audit, lines 37–64 and 157–169, for (6.3.2.3), p. 304. It does not put
the divided pair in the local range: Its functional-equation relation
is a separate condition. The finite Lean comparison (Euler-factorization
audit, lines 622–661) is on $\Re s>1$; the unit argument here is ordinary
mathematics for this character and stage only.
