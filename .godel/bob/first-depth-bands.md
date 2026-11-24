# Removing phase bands from the two-height depth census

At the [real high-endpoint failure](symmetric-first-depth.md), use its two first masks, $R,V,D,t$, and $J=(2/\epsilon)\log D$. For $y=t,3t$ set $x=\gamma-y$ and $d=D(\beta-1/2)$. From $|x|\le J$ remove the following closed bands, **only** within $|x|\le 1/100$:

| Height | Remove when |
|---|---|
| $t$ | $\operatorname{dist}(Dx,2\pi\mathbb Z)\le 1.5$ |
| $3t$ | $\operatorname{dist}(Dx,\pi+2\pi\mathbb Z)\le 1.5$ |

In the remaining windows there is a right zeta zero at $t$ with $d>c_t$ **or** at $3t$ with $d>c_3$, for either row:

| $c_t$ | $c_3$ | Lower bound on limiting price gap |
|---:|---:|---:|
| 1.23684 | 1.23684 | $9.9\cdot10^{-7}$ |
| 1.226 | 1.72 | $3.3\cdot10^{-6}$ |

As before, fix sufficiently small $\epsilon>0$ before taking $q$ sufficiently large. In particular the first-height hole $|x|\le 1.5/D$ is no longer needed in the census, but the center at $3t$ still is. This improves the existence alternatives $(1.230,1.230)$ and $(1.226,1.50)$ in [the common-filter comparison](common-filter-pair.md) on subsets of their windows. It does not improve those signed charge lower bounds. It uses no higher-order measurements, and makes no assertion that a removed band is zero-free.

**A uniform sign on the right of the strip.** Write $L_y(w)=\sum_l b_{y,l}e^{lh(w-1/2)}$, $H_y(x)=L_y(1/2+ix)$, $h=1/100$, and $g(w)=\exp(1-\cos(\epsilon w))$. The positive-sign and negative-sign masks occur at $t$ and $3t$, respectively: Put $s_t=1$, $s_3=-1$. On $1/2\le\Re w\le1$ bound $|L_y'(w)|$ by $B_y=\sum_l |lh b_{y,l}|\exp(\max(0,lh/2))$. On this real interval $s_yL_y(\beta)\ge s_yL_y(1/2)-B_y/2$. For the [actual table](symmetric-first-depth.txt) the derivative bounds are $<.081,.0048$ and the real lower bounds are $>.25,.0028$, respectively. Moving by $ix$, $|x|\le.01$, changes the value by at most $B_y/100$. The ratio of this error to the remaining real lower bound is $<.018$ at either height, so $|\arg(s_y L_y(w))|<.018$ there. Also $2|\arg w|\le4|x|\le.04$ and $|\Im(1-\cos(\epsilon w))|\le .25\sinh(.0025)<.001$ for $0<\epsilon\le1/4$.

Thus on the removed bands the phase of $e^{iDx}g(w)L_y(w)/w^2$ is within $1.5+.018+.04+.001<\pi/2$ of zero modulo $2\pi$. The modulus is bounded below there: The signed real part of $s_yL_y$ is bounded away from zero, $|w|$ is bounded above, and $|g|$ is bounded below on the compact set. Consequently, for some fixed $\kappa>0$ the right residue satisfies

$$\Re Q_y(w)\ge \kappa e^d/R,\qquad Q_y(w)=V^{w-1}g(w)L_y(w)/w^2.$$

This is an estimate on the real part **before** the minus sign in the explicit formula. Positivity just on the critical line would not suffice.

**Why the full-norm price survives the deletion.** Suppose neither remaining window contains a right zero beyond its depth threshold. At each height let $E_y$ be the right zeros *inside* $|x|\le J$ with $d>c_y$; they are all in the removed bands. The signed first prime sum $P_y$ is $O(1)$ even separately, by the fixed translated ramp majorant and Chebyshev. Use the [whole tent identity](opposite-phase-bands.md#use-the-unused-half-of-the-log-axis) with the fixed bounded strip multiplier $L_y$. Up to $O(\epsilon)+o_\epsilon(1)$ it is minus the real sum of $Q_y$ on $\beta\ge1/4$, $|x|\le J$: The lower-strip terms, the two nonleading tent terms on $\beta\ge1/4$, and the smoothed outer tail have the same absolute bounds as for the translated tent. Pair each right zero with its left companion at the same $x$. The [reflection estimate](filtered-reflection-price.md) replaces the pair by $(1+e^{-2d})Q_y(w_+)$ with total absolute error $o_\epsilon(1)$, also on a subset. Indeed $gL_y/w^2$ and its derivative are $O_\epsilon((1+x^2)^{-1})$ on $1/4\le\Re w\le1$; when the left member is omitted its proxy has the extra $e^{-D/4}$. Count line zeros once.

All shallow terms have total absolute size $O_\epsilon(1)$ using only the unit zero counts and the fixed depth thresholds. The terms on $E_y$ all have the same sign, so boundedness of $P_y$ and the uniform lower bound above give

$$ R^{-1}\sum_{E_y}e^d=O_\epsilon(1). \tag{1} $$

Dropping these pairs now gives an upper bound for $P_y$. But simply quoting the all-shallow ordinate limit would be invalid. To recover it, put $b=\beta-1/2$. For each fixed exterior width $a>1/2$ and displacement $v$, replacing $k_{a-b}(x-v)$ by $k_a(x-v)$ costs $O_{a,v}(|b|/(1+x^2))$ per zero, where $k_u(z)=u/(u^2+z^2)$. On shallow zeros $|b|\le c_y/D$. On $E_y$ and its mirrors, (1) gives $R^{-1}\sum |b|=O_\epsilon(1/D)$ since $d\le e^d$. Thus the normalized replacement error on the *entire* local count tends to zero. The tail outside $J$ still costs $o(R)$ by the unit counts. Now the [exterior Poisson trace argument](symmetric-first-depth.md#the-full-first-mask-prices-when-both-windows-are-shallow) applies: After division by $\log y$, the flat-width Poisson integrals tend to $1/2$, vague subsequential limits have these same integrals for all $a>1/2$, and continuation and the approximate identity identify $dx/(2\pi)$. The uniform inverse-square tail permits the full test $|H_y(x)|/(1/4+x^2)$.

On shallow pairs apply the original line replacement and $\cosh(c_y)$ bound. Majorize the sum of their **nonnegative** norm weights by the full local count just priced. Since $\log y/R\to1/3$ at either height and $\exp(1-\cos\epsilon)\to1$, the limiting upper price for $P_t+P_{3t}$ is at most

$$\tfrac13\big(\cosh(c_t)N_t+\cosh(c_3)N_3\big),\qquad N_y=\int |H_y(x)|\,\frac{dx}{2\pi(1/4+x^2)}.$$

The shared prime floor is unchanged. Its strict excess over this price gives the contradiction in the original order of limits. In the asymmetric row the two norms must be priced separately, not both at depth $1.72$.

The price is an existence test, not an arithmetic upper bound on the remaining zeros. For another pair of first masks, check the strip signs and the associated trace error afresh; line signs alone do not transfer this deletion. The separate three-versus-four higher-measurement question in [the four-shift handoff](four-shift-10-2.md) is unchanged.

**Replay.** Run `sage .godel/bob/check-symmetric-first-depth.py` from the repository root with assertions enabled. It checks both original price certificates, the two strip derivative and sign bounds for the new table, the phase slack, and the asymmetric price. No optimization or zero counts at a sampled conductor enter the test.
