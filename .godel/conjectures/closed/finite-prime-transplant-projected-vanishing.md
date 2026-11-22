---
evidence_revision: 022676f32fb32118354a025cb57b7c48d5dac9cf
outcome: parked
---

# Vanishing of the projected finite-prime transplant defect

In the rational weighted radial model, let $L_Y=\prod_{p\le Y}(1-p^{-1/2}S_{\log p})^{-1}$, where $S$ translates log radius, $M$ is a smooth end cutoff, and $f=b'$ for $b\in C_c^\infty((0,\log 2))$. Set $T_Y=A_f(L_Y M L_Y^{-1}-M)$. The proposed vanishing is $\lim_{Y\to\infty}\operatorname{Tr}(P T_Y P)=0$ for the actual theta projection $P$, with the band and then position cutoffs exhausted at each fixed $Y$.

**Parked:** At fixed $Y$ the unprojected trace is zero, but the calculation leaves a projected term with no bound uniform in $Y$. Reopen with a bound or cancellation identity for that term itself.

The paper calculation (`1953ce5cb71f998343e27cbdff64af98d74e4748`) expands over smooth prime products. The unprojected diagonals vanish by support; the projected trace instead becomes $\operatorname{Tr}(J A_f M L_Y^{-1} P L_Y J)$ with $J=1-P$. Range invariance gives $JL_Y=JL_YJ$, not commutation with $P$. Nor does the dense smooth-quotient comparison from [Meyer](https://arxiv.org/abs/math/0311468) transfer a nuclear trace. No Lean verification or scalar counterexample was obtained. This transplant is optional, not a necessary feature of the manuscript.
