---
evidence_revision: d89533430976275b1dd02f20b9e340cbe2a66740
outcome: refuted
---

# A fixed off-diagonal product admits at most one realized tag

Under the finite hypotheses of [`SharedLabelRecoveryFiber.offDiagonal_recovery_bounds`](../../../Proofs/Lemmas/SharedLabelRecoveryFiber.lean), fix the list, two distinct positions, and the product $w=h_i y_j$. Can all realizing columns be recovered using a single signed determinant tag $t$?

**Refuted.** Mallory's finite example uses the list $[9,2]$ in that order, $q=31$, $w=9$, and $H=Z=W=1$. The congruence fixes one residue class modulo $F_j=2$, but both $-1$ and $+1$ belong to that class and to the closed window $[-1,1]$. Both occur on actual witnesses to the finite theorem. Set $h_i=1$ and $y_j=9$ in both:

| Column $(c,d)$ | $h_j$ | $y_i$ | $F_i w-F_j h_j y_i=qt$ | $cF_i h_i-dy_i=q\,\mathrm{gap}$ |
| --- | ---: | ---: | ---: | ---: |
| $(4,1)$ | 5 | 5 | $81-2\cdot25=31$ | $36-5=31$ |
| $(5,1)$ | 4 | 14 | $81-2\cdot56=-31$ | $45-14=31$ |

The columns are positive and primitive, with $d=1\le Z$. The prime $31$ divides neither $F_j=2$ nor $F_i h_i=9$; $W<F_j$, both signed row gaps equal $1$, and $4HZ=4\le9$. Moreover, swapping the tags cannot recover either column from the other tag: For a fixed $c$, $h_i\mid9$ gives $h_i\in\{1,3,9\}$, and $y_i$ must be a positive divisor of the other quotient ($56$ for $c=4$, $25$ for $c=5$) with $|9c h_i-y_i|\in\{0,31\}$. Neither column has such a divisor.

Keep both signs in a finite recovery argument. This refutes the proposed one-tag strengthening, not Eve's two-tag theorem. It does not show that the divisor-sum bound on the number of columns is sharp or that both signs occur in an asymptotic smooth family.
