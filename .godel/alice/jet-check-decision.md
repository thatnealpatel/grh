# Run the accepted check and verify the obstruction identity

**Own decision.** Before running an inherited checker, use the
version in the accepted revision rather than a relative path in
the durable checkout. Gödel run `01a20f12-f972-7e63-9f9b-cce181893f46`
matches Work session `01a20f12-fbfa-73c5-aec0-51d274ba7007` by
its input and final handoff. Both the launch marker and initial
accepted tip were `613da3704308f45df6fc65b56e5d5ddcd74d2b26`.
The checker was present in that revision and read at events 12–13,
but Python could not open the launch-checkout path at events 23–24.
The inline finite computation in the same call still ran. A
campaign workspace ran the baseline successfully at events 29–30;
its intervening base change did not touch the inputs. Running the
self-contained checker directly from the pinned file via `jj file
show | python3 -` also passed in improvement. This reproduces a
successful alternative, not the exact historical checkout state.

There were no child dispatches in Work. Before the all-degree
check, events 23–32 had established the finite two-copy deficit
and full budget cap, not a uniform obstruction. Event 33 tried
SymPy, which was unavailable. The worker still derived the
quadratic, checked its signs with rational arithmetic, and tested
both scripts on the integrated candidate at events 61–62 before
adopting `d500be7bb3a2ac0267c4e9ff493ffedf2154773c`. It correctly
kept the obstruction uniform in the jet parameters and limited it
to the computed exponent bound. No evidence attributes the time
between the failed import and the draft to the failure alone.

**Peer comparison.** Bob's [five-release curvature checker][bob]
at `6ee726b2a7e0bef037bca686fd69ade2c071e1d0` compared its fast
kernel with a direct ordered-pair sum on a small asymmetric mesh.
Its [dispatch replay][dispatch] isolated that check without
weakening the whole-release verification. The comparable choice
is what the small check tests: Alice's adopted script verified the
signs of the displayed quadratic, but did not connect its
coefficients to the original quotient exponents. The strengthened
[axis-LCM checker](check-jet-axis-lcm.py) computes both sides in
standard-library rationals. They have degree at most two, so six
coefficient-determining evaluations check the identity, not just
six signs. This improves verification coverage without adding a
separate stage or claiming either branch is faster overall.

**Replay and null result.** In improvement session
`01a20f19-ee5a-7c62-9018-d53f4d826988`, `qohoayD` and `GPfiWuM`
got the same pre-expansion formulas and pinned baseline. Only the
latter got a sentence asking it to reuse the baseline arithmetic
and recompute the decisive coefficients. The comparison was
whether the first check joined the source formulas to an exact
all-degree sign certificate, without a new dependency. Both did;
the control also found the exact minimum, $14559/16250$, and
cross-checked the jet counts against monomial layers. No support
for adding the recomputation sentence. This replay constrained the
decision to the uniform sign test and establishes no live gain.
Only the accepted-checkout instruction is installed in Work.
Revert it if later runs find it adds staging without preventing a
checkout mismatch; it does not replace exact-candidate testing.

## Next worker

Continue the fixed-reference experiment from the
[axis-LCM proof](jet-axis-lcm.md). To use a common reference
congruence in a wedge, first show that all its rows occupy the same
labeled branch at each credited prime and agree with the same
reference parameter to the claimed depth. Then all row pairs have
that depth. At shared primes use only the increment beyond the
already credited depth in $G$, in the same local parameter; do not
credit a second copy of the base divisor or of the marked row
factor. At $(m,r)=(10000,1200)$, $w=0$, and crossing $.0207$,
that additional common exponent must exceed $.02269924\ldots$
with just one paid copy and no surplus, or $.00027418\ldots$
if two copies and one surplus are already supplied. These are
$(K-\tau V)/V$ and $(K-\tau(2V+ra))/V$, respectively. Neither
assumption about extra depth is forced. Prove the credit or bound
the residual uniformly in one actual reference before changing
what gets summed. The full complement and unrestricted cofactors
remain open. Keep the Alpöge exclusion.

[bob]: ../bob/check-five-release-curvature-33.py
[dispatch]: ../bob/reference-check-dispatch.md
