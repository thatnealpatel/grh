# Fixed-cutoff orbital transfer cannot use only the cut output

**Scope.** Rational trivial compact isotype, standard real Fourier-band
levels, finite band $B>0$, and $p>1$ (a rational prime in the orbital
application). This tests transfer from the **already formed** cut global
output to the orbital quotient, not a shell inserted before the terminal
level projection or a section chosen on the quotient.

## The manuscript interface

Theorem 11.2.1.4 and (11.2.1.8–9), pp. 488–489, place the orthogonal
band projector on the input; (10.4.1.6–7), p. 457, places the geometric
projector after convolution and the position cutoff last. At fixed
cutoffs we retain that input projector. On pp. 495–496, the argument
from (11.3.2.3–4) to (11.3.2.5) proposes matching effects on arbitrary
tests and then invokes orbital basis vectors and a trace computed on the
orbital space. Its cited Theorem 7.4.2.1, p. 367, starts with convolution
**already induced** on the quotient by the prime difference, defined in
(7.4.0.2), p. 366; (11.2.2.12), pp. 490–491, approximates its adjoint on
the zero-line orbital dual space. Neither result gives a representative-independent
map from the cut global output to the orbital output. In particular,
the manuscript's scalar assertion is in a limit, not an explicit claim
of equality at every finite cutoff. The source reading uses the pinned
Markdown and numbered layout extraction; full rendered-page verification
of this comparison is open.

On the standard integer-ring transition over $\mathbb Q$, the real input
is even Schwartz with $b(0)=\widehat b(0)=0$ and
$\operatorname{supp}\widehat b\subset[-B,B]$. The additive band is that
of (7.3.2.14), p. 355, for the real place only. The standard integer-ring
transition is (2.1.4.2–5), p. 71. This uses the empty
auxiliary set, not the extra-place unit factors in (7.3.2.13), and does
not settle the identification of Masullo's enlarged levels on p. 496.
Write $F_b(x)=\Theta_b(e^x)$ for the untwisted theta output and
$O(b)=\sum_{k\in\mathbb Z}F_b(\cdot+k\log p)$ for its orbital class in
the [circle model](trace-orbital-q.md#genuine-global-theta-lifts). The
prime difference is $D_p F=F-F(\cdot+\log p)$ (Definition 5.3.1.2, p. 241,
and (11.2.0.2), p. 484), before the half twist.
For a prime $p$, the actual prime-unit factor applied to the unramified
lift of $c$ gives the same theta difference as the unramified lift of
$d$. The checked test below only uses
that a difference has zero class, not that all zero classes are
differences.

## Checked comparison at fixed cutoffs

Let $\operatorname{supp}f\subset[\ell,\infty)$ and
$\operatorname{supp}\rho\subset(-\infty,R]$. The exact pointwise cut
output on a genuine generator with twist $a$ is

$$T(b)(x)=\rho(x)e^{ax}\int_{\mathbb R}f(y)e^{-ay}F_b(x-y)\,dy.$$

The support conditions are in log coordinates, with inverse-left
convolution as in §9.3.1, p. 426. The manuscript position cutoff of
Definition 9.3.3.1, p. 427, is compact in this coordinate.
For compact smooth $f$ and a bounded compact position cutoff, this is
the raw representative of $M_\rho P A_f Q_B$ on $e^{ax}F_b$ in the
weighted real-band model, including at $a=1/2$ and positive strip
width (9.2.2.34), p. 417, with closed range as in (10.1.1.3), p. 434.
Indeed $Q_B$ fixes the generator, and each translate of
$e^{ax}F_b$ by $y$ is $e^{-ay}$ times the twisted theta of
$b(e^{-y}\,\cdot)$. Those tests preserve both moments and evenness.
The translates are norm-continuous (use the two-sided exponential
bound for the theta profile on compact translation intervals and
dominated convergence), so the compact Bochner convolution stays in the
full closed even theta image. Hence $P$ fixes it. Conjugation to ordinary
$L^2(dx)$ multiplies the displayed output by the positive square root of
the strip weight. These operator identifications are independently
reviewed mathematics; the new Lean endpoints check the pointwise
comparison, including its twist, not the positive-width Bochner theory.

`Masullo.rationalThetaCutOutput_has_null_representative` produces for
every $b$ a generator $d$ in the **same** band $B$ with $O(d)=0$ and
$T(d)=T(b)$. Use the existing backward telescope at norm upper bound
$\exp(R-\ell)$ to find $c$ of band $B/p$ with $d=c-c(p\,\cdot)$ realizing
$F_b$ on $x\le R-\ell$. This interval contains every input read by the
cut convolution. The output equality has no exchange of limits. The
period sums of $d$ vanish as actual convergent series, by exponential
decay in both tails and reindexing the two sums by one period. This
also explains why a cutoff-dependent null representative is allowed:
The proposed comparison is at the very same fixed cutoffs for all
representatives in the band.

If a postprocessor $E$ uses only the cut output and gives an operator
$S$ on orbital classes, it must satisfy $E(T(b))=S(O(b))$ on every
representative to implement that direct transfer. If $S(0)=0$, the
same comparison applied to $d$ forces $E(T(b))=S(O(d))=0$. Lean checks
this implication as `Masullo.rationalThetaCutOutput_orbital_comparison_eq_zero`.
No linearity, trace-class hypothesis, or particular Haar reweighting of
the cut output is needed. This is stronger than showing that one choice
of cut periodization depends on the lift: **No** rule on the already
formed output can implement a nonzero such comparison.

**Nonzero orbital action on this band (reviewed mathematics, not Lean).**
Choose $c_0>1$ and an even Schwartz $g$ whose Fourier transform is a
nonnegative nonzero smooth bump away from zero in $(-B/c_0,B/c_0)$.
Then $g(0)>0$. The uncorrected $F_g$ equals $-g(0)$ sufficiently far
left by Poisson summation, and tends to zero on the right. Thus
$b=g-g(c_0\,\cdot)$ belongs to the band with both zero modes removed,
and integrating the translated difference gives
$\int F_b=-g(0)\log c_0\ne0$. This is the integral of its periodization
over one period by absolute unfolding. For any nonzero nonnegative
smooth $f$ supported in $(0,\log 2)$ the circle convolution with
$e^{-ay}f(y)$ multiplies the constant coefficient by the positive
number $\int e^{-ay}f(y)\,dy$. Consequently this orbital operator has
nonzero action on an actual band input, for every $B>0$. On the short
test its **trace** can still be zero: The periodized prime-power samples
miss the support. The obstruction is at the operator interface, not
that scalar trace.

**Disposition.** Do not try to recover a nonzero periodic shell by
postprocessing the same cut output on *all* representatives, even if
the unsplit Haar lift is normalized and the unit cutoff is rebased.
A map that instead selects an input section, puts a mask before a
projection, or only compares limiting scalar traces is not covered.
The next viable fixed-cutoff test is to specify a section or upstream
shell operation tied to the Haar lift and check its action on an
actual orbital mode, rather than insert an independent circle operator
after forming the global output. The [section construction](trace-orbital-q.md#half-weight-untwisting-and-the-iterated-limit-on-a-section)
supplies the orbit-side control, but not that tie to the Haar diagonal.
Neither the unrestricted projected trace identity nor RH or GRH follows.

**Check provenance.** Owner session `01a205e4-0237-7d93-a13b-f9d9dbc59121`
checks the integrated source, wfail build, joint import, and axioms;
independent fixed-statement and pinned-text review `cutoff-orbit-review`
(`arBwtLA`) in the same owner session, on comparison base
`aa79b7171a8529ec766213f4e5d823f5a685541b`.
