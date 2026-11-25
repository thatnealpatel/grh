# Price the fixed-plane bound before asking for a rescue

## Decision at launch

Gödel run `01a2104f-869d-7dc0-b356-0e692455183c` used
`cmd/alice/WORK.md` at launch `cd007f1241e25b495ce7698b164908a3ffb6fd0d`.
Work session `01a2104f-8f3a-7746-8070-ccd9f08bc147` priced
an unmasked fixed plane (events 25–26), then sent the
missing gain for one-shot review (28–29, `CbPhfjY`). The
brief already flagged the unproved division by $F$, but
mistook the vertical period $de/G$ for the ambient index.
Both the congruences and the projection index $G$ were
available then. There were no Yah child sessions in Work.

For $ho_d=Fq^{-1}\bmod d$ and $\rho_e=Fq^{-1}\bmod e$,
a basis of $\Lambda_0$ is $(1,\rho_d,\rho_e),(0,d,0),(0,0,e)$.
The index is $de$. With primitive normal $n=(a,b,c)$,
image $g\mathbb Z$, and $\lambda=de/g$, write
$R=VH^2/(\lambda\|(Va,Hb,Hc)\|_2)$ and $N=qa+F(b+c)$.
For $N\ne0$ the universal vector gives only

$$R\le \frac{qH^2+2FVH}{de}\frac{g}{|N|}.$$

The two terms before $g/|N|$ have exponents $-.330$ and
$.780$, not $-1.110$ and $0$. The local price is
$q^{o(1)}(1+\sqrt R)$. The target $1.1354$ and the
$G$-bin pair price $q^{1.055+o(1)}/\sqrt G$ allow
$R\le Gq^{.1608+o(1)}$, not just $R\le Gq^{o(1)}$.
Even for that wider allowance this inequality would need
$|N|/g\ge q^{.6192-o(1)}/G$ as a sufficient extra gain.
The $N=0$ branch works: $F\mid a$, so $R\le H^2/F$.

At the fixed-plane dispatch, a basis and the unsimplified
scale substitution should precede the review, instead of
sending a brief that asks the reviewer to rescue an
unnormalized bound. This leaves only the precise missing
gain on named pieces to review, or a choice to count
varying planes. Work corrected course rather than using
the unsupported bound. The subsequent reviews addressed
the new count; in particular `EUvrJxo` (87–88) caught the
fixed $\kappa\ge0$ scope. That check is worth preserving.
The [accepted result][normals] at `df36e0b4e122` is a partial
interior count, not a bound for the full complement.

## Paired replay and peer evidence

At the same pre-review pin in improvement session
`01a21064-aa5e-779e-bcf5-7a5f6dc4c333`, control `zOZOoyh`
and treatment `HEypZRy` were tasked to choose the next
action. The treatment asked for a basis or exact sequence
and scale substitution before dispatch. Both corrected the
index and asked to refine the next question on the masked
named pieces. The treatment additionally constructed the
relaxed obstruction below. This is useful evidence, but
not a different dispatch decision or a measured live gain.
The replay brief itself highlighted the provisional index
and arithmetic, so it does not test whether either prompt
would notice an unflagged normalization error.

Bob's [first-cap obstruction][bob] at `0d870fd32ddc`
certifies the relaxed first caps on the full frequency
line for every remaining mask, and explicitly checks that
the construction violates the omitted quadratic test.
The comparable improvement is to turn the fixed-plane
heuristic into a uniform obstruction and name exactly
which retained conditions have not been tested, before
asking whether to spend a review on rescuing the bound.
Alice's construction does not test the named-piece domain,
so it cannot justify Bob's stronger kind of stopping
decision there. These results do not rank worker speed.

Keep the Work prompt and graph unchanged. The existing
cheap-test rule was enough to elicit the core check under
control. Reconsider a broader instruction if a narrow
pinned replay shows a missed admissible witness or a
changed routing choice, or if a live run repeats the
normalization mistake at a consequential dispatch.

## Exact obstruction in the relaxed congruence lattice

Take $d,e,F$ to be powers of $2,3,5$ at the required
scales, respectively, and prime $q>5$. Then $G=1$.
Set $B=\lfloor q^{.260}\rfloor$. For $k=0,\ldots,B^2$,
put the residues $-qk/(Fe)\bmod d$ and $-qk/(Fd)\bmod e$
in the $B$-by-$B$ grid of the two residue intervals.
The inverses exist. Two indices $k_1<k_2$ share a cell.
Take $a=k_2-k_1$, $b=e$ times the first residue
difference, and $c=d$ times the second. Then $0<a\le B^2$,
$|b|,|c|\le de/B$, and $de\mid qa+F(b+c)$. Since also
$e\mid b$ and $d\mid c$, the congruence implies
$a+b\rho_d+c\rho_e\equiv0$ modulo both $d$ and $e$.
The other basis evaluations $db,ec$ are multiples of
$de$, so the normal maps $\Lambda_0$ into $de\mathbb Z$.

Divide by the coordinate gcd $\delta$ to get the primitive
normal $n_*=(a_*,b_*,c_*)$. If its image generator is $g$,
then $de\mid\delta g$, so $\lambda=de/g\mid\delta$.
Thus $\lambda\|(Va_*,Hb_*,Hc_*)\|_2\le\|(Va,Hb,Hc)\|_2
\le q^{2.240+o(1)}$, whereas $VH^2=q^{2.500+o(1)}$.
Since $0<a_*<F$ for large $q$, $N\ne0$ for this normal.
It gives $R\ge q^{.260-o(1)}$, past the $.1608$
allowance even at $G=1$. This is a plane in the relaxed
lattice, not a plane shown to be named by an outer prism
or populated by any retained triples. It refutes the
unrestricted plane bound, not a retained triple count.

## Next worker

Do not reopen a uniform unmasked-plane price. In the
[unpriced retained interior][normals], test whether the
mask congruences can bound the required overlap
$(a',D/G)>q^{.011}I^2G^{3/2}$, with $S$ and the two forms
held fixed per pair. Count the outside-prism triples
separately. No extra coverage or radius benefit was shown.
Keep the Alpöge exclusion in force.

[normals]: effective-gap-normals.md#remaining-decision-at-target-11354
[bob]: ../bob/eight-knot-first-caps-33.md
