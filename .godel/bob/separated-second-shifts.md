# Which second translates can separate at depth $39/20$?

The [152-slab common law](single-shift-10-2.md) does more than answer one query at a time. In the same $(10,2)$ shallow comparison, it admits **one completion per set of shifts** giving zero second answers at $3t$ on the entire set, if any of the following holds:

* The set consists of two points at distance at least $7$.
* It lies in any affine lattice of step at least $8.5$.
* Its distinct points are at least $9.5$ apart, lattice or not.

Even at smaller gaps every **scalar** two-term mask with opposite-sign coefficients has a zero-answer completion. This last completion may depend on the coefficients; it does not assert two simultaneous zeros. Thus a two-term scalar separator must have same-sign coefficients and gap strictly below $7$. No statement here produces prime or zero data for actual conductors.

Use the accepted first representer $m=-G_B/C_1$, the Cauchy probability $d\mu=dx/(2\pi(1/4+x^2))$, and $v=1-|m|^2$. Nothing changes in the first translates at either height, the zero answers of orders two through ten at $t$, or the strict failure mean. At $3t$ we may choose the conditional second moment $m^2+v g$ for any measurable $|g|\le1$, by the [chord construction](single-shift-decision.md) (mix opposite chords along half the argument of $g$). For one multiplier $H$ the condition is $\int |H|v\,d\mu\ge |\Re\int Hm^2\,d\mu|$. In particular it suffices that $\int |H|(1-2|m|^2)\,d\mu\ge0$.

## One-sided sign test and affine lattices

Let $W(d)=\int\cos(dx)(1-2|m|^2)\,d\mu$. The signed density is even. With $b_z=e^{-z/2}\Delta B(z)$ and $h_p=-2\sum_{z-t=p} b_z b_t/C_1^2$, the difference kernel gives

$$W(d)=e^{-|d|/2}+\sum_p h_p(2+|d-p|)e^{-|d-p|/2}.$$

The [128-bit Sage checker](check-shift-spacing.py) certifies $W(0)>.01148$, $W(d)\le W(0)$ for all $d$, and $|W(d)|\le (.38+10^{-6}d)e^{-d/2}=:w(d)$ for $d\ge0$. Between consecutive nonnegative knots the transformed $e^{d/2}W(d)$ is $A+Bd+(E+Jd)e^d$. The checker encloses it and, on the first interval, its derivative; after the last knot only the affine term remains. The decreasing envelope has $w(7)<W(0)$.

For $0\le b\le a$, the even periodic function $|a-be^{iu}|$ has a cosine series $c_0-\sum_{k\ge1}c_k\cos(ku)$ with $c_k\ge0$, $\sum c_k=c_0-(a-b)$. Indeed expand $(a^2+b^2)^{1/2}(1-\rho\cos u)^{1/2}$ with $\rho=2ab/(a^2+b^2)$ (omit $a=b=0$). All nonconstant binomial terms are negative multiples of powers of $\cos u$; each power has nonnegative cosine coefficients. The binomial coefficients are absolutely summable even at $\rho=1$. Thus for opposite signs the sufficient test for $H=e^{isx}(a-be^{idx})$ costs at worst $\sum c_k W(0)$ against $c_0W(0)$, at **any** gap $d$. Reversing coefficients does not change the modulus. For equal signs replace $u$ by $u+\pi$: The absolute values of the coefficients stay unchanged, so $|W(kd)|\le W(0)$ suffices. This holds for $d\ge7$.

For an affine lattice $s+d\mathbb Z$, the modulus of any finite multiplier supported there is a nonnegative continuous function of $dx\bmod 2\pi$. The pushforward of $(1-2|m|^2)d\mu$ under this map has density $W(0)+2\sum_{k\ge1}W(kd)\cos(ku)$ relative to normalized Haar measure (absolute convergence and Fourier uniqueness). It is positive when $2\sum_{k\ge1}w(kd)<W(0)$, as checked at $d=8.5$ and hence above it.

In both the two-point and the lattice case the scalar tests for **every** real coefficient vector on a finite subset imply a single completion there: The attainable measurement vectors form a compact convex set, being the real affine image of the weak-star compact complex $L^\infty(\mu)$ unit ball under integration against finitely many $L^1$ functions. If zero lay outside, one real linear functional would separate. For an infinite subset take the finite intersection property on the same ball. The construction may be symmetrized by $g(x)\mapsto(g(x)+\overline{g(-x)})/2$ without changing any real answer.

## Off-lattice interpolation

For distinct shifts separated by $D=19/2$ we give an explicit interpolant, rather than relying on periodization. Define $S(s)=\int e^{isx}m(x)^2\,d\mu$ and $R(d)=\int e^{idx}v(x)\,d\mu=(e^{-|d|/2}+W(d))/2$. Both are real by conjugation symmetry. Write $P=.476$, $K=.70$, $\lambda=.48$, and $u=.4$. The replay certifies

$$|S(s)|\le\min(P,Ke^{-\lambda|s-u|}).$$

It groups $b_z b_t/C_1^2$ at $p=-z-t$ and applies the accepted sum kernel $(1+y_++y_+^2/2)e^{-|y|/2}$ at $y=s-p$. Between knots the sum is $(A+Bs+Es^2)e^{-s/2}+Te^{s/2}$. On the left tail only the growing exponential remains; on the right, the exponentially damped quadratic is bounded using $y^je^{-ay}\le j!/a^j$ for $y\ge0$.

Let $\Lambda$ be a nonempty $D$-separated subset of the line. The total $\sum_{s\in\Lambda}|S(s)|$ is less than $.491917$. To see the packing constant, center at $u$ and take the nearest point at distance $h$. For $h\le D/2$, subsequent distances on its side are at least $h+kD$ and on the opposite side at least $kD-h$, $k\ge1$. With $r=e^{-\lambda D}$ the bound is $\min(P,Ke^{-\lambda h})+2Kr\cosh(\lambda h)/(1-r)$. It increases up to $h_*=\log(K/P)/\lambda<D/2$, then is convex, hence is maximized at $h_*$ or $D/2$. For $h>D/2$ both tails start at least $D/2$ away, giving at most the same endpoint bound $2K\sqrt r/(1-r)$. The checker compares both endpoints.

On $\ell^1(\Lambda)$, the matrix $L_{s,t}=R(s-t)$ has diagonal $R(0)>.505743$. Its off-diagonal column sums are less than $.012044$: Bound each of the two tails by $\frac12\sum_{k\ge1}(1+.38+10^{-6}kD)e^{-kD/2}$ using the decreasing envelope. In particular $\|S|_\Lambda\|_1+\|L-R(0)I\|_1<R(0)$. The Neumann series gives a real solution $a=-L^{-1}S|_\Lambda$ with $\|a\|_1<1$. Set $g(x)=\sum_{t\in\Lambda}a_te^{-itx}$. The series converges uniformly, $|g|<1$, and for **all** $s\in\Lambda$ we have $\int e^{isx}(m^2+vg)\,d\mu=0$. This argument does not assume a fundamental period or a bound on the number of shifts.

## Why the same proof cannot settle the nearby positive masks

For $H=1+e^{ix}$ the checker gives $\int |H|v\,d\mu\le\sqrt{2R(0)(R(0)+R(1))}<.853$ by Cauchy–Schwarz, whereas $S(0)+S(1)>.915$. Thus the **fixed** 152-slab first representer fails the exact scalar test. This is a reason to change the prime law for comparable positive coefficients, not evidence for a uniform separator. The gap constants above are sufficient and not asserted optimal.

Replay all bounds from the repository root with `sage .godel/bob/check-shift-spacing.py` (SageMath 10.9, assertions on); this first replays the 152-slab certificate. No grid of sample shifts or solver fit is used as proof.
