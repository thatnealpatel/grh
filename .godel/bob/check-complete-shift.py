#!/usr/bin/env python3
"""Finite certificate for the jointly separated arc test at q=100000007.

Run `python3 .godel/bob/check-complete-shift.py` (CPython 3.12 tested,
standard library only; do not use -O). Includes independent checks. No
log-coordinate substitution, random redraw, or sign-based pool selection.
"""

from bisect import bisect_left
from collections import defaultdict
from decimal import Context, Decimal, ROUND_CEILING, ROUND_FLOOR, ROUND_HALF_EVEN
from fractions import Fraction
from functools import cache
from itertools import combinations
from math import factorial, isqrt, prod


# These intervals have exact Decimal endpoints. Basic operations round out;
# Decimal's correctly rounded ln/exp (half-even) are widened by one neighbor.
LO = Context(prec=60, rounding=ROUND_FLOOR)
HI = Context(prec=60, rounding=ROUND_CEILING)
RN = Context(prec=60, rounding=ROUND_HALF_EVEN)


class I:
    def __init__(self, lo, hi=None):
        self.lo = Decimal(lo)
        self.hi = self.lo if hi is None else Decimal(hi)
        assert self.lo <= self.hi

    def __add__(self, other):
        return I(LO.add(self.lo, other.lo), HI.add(self.hi, other.hi))

    def __neg__(self):
        return I(self.hi.copy_negate(), self.lo.copy_negate())

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        ends = [(x, y) for x in (self.lo, self.hi) for y in (other.lo, other.hi)]
        return I(min(LO.multiply(x, y) for x, y in ends),
                 max(HI.multiply(x, y) for x, y in ends))

    def __truediv__(self, other):
        assert other.lo > 0
        return self * I(LO.divide(1, other.hi), HI.divide(1, other.lo))

    def __abs__(self):
        if self.lo >= 0:
            return self
        return -self if self.hi <= 0 else I(0, max(self.lo.copy_abs(), self.hi))

    def positive_part(self):
        return I(max(0, self.lo), max(0, self.hi))

    def log(self):
        return I(RN.next_minus(RN.ln(self.lo)), RN.next_plus(RN.ln(self.hi)))

    def exp(self):
        return I(RN.next_minus(RN.exp(self.lo)), RN.next_plus(RN.exp(self.hi)))

    def __repr__(self):
        # Exact decimal endpoints, including the last printed digit.
        return f"[{self.lo}, {self.hi}]"


def rational(x):
    return I(LO.divide(x.numerator, x.denominator), HI.divide(x.numerator, x.denominator))


def arctan_inverse(k):
    terms = [Fraction((-1)**i, (2*i+1)*k**(2*i+1)) for i in range(49)]
    # Alternating series: these consecutive partial sums trap arctan(1/k).
    return I(rational(sum(terms[:-1])).lo, rational(sum(terms)).hi)


Q = 100000007
T5 = 32*Q**3  # t**5, exactly
T0 = 126191
HPLUS = 4
N = 2*HPLUS
PERM = factorial(HPLUS-1)*factorial(HPLUS)  # one designated plus label
ZERO, ONE = I(0), I(1)
TAU = I(32)*arctan_inverse(5) - I(8)*arctan_inverse(239)  # Machin, 2*pi
T = I(2)*(rational(Fraction(3, 5))*I(Q).log()).exp()
X = (I(3)*(T/I(2)).log())*(I(3)*(T/I(2)).log())
D = X.log()
XMIN = I(-8).exp()*X
L = T.log()/D
TAYLOR_ERR = rational(Fraction(13**121, factorial(121))).hi


def trig(x, odd):
    assert abs(x).hi < 13  # Includes the direct check's difference arguments.
    term = total = x if odd else ONE
    zz = -(x*x)
    for j in range(2+odd, 121, 2):
        term = term*zz/I(j*(j-1))
        total = total + term
    # Taylor's theorem through degree 120, including zero coefficients.
    return total + I(TAYLOR_ERR.copy_negate(), TAYLOR_ERR)


def prime(p):
    return p >= 2 and all(p % k for k in range(2, isqrt(p)+1))


def certified_geometry():
    assert prime(Q) and T0**5 < T5 < (T0+1)**5
    assert T0 < T.lo <= T.hi < T0+1
    assert 1099 < X.lo <= X.hi < 1100 and 0 < XMIN.lo <= XMIN.hi < 1
    rr = D*D
    assert 49 < rr.lo <= rr.hi < 50
    hh = I(9)*L/I(4)
    assert HPLUS-1 < hh.lo <= hh.hi < HPLUS
    assert 35 < (I(5)*D).lo <= (I(5)*D).hi < 36
    # R_* = X**(1/144) < 2 < r. Every slot is private, and the number of
    # starts approaching the opposite support is zero in both directions.
    assert 1 < X.lo <= X.hi < 2**144 and (I(5)*L/I(4)).hi < N
    assert (I(13)*L/I(4)).lo > 0


def plan(d):
    starts = [p for p in range(2, 1100-d) if prime(p) and prime(p+d)]
    after = [bisect_left(starts, p+50) for p in starts]

    @cache
    def count(i, k):
        if k == 0:
            return 1
        if i == len(starts):
            return 0
        return count(i+1, k) + count(after[i], k-1)

    # Independent unsigned count: skip or take the first available start.
    # It does not use the enumerator's geometric pruning or any ratio test.
    return count(0, 2*N), d, starts, after


def family(starts, after, count):
    def pools(i, k, prefix):
        if k == 0:
            yield prefix
            return
        # Each increasing pool has exactly one first choice at each step.
        for j in range(i, len(starts)):
            if starts[j]+50*(k-1) > starts[-1]:
                break
            yield from pools(after[j], k-1, prefix+(starts[j],))

    rows = list(pools(0, 2*N, ()))
    assert len(rows) == len(set(rows)) == count
    assert all(all(y-x >= 50 for x, y in zip(row, row[1:])) for row in rows)
    return rows


def fits_y(delta, v, t5=T5):
    # |y| = t*abs(delta)/v; fifth powers decide <= 8, including equality.
    return t5*abs(delta)**5 <= (8*v)**5


def possible_min_block(pool, d, h=HPLUS, t5=T5):
    # Orient the minimum plus only for this unsigned bound. All other plus
    # factors are >= those at the h-1 largest starts; all minus factors are
    # <= those at the h smallest remaining starts. If R>1, both the ratio
    # and its reciprocal have absolute defect at least 1-1/R.
    assert h >= 2 and len(pool) >= 2*h
    R = prod(Fraction(p+d, p) for p in (pool[0], *pool[1-h:]))
    R /= prod(Fraction(p+d, p) for p in pool[1:h+1])
    return R, R <= 1 or fits_y(R.numerator-R.denominator, R.numerator, t5)


def rounded_count(plus, u, v, d):
    m = 0
    for p in plus:
        # Omitting this plus slot gives M/N=u*p/[v*(p+d)].
        den = v*(p+d)-u*p
        if den > 0:
            dist = 2*abs(d*u*p-p*den)
            assert dist != den  # no rounding ties in this search
            # Once rounded to p, x is in (p-1/2,p+1/2), hence
            # in [XMIN/2,2X] by the certified endpoint bounds.
            m += dist < den
    return m


def joined_blocks(starts, rows, d):
    """Index balanced compact-window blocks by support, and by eligible pool."""
    bits = {p: 1 << i for i, p in enumerate(starts)}
    masks = [sum(bits[p] for p in pool) for pool in rows]
    incidence = defaultdict(int)
    for i, pool in enumerate(rows):
        for a in combinations(pool, HPLUS):
            incidence[a] |= 1 << i
    ordered = sorted((Fraction(prod(p+d for p in a), prod(a)), a, inc,
                      sum(bits[p] for p in a)) for a, inc in incidence.items())
    quartets = [(f.numerator, f.denominator, a, inc, mask) for f, a, inc, mask in ordered]
    by_pool = [set() for _ in rows]
    blocks = defaultdict(list)
    for i, (a, b, small, inc, sm) in enumerate(quartets):
        for j in range(i+1, len(quartets)):
            c, e, large, other, lg = quartets[j]
            u, v = b*c, a*e  # large product / small product
            delta = u-v
            # (u-v)/u is the lesser of the two absolute defects. Lower
            # bound t by T0 for the early exit; (R-1)/R grows with R=u/v.
            if T0*delta > 8*u:
                break
            common = inc & other
            if not common or sm & lg:
                continue
            assert delta > 0  # disjoint prime endpoints, so unequal ratios
            found = False
            for plus, U, V in ((large, u, v), (small, v, u)):
                if not fits_y(U-V, V):
                    continue
                blocks[sm | lg].append((U, V, rounded_count(plus, U, V, d)))
                found = True
            if found:
                while common:
                    bit = common & -common
                    by_pool[bit.bit_length()-1].add(sm | lg)
                    common ^= bit
    # Incidence intersection visits every eligible pool containing both
    # quartets. Each unordered sign partition was visited exactly once; each
    # orientation was tested individually, including the rounded plus label.
    return masks, by_pool, blocks


def weights(starts, d):
    return {p: (X/I(p)).log()*I(p).log()*I(p+d).log()/X for p in starts}


def evaluate(starts, rows, d, w):
    masks, by_pool, blocks = joined_blocks(starts, rows, d)

    @cache
    def moments(mask):
        c = s = ZERO
        gate = active = maybe = 0
        for u, v, m in blocks[mask]:
            gate += m
            if m == 0:
                continue
            defect = rational(Fraction(u-v, v))
            a = T*defect*(ONE - defect/I(2))
            taper = (ONE - abs(a)/TAU).positive_part()
            if taper.hi > 0:
                active += m
                if taper.lo == 0:
                    maybe += m
                b = I(m)*taper
                c, s = c + b*trig(a, 0), s + b*trig(a, 1)
        return c, s, gate, active, maybe

    for pool, mask, supports in zip(rows, masks, by_pool):
        total = ZERO
        windows = gated = active = uncertain_taper = 0
        for a in sorted(supports):
            b = mask ^ a
            if a >= b or b not in supports:
                continue
            # The complement is the only disjoint 8-set in this 16-set.
            # Smaller mask first, then account for both orders by a factor 2.
            windows += 2*len(blocks[a])*len(blocks[b])*factorial(HPLUS)**4
            ca, sa, ga, aa, ma = moments(a)
            cb, sb, gb, ab, mb = moments(b)
            gated += 2*ga*gb*PERM**2
            active += 2*aa*ab*PERM**2
            uncertain_taper += 2*(aa*ab-(aa-ma)*(ab-mb))*PERM**2
            # cos(a-b)=cos(a)cos(b)+sin(a)sin(b), WITHOUT reversing any
            # sign. Weight product is independent of labels at fixed pool.
            total = total + ca*cb + sa*sb
        yield ((windows, gated, active, uncertain_taper),
               I(2*PERM**2)*prod((w[p] for p in pool), start=ONE)*total)


def direct(pool, d, w):
    """Reference: enumerate both signed copies without ratio/coverage pruning."""
    choose = {a: (prod(p+d for p in a), prod(a)) for a in combinations(pool, HPLUS)}
    compact, gated = defaultdict(int), defaultdict(int)
    terms = defaultdict(list)
    for a, (pa, qa) in choose.items():
        for b in combinations(tuple(p for p in pool if p not in a), HPLUS):
            pb, qb = choose[b]
            u, v = pa*qb, pb*qa
            if T5*abs(u-v)**5 > 8**5*v**5:
                continue
            support = frozenset(a+b)
            compact[support] += factorial(HPLUS)**2
            y = T*rational(Fraction(u-v, v))
            angle = y - y*y/(I(2)*T)
            taper = (ONE - abs(angle)/TAU).positive_part()
            for p in a:
                free = tuple(k for k in a if k != p)
                m = prod(k+d for k in free)*prod(b)
                n = prod(free)*prod(k+d for k in b)
                if m >= n:
                    continue
                x = Fraction(d*m, n-m)
                assert (2*x).denominator != 1 or x.denominator == 1
                if round(x) != p:
                    continue
                assert (XMIN/I(2)).hi <= rational(x).lo <= rational(x).hi <= (I(2)*X).lo
                gated[support] += PERM
                if taper.hi > 0:
                    weight = prod((w[k] for k in free+b), start=ONE)*w[p]*I(PERM)
                    terms[support].append((angle, taper*weight, taper.lo == 0))
    full = frozenset(pool)
    windows = sum(k*compact.get(full-a, 0) for a, k in compact.items())
    gate = sum(k*gated.get(full-a, 0) for a, k in gated.items())
    active = uncertain = 0
    total = ZERO
    # Both ordered copies, explicit designated labels and cosine difference.
    for a, left in terms.items():
        for angle, weight, maybe in left:
            for other, weight2, maybe2 in terms.get(full-a, ()):
                total = total + weight*weight2*trig(angle-other, 0)
                active += PERM**2
                uncertain += (maybe or maybe2)*PERM**2
    return (windows, gate, active, uncertain), total


def compare(pool, d, w, result):
    counts, total = result
    ref_counts, ref = direct(pool, d, w)
    assert counts == ref_counts
    assert max(total.lo, ref.lo) <= min(total.hi, ref.hi)


def self_test():
    # Cutoff fixture with exactly representable t=128: inclusivity and both
    # signs at |y|=8; just outside and a ratio passing only on reversal.
    assert all(fits_y(z, 1600, 128**5) for z in (100, -100))
    assert not any(fits_y(z, 1600, 128**5) for z in (101, -101))
    assert not fits_y(16, 243, 128**5) and fits_y(-16, 259, 128**5)
    # A d=26 block with both orientations in the window and unequal gated
    # label counts. An implementation multiplying one orientation by two fails.
    a, b = (461, 593, 761, 911), (383, 701, 827, 971)
    u, v = prod(p+26 for p in a)*prod(b), prod(p+26 for p in b)*prod(a)
    assert fits_y(u-v, v) and fits_y(v-u, u)
    assert (rounded_count(a, u, v, 26), rounded_count(b, v, u, 26)) == (2, 1)
    # Adjacent-pool regression from adjacent-signed-pools.md. Nonzero weighted
    # and opposite-signed fixtures exercise the evaluator even if d=4 is empty.
    P = (61, 131, 191, 251, 307, 367, 433, 503, 557, 613, 677, 733, 821, 877, 1013, 1063)
    R = tuple(sorted((set(P)-{61}) | {947}))
    starts = sorted(set(P+R))
    assert all(prime(p) and prime(p+6) and XMIN.hi < p < p+6 < X.lo for p in starts)
    assert all(all(y-x >= 50 for x, y in zip(row, row[1:])) for row in (P, R))
    w = weights(starts, 6)
    for pool, result, low, high in zip((P, R), evaluate(starts, (P, R), 6, w), (59, -15), (60, -14)):
        compare(pool, 6, w, result)
        normalized = result[1]/(I(2*PERM**2)*prod((w[p] for p in pool), start=ONE))
        assert low < normalized.lo <= normalized.hi < high
    print("Direct original-formula checks passed on both d=6 regression pools.", flush=True)


def report(pools, rows, w, results):
    P = M = H = absolute = ZERO
    pos = neg = unresolved = exact = 0
    unsigned = [0, 0, 0, 0]
    for pool, (counts, total) in zip(rows, results, strict=True):
        for i, k in enumerate(counts):
            unsigned[i] += k
        if total.lo > 0:
            pos += 1
        elif total.hi < 0:
            neg += 1
        elif total.lo == total.hi == 0:
            exact += counts[2] > 0
        else:
            unresolved += 1
            print(f"  Unresolved pool {pool}: {total}")
        P, M = P + total.positive_part(), M + (-total).positive_part()
        H, absolute = H + total, absolute + abs(total)
    structural = len(pools)-pos-neg-exact-unresolved
    print(f"  A={sum(w.values(), ZERO)}")
    print(f"  ordered pairs: {unsigned[0]} after both windows, {unsigned[1]} after both gates,")
    print(f"    {unsigned[2]} after both tapers (including {unsigned[3]} with uncertain taper positivity)")
    print(f"  pool signs: +{pos}, -{neg}, structural zero {structural}, exact zero {exact}, unresolved {unresolved}")
    print(f"  positive mass={P}\n  negative magnitude={M}\n  H={H}\n  sum abs={absolute}")
    print(f"  H/positive mass={H/P if P.lo > 0 else 'undefined (no certified positive mass)'}")
    print(f"  H/sum abs={H/absolute if absolute.lo > 0 else 'undefined (no certified absolute mass)'}")
    scale = X/D/I(16**N)/T
    endpoint = scale*scale
    print(f"  finite endpoint reference={endpoint}; H/reference={H/endpoint}", flush=True)


def main():
    certified_geometry()
    self_test()
    # Compute the unsigned ranking over the entire allowed shift range.
    # The smallest nonempty family is the requested d=4. Following its null,
    # evaluate the first shift that survives the min-block test, irrespective
    # of the signs of the resulting pools.
    plans = sorted(p for d in range(1, 36) if (p := plan(d))[0])
    assert [(n, d, len(s)) for n, d, s, _ in plans[:3]] == [
        (2160, 4, 44), (18656, 20, 52), (28592, 26, 44)]
    for count, d, starts, after in plans:
        pools = family(starts, after, count)
        rows = []
        min_ratio = None
        for pool in pools:
            ratio, possible = possible_min_block(pool, d)
            min_ratio = ratio if min_ratio is None else min(min_ratio, ratio)
            if possible:
                rows.append(pool)
        print(f"d={d}: {len(starts)} starts, {len(pools)} pools, {len(rows)} after min-block test; "
              f"min ratio bound={min_ratio}", flush=True)
        w = weights(starts, d)
        assert sum(w.values(), ZERO).lo > Decimal('0.25')
        results = list(evaluate(starts, rows, d, w))
        if d == 4:
            # Independently recompute the original terms on an excluded pool.
            compare(pools[-1], d, w, ((0, 0, 0, 0), ZERO))
            print("  Direct original-formula check passed on last d=4 pool.")
        elif rows:
            # Fix a direct-check pool with both gated blocks and asymmetric
            # label counts (see self_test); no selection on its weighted sign.
            pool = (47, 101, 167, 251, 311, 383, 461, 521, 593, 647, 701,
                    761, 827, 911, 971, 1061)
            assert d == 26 and results[rows.index(pool)][0][1] > 0
            compare(pool, d, w, results[rows.index(pool)])
            print("  Direct original-formula check passed on joined d=26 pool.")
        report(pools, rows, w, results)
        if rows:
            break


if __name__ == '__main__':
    main()
