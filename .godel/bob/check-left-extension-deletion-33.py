"""Exclude measurable fixed-B left refits of the tail-fiber near-witness."""
from decimal import Decimal
from functools import cache
from math import factorial
from pathlib import Path
from runpy import run_path

from sage.all import QQ

if not __debug__:
    raise SystemExit('Run with assertions enabled.')

base = Path(__file__).resolve().parent
fiber = run_path(str(base/'check-fiber-deletion-33.py'))
joint = fiber['joint']
F, K, Ct = (joint[k] for k in ('F', 'K', 'Ct'))
laws = base/'deletion-laws'


def profile():
    z, raw_A, B, U = joint['unfold']['lattice']['prime_rows'](
        (laws/'delete-33-tail-baseline.txt').read_text())
    assert len(z) == 1257 and z[0] == -QQ(144)/25 and z[-1] == QQ(29)/5
    assert z.index(0) == 494 and all(l < r for l, r in zip(z, z[1:]))
    A = list(map(F, raw_A))
    end = z[1:] + [None]
    sites = {}
    for line in (laws/'delete-33-tail-fiber.triples').read_text().splitlines():
        k, *triple = map(int, line.split())
        t = QQ(k)/400
        assert t >= 0 and t not in sites
        sites[t] = triple
    surplus = -F(8)/9
    step = joint['step']
    for i, (l, r) in enumerate(zip(z, end)):
        if l < 0:
            continue
        u, _ = fiber['bounds'](raw_A[i], B[i], U[i], sites.pop(l))
        if l == QQ(49)/25:
            assert r == QQ(393)/200 and -1 < B[i] < 1
            atom_x = (F(B[i]).arccos()/3).cos()
            a = QQ(53)/1000
            u = (1-a)*u + a*((1+atom_x)/2).sqrt()
            A[i] = (1-a)*A[i] + a*atom_x
        surplus += (step(l, 0) - (0 if r is None else step(r, 0)))*u
    assert not sites and F('9.38794e-9') < surplus < F('9.38795e-9')
    # The exact modified atom has third harmonic B[i] by the triple-angle
    # identity; the fixed-field polish has exactly the input A and B.
    return z, end, A, B, surplus


def main():
    z, end, A, B, surplus = profile()
    cuts = []
    for line in (laws/'delete-33-left-extension.cuts').read_text().splitlines():
        if line.startswith('#'):
            continue
        x, u, v = (QQ('%s/%s' % Decimal(s).as_integer_ratio()) for s in line.split())
        assert x >= 0
        cuts.append((x, K(u, v)))
    assert cuts
    budget = sum(abs(h) for _, h in cuts)
    assert budget > 0
    cx = [(K(-QQ(1)/2, x), h/(Ct*K(QQ(1)/2, x))) for x, h in cuts]

    @cache
    def prim(t):
        return F(0) if t is None else sum((c*(w*t).exp()).real() for w, c in cx)

    # prim(l)-prim(r) is exactly the coefficient of A on a slab [l,r).
    base_gap = sum(a*(prim(l)-prim(r)) for l, r, a in zip(z, end, A))-budget
    jumps = joint['jumps'](z, A, Ct)
    jump_gap = sum((h*sum(j*K(0, x*t).exp() for t, j in zip(z, jumps))
                    /K(QQ(1)/2, x)).real() for x, h in cuts)-budget
    assert (base_gap-jump_gap).contains_zero()
    zero = 2*sum(jumps)
    assert F('1.00000342429') < zero < F('1.00000342430')
    print('Fixed positive surplus:', surplus, '; reference t value at 0:', zero, flush=True)

    # -prim'(t) = exp(-t/2)*phi(t). Bound phi by a centered Taylor
    # polynomial instead of separately ranging each oscillatory summand.
    n = 6
    terms = []
    for (x, _), (w, c) in zip(cuts, cx):
        k = K(0, x)
        terms.append((k, [-w*c*k**j/factorial(j) for j in range(n+1)]))
    remainder = sum(abs(cs[-1]) for _, cs in terms)

    @cache
    def weight(t):
        return (-F(t)/2).exp()

    cells = [0, 0]  # fixed sign, absolute envelope

    def variation(l, r):
        x, rad = (l+r)/2, (r-l)/2
        ej = [(k*x).exp() for k, _ in terms]
        coeff = [sum((e*cs[j]).real() for e, (_, cs) in zip(ej, terms)) for j in range(n)]
        wobble = sum(abs(coeff[j])*rad**j for j in range(1, n)) + remainder*rad**n
        signed = abs(prim(l)-prim(r))
        if abs(coeff[0]) > wobble:
            cells[0] += 1
            return signed
        envelope = 2*(weight(l)-weight(r))*(abs(coeff[0])+wobble)
        # The allowed integral overpayment is 1e-10 per unit length.
        if envelope-signed < F('1e-10')*(r-l):
            cells[1] += 1
            return envelope
        assert rad > QQ(1)/2**32
        return variation(l, x)+variation(x, r)

    def correction(l, r, a, b):
        hi = (F(b).arccos()/3).cos()
        lo = -(F(-b).arccos()/3).cos()
        # Both endpoints attainable; B fixed even on the extension.
        assert lo <= a <= hi and hi-lo > 0
        cen, radius = (hi+lo)/2, (hi-lo)/2
        return (cen-a)*(prim(l)-prim(r)) - radius*variation(l, r)

    # The 1/25 cells here are for integration only, not a law partition.
    ext = sum(correction(QQ(k)/25, QQ(k+1)/25, F(0), QQ(0)) for k in range(-250, -144))
    neg = sum(correction(l, r, a, b) for l, r, a, b in zip(z, end, A, B) if l < 0)
    gap = base_gap+ext+neg
    floor = 1+gap/budget
    print('Cut budget:', budget, '; reference gap:', base_gap, flush=True)
    print('Corrections (extension, original):', ext, neg, '; cells:', cells, flush=True)
    # floor encloses a lower bound, not the cap norm itself.
    print('Normalized lower-bound expression for every refit:', floor, flush=True)
    assert gap > F('1.1769e-6') and floor > F('1.00000117')


if __name__ == '__main__':
    main()
