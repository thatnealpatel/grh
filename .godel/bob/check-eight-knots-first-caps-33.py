"""Delete-33: A high-mass flat-B splice meeting both full first caps."""
import argparse
import json
from pathlib import Path
from runpy import run_path

from sage.all import QQ

base = Path(__file__).resolve().parent
s = run_path(str(base/'check-tail-deletion-33.py'))
F, C, Ct, cap, jumps, step = (s[n] for n in ('F', 'C', 'Ct', 'cap', 'jumps', 'step'))
EPS = QQ(1)/10**8


def splice(z, A):
    A = [v*QQ(9999)/10000 for v in A]
    j = z.index(QQ(-218)/400)
    assert z[j:j+3] == [QQ(k)/400 for k in (-218, -216, -214)]
    l = j+1
    before = A[j]+A[l]
    A[j] -= QQ(1)/4-A[l]
    A[l] = QQ(1)
    z = z[:l+1]+[QQ(-215)/400]+z[l+1:]
    A.insert(l+1, -QQ(1)/2)
    assert A[j]+(A[l]+A[l+1])/2 == before
    return z, A, l


def third(y):
    return 4*y**3-3*y


def reference():
    z0 = [QQ(k)/400 for k in (-218, -216, -214)]
    z, A, l = splice(z0, [QQ(1), -QQ(1)/2, QQ(0)])
    assert z == [QQ(k)/400 for k in (-218, -216, -215, -214)]
    assert l == 1 and A == [QQ(4999)/20000, QQ(1), -QQ(1)/2, QQ(0)]
    assert [third(y) for y in A[l:l+2]] == [1, 1]
    d, v = s['second_tangent']([QQ(0)], [F(1)], list(map(F, (0, 1, 0))), [F(2)])
    t = F(6)/25  # Only the middle H coefficient is nonzero.
    assert d == 2 and abs(v[0]-(4+(1+t+t*t/2)*(-t/2).exp())) < F('1e-35')
    print('Reference controls: splice, flat third harmonic, and quadratic normalization passed', flush=True)


def main():
    laws = base/'deletion-laws'
    load = s['unfold']['lattice']['prime_rows']
    z, A, _, _ = load((laws/'delete-33-tail-baseline.txt').read_text())
    assert len(z) == 1257 and z[0] == -QQ(144)/25 and z[-1] == QQ(29)/5
    z, A, l = splice(z, A)
    assert all(-1 <= y <= 1 for y in A)
    B = [third(y) for y in A]
    U = [((1+F(y))/2).sqrt() for y in A]
    assert A[l]-A[l+1] == QQ(3)/2 and B[l] == B[l+1] == 1
    E = [(-F(t)/2).exp() for t in z[l:l+3]]
    mean = ((E[0]-E[1])*F(A[l])+(E[1]-E[2])*F(A[l+1]))/(E[0]-E[2])
    assert mean > QQ(1)/4
    mass = sum((step(x, 0)-step(y, 0))*u for x, y, u in zip(z[:-1], z[1:], U[:-1], strict=True))
    mass += step(z[-1], 0)*U[-1]
    assert mass-F(8)/9 > F('.0002837')
    print('A mean and mass surplus:', mean, mass-F(8)/9, flush=True)

    peak_a, peak_b = F('.99999'), F('.999')
    b = jumps(z, B, C)
    cap(z, jumps(z, A, Ct), peak_a)
    cap(z, b, peak_b)
    cert = json.loads((laws/'delete-33-five-release-disk-price-k8.json').read_text(), parse_float=str)
    tangent, = [row for row in cert['cuts'] if len(row) == 3]
    lam = list(map(F, tangent[1]))
    q = s['second_majorant'](lam)
    d, v = s['second_tangent'](z, b, lam, q)
    excess = sum(x*y for x, y in zip(b, v, strict=True))-d
    print('Q minus d:', excess, flush=True)
    assert excess > F('.491')

    # Any extra splits use deterministic X within EPS of the anchor value,
    # and leave the two halves of -216 alone. These bounds are uniform in
    # the chosen pieces and positions, including multiple splits on a slab.
    assert all(-1+EPS <= y <= 1-EPS for i, y in enumerate(A) if i not in (l, l+1))
    a_error = 2*(-F(z[0])/2).exp()*F(EPS)/Ct
    b_error = 9*a_error*Ct/C
    assert a_error < F('1e-6') and b_error < F('3e-6')
    assert peak_a+a_error < 1 and peak_b+b_error < 1
    perturb_mass = F(EPS/2).sqrt()
    assert mass-F(8)/9-perturb_mass > F('.000212')
    l1 = sum(map(abs, lam))+abs(q[0])+2*sum(map(abs, q[1:]))
    perturb_q = (2*b_error+b_error*b_error)*l1
    assert perturb_q < F('.001') and excess-perturb_q > F('.49')
    print('Uniform perturbation bounds (A, B, M, Q):', a_error, b_error, perturb_mass, perturb_q, flush=True)


if __name__ == '__main__':
    assert __debug__
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reference', action='store_true', help='only run small reference controls')
    args = parser.parse_args()
    reference()
    if not args.reference:
        main()
