"""Certify independently measurable negative and tail laws at c=39/20."""
import argparse
import json
from pathlib import Path
from runpy import run_path

from sage.all import QQ

base = Path(__file__).resolve().parent
shared = run_path(str(base/'check-tail-deletion-33.py'))
F, K, C, Ct = (shared[k] for k in ('F', 'K', 'C', 'Ct'))
tail_data, second_majorant = (shared[k] for k in ('tail_data', 'second_majorant'))


def atom_upper(a, b):
    # Max on [-1,1] of the odd cubic (3b-a)X-4bX^3.
    end = abs(a+b)
    if not abs(b) > 0:
        return abs(a)+abs(b)
    r2 = (3*b-a)/(12*b)
    if r2 < 0 or r2 > 1:
        return end
    r = F(max(0, min(1, r2.upper()))).sqrt()
    return F(max(end.upper(), (8*abs(b)*r**3).upper()))


def curved_error(z, B, data, den):
    # An envelope L3*exp(-t/2) for the third derivative of the atom
    # objective on open cells. There is no mass term on the negative side.
    h = QQ(1)/den
    L3 = F(0)
    for row in data:
        j, scale = int(row[0]), F(row[-1])
        if len(row) == 5:
            L3 += scale/(Ct if j == 0 else C)*abs(K(F(1)/2, F(row[1])))**3
        else:
            lam = list(map(F,row[1]))
            q = second_majorant(lam)
            qnorm = abs(q[0])+2*sum(abs(a) for a in q[1:])
            bnorm = sum(abs(b) for b in shared['jumps'](z,B,C))
            L3 += 2*scale/C*bnorm*(3*qnorm+8*sum(abs(a) for a in lam))
    return h**3/192 * L3 * (F(h)/2).exp() * 2*((-F(z[0])/2).exp()-1)


def negative_gain(z, A, B, data):
    den = 1600
    assert den % 400 == 0  # Every kernel branch point lies on a cell endpoint.
    lo = int(den*z[0])
    assert lo == den*z[0]
    error = curved_error(z,B,data,den)
    print('Negative: quadratic interpolation allowance',error,flush=True)
    assert error < F('1e-8')

    a, b, *_ = tail_data(z,B,data,range(2*lo,1),2*den)
    ends = [atom_upper(x,y) for x,y in zip(a[::2],b[::2])]
    controls = sum(atom_upper(2*a[i]-(a[i-1]+a[i+1])/2,
                              2*b[i]-(b[i-1]+b[i+1])/2)
                   for i in range(1,len(a)-1,2))
    atom_integral = (2*sum(ends)-ends[0]-ends[-1]+controls)/(3*den)
    # Integrate the reference on its OWN slab partition, not by sampling it.
    i0 = z.index(0)
    points = [int(t*400) for t in z[:i0+1]]
    assert all(p == t*400 for p,t in zip(points,z))
    ar, br, *_ = tail_data(z,B,data,points,400,primitive=True)
    reference_term = sum(A[i]*(ar[i]-ar[i+1])+B[i]*(br[i]-br[i+1]) for i in range(i0))
    nominal = atom_integral+reference_term
    print('Negative: atom integral upper',atom_integral,'reference term',reference_term,
          'nominal gain upper',nominal,'total gain upper',nominal+error,flush=True)
    return nominal+error


def self_test():
    # Nonuniform signed jumps, both sides of knots and shifts, exact zero
    # arguments, and output points between and outside the reference knots.
    z = [QQ(i)/400 for i in (-31,4,89)]
    B = [QQ(1)/3, -QQ(2)/5, QQ(4)/7]
    points = [-251,-239,-185,-100,-65,-31,4,23,89,108,143,241]
    lam = list(map(F,['.7264553101249','.9816283566088','1']))
    q = second_majorant(lam)
    data = [[1,lam,'1']]
    jumps = shared['jumps'](z,B,C)

    def direct(t, s, hankel, primitive):
        # s is the branch point. Integrate a constant (or zero) below s,
        # and a polynomial times exp(-t) above it, independently of indexing.
        u = F(max(t-s,0))
        term = (F(s)/2-max(t,s)).exp()
        if hankel:
            return term*(1+u+u*u/2 if primitive else u*u/2)
        if primitive:
            return term*(2+abs(t-s))
        return term*(1+u)

    for primitive in (False, True):
        _, bb, *_ = tail_data(z,B,data,points,400,primitive=primitive)
        for p,v in zip(points,bb):
            t = QQ(p)/400
            expected = 2/C*sum(b*(
                sum(q[abs(k)]*direct(t,s-QQ(13)*k/25,False,primitive)
                    for k in range(1-len(q),len(q)))
                + sum(a*direct(t,-s-QQ(k)/25,True,primitive) for a,k in zip(lam,(-7,6,19))))
                for s,b in zip(z,jumps))
            assert abs(v-expected) < F('1e-29'), (p,primitive,v,expected)
    assert abs(atom_upper(F(3),F(0))-3) < F('1e-36')
    assert abs(atom_upper(F(4),F(1))-5) < F('1e-36')
    assert abs(atom_upper(F(-1),F(1))-8/(3*F(3).sqrt())) < F('1e-35')
    print('Signed kernel and cubic atom checks passed',flush=True)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--self-test', action='store_true')
    args = p.parse_args()
    self_test()
    if args.self_test:
        return
    laws = base/'deletion-laws'
    z,A,B,U = shared['unfold']['lattice']['prime_rows']((laws/'delete-33-tail-baseline.txt').read_text())
    assert len(z) == 1257 and z[0] == -QQ(144)/25 and z[-1] == QQ(29)/5 and z.index(0) == 494
    data = json.loads((laws/'delete-33-full-negative-dual.json').read_text(), parse_float=str)
    # Only baseline and slack enter the starting price. Reprice both free
    # regions below rather than evaluating any of the fixed-slab allowances.
    off, _, _ = shared['price'](z,A,B,U,data,omit=set(z))
    negative = negative_gain(z,A,B,data)
    tail = shared['continuous_tail'](z,A,B,U,data,den=2400)
    budget = -off-tail
    bound = negative-budget
    print('Available negative gain budget:',budget,flush=True)
    print('Measurable negative and tail, unchanged pre-tail:',bound,flush=True)
    assert bound < F('-4.13e-8')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run with assertions enabled.')
    main()
