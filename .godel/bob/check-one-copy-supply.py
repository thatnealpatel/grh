#!/usr/bin/env python3
"""Enclose both completed log-window masses for the one-copy d=26 fixture."""
from fractions import Fraction
from itertools import combinations
from math import prod
from pathlib import Path
from runpy import run_path


def main():
    m = run_path(str(Path(__file__).with_name('check-complete-shift.py')))
    m['certified_geometry']()
    d = 26
    _, _, starts, _ = m['plan'](d)
    w = m['weights'](starts, d)
    I, T, tau = m['I'], m['T'], m['TAU']
    # Store integer enclosures; avoid Decimal operations in the window scan.
    W, K, F, M = 10**30, 10**12, 10**6, 10000

    def ends(i, scale):
        return (int(Fraction(i.lo)*scale//1), -int(-Fraction(i.hi)*scale//1))

    # Multiplication by exp(i/M), with outward interval endpoints.
    base = I(1)/I(M)
    c, s = m['trig'](base, False), m['trig'](base, True)
    u, v = I(1), I(0)
    gs = []
    for j in range(62833):
        g = (I(1)-I(j)/(I(M)*tau)).positive_part()*u
        gs.append(ends(g, K))
        u, v = u*c-v*s, v*c+u*s

    iof = {p: i for i, p in enumerate(starts)}
    near = {p: sum(1 << iof[q] for q in starts if abs(p-q) < 50) for p in starts}
    quartets = []
    for a in combinations(starts, 4):
        if any(y-x < 50 for x,y in zip(a,a[1:])):
            continue
        mask = sum(1 << iof[p] for p in a)
        banned = near[a[0]] | near[a[1]] | near[a[2]] | near[a[3]]
        ratio = Fraction(prod(p+d for p in a), prod(a))
        lo, hi = ends(prod((w[p] for p in a), start=I(1)), W)
        assert lo > 0
        quartets.append((ratio,a,mask,banned,lo,hi))
    quartets.sort()
    assert len(quartets) == 80331
    blocks = [(r.numerator,r.denominator,a,mask,banned,lo,hi)
              for r,a,mask,banned,lo,hi in quartets]
    tf = ends(T,F)[0]
    assert Fraction(T.hi)*F < tf+1
    xcap = Fraction(4, m['T0'])
    assert 2*xcap/F + 2*(m['T0']+1)*xcap**3/(1-xcap**2) < Fraction(1, 10**8)
    assert m['Decimal']('6.2831') < tau.lo <= tau.hi < m['Decimal']('6.2832')
    totals = [0]*4  # lower and upper for each of G_+ and G_-
    removed = [0]*4  # restore just the rejected rounded slots
    for i,(a,b,small,_,banned,wl,wh) in enumerate(blocks):
        for j in range(i+1,len(blocks)):
            c,e,large,mask,_,vl,vh = blocks[j]
            U,V = b*c,a*e
            delta = U-V
            # x=(U-V)/(U+V); |z|=2t atanh(x). Monotone in U/V.
            num,den = 2*tf*delta,F*(U+V)
            if num > 7*den:
                break
            if mask & banned:
                continue
            assert delta > 0
            gbin, rem = divmod(M*num, den)
            if gbin >= 62832:  # 6.2832 > 2*pi, and z >= gbin/M
                continue
            # Here x < 4/T0. Since t-tf/F < 1/F and t < T0+1,
            # 0 <= z-num/den <= 2*x/F + 2*t*x**3/(1-x*x) < 10**-8.
            # Interpolate G at num/den, enclosing the error: Off 2*pi,
            # |G''| < 2. Across the one kink cell use |G'| < 2 instead.
            kr = 2*(K//10**8) + (K//M**2 if gbin != 62831 else 2*K//M)
            gl = ((den-rem)*gs[gbin][0]+rem*gs[gbin+1][0])//den-kr
            gh = -(-((den-rem)*gs[gbin][1]+rem*gs[gbin+1][1])//den)+kr
            k = (m['rounded_count'](large,U,V,d)+m['rounded_count'](small,V,U,d))*m['PERM']
            for z, y in enumerate((max(gl,0),max(gh,0),max(-gh,0),max(-gl,0))):
                mass = y*(wl*vl if z % 2 == 0 else wh*vh)
                totals[z] += k*mass
                removed[z] += (8*m['PERM']-k)*mass

    def report(name, lo, hi):
        scale = 10**12
        print(name, (lo*scale)//1, -((-hi*scale)//1), "in units of 10^-12")

    u0,u1,v0,v1 = [Fraction(z,K*W**2) for z in totals]
    for name,lo,hi in [('u',u0,u1),('v',v0,v1),('u-v',u0-v1,u1-v0),('v/u',v0/u1,v1/u0)]:
        report(name, lo, hi)
    assert 87024*u1 < 100000*v0 <= 100000*v1 < 87025*u0
    assert Fraction(19007,10**12) < u0-v1 <= u1-v0 < Fraction(19008,10**12)
    # Unit normalization for the earlier endpoint detector, not a fitted B.
    scale_b = m['X'] / (m['D']*T*I(16**m['N']))
    assert 65000*Fraction(scale_b.hi) < u0-v1 <= u1-v0 < 66000*Fraction(scale_b.lo)
    p0,p1,n0,n1 = [Fraction(z,K*W**2) for z in removed]
    report('change from restoring rejected slots', p0-n1,p1-n0)
    jlo, jhi = u0-v1+p0-n1, u1-v0+p1-n0
    assert Fraction(-7800,10**12) < jlo <= jhi < Fraction(-7799,10**12)
    report('ungated signed sum',jlo,jhi)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without -O for certificate checks')
    main()
