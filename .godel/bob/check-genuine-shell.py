#!/usr/bin/env python3
"""Enclose the genuine [t, 5t/4] high-branch integral. Run without -O."""
from bisect import bisect_left, bisect_right
from collections import defaultdict
from functools import cache
from pathlib import Path
from runpy import run_path

f = run_path(str(Path(__file__).with_name('check-complete-shift.py')))
I, t, X, D, tau, trig = (f[k] for k in ('I','T','X','D','TAU','trig'))
f['certified_geometry']()
p = f['plan'](26)[2]
w = [(X/I(i)).log()*I(i).log()*I(i+26).log()/X for i in p]
a = [(I(i+26)/I(i)).log() for i in p]
F = 2**50
first, stop = 126191, 157740
end = I(5)*t/I(4)
assert first < t.lo <= t.hi < first+1 and stop-1 < end.lo <= end.hi < stop
assert end.hi < (I(13)*t.log()/I(8)).exp().lo and t.lo > 1
cut = (-D/I(5)).exp()*I(F*F)


def fixed(z):
    z = z*I(F)
    v = int(z.lo)
    assert (z-I(v)).lo >= -2 and (z-I(v)).hi <= 2
    return v


def cis(z, weight):
    z = z - I(int((z/tau).lo))*tau
    return fixed(weight*trig(z,False)), fixed(weight*trig(z,True))


def rotate(c, rot, sign=1):
    return [((u*x-sign*v*y)//F, (v*x+sign*u*y)//F)
            for (u,v),(x,y) in zip(c,rot)]


c = [cis((I(first)+I('.5'))*v,g) for v,g in zip(a,w)]
one = [cis(v,I(1)) for v in a]
depth = 9
turn = [[cis(v/I(2**(j+2)),I(1)) for v in a] for j in range(depth)]
# Complex error < 3/F initially. At each rotation, errors are propagated
# by the exact unit rotation; the approximate input has norm < 1 by
# induction (true norm < .5), so the rounded multiplier adds < 3/F,
# and the two final integer divisions add < 2/F. All paths use < 32000
# rotations. The padding below includes this entire absolute error.
assert max(v.hi for v in w) < .5 and stop-first+depth < 32000
pad = [[160010 + int((I(F)*v*g/I(2**(j+1))).hi)+1 for v,g in zip(a,w)]
       for j in range(depth+1)]
nb = [(bisect_left(p, i-49), bisect_right(p, i+49)) for i in p]


def prod(al, ah, bl, bh):
    e = al*bl, al*bh, ah*bl, ah*bh
    return min(e), max(e)


def sq(lo, hi):
    return (0 if lo<=0<=hi else min(lo*lo,hi*hi)), max(lo*lo,hi*hi)


@cache
def exponential(hundredths):
    return (I(hundredths)/I(100)).exp()


@cache
def kernel(block):
    bounds = I(max(first, block*1000), min(stop, (block+1)*1000))
    z = abs(tau/I(2)*(bounds/t-I(1)))
    z2 = z*z
    lo = I(1)-z2/I(6)
    hi = lo+z2*z2/I(120)
    assert z.hi < 1 and lo.lo > 0
    return I((lo*lo).lo,min(1,(hi*hi).hi))


byblock = defaultdict(lambda: I(0))
tB = X/D/I(16**8)

crest = I(0)


def visit(c, j, unit, index):
    global crest
    e = pad[j]
    error = sum(e)
    R = sum(u for u, _ in c)
    J = sum(v for _, v in c)
    rl, rh, jl, jh = R-error, R+error, J-error, J+error
    l, h = sq(rl, rh)
    m, k = sq(jl, jh)
    l += m
    h += k
    if h < cut.lo:
        return
    if j < depth:
        for sign in (-1,1):
            visit(rotate(c,turn[j],sign),j+1,unit,2*index+(sign==1))
        return
    assert l>0
    # Numerators of Re(c_i/Z); common denominator |Z|^2.
    lows = [0]
    highs = [0]
    for (u,v),err in zip(c,e):
        bl, bh = prod(u-err, u+err, rl, rh)
        dl, dh = prod(v-err, v+err, jl, jh)
        lows.append(lows[-1]+bl+dl)
        highs.append(highs[-1]+bh+dh)
    ql = qh = 0
    for i,(b,endidx) in enumerate(nb):
        v,V=prod(lows[i+1]-lows[i],highs[i+1]-highs[i],
                 lows[endidx]-lows[b],highs[endidx]-highs[b])
        ql += v
        qh += V
    # E = -32 Q/|Z|^4. Directed integer divisions in hundredths.
    lo = min((-3200*qh)//den for den in (l*l, h*h))
    hi = max(-((3200*ql)//den) for den in (l*l, h*h))
    val = I(l**4,h**4)/I(F**8) * I(exponential(lo).lo,exponential(hi).hi)
    val = val*kernel(unit//1000)/(I(2**depth)*tB)
    if l <= cut.hi or unit in (first,stop-1):
        val=I(0,val.hi)  # threshold-straddling or partly outside the shell
    byblock[unit//1000] = byblock[unit//1000]+val
    # Charge the intersection with the distinguished 0.2-wide interval.
    if 133637 <= unit <= 133638:
        left = 10*((unit-133638)*2**depth+index)
        right = left+10
        if left < 2**depth and right > -2**depth:
            crest = crest + (val if -2**depth <= left and right <= 2**depth
                             else I(0,val.hi))


for unit in range(first,stop):
    visit(c,0,unit,0)
    c=rotate(c,one)
total = sum(byblock.values(), I(0))
# A sliding length-1000 interval touches at most two consecutive blocks
# in positive measure. Bound the fraction, paying the complement below.
fractions = []
for b in range(first//1000-1, stop//1000+1):
    pair = byblock[b]+byblock[b+1]
    outside = sum((v for k,v in byblock.items() if k not in (b,b+1)), I(0))
    fractions.append((I(pair.hi)/(I(pair.hi)+I(outside.lo))).hi)
named = [cis(t*v,g) for v,g in zip(a,w)]
u = sum(x for x, _ in named)
v = sum(y for _, y in named)
err = 2*len(p)
assert sq(u-err,u+err)[1]+sq(v-err,v+err)[1] < cut.lo
assert 11290 < total.lo <= total.hi < 13440
assert max(fractions) < I('.252').lo
assert 127 < crest.lo <= crest.hi < 300
print('Shell mass in (11290, 13440) B_unit; every length-1000 interval takes < 25.2%.')
print('Named center below cutoff; [133637.9, 133638.1] contributes (127, 300) B_unit.')
