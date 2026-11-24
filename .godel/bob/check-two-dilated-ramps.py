#!/usr/bin/env python3
"""Exact rational lower certificate for the two signed, dilated traces."""
from fractions import Fraction as F
from math import factorial, lcm

S1, S3 = F(3, 100), F(1, 5)   # log cutoff ratios
A, LAM = F(197, 200), F(69, 20)
N, D = 512, 10**14


def exp_box(x):
    # Taylor for exp(x/16), with absolute tail bounded by a geometric sum.
    r = x / 16
    assert abs(r) <= 1
    q = sum(r**j / factorial(j) for j in range(17))
    err = 2 * abs(r)**17 / factorial(17)
    assert q > err
    lo, hi = D*(q-err)**16, D*(q+err)**16
    return F(lo // 1, D), F(-(-hi // 1), D)


def scale(s, a):
    lo, hi = exp_box(-s/2)
    return a*lo, a*hi


A0, A1 = scale(S1, A)
B0, B1 = scale(S3, 1-A)
GRID = [(2*i*i*N**4-N**6,
         -32*i**6+48*i**4*N**2-18*i*i*N**4+N**6,
         i*N**5) for i in range(N+1)]


def minimum(r, s, z):
    # Bound the polynomial minimum with nonnegative kernel values r,s,
    # a mean coefficient z, and uncertain scale factors boxed above.
    a, b, c = A0*r, B0*s, z
    d = lcm(a.denominator, b.denominator, c.denominator)
    ai, bi, ci = (int(d*x) for x in (a, b, c))
    v = F(min(ai*u+bi*w-ci*y for u,w,y in GRID), d*N**6)
    # At an interior minimizer the derivative is zero; P'' <= 4a+51b.
    # Both endpoints are sampled, and distance to a sample is <= 1/(2N).
    out = v - (4*a+51*b)/(8*N*N) - (A1-A0)*r - (B1-B0)*s
    assert out <= 0
    return out


def endpoint(t):
    return minimum(max(0,t+S1), max(0,t+S3), LAM*max(0,t))


def weights(h):
    # Upper bounds for integrals of (1-z/h)*exp(-z) and (z/h)*exp(-z)
    # on [0,h]; integrate the fourth Taylor polynomial for exp(-z).
    w0 = sum((-h)**j / (factorial(j)*(j+1)*(j+2)) for j in range(5))
    w1 = sum((-h)**j / (factorial(j)*(j+2)) for j in range(5))
    return h*w0, h*w1


def main():
    # Finer mesh near z=0, where the minimum bends most sharply.
    t = ([-S3] + [-S1*i/16 for i in range(16,0,-1)]
         + [F(i,256) for i in range(128)]
         + [F(i,16) for i in range(8,16*8+1)])
    assert t[0] == -max(S1,S3) and {-S1,-S3,F(0)} <= set(t)
    assert all(x < y for x,y in zip(t,t[1:]))
    v = list(map(endpoint,t))
    lb = LAM*F(8,9)
    for x,y,l,r in zip(t,t[1:],v,v[1:]):
        w0,w1 = weights(y-x)
        # The envelope is concave between cutoffs and lies above this chord.
        # Both endpoint lower bounds are nonpositive; use upper weight bounds.
        lb += exp_box(-x)[1]*(l*w0 + r*w1)
    # For t >= t[-1] the unminimized expression is affine in t.
    # Lower-bound it by v[-1] + (t-t[-1])*minimum(1,1,LAM),
    # then integrate this line; both required exponential moments are 1.
    lb += exp_box(-t[-1])[1]*(v[-1] + minimum(F(1), F(1), LAM))
    # Truncate the displayed result downwards in exact arithmetic.
    digits = 10**10
    low = (digits*lb)//1
    assert F(low,digits) > F('.5895') > F('.587125')
    print(f'Certified lower bound: {low//digits}.{low%digits:010d} > .5895 > .587125')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O.')
    main()
