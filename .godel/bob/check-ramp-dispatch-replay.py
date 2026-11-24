#!/usr/bin/env python3
"""Exact rational replay of the two signed ramp tests. Run without -O."""
from fractions import Fraction as Q
from functools import cache
from math import comb

D = 10**20

def down(x):
    return Q(x * D // 1, D)

def up(x):
    return -down(-x)

@cache
def expI(x):
    """Return rational bounds on exp(x): scale, Taylor + geometric tail, power."""
    if x < 0:
        a,b = expI(-x)
        return down(1/b), up(1/a)
    r = x/32
    assert 0 <= r <= Q(1,2)
    term = s = Q(1)
    for i in range(1,21):
        term *= r/i
        s += term
    e = term*r/21 / (1-r/22)
    return down(s**32), up((s+e)**32)

def price(c):
    a,b = expI(c)
    d,e = expI(-c)
    return (a+d)/6, (b+e)/6

def bern(p):
    n = len(p)-1
    return [sum(p[i]*Q(comb(k,i),comb(n,i)) for i in range(k+1))
            for k in range(n+1)]

def split(b):
    left,right = [b[0]],[b[-1]]
    while len(b)>1:
        b = [(x+y)/2 for x,y in zip(b,b[1:])]
        left.append(b[0]);right.append(b[-1])
    return left,right[::-1]

def minlo(p, tol):
    """Certify min p >= best-tol. Stack covers all unpruned subintervals."""
    b = bern(p)
    best = min(b[0],b[-1]) # values at endpoints, so an upper bound
    stack = [(b,0)]
    while stack:
        b,depth = stack.pop()
        best = min(best,b[0],b[-1])
        if min(b) >= best-tol:
            continue
        assert depth < 30
        left,right = split(b)
        stack.extend(((left,depth+1),(right,depth+1)))
    return best-tol

def lower():
    l1,l3,alpha,k = map(Q, ('.028','.21','.985','3.454'))
    # Rational surrogate weights; integrate their absolute errors globally.
    def round_exp(l):
        a,b = expI(-l/2)
        return (a+b)/2, (b-a)/2
    v1,e1 = round_exp(l1)
    v3,e3 = round_exp(l3)
    change = alpha*e1*expI(l1)[1]+(1-alpha)*e3*expI(l3)[1]
    def w(z):
        return alpha*v1*max(z+l1,0), (1-alpha)*v3*max(z+l3,0), k*max(z,0)
    right = 16
    grid = sorted(set([-l3,-l1] + [Q(j,50) for j in range(50*right+1)]))
    bs=[]
    for z in grid:
        A,B,L=w(z)
        bs.append(minlo([B-A,-L,2*A-18*B,0,48*B,0,-32*B], Q(1,1000000)))
    assert all(b<0 for b in bs)
    ans = k*Q(8,9)-change
    for x,y,b,c in zip(grid,grid[1:],bs,bs[1:]):
        h = y-x
        assert 0<h<1
        u,v = expI(-x)
        s,t = expI(-y)
        # Upper bounds on positive interpolation weights, b and c are negative.
        Wleft=((h-1)*u+t)/h
        Wright=(v-(1+h)*s)/h
        assert Wleft>0 and Wright>0
        ans += down(b*Wleft+c*Wright)
    # On z >= right, min polynomial is bounded below by -A-B-L.
    A,B,L=w(Q(right+1))
    ans -= (A+B+L)*expI(Q(-right))[1]
    assert price(Q('1.17'))[1] < Q('.588727') < Q('.58947') < ans
    print('fixed-pair certificate > .58947; rational floor at 1e-10:', ans*10**10//1)


def upper():
    L,a,p=map(Q,('.28','.8824','.8333'))
    Mlo=(1+L)*expI(-L)[0]
    meanlo=Q(1,2)+(1-p*(1-a)-Q(1,2))*Mlo
    assert meanlo > Q('.88889987') > Q(8,9)
    funcs=[lambda u:2*u*u-1, lambda u:1-18*u*u+48*u**4-32*u**6]
    for h,x,y in zip(funcs, map(Q,('.36390','.23397')), map(Q,('.36391','.23398'))):
        d=p*h(a)+(1-p)*h(Q(1))
        b=-h(Q(1,2))
        q=d+b
        assert b>0 and d>0 and 0<x<y<1
        # All l >= -L have t=l+L >= 0; derivative sign is sign of q(1-t)-b exp(t).
        assert q*(1-x)-b*expI(x)[1]>0
        assert q*(1-y)-b*expI(y)[0]<0
        brackethi=-b*expI(x/2)[0]+q*(1+y)*expI(-x/2)[1]
        assert brackethi>0
        hi=expI(-L/2)[1]*brackethi
        # l < -L gives d exp(l/2) <= C(-L) <= this maximum.
        assert hi<Q('.59702')
        print('uniform signed upper bound < .59702; rational ceiling at 1e-10:', -(-hi*10**10//1))
    assert Q('.59702') < Q('.60355') < price(Q('1.2'))[0]

if __name__=='__main__':
    if not __debug__:
        raise SystemExit('Run without -O.')
    lower()
    upper()
