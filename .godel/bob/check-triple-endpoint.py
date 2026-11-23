"""Sign-relaxed endpoint caps on prime blocks, at and around the named y."""
from itertools import combinations, product

from sage.all import ComplexIntervalField, QQ, RealIntervalField, prime_range

if not __debug__:
    raise RuntimeError('run with assertions enabled')
R = RealIntervalField(160)
CC = ComplexIntervalField(160)
y = R(2**127-1)**(QQ(3)/5)
x = (3*y.log())**2
x_moving = (3*(y+R(-11, 11)).log())**2
assert 25107 < x_moving < 25108
logs = [R(p).log() for p in prime_range(25108)]
weights = [a*(x.log()-a)/x for a in logs]
cutoff_cost = sum(abs(a*(x_moving.log()-a)/x_moving-w)
                  for a, w in zip(logs, weights))
assert cutoff_cost < QQ(1)/10**18

for size in (2, 3):
    cap = lip = diagonal = cross = first = score = R(0)
    for i in range(0, len(logs), size):
        a, w = logs[i:i+size], weights[i:i+size]
        m = sum(w)
        assert all(v > 0 for v in w)
        root = a[len(a)//2]
        phases = [y*(v-root) for v in a]
        z = [b*CC(u.cos(), u.sin()) for b, u in zip(w, phases)]
        best = R(0)
        for signs in product((1, -1), repeat=len(z)-1):
            best = best.max(abs(z[0]+sum(s*v for s, v in zip(signs, z[1:]))))
        cap += best
        lip += sum(b*abs(v-root) for b, v in zip(w, a))
        if size == 3:
            diagonal += sum(b*b for b in w)/m
            for j, k in combinations(range(len(a)), 2):
                coeff = 2*w[j]*w[k]/m
                u = 2*y*(a[k]-a[j])
                cross += coeff
                c1 = coeff*u.cos()
                first += c1
                score += 7*c1-coeff*(2*u).cos()
    radius = {2: 1, 3: 11}[size]
    assert cap+radius*lip+cutoff_cost < QQ(8)/9
    if size == 2:
        assert QQ(883795)/10**6 < cap < QQ(883796)/10**6
    else:
        assert QQ(839117)/10**6 < cap < QQ(839118)/10**6
        assert lip < QQ(437)/10**5
        mass = sum(weights)
        one_cap = (mass*(mass+(mass*(diagonal+first)).sqrt())/2).sqrt()
        assert QQ(872976)/10**6 < one_cap < QQ(872977)/10**6
        linear_cap = (mass*(diagonal+2*cross/3+score/18)).sqrt()
        assert QQ(867177)/10**6 < linear_cap < QQ(867178)/10**6
        print('two-mode cap at center:', linear_cap)
    print(size, 'block cap, frozen Lipschitz bound:', cap, lip)
