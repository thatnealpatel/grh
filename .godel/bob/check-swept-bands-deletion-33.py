"""Price measurable laws in the bands swept by delete-33 seed boundaries."""
from pathlib import Path
from runpy import run_path

from sage.all import QQ

base = Path(__file__).resolve().parent
m = run_path(str(base/'check-mobile-mesh-deletion-33.py'))
F, seed, support = (m[k] for k in ('F', 'seed', 'maximum'))


def swept(radius, cells):
    phi, price, third = m['primitives']()
    assert radius > 0 and cells > 0 and cells % 2 == 0
    assert all(b-a > 2*radius for a, b in zip(seed, seed[1:]))
    h = 2*radius/cells
    core = bands = remainder = F(0)
    for i, z in enumerate(seed):
        l, r = z-radius, z+radius
        start = phi(r)
        end = phi(seed[i+1]-radius) if i+1 < len(seed) else (F(0),)*3
        core += support(*(a-b for a, b in zip(start, end)))
        # On each cell and for every u, the density price is bounded by
        # the chord plus h^2/8 times a uniform second derivative bound.
        # The endpoints' maximizing atoms need not coincide.
        nodes = [l+j*h for j in range(cells+1)]
        assert not (l < 0 < r) or 0 in nodes
        prices = [support(*(-v for v in phi(t, 1))) for t in nodes]
        bands += h*((prices[0]+prices[-1])/2+sum(prices[1:-1]))
        d3 = sum(third)*(-F(l)/2).exp() + (3 if r > 0 else 0)
        remainder += (r-l)*h**2*d3/8
    total = price+core+bands+remainder
    print(f'radius {radius}, {cells} cells/band, chord error {remainder}, upper surplus {total}', flush=True)
    return total


def relaxed_floor(radius, cells):
    """Lower bound on this dual's support price, not on a feasible surplus."""
    phi, price, _ = m['primitives']()
    assert radius > 0 and cells > 0
    assert all(b-a > 2*radius for a, b in zip(seed, seed[1:]))
    cuts = [z-radius+2*radius*j/cells for z in seed for j in range(cells+1)]
    values = [phi(t) for t in cuts]
    # Each Bernstein endpoint tested is the value at an actual atom.
    # The subslabs can choose these atoms independently in the relaxation.
    total = price + sum(support(*(a-b for a, b in zip(s, t)), lower=True)
                        for s, t in zip(values, values[1:]+[(F(0),)*3]))
    print(f'radius {radius}, {cells} subslabs/band, relaxed price >= {total}', flush=True)
    return total


if __name__ == '__main__':
    assert swept(QQ(1)/1000, 8) < F('-6.59e-7')
    assert swept(QQ(7)/4000, 16) < F('-7.90e-8')
    assert relaxed_floor(QQ(1)/250, 4) > F('5.01e-7')
