"""Reprice the five releases with independent laws at depth 39/20."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
from runpy import run_path

from sage.all import QQ

base = Path(__file__).resolve().parent
j = run_path(str(base/'check-five-release-joint-refit-33.py'))
p, s, F, z = (j[k] for k in ('p', 's', 'F', 'z'))
DEN, SITES, support = (j[k] for k in ('DEN', 'SITES', 'support'))
laws = p['laws']


def moved_tangent():
    raw = (laws/'delete-33-five-release-joint-refit.json').read_bytes()
    assert sha256(raw).hexdigest() == '0b288072bc772e52fc7fb42aea4ca8544cc2d5e40d90e19d1d18e2de47bb54e2'
    cert = json.loads(raw, parse_float=str)
    raw_weights = (laws/'delete-33-five-release-independent-price.json').read_bytes()
    assert sha256(raw_weights).hexdigest() == 'aa5b9753c4eea8f0c460a7505bf606fa88cc77e4e0e1f9d4b208841825d3568c'
    weights = json.loads(raw_weights)
    rows = [row for row in cert['cuts'] if len(row) == 5]
    assert len(weights) == 91
    for key, w in weights.items():
        i = int(key)
        assert str(i) == key and 0 <= i < len(rows)
        assert rows[i][0] == 0 and F(w) > 0
        rows[i][-1] = w
    return p['tangent_data'](cert)


def mesh_upper(data, center, constant):
    # This mesh and remote law match the stored recovery law. No atom
    # table, grouping, or restrictions on probability weights are used.
    scale = DEN//400
    tail = [*range(2320, 5200, 8), *range(5200, 8800, 16),
            *range(8800, 12800, 32), *range(12800, 16000, 64),
            *range(16000, 22400, 128), 22400]
    fixed = [int(t*400) for t in z[:-1]]+tail
    interior = [i for k in SITES for i in range(k*scale+1, (k+2)*scale)]
    points = {}
    for nodes, den in ((fixed, 400), (interior, DEN)):
        a, b, *_ = s['tail_data'](z, center, data, nodes, den, primitive=True)
        points.update((k*(DEN//den), (aa, bb, s['step'](QQ(k)/den, 0)))
                      for k, aa, bb in zip(nodes, a, b, strict=True))
    mesh = sorted(points)
    assert len(mesh) == 2702
    A, B, U = s['unfold']['lattice']['prime_rows'](p['ref'].decode())[1:]
    a, b, m = points[mesh[-1]]
    remote = m*U[-1]-a*A[-1]-b*B[-1]
    return constant+remote+sum(support(*(a-b for a, b in zip(points[l], points[r])))[1]
                               for l, r in zip(mesh, mesh[1:]))


def measurable_upper(data, center, constant):
    # Replace the ordinary mesh supports on the five selected slabs
    # by pointwise support integrals. The tail is entirely measurable.
    _, ordinary, slab, _ = p['mesh_prices'](data, center, constant, 400, [], 60, tail_den=800)
    den = 12800
    assert den % 400 == 0  # Kernel branches lie on cell endpoints.
    spans = [range(k*(2*den//400), (k+2)*(2*den//400)+1) for k in SITES]
    nodes = sorted({i for span in spans for i in span})
    a, b, *_ = s['tail_data'](z, center, data, nodes, 2*den)
    m = [F(i)/(2*den)*(-F(i)/(2*den)).exp() for i in nodes]
    sample = dict(zip(nodes, zip(a, b, m), strict=True))
    h = F(1)/den
    scale = p['neg']['curved_error'](z, center, data, den)/(2*((-F(z[0])/2).exp()-1))
    scale += 3*h**3*F(h/2).exp()/192
    upper = ordinary
    for k, span in zip(SITES, spans, strict=True):
        rows = [sample[i] for i in span]
        ends = [support(*row)[1] for row in rows[::2]]
        controls = [support(*(j['control'](*v) for v in zip(*rows[i-1:i+2])))[1]
                    for i in range(1, len(rows)-1, 2)]
        err = 2*scale*((-F(k)/800).exp()-(-F(k+2)/800).exp())
        upper += h*(2*sum(ends)-ends[0]-ends[-1]+sum(controls))/3+err-slab[QQ(k)/400]
    return upper


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--self-test', action='store_true')
    args = ap.parse_args()
    j['self_test']()
    if args.self_test:
        data, _, _, _ = moved_tangent()
        assert sum(len(row) == 3 for row in data) == 1
        return
    data, center, _, constant = moved_tangent()
    upper = mesh_upper(data, center, constant)
    print('Independent-atom mesh upper:', upper, flush=True)
    assert upper < F('-7.2e-10')
    upper = measurable_upper(data, center, constant)
    print('Full measurable upper:', upper, flush=True)
    assert upper < F('-6.0e-10')


if __name__ == '__main__':
    assert __debug__
    main()
