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
ASSIGNMENTS = (tuple((0, 2, 4, 6, k) for k in (8, 10, 12, 14, 16))
               + ((0, 2, 4, 8, 10), (0, 2, 4, 8, 12)))
RECENTERED = (0, 2, 4, 6, 14)


def release_spans(den, assignments=ASSIGNMENTS):
    assert den % 400 == 0  # Kernel branches lie on cell endpoints.
    right = dict(zip(z, z[1:]))
    sites = sorted({k for assignment in assignments for k in assignment})
    for k in sites:
        assert right[QQ(k)/400] == QQ(k+2)/400
    return {k: range(k*(2*den//400), (k+2)*(2*den//400)+1) for k in sites}


def moved_tangent(recentered=False):
    raw = (laws/'delete-33-five-release-joint-refit.json').read_bytes()
    assert sha256(raw).hexdigest() == '0b288072bc772e52fc7fb42aea4ca8544cc2d5e40d90e19d1d18e2de47bb54e2'
    cert = json.loads(raw, parse_float=str)
    if recentered:
        name = 'recentered'
        digest = '6919aabb9f9a92fe8640707a5d1aeb754c89b4771df73aa3508149d40ec235ec'
    else:
        name = 'independent'
        digest = 'aa5b9753c4eea8f0c460a7505bf606fa88cc77e4e0e1f9d4b208841825d3568c'
    raw_weights = (laws/f'delete-33-five-release-{name}-price.json').read_bytes()
    assert sha256(raw_weights).hexdigest() == digest
    weights = json.loads(raw_weights)
    rows = [row for row in cert['cuts'] if len(row) == 5]
    assert len(rows) == 665
    assert len(weights) == (len(rows) if recentered else 91)
    for key, w in weights.items():
        i = int(key)
        assert str(i) == key and 0 <= i < len(rows)
        assert (recentered or rows[i][0] == 0) and F(w) > 0
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


def measurable_uppers(data, center, constant, assignments=ASSIGNMENTS):
    # Each assignment replaces only its five ordinary slab supports.
    # The unmodified slabs and the entirely measurable tail are shared.
    _, ordinary, slab, _ = p['mesh_prices'](data, center, constant, 400, [], 60, tail_den=800)
    den = 12800
    spans = release_spans(den, assignments)
    nodes = sorted({i for span in spans.values() for i in span})
    a, b, *_ = s['tail_data'](z, center, data, nodes, 2*den)
    m = [F(i)/(2*den)*(-F(i)/(2*den)).exp() for i in nodes]
    sample = dict(zip(nodes, zip(a, b, m), strict=True))
    h = F(1)/den
    scale = p['neg']['curved_error'](z, center, data, den)/(2*((-F(z[0])/2).exp()-1))
    scale += 3*h**3*F(h/2).exp()/192
    increment = {}
    for k, span in spans.items():
        rows = [sample[i] for i in span]
        ends = [support(*row)[1] for row in rows[::2]]
        controls = [support(*(j['control'](*v) for v in zip(*rows[i-1:i+2])))[1]
                    for i in range(1, len(rows)-1, 2)]
        err = 2*scale*((-F(k)/800).exp()-(-F(k+2)/800).exp())
        increment[k] = h*(2*sum(ends)-ends[0]-ends[-1]+sum(controls))/3+err-slab[QQ(k)/400]
    return {ks: ordinary+sum(increment[k] for k in ks) for ks in assignments}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--self-test', action='store_true')
    ap.add_argument('--recentered', action='store_true',
                    help='Use the separate all-row price for the release at 14/400.')
    args = ap.parse_args()
    j['self_test']()
    spans = release_spans(12800)
    assert SITES in ASSIGNMENTS and all(len(set(ks)) == 5 for ks in ASSIGNMENTS)
    assert list(spans) == list(range(0, 17, 2)) and all(len(span) == 129 for span in spans.values())
    assert spans[12].start == 768 and spans[12][-1] == 896
    assert tuple(release_spans(12800, (RECENTERED,))) == RECENTERED
    data, center, _, constant = moved_tangent(args.recentered)
    if args.self_test:
        assert sum(len(row) == 3 for row in data) == 1
        return
    if args.recentered:
        bounds = measurable_uppers(data, center, constant, (RECENTERED,))
        print('Recentered measurable upper', RECENTERED, bounds[RECENTERED], flush=True)
        assert bounds[RECENTERED] < F('-1e-10')
        return
    upper = mesh_upper(data, center, constant)
    print('Independent-atom mesh upper:', upper, flush=True)
    assert upper < F('-7.2e-10')
    bounds = measurable_uppers(data, center, constant)
    for ks, upper in bounds.items():
        print('Full measurable upper', ks, upper, flush=True)
    assert bounds[(0, 2, 4, 6, 16)] < F('-6.0e-10')
    assert bounds[(0, 2, 4, 8, 12)] < F('-4.0e-10')


if __name__ == '__main__':
    assert __debug__
    main()
