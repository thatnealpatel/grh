"""Price the eight-knot frontier and localize five measurable delete-33 releases."""
import argparse
from concurrent.futures import ProcessPoolExecutor
from hashlib import sha256
from itertools import combinations_with_replacement
import json
from pathlib import Path
from runpy import run_path

from sage.all import QQ


base = Path(__file__).resolve().parent
prior = run_path(str(base/'check-seven-knots-deletion-33.py'))
p = run_path(str(base/'refined-prices-33.py'))
F, z, s = (p[key] for key in ('F', 'z', 's'))
UNIT, CUTOFF, CASES = (prior[key] for key in ('UNIT', 'CUTOFF', 'CASES'))
RELEASE_CASES = ('five-releases', 'five-release-minus-216', 'five-release-minus-2304')
DEN = 3200


def rounded(value):
    return int((value.upper().exact_rational()*UNIT).ceil())


def double_costs(center, data, sites):
    slabs = [(t,r) for t,r in zip(z,z[1:]) if int(400*t) in sites]
    assert len(slabs) == len(sites)
    points = sorted({j for t,r in slabs for j in range(int(2*DEN*t),int(2*DEN*r)+1)})
    a, b, _, _, curv = s['tail_data'](z,center,data,points,2*DEN,primitive=True)
    primitive = {j:(x,y,s['step'](QQ(j)/(2*DEN),0)) for j,x,y in zip(points,a,b)}
    eps = F('1e-14')

    def price(v,w):
        return s['bern_upper'](*(x-y for x,y in zip(v,w)),eps)

    costs = {}
    for t,r in slabs:
        lo, hi = int(2*DEN*t), int(2*DEN*r)
        controls = [primitive[j] if j%2 == 0 else
                    tuple(2*x-(y+w)/2 for x,y,w in
                          zip(primitive[j],primitive[j-1],primitive[j+1]))
                    for j in range(lo,hi+1)]
        left = [price(controls[0],v) for v in controls]
        right = [price(v,controls[-1]) for v in controls]
        # Ordered knots have a common ordered Bernstein coupling.
        maximum = max((left[i]+price(controls[i],controls[j])+right[j]).upper()
                      for i,j in combinations_with_replacement(range(len(controls)),2))
        error = (curv+(2 if t>=0 else 0))*(-F(t)/2).exp()/(DEN**3*72*F(3).sqrt())
        # bern_upper returns a lower bound for support plus eps. Subtract
        # the lower bound so this increment works with the prior base price.
        costs[int(400*t)] = max(0,rounded(F(maximum)+2*error-(left[-1]-eps)))
    return costs


def original_double_costs(job):
    case, sites = job
    data, center, _, _ = p['tangent_data'](p['load_certificate'](case))
    return double_costs(center,data,sites)


def new_prices(job):
    case, single_sites, double_sites, release_sites = job
    data, center, _, constant = p['tangent_data'](p['load_certificate'](case))
    _, original, old, _ = p['mesh_prices'](data,center,constant,400,[],60)

    def release(sites, den):
        return p['costs']['release_costs'](z,center,data,old,den,{QQ(k)/400 for k in sites})

    # Avoid recomputing prices on slabs not in any outstanding assignment.
    values = dict(zip(sorted(single_sites),release(single_sites,1600)))
    extra = [values.get(int(400*t),0) for t in z[:-1]]
    split, _ = p['single_knot_costs'](z,center,data,old,extra,QQ(15)/10**9,DEN)
    eight = {(int(400*t),1):int((v*UNIT).ceil()) for t,v in zip(z[:-1],split)
             if int(400*t) in single_sites}
    eight.update({(k,2):v for k,v in double_costs(center,data,double_sites).items()})
    five = {(k,1):int((v*UNIT).ceil()) for k,v in zip(sorted(release_sites),release(release_sites,DEN))} if release_sites else {}
    return rounded(original), eight, five


def screen(pending, base_price, costs):
    return [row for row in pending if base_price+sum(costs[k,c] for k,c in row) >= CUTOFF]


def original_case_price(case):
    # Wrap the run_path function so subprocesses can pickle the entry point.
    return prior['case_price'](case)


def omission_price(job):
    script = run_path(str(base/'check-eight-knots-omit-slab-33.py'))
    return script['price'](job)


def refit_prices(single_sites, double_sites):
    disk = run_path(str(base/'check-five-release-disk-price-33.py'))
    raw = (p['laws']/'delete-33-five-release-disk-price-k8.json').read_bytes()
    assert sha256(raw).hexdigest() == '4150ddbca857c6d79966354328bdb8791a3818a12e8506a9aafd844e8a9cc2ee'
    cert = json.loads(raw, parse_float=str)
    assert disk['tests_of'](cert) == disk['tests_of'](p['load_certificate']('eight-knots'))
    data, center, _, constant = p['tangent_data'](cert)
    _, original, old, _ = p['mesh_prices'](data, center, constant, 400, [], 60, tail_den=800)
    sites = single_sites | double_sites
    values = p['costs']['release_costs'](z, center, data, old, 1600, {QQ(k)/400 for k in sites})
    release = dict(zip(sorted(sites), values, strict=True))
    extra = [release.get(int(400*t), 0) for t in z[:-1]]
    split, _ = p['single_knot_costs'](z, center, data, old, extra, QQ(5)/10**9, 6400)
    costs = {(int(400*t), 1): int((v*UNIT).ceil()) for t, v in zip(z[:-1], split, strict=True)
             if int(400*t) in single_sites}
    costs.update({(k, 2): min(v, int((release[k]*UNIT).ceil()))
                  for k, v in double_costs(center, data, double_sites).items()})
    return rounded(original), costs


def cross_check(eight, omit_third, map_jobs):
    omit = run_path(str(base/'check-eight-knots-omit-slab-33.py'))['CASES']
    assert {sites for _, sites, _ in omit} == omit_third
    for (_, sites, _), value in zip(omit, map_jobs(omission_price, omit), strict=True):
        print('Omitting slab 4:', sites, value, flush=True)
        assert value < QQ(CUTOFF)/UNIT
    eight = [row for row in eight if 4 in dict(row)]
    assert len(eight) == 774
    single_sites, double_sites = ({k for row in eight for k, c in row if c == n} for n in (1, 2))
    base_price, costs = refit_prices(single_sites, double_sites)
    eight = screen(eight, base_price, costs)
    doubles = sum(any(c == 2 for _, c in row) for row in eight)
    assert (len(eight), doubles) == (155, 14)
    assert all(sum(dict(row).values()) == 8 and {0, 2, 4} <= dict(row).keys() for row in eight)
    negative = [[k for k, c in row if k < 0 for _ in range(c)] for row in eight]
    assert [sum(len(ks) == n for ks in negative) for n in range(3)] == [1, 109, 45]
    assert all(not ks or {-216, -2304}.intersection(ks) for ks in negative)
    assert [sorted(row) for row, ks in zip(eight, negative, strict=True) if not ks] == [
        [(k, 1) for k in range(0, 16, 2)]]
    print('k8 cross-price:', len(eight), 'unpaid;', doubles, 'with a double slab;',
          'negative units 0/1/2: 1/109/45', flush=True)
    return sorted(sorted(row) for row in eight)


def check(map_jobs):
    tables = list(map_jobs(original_case_price,CASES))
    prior['check'](tables,False)
    eight = prior['screen'](tables,8)
    assert len(eight) == 1289
    # The capped encoding records min(actual count, 2). At total 8
    # each 2 therefore represents exactly two, not more.
    assert all(sum(c for _,c in row)==8 for row in eight)
    double_sites = {k for row in eight for k,c in row if c==2}
    for (base_price,costs), local in zip(tables,map_jobs(original_double_costs,
            [(case,double_sites) for case,_,_ in CASES])):
        eight = [row for row in eight if base_price+sum(
            min(costs[k][2],local[k]) if c==2 else costs[k][c] for k,c in row) >= CUTOFF]
    assert len(eight) == 933
    doubles = [sum(c==2 for _,c in row) for row in eight]
    assert max(doubles) == 1 and sum(doubles) == 75
    print('Eight knots: 933 unpaid; only 75 with a double slab, none with two',flush=True)

    releases = [(b,{k:(0,v[2]) for k,v in cost.items()}) for b,cost in tables]
    five = prior['screen'](releases,5,(1,))
    assert len(five) == 14
    single_sites = {k for row in eight for k,c in row if c==1}
    double_sites = {k for row in eight for k,c in row if c==2}
    release_sites = {k for row in five for k,_ in row}
    cases = (*RELEASE_CASES,'eight-knots')
    jobs = [(case,single_sites,double_sites,release_sites if case in RELEASE_CASES else set())
            for case in cases]
    eight_counts = (884,878,812,776)
    five_counts = (9,8,7,7)
    for case, n8, n5, (base_price, knot_costs, release_costs) in zip(
            cases,eight_counts,five_counts,map_jobs(new_prices,jobs)):
        eight = screen(eight,base_price,knot_costs)
        if release_costs:
            five = screen(five,base_price,release_costs)
        print(case, 'unpaid eight-knot / five-release:',len(eight),len(five),flush=True)
        assert (len(eight),len(five)) == (n8,n5)
    assert sum(any(c==2 for _,c in row) for row in eight) == 67
    assert all(all(c == 1 for _, c in row) for row in eight if 4 not in dict(row))
    omit_third = {tuple(sorted(k for k,_ in row)) for row in eight if 4 not in dict(row)}
    assert omit_third == {(-2304,-216,0,2,6,8,10,12), (-216,0,2,6,8,10,12,14)}
    print('Eight knots: 67 unpaid with a double slab; omitting slab 4:',sorted(omit_third),flush=True)
    sites = {tuple(sorted(k for k,_ in row)) for row in five}
    assert sites == {(0,2,4,6,k) for k in range(8,17,2)} | {(0,2,4,8,10),(0,2,4,8,12)}
    print('Five measurable releases: unpaid slab starts in /400 units:',sorted(sites),flush=True)
    return cross_check(eight, omit_third, map_jobs)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs',type=int,default=1)
    parser.add_argument('--write-eight', type=Path,
                        help='write the checked residual assignments as JSON pairs [400*start, count]')
    args = parser.parse_args()
    if args.jobs == 1:
        eight = check(map)
    else:
        with ProcessPoolExecutor(max_workers=args.jobs) as pool:
            eight = check(pool.map)
    if args.write_eight:
        args.write_eight.write_text(json.dumps(eight, separators=(',', ':'))+'\n')
