"""Reprice refined finite delete-33 meshes with moved quadratic tangents."""
import argparse
from fractions import Fraction
from pathlib import Path
from runpy import run_path

from sage.all import QQ


price = run_path(str(Path(__file__).resolve().with_name('refined-prices-33.py')))
F, s, costs, z, B = (price[k] for k in ('F', 's', 'costs', 'z', 'B'))
upper, single_knot_costs = (price[k] for k in ('upper', 'single_knot_costs'))

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--certificate', choices=('three-midpoints', 'first-fit', 'eight-piece', 'six-knots'), default='three-midpoints')
case = parser.parse_args().certificate
data, center, sigma, constant = price['tangent_data'](price['load_certificate'](case))
refined = case in ('eight-piece','six-knots')
finite_den = 1600 if refined else 400
added = [j for j in range(1,24) if j % 8] if refined else [1,3,5]
bound, original, old, tail_data = price['mesh_prices'](data, center, constant, finite_den, added)
a, b, m, den, tail, err, remote = tail_data
print(case, 'fixed mesh, surplus upper:',bound,flush=True)
if case == 'first-fit':
    assert bound < F('-1.43881e-8')
    raise SystemExit(0)

extra = costs['release_costs'](z,center,data,old)
rank = sorted(zip(extra,z[:-1]),reverse=True)
print('Original price and top measurable increments:',original,rank[:5],flush=True)
if case == 'eight-piece':
    assert bound < F('-4.60062e-8')
    early = original+sum(e for t,e in zip(z,extra) if QQ(0)<=t<QQ(3)/200)
    four = original+sum(e for e,_ in rank[:4])
    five = original+sum(e for e,_ in rank[:5])
    negative = original+sum(e for t,e in zip(z,extra) if t<0)
    print('Measurable on [0,3/200), surplus upper:',early,flush=True)
    print('Best four and five finite releases, upper prices:',four,five,flush=True)
    print('All negative and all finite releases, upper prices:',negative,original+sum(extra),flush=True)
    assert early < F('-4.13718e-8') and four < F('-3.83838e-9')
    assert negative < F('-4.68429e-8')
    split, _ = single_knot_costs(z,center,data,old,extra,QQ(20)/10**9)
    negative_one = negative+max(j for t,j in zip(z[:-1],split) if t>=0)
    print('All negative releases plus one nonnegative real knot, surplus upper:',negative_one,flush=True)
    assert negative_one < F('-4.0298e-9')
    raise SystemExit(0)
if case == 'six-knots':
    split, _ = single_knot_costs(z,center,data,old,extra,QQ(15)/10**9)
    # Each slab can be unchanged, get one knot, or be released for
    # the price of two knots. The budget is at most k knots.
    best = [QQ(0)]*7
    for j,d in zip(split,extra):
        best = [max(best[k], best[k-1]+j if k>=1 else 0,
                    best[k-2]+d if k>=2 else 0) for k in range(7)]
    five_knots, six_knots = (original+best[k] for k in (5,6))
    five_releases = original+sum(e for e,_ in rank[:5])
    print('Five and six real knots, surplus uppers:',five_knots,six_knots,flush=True)
    print('Best five finite releases, upper price:',five_releases,flush=True)
    assert five_knots < F('-2.78406e-8') and six_knots < F('-3.38686e-10')
    raise SystemExit(0)
assert bound < F('-2.51350e-8')

split, prim = single_knot_costs(z,center,data,old,extra,QQ(32)/10**9)
worst = sorted(zip(split,z[:-1]),reverse=True)[:3]
print('Largest single-knot increments (left endpoint, upper increment):',
      [(t,float(y)) for y,t in worst],flush=True)
distinct = original + sum(y for y,_ in worst)
# If two or more knots land on one slab, release it completely. The
# remaining knot may split another slab or land on the released slab.
repeated = original+max(e+max(split[:i]+split[i+1:]) for i,e in enumerate(extra))
print('Three distinct slabs; repeated slab:',distinct,repeated,flush=True)
assert distinct < F('-1.46808e-8') and repeated < F('-3.83716e-8')

# If there is no limit on the subdivisions in each of three chosen
# slabs, which triples are not already excluded by the measurable price?
unpaid = []
for i,(e,t) in enumerate(rank[:-2]):
    if original+3*e < 0:
        break
    for j in range(i+1,len(rank)-1):
        f,r = rank[j]
        if original+e+2*f < 0:
            break
        for g,v in rank[j+1:]:
            if original+e+f+g < 0:
                break
            unpaid.append(sorted(int(400*x) for x in (t,r,v)))
print('Unpaid measurable triples (left endpoints in units 1/400):',sorted(unpaid),flush=True)

# Restore the quadratic remainder; also test one contrast per moment
# on each refined slab. Delta is the mean on its right four pieces
# minus the mean on its left four pieces (equal widths).
coeff = [[x-y for x,y in zip(prim[j],prim[j+2])] for j in range(0,48,2)]
unit = [upper(*v) for v in coeff]
free = original-sum(old[QQ(t)/400] for t in (0,2,4))+sum(unit)
print('Eight-piece upper price; necessary Q(V_B-Z) upper:',free,free/F(sigma),flush=True)
# Every first-cap slack is nonnegative and enters the SAME raw price
# as the quadratic remainder. Test the total response needed in a band.
band = [r for r in data if len(r)==5 and r[0]==1 and 40<=Fraction(r[1])<=80]
assert len(band)==254
S = sum(F(r[-1]) for r in band)
_, band_prim, *_ = s['tail_data'](z,B,band,[int(400*t) for t in z],400,primitive=True)
hb = [l-r for l,r in zip(band_prim,band_prim[1:])]
ref_slack = S-sum(h*y for h,y in zip(hb,B))-band_prim[-1]*B[-1]
# Everywhere |delta B| <= 2 and the directional density is bounded
# by S exp(-t/2)/C. Release even measurable fields on [0,.015) and tail.
release = 4*S/s['C']*(1-(-F(3)/400).exp()+(-F(29)/10).exp())
positive = sum(abs(h)-h*y for t,h,y in zip(z,hb,B) if t>=QQ(3)/200)
needed = ref_slack-free-release-positive
radius = QQ(915)/10000
possible = sum(min((abs(h)*radius).upper(), (abs(h)-h*y).upper()).exact_rational()
               for t,h,y in zip(z,hb,B) if t<0)
print('Band reference slack, release, positive, needed negative, capped negative:',
      ref_slack, release, positive, needed, F(possible),flush=True)
assert ref_slack > F('5.11565e-8') and ref_slack-free > F('4.1530e-8')
assert positive < F('1.1550e-8')
assert needed > F('1.9284e-8') and needed > possible
for i in (0,8,16):
    gains = []
    for col in range(3):
        lows = []
        for n in range(-30,-7):
            k = F(2)**n
            total = free-sum(unit[i:i+8])
            for j in range(8):
                v = coeff[i+j][:]
                # The score has coefficients (-a,-b,+m).
                v[col] += (1 if (col==2)==(j<4) else -1)*k/4
                total += upper(*v)
            lows.append((-total/k).lower())
        gains.append(float(max(lows)))
    print('Necessary right-minus-left four-piece means (A,B,U), slab',i//8,':',gains,flush=True)

# Preflight the retained *linear* functional on step tails as well.
# bern_upper returns best+eps with best attained or exceeded by a
# sampled atom. Integrate interpolants before maximizing for a lower
# bound (one atom per coarse cell); subtract the uniform errors.
def lower(a,b,m):
    return upper(a,b,m)-F('1e-14')

cells = []
for v in (a,b,m):
    cells.append([(l+4*mid+r)/(6*den) for l,mid,r in zip(v[::2],v[1::2],v[2::2])])
rest = original-tail-err-remote-sum(old[QQ(t)/400] for t in (0,2,4))
# 1,253 retained finite slab bounds, each within eps of its support.
rest -= (len(z)-1-3)*F('1e-14')
for width in (40,20,10,1):
    tail_lower = sum(lower(*(sum(v[i:i+width]) for v in cells)) for i in range(0,len(cells[0]),width))-err-remote
    # Fixed equal subdivisions on all three slabs; no optimization of
    # their positions. Bound the true unpenalized-by-caps atom support
    # of the raw linear price from below, not the objective surplus.
    for pieces in (4,8):
        stride = 16//pieces
        early = sum(lower(*(x-y for x,y in zip(prim[j],prim[j+stride]))) for j in range(0,48,stride))
        print('Linear price lower, finite pieces per released slab and tail step:',pieces,QQ(width)/den,rest+early+tail_lower,flush=True)
    if rest+early+tail_lower > 0:
        break
