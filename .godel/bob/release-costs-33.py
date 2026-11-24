"""Upper increments for independently measurable release on each finite slab."""
from pathlib import Path
from runpy import run_path

from sage.all import QQ

base = Path(__file__).resolve().parent
neg = run_path(str(base/'check-measurable-negative-deletion-33.py'))
s = neg['shared']
F = s['F']


def release_costs(z, B, data, old):
    # Integrate the competitor's atom price only. The signed reference
    # correction is exactly the same in the cell and slab bounds.
    den = 1600
    h = QQ(1)/den
    lo, hi = int(2*den*z[0]), int(2*den*z[-1])
    assert all((t*400).is_integer() for t in z)
    a, b, *_ = s['tail_data'](z,B,data,range(lo,hi+1),2*den)
    m = [F(max(0,j))*h/2*(-F(max(0,j))*h/2).exp() for j in range(lo,hi+1)]

    def upper(a,b,m,negative):
        if negative:
            assert m.is_zero()
            return neg['atom_upper'](a,b)
        return s['bern_upper'](a,b,m,F('1e-12'))

    # curved_error includes h^3 exp(h/2)/192 and the negative envelope integral.
    scale = neg['curved_error'](z,B,data,den)/(2*((-F(z[0])/2).exp()-1))
    mass_scale = 3*h**3*(F(h)/2).exp()/192
    extra = []
    for t,r in zip(z,z[1:]):
        l0, r0 = int(2*den*t)-lo, int(2*den*r)-lo
        negative = t < 0
        ends = [upper(a[j],b[j],m[j],negative) for j in range(l0,r0+1,2)]
        controls = [upper(*(2*v[j]-(v[j-1]+v[j+1])/2 for v in (a,b,m)),negative)
                    for j in range(l0+1,r0,2)]
        val = h/3*(2*sum(ends)-ends[0]-ends[-1]+sum(controls))
        rem = (scale+(0 if negative else mass_scale))*2*((-F(t)/2).exp()-(-F(r)/2).exp())
        # If removing constancy slightly improves the computed upper due to
        # enclosure precision, use zero when accounting for optional releases.
        extra.append(max(0,(val+rem-old[t]).upper().exact_rational()))

    return extra
