"""Replay the gap bridges using squared-imbalance pricing of mixtures."""
from runpy import run_path
from sage.all import QQ

root = '.godel/bob/'
neg = run_path(root+'check-negative-slab-strip.py')
mid = run_path(root+'check-midgap-sector.py')
engine = run_path(root+'check-imbalance-chords.py')
H = neg['H']
jumps, strip = engine['jumps'], engine['strip']
laws = [mid, dict(z=neg['z'], B=neg['changed']), H]
profiles = [jumps(H, law) for law in laws]


def bridge(weights, lo, hi):
    mix = {}
    for w, beta in zip(weights, profiles):
        for t,b in beta:
            if w:
                mix[t] = mix.get(t, 0) + QQ(w)/sum(weights)*b
    strip(sorted(mix.items()),QQ(lo),QQ(hi),H)


bridge((1,4,5), '663/1000', '18/25')
bridge((1,2,7), '18/25', '39/50')
bridge((1,0,9), '47/50', '1')
bridge((3,0,2), '141/100', '3/2')
bridge((9,0,1), '3/2', '37/20')

# In the remaining gap interval the hard-pair law covers the right tail.
strip(profiles[2],QQ(1),QQ(141)/100,H,s_min=QQ(1)/5)
