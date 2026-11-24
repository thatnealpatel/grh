"""Close the final two-query rectangle. Run with Sage from the repository root."""
from os import environ
from runpy import run_path
from sage.all import QQ

root = '.godel/bob/'
environ['TWO_TERM_LAW'] = 'hard-pair'
hard = run_path(root+'check-two-term-10-2.py')
right = run_path(root+'right-sector-check.py')
engine = run_path(root+'check-imbalance-chords.py')
assert right['name'] == 'right-sector' and hard['hard_pair']
# Constant mixture of whole prime laws. Sum jumps at coincident knots
# before computing either quadratic kernel of the new first moment.
beta = {}
for n, law in [(3, right), (7, hard)]:
    for t, b in engine['jumps'](hard, law):
        beta[t] = beta.get(t, 0) + QQ(n)/10*b
surplus = (3*right['mean_margin']+7*hard['mean_margin'])/10
assert surplus > QQ(266)/10**9
print('Mixed-law angular surplus:', surplus, flush=True)
engine['strip'](sorted(beta.items()), QQ(1), QQ(141)/100, hard, s_min=-QQ(9)/50)
