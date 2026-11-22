# Direct arguments versus `tool_think`

Should Blitz call `tool_think` before attempting a bounded argument? In session
`01a203d3-a354-7089-ae50-bcb5f1d71d4d`, Sol agent `JVjyCLb` reconstructed one
scoped result per historical commit, not the whole commit. It froze the direct
answers before giving the same nine problem packets to `tool_think`, without the
direct answers. Each call returned two candidates. The agent chose return index
zero as primary after the first call and before inspecting the landed solutions;
it did not pick whichever answer later scored better.

| Formulation | Historical revisions | Direct passes | Primary tool passes | Median seconds, direct / tool |
| --- | --- | ---: | ---: | ---: |
| Prose | `712bcb9f1779`, `110c36e69086`, `e46ddc2d6060` | 3/3 | 3/3 | 13 / 51 |
| Lean | `98af67e3eaae`, `bedd6b317afc`, `9bfb408ef0c7` | 0/3 | 1/3 | 24 / 80 |
| Mixed | `7026d477e8ee`, `69346197c3e5`, `651eb7207c2b` | 2/3 | 2/3 | 23 / 70 |

A pass required a complete argument for prose, a compiling declaration with only
the allowed axioms for Lean, and both for mixed. Submitted Lean proofs were not
repaired. The extra Lean pass was a local character integral: Both answers found
the translation argument, but only the tool's declaration compiled. It also
included unrequested prose. Counting the declarations-only instruction, both
workflows met the full request on five of nine cases. On the Gaussian spectral
trace the tool gave a valid alternative using the adjoint action, not a faster
answer. One negative-log-tail scaffold lacked an import for an advertised lemma.

These are turnaround times from prepared packets to a recorded direct answer or
a full two-answer tool bundle, excluding preparation and verification. The tool
returned later on all nine pairs. The sample was small and selected, and the
direct solver prepared the packets. Historical proof-writing times were not
available; this is not a comparison with how long the original authors took.

**Decision:** In Blitz informal passes, start directly. Use `tool_think` for an
alternative construction or counterexample when a particular step is stuck.
Check suggestions against the hypotheses; they do not replace independent review.
