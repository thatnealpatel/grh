# Formalize dispositions

This directory holds accepted, per-passage receipts from [Formalize](../../cmd/formalize/README.md). The [coordinator protocol](../../cmd/formalize/coordinator.md#per-assignment-receipt) specifies their JSON format. These are campaign changes, not live state. Keep valid receipts in the accepted tree; a new meaningful Walk record revision has its own path.

- `landed`: checked Lean work and its receipt, accepted in a single candidate. The commit carrying the receipt identifies its evidence revision. A scoped result does not establish the rest of the passage.
- `already_covered`: exact accepted Lean references establish the assigned scope without new proof work.
- `substantive_failure`: a durable rendered-source and mathematical finding, including the exact unmet scope and condition for trying again. A timeout, missing tool, or ambiguous adoption is not a finding.

If later accepted changes invalidate evidence, explicitly retire the affected receipt as part of reconciliation. Do not overwrite an unchanged failure to trigger automatic attempts. Where the recorded retry evidence has actually changed, prefer a new Walk review via its normal process or explicitly retire the obsolete receipt via the campaign with the reason. Nothing here instructs a reader to edit Walk's private checkpoints.
