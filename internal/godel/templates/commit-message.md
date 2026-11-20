Write the message for one reviewable decision. Use the narrowest recognizable path or mathematical subject as the scope; reserve `all` for a genuinely repo-wide change. Start the summary with a lowercase imperative verb, as in `internal/godel: add source review template`.

For changes to `.godel/`, use exactly `.godel:` as the scope. Make each handoff commit self-contained: Record one decision or finding and enough context to understand it without opening another file or reading the run transcript. Do not include file paths in the subject or body. Name the passage, obligation, or remaining premise instead. For example: `.godel: record the missing divisor statement on page 522`.

Choose a verb the evidence supports. Use `record` for a source finding. For `derive`, name the remaining premise if omitting it would make the result sound unconditional. Use `prove` only for the statement actually proved. Keep workflow policy changes separate from proof changes.

A subject can stand alone. If a reviewer needs more, leave a blank line and explain why the decision was made, what was checked, and what remains open. Wrap body prose at 60 columns. Keep the decision in history, not a transcript of the run.
