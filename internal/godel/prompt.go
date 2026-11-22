// Package godel contains policy shared by the GRH Gödel programs.
package godel

// ScratchPath is relative to the user's home directory.
const ScratchPath = "t/grh"

const ScratchPolicy = `Use ~/` + ScratchPath + ` as scratch for inconsequential or tangential material outside project history. Keep consequential proofs, decisions, needed evidence, and self-contained handoffs in accepted history. Scratch artifacts must not be required evidence or necessary to use a durable handoff.`
