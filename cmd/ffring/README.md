# ffring: Signed floor-grid increments

From this directory:

```sh
printf '%s\n' 'Can the centered signed trace remainder be summed across dyadic refinement levels?' | go run .
```

The floor grids, metric, limit order, and node assignments are built in. Stdin supplies the task or additional evidence. As in `cmd/ff`, the default runs one Gödel work node; `go run . graph` reads stdin directly without Gödel history. Both send the task to the same fixed inference proxy and print only the decision.

A successful run makes 13 calls. A1–A4 derive the phase mean, weighted projection increment, convolution estimate, and obstruction. Each B node challenges its A node and the next one around the ring. Each C node repairs its own derivation using both challenges that read it. D1 reads just the four repairs and reports a summable bound, a counterexample to a stated bound, or the first uncontrolled term. Within a layer the four calls run concurrently; failure cancels siblings and prevents later layers from starting.
