# Alice and Bob

`cmd/alice` and `cmd/bob` start as identical, separately editable packages. The Go package name in the executable's build information supplies the command identity; the stable `cmd/<name>` directory gives each loop its own Gödel history. Each runs one full Yah work node followed by one full Yah improvement node. Both nodes start Yah with `gpt-6.2-astra` at high effort in the absolute root of the durable launch workspace. They append the local `WORK.md` or `IMPROVE.md` to Yah's usual instructions. Work can use its tools directly, call `cmd/ff`, or dispatch Yah agents. Neither peer starts the other. There is no shared inbox or synchronization point.

To start a peer deliberately, use the root of a durable GRH workspace that already contains its command directory and bootstrap. Adoption alone does not update an older launch checkout. With the Linux/systemd, Go, and Yah prerequisites in `cmd/godel/README.md`, run just the desired command in its own job:

```sh
printf '%s\n' 'Choose and pursue a decisive question toward RH or GRH.' | go run ./cmd/alice
```

For Bob, replace `./cmd/alice` with `./cmd/bob`. Supply a nonblank objective on the first run. Subsequent launches can use that peer's previous work output. An adopted program change takes effect at the next accepted launch, not in the running invocation. To stop, send INT or TERM to the job, not KILL to its outer Go wrapper. To check the starter wiring without running any research, use `go test ./cmd/alice ./cmd/bob`.
