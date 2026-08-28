---
name: pulp-elau-failures
description: Summarise why pulp-elau benchmark runs fail in benchtest/out/pulp-elau, grouping failures by root cause rather than by error string
argument-hint: "[design or error class to focus on]"
---

# Summarising pulp-elau failures

You are analysing the results of the `pulp-elau` benchtest target and reporting
*why* each benchmark failed. The existing Shakefile target
(`out/pulp-elau/summary.csv`) only classifies each run as `OK` or `Error`. Your
job is to go one level deeper: group runs by **root cause**, and for each cause
name the specific Verilog construct that Vera choked on.

## Where the results are

Everything lives under `benchtest/out/pulp-elau/<Design>/<variant>.*`, where
`variant` is one of `slow`, `medium`, `fast` (the `speed` parameter the design
was elaborated with). Per design/variant there are three stages:

| File | Stage | What it is |
|---|---|---|
| `<variant>.sv` | yosys | Flattened, lowered Verilog produced by `read_slang ... ; flatten; write_verilog` |
| `<variant>.sv.log` | yosys | yosys stdout/stderr |
| `<variant>.lowered.vera` | vera | **stdout of `vera lower pre-smt`** — this is where Vera's error messages go |
| `<variant>.lowered.vera.log` | vera | stderr: the `VERA_TRACE` phase timings, and OCaml exception backtraces |

**The single most important thing to know:** Vera's `Error: ...` messages are
written to *stdout*, i.e. the `.lowered.vera` file, not the `.log`. The `.log`
only contains trace lines and uncaught-exception backtraces. Grepping only the
logs (which is what the Shakefile target does) misses almost every failure.

A run failed if either:
- `.lowered.vera` starts with `Error: ...` (a clean Vera error), or
- `.lowered.vera` is empty and `.lowered.vera.log` contains
  `internal error, uncaught exception` (a crash), or a timeout with no output.

A run succeeded if `.lowered.vera` starts with `Verilog.module <Name> {`.

## Procedure

1. **Bucket every run by its first stdout line.** This gives the raw error
   classes cheaply:

   ```bash
   cd benchtest/out/pulp-elau
   head -qn1 */*.lowered.vera | sort | uniq -c | sort -rn
   ```

   Empty `.lowered.vera` files produce no line; find them separately and read
   the corresponding `.log` for the exception message:

   ```bash
   for f in */*.lowered.vera; do [ -s "$f" ] || echo "$f"; done
   grep -h -A3 "uncaught exception" */*.lowered.vera.log | sort | uniq -c
   ```

2. **Check the yosys stage too** before blaming Vera — a design that never got
   a valid `.sv` will fail downstream for an unrelated reason:

   ```bash
   grep -lE "^ERROR|error:" */*.sv.log
   for f in */*.sv; do [ -s "$f" ] || echo "empty: $f"; done
   ```

3. **For each error class, find the root cause in the generated `.sv`.** This is
   the part that makes the summary worth more than a `grep`. Pick 2–3
   representative designs per class, open their `.sv`, and identify the
   construct responsible. Guidance per known class is below.

4. **Check whether the cause varies with `speed`.** Designs are elaborated at
   three speeds; if `slow`/`medium`/`fast` of the same design fail differently,
   that is worth calling out, and it usually points at a structurally different
   prefix-tree implementation rather than a different Vera limitation.

5. **Report** in the format below.

## Known error classes and how to root-cause them

### `Error: Invalid assignment LHS`

Vera only supports assignment to a whole variable (and, since recently, to a
slice). yosys' `write_verilog` output for these designs contains per-bit
assignments to array elements, e.g.

```verilog
assign \prefix.prefix.fastPrefix.PT [8] = \prefix.prefix.fastPrefix.PT [0];
```

To confirm for a given design, look for `assign` lines whose LHS is indexed:

```bash
grep -nE "^\s*assign +\\\\?[A-Za-z_0-9. \\\\]*\[" <Design>/<variant>.sv | head
```

Report which LHS *forms* appear (bit-select `x[i]`, part-select `x[hi:lo]`,
concatenation `{a,b} = ...`), since they need different support in Vera.

### `Error: Module not sortable`

Vera topologically sorts assignments and rejects modules with dependency
cycles. Distinguish the two very different causes:

- **A genuine combinational loop** in the design (rare here).
- **A false cycle from per-bit assignment**: when `x[3]` is assigned from
  `x[1]`, Vera's dependency graph works at whole-variable granularity, so `x`
  depends on `x` and the module looks cyclic even though the bit-level
  dependencies are acyclic. This is the expected cause for the prefix-tree
  designs (`PrefixAndOr*`, `LeadOneDet`, `LeadZeroDet`, `LeadSignDet`,
  `AddMod2N*`, …).

Tell them apart by checking whether any variable appears on both sides of an
assignment at different indices:

```bash
grep -oE "\\\\[A-Za-z_0-9.]+ \[[0-9]+\]" <Design>/<variant>.sv | sort -u | head
```

Note that this class is usually the *same underlying limitation* as
`Invalid assignment LHS` — which error you get depends on which check fires
first. Say so in the summary rather than presenting them as two independent
problems.

### `Error: Slice indices (lhs) out of bounds`

A part-select LHS whose bounds Vera computes as outside the declared width.
Find the offending assignment and report the declared width of the target and
the slice bounds used — this is likely a real bug in Vera's slice bounds
checking rather than an unsupported construct, so it deserves a pointer to the
exact line.

### Uncaught exception: `'Call' is not a known value of kind 'expression kind'`

`bin/driver/ParseSlang.ml` does not handle function-call expressions in the
slang JSON. Report which design and which source construct produced the call.

### Uncaught exception: `Expected 'AlwaysComb, AlwaysFF, or Initial', but got 'Always'`

The design uses a plain `always` block; Vera's parser only accepts
`always_comb`/`always_ff`/`initial`. Sequential designs (e.g. `Reg`) are out of
scope for the combinational subset — say that explicitly rather than filing it
as a parser gap.

### Timeouts / no output, no exception

Empty `.lowered.vera` with a trace log that stops mid-phase means the run hit
the Shake `Timeout` or the `VERA_MAX_MEMORY` limit. Report the last phase
reached from the trace lines — that localises the blow-up (`Sort`, `Simplify`,
`Typecheck`, …).

## Output format

Produce a Markdown report with:

1. **Headline counts** — total runs, succeeded, failed, and a table of failure
   classes with counts and the share of total runs.
2. **One section per root cause**, not per error string. Merge error strings
   that share a cause (see the note under `Module not sortable`). Each section
   gives: what Vera rejects, the specific construct in the generated Verilog
   with a quoted example line and its `file:line`, the affected designs, and
   whether it is an unsupported-feature gap or a likely Vera bug.
3. **A "designs that succeed" list**, so the working set is visible.
4. **A short "what to fix first" ordering**, ranked by how many runs each fix
   would unblock.

Keep it factual. Every claim about a root cause must be backed by a line you
actually read out of a `.sv` or `.log` file — cite it as
`benchtest/out/pulp-elau/<Design>/<variant>.sv:<line>`. If you cannot determine
the cause for a bucket, say so rather than guessing.
