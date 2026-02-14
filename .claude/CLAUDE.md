# Vera: A Verified Verilog Equivalence Checker

## What is Vera?

Vera is a **formally verified** Verilog-to-Verilog equivalence checker written in Rocq (formerly Coq). It checks whether two Verilog modules are semantically equivalent by translating them to SMT-LIB and querying an SMT solver. The entire translation and equivalence checking algorithm is **proven correct** using machine-checked proofs.

**Key Properties:**
- **Soundness**: If the tool reports "not equivalent", the modules genuinely differ
- **Completeness**: If modules are equivalent, the tool will report them as such (modulo SMT solver correctness)
- **Verified**: The translation from Verilog to SMT and equivalence query construction are proven correct in Rocq

## Repository Structure

### Main Directories

- **`vera/`** - Core Rocq proof development (~120 .v files)
- **`bin/`** - OCaml driver and extraction for command-line tool
- **`examples/`** - Sample Verilog test modules
- **`test/`** - Test suite including EPFL arithmetic benchmarks

### Key Source Files by Category

#### 1. Verilog Representation
- **`Verilog.v`** - Dependently-typed Verilog AST with bit-width information
- **`VerilogSemantics.v`** - Operational semantics for combinational circuits
- **`VerilogSort.v`** - Topological sorting of module items by dependencies

#### 2. Translation to SMT
- **`VerilogToSMT/VerilogToSMT.v`** - Translation algorithm from Verilog to SMT-LIB
- **`VerilogToSMT/VerilogToSMTCorrect.v`** - **Main correctness proof** of translation
- **`VerilogToSMT/Expressions.v`** - Expression evaluation correspondence proofs
- **`VerilogToSMT/Match.v`** - State matching between Verilog and SMT valuations

#### 3. Equivalence Checking
- **`VerilogEquivalence.v`** - Constructs equivalence queries for two modules
- **`VerilogEquivalenceCorrectness.v`** - **Main soundness/completeness theorems**

#### 4. Optimizations
- **`AssignmentForwarding/AssignmentForwarding.v`** - Variable inlining optimization
- **`AssignmentForwarding/AssignmentForwardingCorrect.v`** - Correctness proof for optimization

#### 5. Supporting Infrastructure
- **`SMTLib.v`** - SMT-LIB term representation
- **`SMTQueries.v`** - Query construction with reflection
- **`Bitvector.v`** - Three-valued (0/1/X) bitvector library
- **`Common.v`** - General utilities, maps, bijections, lemmas

### Build System

- **Dune-based build** for Rocq/Coq with OCaml extraction
- **Nix flake** for reproducible development environment
- Dependencies: Coq 8.x, coq-ext-lib, coq-equations

**Build commands:**
```bash
dune build          # Build everything
dune build @check   # Type-check Coq files
dune exec vera      # Run extracted OCaml tool
```

## Implementation Details

### Verilog AST Design

**Two-Level AST:**
1. **RawVerilog** - Untyped AST (parsed from Verilog source)
2. **Verilog** - Dependently-typed AST with width information indexed by types

**Key Design:** Expressions are indexed by their bit-width at the type level:
```coq
Inductive expression : N -> Type :=
  | ArithmeticOp {w} (op : arithmeticop) : expression w -> expression w -> expression w
  | BitSelect {w_val w_sel} : expression w_val -> expression w_sel -> expression 1
  | Concatenation {w1 w2} : expression w1 -> expression w2 -> expression (w1 + w2)
  ...
```

This ensures **width correctness by construction** - ill-typed expressions cannot be represented.

### Supported Verilog Subset

**Currently Supported:**
- Combinational logic only (`always_comb` blocks)
- Arithmetic: `+`, `-`, `*`
- Bitwise: `&`, `|`, `^`, `~`
- Shift: `<<`, `>>`, `<<<`
- Conditionals: `? :`
- Bit selection: `signal[idx]`
- Bit concatenation: `{a, b}`
- Only blocking assignments (`=`) to single variables

**Not Supported:**
- Sequential logic (clocks, flip-flops)
- Non-blocking assignments (`<=`)
- Arrays, structs, unions
- Procedural code (loops, functions)
- Multi-driven nets

### Three-Valued Logic

The semantics uses **XBV** (extended bitvectors) with three possible bit values:
- **0** - Logic low
- **1** - Logic high
- **X** - Unknown/uninitialized

**Why X?** Enables conservative approximation when variables aren't fully specified. X propagates through operations (e.g., `1 & X = X`).

### Execution Model

```coq
RegisterState := variable -> option (XBV.xbv width)
exec_module_body : RegisterState -> list module_item -> option RegisterState
```

**Semantics:**
- Executes assignments in order (order matters before sorting!)
- Returns `None` on errors (undefined variables, width mismatches)
- Topological sorting makes execution order-independent

### Translation Algorithm: Verilog → SMT

**Step 1: Variable Assignment**
- Map each Verilog variable to a fresh SMT identifier
- Maintain bijection between Verilog and SMT names
- Tag variables as "Left" or "Right" to avoid name collisions when comparing two modules

**Step 2: Expression Translation**
- Recursively translate Verilog expressions to SMT-LIB terms
- Arithmetic ops → `bvadd`, `bvsub`, `bvmul`
- Bitwise ops → `bvand`, `bvor`, `bvxor`
- Conditionals → `ite`
- Handle width conversions carefully (zero-extension, truncation)

**Step 3: Constraint Generation**
- Each assignment `v = expr` becomes an SMT equality `(= v (translate expr))`
- Conjoin all constraints

**Step 4: Equivalence Query Construction**
```coq
equivalence_query v1 v2 =
  let (vars1, constraints1) := verilog_to_smt Left 0 v1 in
  let (vars2, constraints2) := verilog_to_smt Right (length vars1) v2 in
  let inputs_same := forall i in inputs, Left.i = Right.i in
  let outputs_differ := exists o in outputs, Left.o != Right.o in
  (inputs_same ∧ constraints1 ∧ constraints2 ∧ outputs_differ)
```

**Query Interpretation:**
- **SAT** → Found input where modules differ → NOT EQUIVALENT
- **UNSAT** → No such input exists → EQUIVALENT

### Critical Constraints

For translation to succeed, a Verilog module must satisfy:
1. **Inputs disjoint from outputs** - No signal can be both input and output
2. **All variables driven** - Every variable is either an input or assigned exactly once
3. **No combinational loops** - Assignment dependencies must be acyclic
4. **Assignments sortable** - Dependencies must allow topological ordering

These are checked at translation time and return errors if violated.

### Optimizations

**Assignment Forwarding (Variable Inlining):**
- Replaces intermediate variables with their definitions
- Example: `v = x; out = v + y` → `out = x + y`
- Reduces SMT query size
- **Proven correct** via substitution lemmas showing semantic equivalence

**Topological Sorting:**
- Orders assignments by data dependencies
- Ensures variables are assigned before use
- Enables proof that execution order doesn't affect result (when sorted)

## Proof of Correctness

### Main Theorems

#### 1. Translation Correctness (`VerilogToSMTCorrect.v:verilog_to_smt_correct`)

```coq
Theorem verilog_to_smt_correct :
  verilog_to_smt tag start v = inr smt ->
  smt_reflect (query smt)
    (fun ρ => valid_execution v (execution_of_valuation tag (nameMap smt) ρ))
```

**Meaning:** If translation succeeds, then:
- Every SMT model corresponds to a valid Verilog execution
- Every valid Verilog execution has a corresponding SMT model

This establishes **semantic correspondence** between Verilog and SMT.

#### 2. Equivalence Query Soundness (`VerilogEquivalenceCorrectness.v:equivalence_query_sat_correct`)

```coq
Theorem equivalence_query_sat_correct :
  equivalence_query v1 v2 = inr smt ->
  satisfied_by ρ (query smt) ->
  counterexample_execution v1 (exec_of_val Left m ρ) v2 (exec_of_val Right m ρ)
```

**Meaning:** If the SMT query is satisfiable, then there exists an input on which the two modules produce different outputs. This proves **soundness** - we don't have false negatives.

#### 3. Equivalence Query Completeness (`VerilogEquivalenceCorrectness.v:equivalence_query_unsat_correct`)

```coq
Theorem equivalence_query_unsat_correct :
  equivalence_query v1 v2 = inr smt ->
  (forall ρ, ~ satisfied_by ρ (query smt)) ->
  equivalent_behaviour v1 v2
```

**Meaning:** If the SMT query is unsatisfiable, then the modules produce the same outputs on all inputs. This proves **completeness** - equivalent modules are recognized as such.

### Proof Architecture

The proofs are layered from bottom to top:

**Layer 1: Expression Level**
- `expr_to_smt_value`: SMT term evaluation matches Verilog expression evaluation
- Proven by structural induction on expressions
- Handles all operators and width conversions

**Layer 2: Statement Level**
- `verilog_smt_match_states_partial`: Register states correspond to SMT valuations
- Individual assignments preserve the correspondence
- Uses substitution lemmas for variable replacement

**Layer 3: Module Level**
- `verilog_to_smt_correct`: Full module execution corresponds to SMT satisfaction
- Combines expression and statement level results
- Handles initialization, sequencing, and final state extraction

**Layer 4: Equivalence Level**
- `equivalence_query_sat_correct` and `equivalence_query_unsat_correct`
- Connect module-level correspondence to equivalence checking
- Construct counterexample executions from SMT models

### Key Proof Techniques

- **Dependent type manipulation**: Heavy use of `eq_rect`, proof irrelevance, heterogeneous equality
- **Permutation reasoning**: Prove execution is order-independent when dependencies allow
- **Well-founded recursion**: Using `Equations` library for structurally complex functions
- **Monadic reasoning**: Error handling with `option` and `sum` monads
- **Bijection maintenance**: Track 1-1 correspondence between Verilog and SMT names
- **Reflection**: Connect Rocq-level semantics to extracted OCaml SMT queries

### Trust Base

**What IS formally verified:**
- ✓ Verilog semantics definition
- ✓ Translation from typed Verilog AST to SMT-LIB terms
- ✓ Equivalence query construction logic
- ✓ Soundness: SAT → modules differ
- ✓ Completeness: UNSAT → modules equivalent
- ✓ Assignment forwarding optimization correctness

**What is NOT verified (trusted components):**
- ✗ OCaml extraction correctness (trust Rocq's extraction mechanism)
- ✗ SMT solver correctness (trust Z3/CVC5/Bitwuzla)
- ✗ Verilog parser (sv-lang tool)
- ✗ Pretty printers and CLI interface
- ✗ String serialization of SMT queries

**No admitted lemmas in the correctness path!** The critical theorems are fully proven. You can verify this:
```coq
Print Assumptions verilog_to_smt_correct.
Print Assumptions equivalence_query_sat_correct.
Print Assumptions equivalence_query_unsat_correct.
```

## Development Guidelines

### Working with the Codebase

**When modifying Verilog AST:**
- Remember expressions are dependently typed by width
- Width calculations must be exact (`w1 + w2` for concatenation, etc.)
- Update both AST definition and semantics consistently

**When modifying translation:**
- Maintain the bijection between Verilog and SMT variables
- Update correspondence proofs in `VerilogToSMT/Match.v`
- Check that `verilog_to_smt_correct` still holds

**When adding optimizations:**
- Define transformation as a function on the Verilog AST
- Prove semantic equivalence: `forall v, equivalent_behaviour v (optimize v)`
- Update the main correctness theorem to compose with your optimization

**When extending supported Verilog subset:**
- Add constructors to the AST in `Verilog.v`
- Define semantics in `VerilogSemantics.v`
- Add translation case in `VerilogToSMT.v`
- Prove correspondence in expression/statement level lemmas
- Propagate changes through all proofs

### Important Lemmas to Know

- **`exec_module_body_permute`** - Execution invariant under permutation (when dependencies allow)
- **`expr_to_smt_value`** - Expression evaluation correspondence
- **`verilog_smt_match_states_partial`** - State correspondence between Verilog and SMT
- **`subst_expr_eval`** - Substitution preserves evaluation (for assignment forwarding)
- **`verilog_sort_correct`** - Topological sort preserves semantics

### Common Proof Patterns

**Proving new expression forms:**
1. Add semantic case in `VerilogSemantics.v`
2. Add translation case in `VerilogToSMT.v`
3. Extend `expr_to_smt_value` by induction
4. Use expression correspondence to lift to statement level

**Proving new optimizations:**
1. Define transformation function
2. Prove termination (if recursive)
3. Prove semantic equivalence by simulation or bisimulation
4. Integrate into main pipeline and update end-to-end theorem

**Debugging proof failures:**
- Use `Print Assumptions` to check for admits
- Use `Set Printing All` to see implicit arguments
- Use `pose proof` to instantiate difficult lemmas
- Simplify dependent types with `dependent destruction` or `revert` + `induction`

## Research Context

Vera is part of research on **verified hardware design tools**. The key insight is that while we cannot verify the SMT solver itself, we can verify that our translation correctly captures the semantics of Verilog, so any answer from the SMT solver is meaningful.

**Related work:**
- Hardware compilation with correctness proofs (CompCert for software as inspiration)
- Verified translators for other hardware languages (KAMI, Kami-Lite)
- SMT-based equivalence checking (unverified tools like ABC, Yosys)

**Research contributions:**
- First verified equivalence checker for Verilog subset
- Dependent types for hardware bit-widths
- Formal semantics for Verilog with X propagation
- Proof techniques for dependent AST transformations

## Quick Reference

**Check if a proof is complete:**
```bash
rg -l "admit\|Admitted" vera/  # Should return nothing in core files
```

**Build and run:**
```bash
dune build
dune exec vera -- module1.v module2.v
```

**Run tests:**
```bash
dune runtest
```

**Common Rocq commands in files:**
- `Equations` - Define functions with pattern matching and well-founded recursion
- `dependent destruction` - Case analysis on dependent types
- `rewrite`, `setoid_rewrite` - Rewriting with equivalences
- `pose proof`, `specialize` - Working with complex hypotheses
