# Vera: A Verified Verilog Equivalence Checker

Vera is a formally verified Verilog-to-Verilog equivalence checker written in
Rocq. It checks whether two Verilog modules are semantically
equivalent by translating them to SMT-LIB and querying an SMT solver. The
translation and equivalence checking algorithm are proven correct using
machine-checked proofs.

## Getting Started

### Option A: Docker (recommended)

Requires Docker or Podman.

```bash
docker build . -t vera
docker run -it vera
```

This will drop you into a shell with all dependencies available. The first run
will download dependencies via Nix, which may take some time depending on your
connection.

### Option B: Nix (if you already have it)

If you have Nix with flakes enabled, you can skip Docker entirely:

```bash
nix develop
```

This gives you the same environment as the Docker container.

## Building

Once inside the development shell (via either method):

```bash
dune build
```

This type-checks all Rocq proofs and builds the extracted OCaml tool. It will also print the list of axioms used by the top-level proof. They are standard logical axioms from the Rocq standard library, which are known to be compatible with each other. You should see this exact list in the output of the last command:

```
Axioms:
ProofIrrelevance.proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2
functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
Eqdep.Eq_rect_eq.eq_rect_eq :
  forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
  x = eq_rect p Q x p h
Classical_Prop.classic : forall P : Prop, P \/ ~ P
Axioms:
ProofIrrelevance.proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2
functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
Eqdep.Eq_rect_eq.eq_rect_eq :
  forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
  x = eq_rect p Q x p h
Classical_Prop.classic : forall P : Prop, P \/ ~ P
```

You can also check 

```bash
grep -r "Admitted" vera/
```

This should return no results in the core proof files.

## Running the Tool

```bash
dune exec vera -- compare module1.sv module2.sv
```

This parses the two Verilog modules, translates them to SMT-LIB, and checks
equivalence.

## Running the Benchmarks

The benchmarks compare Vera against EQY on the EPFL arithmetic benchmark suite.
From the development shell:

```bash
cd benchtest
./build.sh epfl
```

Results are written to `benchtest/out/EPFL-benchmarks/summary.csv`.

By default, this will run the tests as described on the paper (1 hour time limit, 64GB memory limit, Z3 backend). To change these settings look for the section in the file marked with `--- SETTINGS`.

## Repository Structure

- `vera/` -- Core Rocq proof development
- `bin/` -- OCaml driver and extraction
- `benchtest/` -- Benchmark suite (EPFL arithmetic benchmarks)
- `flake.nix` -- Nix development environment
- `Dockerfile` -- Docker setup for artifact evaluation
