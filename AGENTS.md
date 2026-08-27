# Agent Instructions

## Collaboration Style

- Make the smallest correct change. Do not address adjacent issues or expand the task unless required for correctness.
- Avoid speculative abstractions, broad refactors, excessive defensive code, and repeated review/fix loops.
- Ask before substantially expanding scope, even when additional work appears beneficial.
- Prefer user steering and short feedback cycles over attempting to anticipate and complete everything independently.

## Proofs

- Attempt to one-shot proofs first. If that doesn't work, use your MCP tools (rocq_*) to build the proof interactively. Don't rely on output from `dune build` to repair proofs.
- Conciseness is highly valued, as long as it doesn't subtract from readability.
- Avoid relying on generated names (H1, H2, etc.). If possible, give hypotheses names when they're introduced. Failing that, use tactics that don't rely on names, or the `rename_match` tactic from `Tactics.v`, to give names to any hypothesis.
- Heavily rely on existing lemmas and tactics.
- Prefer funelim for Equations definitions. Solve exceptional branches first, then use all: to share normalization, rewriting, and inversion across the remaining branches.
- Avoid numbered generated names, but do not replace a concise funelim proof with manual induction merely to name every premise. Prefer assumption, intuition, and domain-specific automation.
- Clear irrelevant equations such as Heqcall early when they only clutter later automation.
- Control simplification by making implementation-heavy decision procedures opaque when necessary; this often allows a concise cbn in * instead of long explicit reduction lists.
- Prefer rewriting with existing relational lemmas over creating intermediate pose proof facts. If rewriting is blocked by valid monotonicity or antitonicity, suggest providing the appropriate reusable Proper instance.
- Let specialized solvers discharge both the rewritten goal and generated side conditions, using patterns such as all: LocationSet.setdec.
- Use patterns such as `<tac>; try assumption; expect 1` when a tactic generates subgoals solvable with the same tactic with one or two exceptions. The `expect` means that this pattern fails early if the number of subgoals changes.
