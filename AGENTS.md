# Expanding Codes with Polynomial Stretch

## Objective and coordinator

The user authorized sustained work to solve the exact Prove2 mission in Lean
4.33.1 and implement a recursive, agentic proof harness. The root agent remains
the main coordinator. Workers use `gpt-6.1-sol` with `high` or `xhigh` reasoning;
the coordinator may use `gpt-6-astra` with `high` reasoning for stuck branches.
Workers must return results and preserve their assigned file ownership.

## Proof integrity

- Preserve the mission's exact statements and definitions when obtained. Until
  then mark locally proposed interfaces as provisional, never platform canonical.
- Use meaningful, acyclic reductions. A child that merely renames its parent,
  assumes its conclusion, or buries the same difficulty behind an equivalent
  assertion is not progress. Explain what each child isolates and its proof route.
- `sorry` is allowed only for explicitly registered open theorem bodies. Never
  use it to define data, predicates, structures, programs, or encodings.
- Keep reductions free of inline holes; call named, registered child lemmas.
- No custom axioms, circular imports, target/ancestor imports, unsafe proof
  backdoors, altered model assumptions, or weakened theorem statements.
- A compiling skeleton is a reduction, not a completed proof. Completion requires
  auditing the final declaration's transitive axiom dependencies and a clean build.
- Do not edit another worker's files or shared interfaces without coordination.
- Keep in-progress proof drafts in your assigned `harness/attempts/<task>/`
  directory. Preserve the last compiling public module (including its registered
  theorem stub when open) while iterating. Promote a draft only after its direct
  compiler check passes, then rebuild and audit the public module. This prevents
  one leaf's draft errors from blocking independent parent reductions.

## Local environment

Lean: `leanprover/lean4:v4.33.1`.
Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
If `lake` is absent from PATH, use `$HOME/.elan/bin/lake`.
The configured REPL launcher is `tools/lean-repl`.
Run Lean checks with auto-implicit variables disabled.
Use `./tools/lake-serial build ...` or `./tools/lake-serial env lean ...` for
compiler jobs. This serializes compiler processes across workers to avoid
duplicating large imports and exhausting workstation memory.
Persistent/shared REPL use is disabled after excessive memory growth. Do not
run `harness/warm_repl.py` or `tools/lean-repl` for proof work. Use short-lived
serialized compiler processes only; the wrapper and package apply Lean's
6144 MB default memory limit and one-thread setting. The user permits up to
8192 MB, never above; only the coordinator may change the limit after measuring.
The wrapper builds local modules in dependency order so only one Lean compiler
runs at a time. Keep one pending check per worker.

Public source references are listed in `docs/SOURCES.md`. Source papers and
local extraction scratch files are supplied separately and are not versioned.

## Task records

Keep exact goals, proof routes, failed approaches, source locations, file ownership,
and unresolved dependencies in the durable harness records. A worker should
attempt a bounded direct proof, then return a checked proof, a meaningful checked
decomposition, a concrete obstruction, or a counterexample. Do not create an
unbounded recursive task tree or count renaming as progress.
