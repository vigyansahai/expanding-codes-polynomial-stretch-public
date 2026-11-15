# Proof-solving workflow

## Objective and environment

The task was to prove the mission's exact theorem in Lean 4.33.1, preserving its definitions and operational efficiency requirements. The corresponding paper is *Expanding Codes with Polynomial Stretch* by Isaac M Hair and Amit Sahai, especially Section 2. [SOURCES.md](SOURCES.md) lists the public references. Source PDFs and extracted paper text are supplied separately; historical notes retain citations to the original extraction's line numbers.

The version pins are `lean-toolchain`, `lake-manifest.json`, and `lakefile.lean`. The exact ten-definition platform closure and its hashes are recorded in `harness/platform/definition-manifest.json`. Initial interfaces were marked provisional until authenticated API access supplied the canonical definitions; those early attempts remain available for provenance.

## Coordinator and bounded workers

The coordinator owns the proof DAG, statement review, shared interfaces, scheduling and final acceptance. Workers used `gpt-6.1-sol` at high/xhigh reasoning, with an Astra high escalation available for difficult branches. The harness does not itself call model APIs or autonomously spawn an unbounded agent tree. The surrounding coordinator dispatches the generated packets.

Each task records its exact proposition, signature hash, owning file, source references, intended proof route, failed approaches and dependencies. A worker receives a compact packet containing its interface and selected context, rather than the entire conversation. Generate one with:

```sh
python3 harness/engine.py packet headline --output tmp/headline-packet.json
```

The packet includes an editable-file boundary, a scratch directory and forbidden ancestor imports. `harness/worker_prompt.txt` supplies the common instructions. Detailed assignments and returned work are in `harness/tasks/`; drafts and failed proof attempts are in `harness/attempts/`.

## Recursive proof construction

1. Attempt a bounded direct proof of the current proposition.
2. If necessary, propose named child lemmas and a parent proof using only those interfaces.
3. Review each child for mathematical usefulness: what difficulty does it isolate, and what is its proof route? Renaming the parent, assuming its conclusion, or moving an equivalent obligation is insufficient.
4. Register the children, check that the dependency graph is acyclic, and compile the parent reduction.
5. Dispatch children independently, repeating this process only while the reductions remain meaningful.
6. Promote checked drafts into their public modules, then rebuild and audit the declaration and its closure.

`sorry` was permitted only in explicitly registered open theorem bodies. Data, predicates, encodings, structures and programs required genuine definitions. A compiling reduction was recorded as `reduction_checked`, not `proved`. Final completion required exact type compatibility and no transitive `sorryAx` or custom axioms.

The CLI exposes `register`, `packet`, `verify`, and `verify-many`; run `python3 harness/engine.py --help` for arguments. `register` accepts new open tasks without silently revising existing signatures. Coordinator review determines whether a decomposition is meaningful; the lexical source checks do not claim to solve semantic equivalence.

## Proof branches

The mathematical development separates finite-field geometry and Reed–Muller algebra, code dimension/rate limits, affine symmetry and erasure capacity, Boolean Fourier/sharp-threshold arguments, concentration/rank bounds, and the two expansion stages. The operational development adds explicit binary-field representations, finite source programs, a source-to-NKtLB compiler, random-table sampling, physical matrix construction and Gaussian elimination.

The final sampler and tester use the same `binaryGeometry`. The sampler's probability law is proved exact for a finite fair-bit tape. The tester computes the canonical rank predicate with integer/rational arithmetic. Both are fixed finite machines chosen before the runtime size and input word, with proved polynomial clocks. These clauses are assembled into the canonical `EfficientFamily` predicate and the universal arity bound.

## Memory and promotion policy

Use `tools/lake-serial` for every compiler invocation. It serializes compilers across workers, runs Lean with `-j1` and a default `-M6144` cap, and builds module dependencies one at a time. The hard allowed ceiling is 8192 MB. Keep one pending compiler job per worker.

The shared/persistent REPL was disabled after memory growth. `harness/warm_repl.py` and the vendored REPL remain historical artifacts, not supported proof-check commands.

Workers preserve the last compiling public module while working in `harness/attempts/<task>/`. A broken draft should not block independent branches. Only a direct-compiler-passing draft is promoted; the public module is then rebuilt and audited.

## Final verification

The original final pass began from an empty project build cache, built 159 local modules, and checked all 54 registered nodes against their exact propositions and transitive axiom sets. Peak recorded resident memory was about 5995 MB under the 6144 MB cap.

Primary records are:

- `harness/runs/final-fresh-build.log`
- `harness/runs/final-verification.log`
- `harness/runs/final-source-manifest.json`
- `harness/runs/final-verification-plan.json`
- `harness/graph.json`
- `artifacts/Verify.lean` and `artifacts/verify-output.log`

Run `python3 harness/engine.py verify headline --mode prove` to repeat the closure verification. It checks source, versions, platform-definition hashes, exact types and transitive axioms, and refreshes the verification receipts. It may take substantial time on a fresh clone. Historical compiler records and cached receipts alone are not fresh proof checks.

The public snapshot redacts personal metadata in historical logs and receipts. Its graph receipts were refreshed with all 54 nodes checked by Lean after the redaction; see [PUBLIC_SNAPSHOT.md](PUBLIC_SNAPSHOT.md). The original source manifest retains historical hashes and separately records the instruction and compiler-path portability updates.
