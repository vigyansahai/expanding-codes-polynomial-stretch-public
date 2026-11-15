# Runtime modular transplant task

Owner: runtime worker. Owns only `harness/submission/runtime/` and compilation outputs for its staged modules. Root owns external API and credentials. Frozen original proof files, graph, attempts, configuration, and `harness/submission/Upload.lean` remain unchanged.

Goal: preserve exact original finite-machine sampler and tester source implementation statements on common `binaryGeometry`, while splitting verified upload into one foundational Definition and two proved theorem nodes, with each source <= 1,048,576 bytes and no nonstandard axioms or holes.

Input frozen Upload SHA256: `4624ce0405f3ef91e6bef78156cfbcb968ff48c58efc69ce42d8e05d44990dcc`.
Authoritative Stage 1 graph and whole-command syntax facts: sibling `prune/decl_graph.jsonl`, `prune/parser-facts.jsonl`. Positions for internal edits are extracted using sanctioned Stage 2 traversals in this directory. No regex declaration/proof cuts or renames.

Plan after measured graph closures: 961 foundational commands / 222,204 declaration bytes; sampler 978 proof commands / 707,365 declaration bytes; tester 974 proof commands / 818,708 declaration bytes. Data includes 42 theorem commands / 17,339 bytes strictly necessary for data construction (finite-field certificates, Fin injection bounds, computational deciders). Actual sampler/tester algorithm correctness stays in solution bodies.

Data-side private boundaries: `Gaussian.prodSubmoduleEquiv`, `GaussianPivot.decidablePreserves`. Remove only exact Stage 2 `privateTok` span; user names unchanged, public collision check required. Proof-side privates remain inline. Instances from participating original modules are roots; structure accessors sharing data command spans are provided by the bundle.

Compile: only short-lived `./tools/lake-serial env lean` jobs, 6144 MB and one thread, one pending job. Never REPL or memory-cap changes. All changes staged here; no originals promoted or modified.

First data compile: 54.0 seconds, failed with a scope-open alias cascade from omitted `CounterCompiler.getD_append_singleton`, and at original `writerRegisters_injective` omega step because `Storage.low_val`/`Storage.neighbor_val` are source-level simplification references erased from Expr dependencies. Correct response is restore exact registered source commands and dependency closure, never edit the original proof.

To close this class of omission in all three files, `ExtractRefsStream.lean` uses the sanctioned Stage 2 `collectRefs` traversal over frozen Upload, but steps the public Lean frontend one command at a time and drops the completed command's InfoTrees. This bounds memory without disabling semantic elaboration. Output source ranges add declaration-level closure edges in `plan.py`; no proof transformations result.

Local proved-cache plan: actual exact uploaded solutions are compiled/audited separately. For final main standard-axiom audit, a shared cache-only runtime proof core contains the union of original exact sampler/tester proof commands, omitting generated `solution` wrappers; two canonical Theorems forwarding modules import that shared proof core. This avoids duplicate global `solution` and shared helper names. The cache core is not uploaded; source cap applies only to actual definition/solution payload files.

`CounterCompiler.getD_append_singleton` is restored as an exact structural source-scope root, because `open CounterCompiler (... getD_append_singleton ...)` elaborates names without TermInfo constants. The source scope command is retained verbatim.

Data corrected compile passed 36.116 s, all 2,244 data declarations passed transitive standard-axiom audit in 19.075 s. Selective `open CounterCompiler (...)` resolves atomically: an omitted proof-only `tape_write_scanned` alias caused a cascade. The generator now removes only that exact original parser token from Data's preserved selective-open command, instead of putting compiler correctness in Data. Proof solutions retain the original alias and its proof.

API Definition attempt 001 rejected the ordinary identifier `prelude` as a forbidden prelude command; no definition was published. Coordinator authorized an export-only rename of the actual graph declaration `ExpandingCodes.Computation.SamplerAssembly.prelude` to `ExpandingCodes.Computation.SamplerAssembly.samplerFrontendProgram`. `export-rename-map.json` records all four sanctioned Stage 2 reference spans including the binding. They are applied only to retained commands, never by text matching or regex. All original sources remain frozen. Renamed Data is 296,264 bytes / SHA256 `a9d7bd4747c0e4a8fa7fd2079242f7e6ec20effd8e8ffd08bc492d4b8e501778`; direct compile passed 49.023 s.

Exact common publication preamble plus both exact registered theorem stubs passed in 18.694 s. Preambles include `set_option autoImplicit false`.

Cache-only `ProofCore.lean` mechanically unions sampler/tester/auxiliary-rate original command closures after Data subtraction, privatizes every non-endpoint helper (including auxiliary definitions), and keeps exactly the three intended endpoints public. Parser modifier insertion positions handle ordinary declarations; exact original `lemma` keyword token positions handle the Batteries macro. This source is never uploaded and contains no global `solution`, axioms, or holes. It prevents both imported helper name conflicts and `solution` collisions in a closed local final-main audit.

Actual sampler attempt 001 failed only at `TapeArrays.seekRight_stops` because an implicit global simp application of the rfl projection `moved_reg` was erased from both Expr deps and explicit TermInfo refs. Full original parser inspection found 75 decorated declaration commands, all `@[simp]`, with no other tactic attributes or standalone attribute commands. The 56 runtime-module simp APIs are now proof-side roots (not Data). Failed source/log/result/manifest are preserved under `attempts/sampler-001/`.

Final upload sampler: 778,658 bytes / SHA256 `85a58281f3c5a8a2a277a2b39a95d6cefccb71864891e05b9fcf1842c5620257`. Exact source compile passed 178.788 s; audit passed 22.461 s; elaborated type is byte-identical to the original frozen Upload endpoint type; transitive axioms exactly `propext`, `Classical.choice`, `Quot.sound`. Evidence: `sampler-preflight.json`.

Final upload tester: 884,899 bytes / SHA256 `f8f15d52a5369813ae32df8d62d7293d71e487c369982f3167d0541429051230`. Exact source compile passed 222.231 s; audit passed 20.393 s; elaborated type is byte-identical to the original frozen Upload endpoint type; transitive axioms exactly the same three standard axioms. Evidence: `tester-preflight.json`.

Coordinator published the renamed Data and the exact two endpoint statements and is handling all API verification jobs. Data is frozen at its published hash, enforced by `generate.py` before writing. Both actual solution files are complete and ready for verification.

Cache Core retains all 75 original simp APIs for proof elaboration, then clears its 73 non-Data helper simp attributes with ordinary Lean `attribute [-simp]` commands before export. There are no non-Data source instances. The Main worker's independent `PrivateScopeSmoke.lean` passed, checking private declarations across sections, selective-open from another namespace, and fully qualified attribute removal with actual simp-set presence/absence assertions. The cache Core audit also checks for leaked helper simp/instance attributes after import.

## Final ownership and local status (frozen)

The coordinator handled all network/API actions. The original proof/configuration/graph/Upload sources were never edited; frozen Upload SHA remains `4624ce0405f3ef91e6bef78156cfbcb968ff48c58efc69ce42d8e05d44990dcc`. Canonical original Aux cache artifacts were never overwritten and were checked byte-identical to their backups.

The published RuntimeData is frozen at 296,264 bytes / SHA `a9d7bd4747c0e4a8fa7fd2079242f7e6ec20effd8e8ffd08bc492d4b8e501778`.

After the two independently proved large runtime uploads hit server timeouts, the coordinator assigned ten meaningful concrete operational helper cuts to the partition worker. The shared read-only `export_builder.py` supplies exact command subtraction, source refs/implicit simp roots, original metadata spans and sanctioned export renames. The partition worker owns the helper sources/manifests. This worker explicitly owned the sampler_frontend/tester_frontend compile/cache/forwarder/preflight gates and the initial Gaussian timing check; corrected Gaussian full retry returned to the partition worker. All ten helper local gates and API proofs are complete per coordinator; no remaining worker checks.

Final runtime parent sampler: 245,145 bytes / SHA `017b6230547b7a7c0defed842f3555d25e806901db6ea5f5ce3e224484b42e72`. Exact source passed pure child-stub portability, proper-child closed compile, original-type equality, standard-three-axiom audit and no-ancestor/original-proof-module guard. SDK-ready `sampler-preflight.json`. Coordinator confirmed Prove2 Accepted attempt002 `bba1221f-928f-41c5-9e51-659d7e41dedd`.

Final runtime parent tester: 186,497 bytes / SHA `df1feba6bcb5b397d89c844623c19a17806924753ea9cc99c1f77ff808240722`. Exact source passed pure child-stub portability 97.216s, proper-child closed compile 98.164s, and original-type/standard-three-axiom/no-ancestor audit 72.985s. SDK-ready `tester-preflight.json`. Coordinator submitted attempt002 `6f879b30-966c-43e5-91e4-39cba94cfae4`; remaining server polling belongs to coordinator.

Main's exact217365-byte proof passed independent closed-Core and pure-statement portability checks, owned by the Main worker. The cache Core's 73 private helper simp annotations are explicitly recorded; they are never used as sole evidence of API portability. Its closed certificate plus isolated statement-stub checks preserve both logical closure and server-context compatibility. `closed-cache/manifest.json` archives Data, Core and three closed forwarding artifacts without canonical Aux cache swaps.

A generic-export header had globally enabled Classical, changing Matrix ext lemma selection in Gaussian rank_fromBlocks_zero. The exact original-scope fragment passed. Only the unsubmitted Gaussian upload/cache and tester reduction received the approved10-byte generated-header correction; original commands/proofs remain byte-identical. Gaussian failed sources/log/result are archived under partition/attempts/gaussian-global-scope-001; sampler and the five accepted independent helper sources remained untouched. Independent reviewer confirmed these deltas.

All proof source/cache/preflight artifacts are now frozen at coordinator request. No unresolved local proof, compile, type or axiom checks remain. Final remaining API acceptance and mission submission are coordinator-owned.
