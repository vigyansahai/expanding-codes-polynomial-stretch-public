# Runtime proof partition for server verification budgets

Owner: `/root/runtime_partition`. Only files below this directory are owned by
this worker. Original proof files, canonical definitions, and the published
RuntimeData are frozen. No helper proof/cache imports an ancestor endpoint Core.

## Exact goal and obstruction

The original complete proof is locally closed, but its two source-runtime leaf
proofs exceeded the platform 300-second job limit. The published foundational
`Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime` contains runtime
data and necessary constructor proofs. Further cuts must be proper algorithmic
correctness lemmas, with their original statements, rather than aliases of the
parent endpoints or complex additional Definition bundles.

## Proof route and measured decomposition

`nodes.json` registers ten submitted theorem bodies and their source-readable
exact formal statements, source locations, child dependencies, and proof routes.
`candidate-cuts.json` records measured marginal cut effects. The selected DAG is:

- TapeCompiler.compile_halts: generic source execution to NKtLB simulation.
- SourceFieldSetup.setup_stops: bounded canonical modulus/environment setup.
- SourceFieldArithmetic.multiply_stops: modular polynomial multiplication;
  the modulus index is arbitrary, so no field irreducibility is assumed.
- SourceFieldArithmetic.addition_stops: binary coefficient-vector addition;
  the statement also permits ell=0.
- SourceFieldArithmetic.inverse_stops: total canonical field inversion.
- SamplerProgram.layer_stops: uses multiplication and addition contracts.
- SamplerAssembly.prelude_stops: uses the field setup contract.
- TesterFrontend.program_stops: uses the field setup contract.
- TesterGram.program_stops: uses multiplication and addition contracts.
- GaussianDriver.rankProgram_stops_canonical: uses multiplication, addition,
  and inversion contracts.

The final parents retain 172825 (sampler) and 113197 (tester) declaration bytes.
All ten actual generated helper source files are below 329KB; exact byte counts,
SHA256s, source paths, cuts, and cache paths are in `generation-manifest.json`.
The generic compiler boundary alone saved only 24KB per parent, so it could not
resolve the timeout obstruction by itself.

## Reproducibility and integrity

`analyze.py` loads the immutable original flattening, declaration graph, exact
whole-command parser facts, and streaming Stage2 explicit source references.
It retains the source's runtime simp API to preserve erased simp/rfl roots.
`prepare.py` creates selections and metadata. Header constant qualification uses
exact Stage2 reference ranges and leaves dot projections unchanged. Only the
actual inherited section variables are inserted. The sampler frontend function
rename uses the sanctioned published RuntimeData map.

`StatementTypeAudit.lean` is METADATA ONLY. It imports the already closed parent
proof environment solely to locate private original declarations and compare
proposed statement types with Meta.isDefEq. This audit is never imported by a
helper proof, cache, forwarder, or uploaded solution. All ten exact type checks
passed in `statement-type-audit-002-result.json` (19.57s). The initial audit
command failed only because `matches` is a Lean reserved token; renamed to
`candidates`, with no changes to the statements.

`generate.py` uses the runtime worker's read-only `export_builder.py` to generate
actual standalone source proofs and distinct per-helper caches. Each cache
contains only its own target/dependency closure, hides all non-target helpers,
and checks its target's transitive axioms against propext/Classical.choice/
Quot.sound. Caches import Data plus already-closed children, never any original
endpoint Core. Closed forwarders expose the cache target under canonical
Theorems module names.

`check.py` runs every compiler through `./tools/lake-serial env lean` with the
wrapper's 6144MB and one-thread limits. `stub` builds locally registered theorem
statement artifacts into an isolated statement-cache. `upload` independently
checks the exact uploaded bytes; child theorem imports are overridden through
Lean's `--setup` importArts to those statement stubs, without mutating shared
canonical cache state. `cache` validates the closed proof and standard axioms;
`forwarder` installs its local canonical child import artifact.

## Open work

Compile all ten actual source uploads and per-node closed proof caches, then
report checked artifacts to the root for API posting. The root alone performs
API actions and may polish natural statements in its own files. API acceptance
of all helpers, regenerated source parents, and exact main mission is the final
goal; source generation or a compiling skeleton is not completion.

## Progress after first acceptance

- All ten pure statement stub artifacts compiled in
  `statement-cache/Theorems/`; these are never installed as canonical closed
  proof artifacts. All later `upload` checks use explicit isolated `--setup`
  artifact mappings, including required `dynlibs` and `plugins` empty arrays.
- The exact compiler helper upload independently compiled, matched its solution
  type, and audited to the standard three axioms. Source-bound preflight is
  `tape_compile-preflight.json`; the root posted it and reported API acceptance
  of submission `c181466d-860c-4142-b798-90f0a511b314` in 88 seconds.
- `pipeline.py` gives priority to actual source+type/axiom checks for the remaining
  four independent leaves, refreshing `ready-for-api.json` after every leaf.
  It then builds each own closed cache and canonical local forwarder before
  checking the five dependent helpers in both portability and closed contexts.
  Every subprocess uses the serial wrapper and only one is pending at a time.
- `statement-check-ledger.json` binds each exact formal statement to the passing
  metadata-only exact-type audit source. `preflight.py` additionally binds the
  frozen RuntimeData hash, actual uploaded bytes, compiler command/source hash,
  isolated stub context, closed cache command selection, and standard axioms.
- `fallback-cut-measurements.json` contains bounded measurements only, with no
  additional registered task or proof hole. They are unnecessary unless an
  accepted ten-node budget plan encounters a further real timeout.

## Scheduling and first scope-context correction

The root reported all five independent helpers API Proved: compiler, field setup,
modular multiplication, coefficient addition, and total inversion. IDs and API
receipts are root-owned; local individual preflights remain the source-bound
proof gates.

`external-check-ownership.json` explicitly assigns sampler_frontend and
 tester_frontend upload/cache/forwarder checks, logs, setup files, and per-key
preflights to `/root/submission_runtime_modules`, with source text frozen. The
pipeline was stopped between compiler jobs and restarted with explicit external
key skips, preserving every passed result/source hash. `preflight.py KEY` writes
only that key; no-argument refreshes skip external per-key ownership. The shared
ready catalog is an atomic index over existing individual gates.

The early Gaussian portability check failed at the unchanged original
rank_fromBlocks_zero ext/simp/rfl proof. It consumed only 69.4 CPU seconds and
3816 MiB, so no extra semantic cut is needed. The runtime worker isolated the
exporter's additional global Classical scope as the changed elaboration context.
The accepted five uploads remain frozen. Only the unsubmitted Gaussian upload
and cache may remove that exporter-added global scope; original module-scoped
commands and declaration/proof bytes are preserved. Failed source/log/result
must be archived before correction. `generate.py` records the same targeted
header correction for reproducibility without regenerating any frozen source.

## Final owned-work handoff

`final-local-summary.json` records the final read-only integrity pass: nine
completed helpers have current source/cache hashes and bytes matching their
manifests, successful exact-upload builds, exact statement-type witnesses,
standard-three-only transitive cache axioms, and installed canonical closed
forwarders. Upload and cache imports are exactly Data/Mathlib plus their reached
acyclic child cuts. The frozen RuntimeData hash was checked again. Largest
source is the corrected Gaussian upload at 328588 bytes. No further compiler
job is pending from this worker.

The tester_frontend checks and per-key preflight remain with the runtime worker;
no missing result is counted as completion. The old running pipeline's final
stdout line was broader than its external assignment; authoritative per-key
results and this summary distinguish the remaining external work. Future
pipeline code prints the external remainder accurately.

All nine completed proof sources, caches, and preflights are frozen on the
coordinator's instruction. API verdict metadata stays coordinator-owned. At the
last coordinator update, eight helpers were API Accepted and the corrected
Gaussian proof had been posted; the parent endpoints and exact mission remain
part of the root goal until their API acceptance.
