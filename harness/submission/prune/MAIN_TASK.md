# Final main export

Target: exact `ExpandingCodes.PolynomialStretch.expanding_codes`, theorem ID
`35a9bc65-151f-4a09-baa1-2c28821d6cd3`; original server type is in
`harness/submission/target.json`.

Owned files: `harness/submission/prune/prepare_main.py`, `Main.lean`, `MainAudit.lean`,
`main-manifest.json`, and their check logs. Original public proof files and immutable
attempt 001 `harness/submission/Upload.lean` must remain unchanged.

The export imports the exact binary sampler and tester implementation-source
endpoints and canonical `auxiliary_rate`. The shared BinaryRuntime definition bundle
owns the actual executable data and its necessary embedded correctness witnesses.
Main retains all other required proof declarations, selected by the actual compiled
Upload declaration graph and whole Lean parser command spans. Source-resolved Stage 2
references restore named helpers erased from final proof terms. Each retained source
module stays in its original independent section; no proof bodies are edited.

`prepare_main.py` reads the runtime worker's current final generation manifest and
source-reference facts. It treats every whole declaration command supplied by Data as
provided, so compiler-restored Data declarations cannot be redeclared in Main. The
three endpoint statements are treated as imported constants. It keeps all remaining
participating local instances as roots and closes constructor/source-command groups.

The Data export's `SamplerAssembly.prelude` identifier was rejected by the platform's
header-token guard. Its export-only rename is handled by the runtime worker using
Stage 2 occurrence ranges. Main owns neither the old declaration command 3618 nor any
of its four source-reference commands, so no Main occurrence rewrite is required.

Local final axiom audit requires a cache containing proved endpoint declarations,
with all non-endpoint cache helpers private. Importing canonical sorry stubs only
checks a reduction, not a closed proof. Public cache helpers would collide with
Main's standalone helper declarations; a cache-only private proof core solves this
without changing upload source. Final completion requires exact Main compilation,
whole-type `@solution` check, and standard-only transitive axioms.

Implicit automation coverage: final Main roots all 75 parser-identified original
`@[simp]` commands, not merely final-Expr or explicit TermInfo references. It also
retains the nine small project-local `NKtLB.Machine` API theorems because the streaming
source oracle filtered references by the `ExpandingCodes` namespace. These additions
keep Main below 216 KB. The cache-only Core must remove its non-Data helper simp
attributes after checking endpoint proofs, and its audit must confirm no non-Data
instances or extra public helper declarations. This prevents local automation from
silently acquiring facts unavailable under the server's statement-only theorem imports.
