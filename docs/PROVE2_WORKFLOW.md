# Getting Prove2 to accept the proof

## Final result

The exact theorem `ExpandingCodes.PolynomialStretch.expanding_codes`, ID `35a9bc65-151f-4a09-baa1-2c28821d6cd3`, is **Proved**. Main submission `ead073dd-a76a-4ffe-9fe4-851e4405b099` was accepted. The final source has 217,365 UTF-8 bytes and SHA256 `882837bb5d42db9080a4d1f47af80d7fc21d999aa923aeb8cce49141a6f726ce`.

`harness/submission/final-api-verification.json` records all 14 accepted proofs, exact submitted source hashes, archive paths, IDs and acceptance receipts. `artifacts/prove2-verification-summary.json` is a second copy. Public mathematical explanations are preserved alongside the upload scripts and source files.

## API client and credentials

`tools/prove2.py` handles authentication and read-only fetches. `tools/prove2_submit.py` handles proof submission, definition/problem publication and status polling. They use the fixed HTTPS API origin and refuse authenticated redirects. The authentication cache is private and ignored at `tmp/prove2-token.json`; the key comes from `PROVE2ME_API` in the environment or local `.env`.

No login material is required for offline proof verification. To enable API operations locally:

```sh
cp .env.example .env
# Edit .env locally; do not paste the key into a Git command or commit it.
python3 tools/prove2.py auth
```

The archived client targets the API/skill version used for this run, `0.13.10`; the mutation client stops if authentication reports a different version. Check current official documentation before adapting it to a later service version. The pinned workspace documentation used in this run is saved in `prove2me_workspace/`.

The CLI can fetch an exact theorem, submit a Lean file with its mathematical explanation, poll a submission, queue new definitions/problems, and poll their publication jobs. `--preflight` checks readiness, exact proof SHA256, byte count and successful local compile evidence. Each attempt writes an immutable copy of its submitted source/payload under `submitted/`, records the returned ID, and avoids blindly duplicating an already-recorded request.

## First export: source-size failure

The locally complete project initially flattened to a 1,789,284-byte single file. It compiled and passed exact-type/axiom checks locally, but the service rejected it before Lean because its token scanner capped source at 1,048,576 bytes. The original bytes and rejection are preserved in `Upload.lean`, `attempt-001.json`, and `verdict-001.json`.

The exporter used Lean declaration dependencies and exact parser/source-reference spans, rather than regular expressions to infer declaration semantics. Stage 1 graph extraction identifies type/value dependencies and generated companions. Stage 2 records source commands, bindings and resolved references. Selection then subtracts whole unneeded declaration commands while retaining namespaces, sections, variable contexts and notation.

The scripts and data are in `harness/submission/prune/`, `runtime/`, and the vendored workspace's `scripts/`. The full original graph, parser facts and source-reference stream are committed so the decomposition can be studied without recovering an old compiler session.

Expression dependencies alone missed references erased by simplification or `rfl`. Explicit source-reference edges restored named lemmas. Implicit `@[simp]` dependencies required separate roots, as did retained selective `open` commands. Unsupported aliases in generated scopes were trimmed at exact parser-owned token spans. Compiler-generated declarations and structure-owned accessor spans were handled by their source owners.

## Runtime definitions and proper theorem cuts

Unused-code removal and cuts at the existing mathematical milestones could not fit the entire proof into the scanner limit. A new foundational bundle, `ExpandingCodes_PolynomialStretch_BinaryRuntime`, supplied the explicit runtime data, field representation, program factories, predicates, necessary constructor proofs and instances. Algorithm correctness remained in proper theorem submissions.

Its final source is in `runtime/staged/Definitions/`. One ordinary helper named `SamplerAssembly.prelude` triggered the server's reserved-command scanner. All four Lean-resolved binding/reference occurrences were renamed to `samplerFrontendProgram`; the mission's canonical definitions were untouched. `runtime/export-rename-map.json` records the exact spans.

The first sampler and tester exports were within the byte limit and locally fully checked, but each exceeded the server's 300-second verification limit. Ten meaningful, already-proved runtime boundaries then supplied smaller verification jobs:

| Key | Contract | Children |
| --- | --- | --- |
| `tape_compile` | Actual finite source-to-NKtLB simulation, time at most `1 + 2t` | — |
| `field_setup` | Canonical modulus search and field environment | — |
| `field_multiply` | Modular polynomial product on physical tapes | — |
| `field_add` | Binary coefficient-vector sum, including length zero | — |
| `field_inverse` | Canonical inverse, including inverse zero | — |
| `sampler_layer` | One layer's actual neighbor computation and frame | multiply, add |
| `sampler_frontend` | Size/random-table/field initialization | setup |
| `tester_frontend` | Word decoding, field/degree setup and core invariant | setup |
| `tester_gram` | Full padded Gram construction and storage invariant | multiply, add |
| `gaussian_rank` | Actual elimination and canonical matrix rank | multiply, add, inverse |

`partition/nodes.json` preserves exact statements, proof routes and dependency information. `partition/generation-manifest.json` records the selected declarations and source hashes. `partition/staged/Solutions/` and `submitted/` hold the proof bytes. The public definition bundle is not a container for these algorithm-correctness proofs.

## Local validation and export-context fixes

Every proof used the pinned Lean/Mathlib environment and the serialized memory cap. Helper/parent proofs were checked in two relevant contexts: pure child-statement stubs for portability, and actual closed child proofs for exact-type and standard-axiom verification. The stubs were registered child propositions; their imported `sorryAx` was expected only in that portability context, never evidence of completion.

Private cache helpers could leak simp attributes through legacy imports even after a same-file `attribute [-simp]`. Separate minimal-interface checks prevented those extra rules from masking missing server dependencies. Official Lean `--setup` import-artifact mappings isolated the check contexts without swapping the original canonical Aux cache.

An exporter-added global Classical scope changed `ext` behavior in `Gaussian.rank_fromBlocks_zero`. Removing only those ten generated-header bytes restored the original proof context in the unsubmitted Gaussian and tester exports. The entire original statement/proof suffix remained byte-identical. Independent reviews, scope correction records and failed attempts are retained.

The final reduced sampler and tester were 245,145 and 186,497 bytes. Main retained its exact statement and was independently checked against both the proved endpoint context and the clean platform-style interface context. `prune/main-preflight-summary.json` contains both checks; only the closed context establishes a closed proof.

## Publication order and replay

The actual order was: publish runtime definitions, publish exact helper statements, verify independent leaves, verify phase contracts, verify the sampler/tester reductions, then submit Main. The existing mission's auxiliary-rate milestone was independently accepted first. A `202` publication response was treated as queued work; jobs were polled to `PUBLISHED`. Proofs were polled to `ACCEPTED`, and the main theorem was freshly fetched to confirm `Proved`.

For a new verification attempt against the already-existing public theorem, use a fresh state path. For example, after preparing local credentials:

```sh
mkdir -p tmp/replay
python3 tools/prove2_submit.py submit \
  --theorem-id 35a9bc65-151f-4a09-baa1-2c28821d6cd3 \
  --file harness/submission/submitted/main-attempt-002.lean \
  --explanation-file harness/submission/explanation.txt \
  --state tmp/replay/main-attempt.json
python3 tools/prove2_submit.py poll --state tmp/replay/main-attempt.json
```

This performs a real external submission when explicitly run. It does not create a new mission or change the theorem. The accepted dependency IDs and byte-exact source archives are already listed in the final report. Do not republish existing definition/problem names or overwrite the historical attempt records.

Historical JSON commands, `.setup.json` files, and API receipts have had workstation paths and account fields redacted for public distribution. Treat them as historical evidence, not portable shell scripts or resumable authentication sessions. Historical hashes of redacted metadata describe the original records; the accepted Lean upload hashes still match the preserved source bytes. The included Python generators compute roots from their location and regenerate setup/audit artifacts. For a new export investigation, work in a separate copy/branch, regenerate preflight files and attempt sessions, and rebuild excluded compiler caches in dependency order. Keep the accepted upload bytes immutable. The supported portable closed-proof reproduction path is the complete local project described in the README; neither saved API receipts nor stub-only compilation replaces that proof check.
