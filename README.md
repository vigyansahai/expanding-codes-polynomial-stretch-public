# Expanding Codes with Polynomial Stretch

Lean formalization of the exact [Prove2 mission](https://prove2.me/missions/Expanding_Codes_with_Polynomial_Stretch), together with the coordinator-driven proof harness and the complete publication workflow used to get the result accepted.

The main theorem is **Proved** on Prove2. The final publication consists of 14 accepted proofs and one published runtime-definition bundle. The local development has 54 verified proof-DAG nodes, including actual finite sampler/tester programs, their execution and random-output laws, and polynomial running-time bounds.

## Start here

| Material | Location |
| --- | --- |
| Complete local theorem | [Solutions/Sol_ExpandingCodes_PolynomialStretch_expanding_codes.lean](Solutions/Sol_ExpandingCodes_PolynomialStretch_expanding_codes.lean) |
| Proof architecture and agent workflow | [docs/PROOF_WORKFLOW.md](docs/PROOF_WORKFLOW.md) |
| Prove2 export, decomposition, and submission workflow | [docs/PROVE2_WORKFLOW.md](docs/PROVE2_WORKFLOW.md) |
| GitHub login and first push | [docs/GITHUB.md](docs/GITHUB.md) |
| Proof task DAG and worker instructions | [harness/graph.json](harness/graph.json), [harness/worker_prompt.txt](harness/worker_prompt.txt), [AGENTS.md](AGENTS.md) |
| Final platform acceptance record | [artifacts/prove2-verification-summary.json](artifacts/prove2-verification-summary.json) |
| Exact accepted main upload | [harness/submission/submitted/main-attempt-002.lean](harness/submission/submitted/main-attempt-002.lean) |
| Original standalone proof bundle | [artifacts/expanding-codes-proof-lean-4.33.1.zip](artifacts/expanding-codes-proof-lean-4.33.1.zip) |

## Reproduce the local proof

The environment is pinned to Lean `4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Python tooling uses the standard library; Python 3.10 or later is recommended.

With [Elan](https://github.com/leanprover/elan) installed, run from this directory:

```sh
export PATH="$HOME/.elan/bin:$PATH"
elan toolchain install leanprover/lean4:v4.33.1
lake exe cache get
./tools/setup-repo
./tools/lake-serial build Solutions.Sol_ExpandingCodes_PolynomialStretch_expanding_codes
./tools/lake-serial env lean artifacts/Verify.lean
```

To rerun the proof-DAG verifier, including exact statement and transitive axiom checks:

```sh
python3 harness/engine.py verify headline --mode prove
```

The compiler wrapper serializes jobs, uses one Lean thread, and defaults to a 6144 MB memory cap. Persistent REPL use was disabled after excessive memory growth. All completed proofs use only `propext`, `Classical.choice`, and `Quot.sound` as axioms.

For fast checks of saved records and harness behavior, without running Lean or using an API key:

```sh
python3 tools/check_saved_workflow.py
python3 harness/engine.py validate
python3 -m unittest harness.test_engine
```

`validate` and the saved-record checker inspect evidence; they do not replace a fresh Lean build and audit.

## What is preserved

The repository keeps proof sources, exact platform definitions, task packets, proof routes, reviews, failed attempts, compiler logs, dependency/source-reference extraction data, export generators, accepted upload bytes, API submission receipts, and mathematical explanations. Historical scratch drafts may contain incomplete proofs; the completed theorem is the `solution` linked above.

`harness/coordinator.json` and individual task notes contain historical intermediate snapshots. Final truth is recorded in `harness/graph.json`, `harness/runs/final-verification.log`, and `harness/submission/final-api-verification.json`.

The upstream Prove2 workspace and Lean REPL source are included as ordinary source snapshots. Their exact upstream commits and local REPL toolchain adjustment are recorded in [docs/upstream-provenance.json](docs/upstream-provenance.json). Upstream notices and licenses remain in their source trees. The REPL is preserved for history and is not part of the supported checking path.

Compiler outputs, downloaded package caches, nested Git metadata, credentials, temporary authentication state, source PDFs, and extracted paper text are excluded. Public references are in [docs/SOURCES.md](docs/SOURCES.md). Historical task notes may cite line numbers from locally extracted text that is supplied separately.

Workstation paths and account metadata in historical records have been redacted. [docs/PUBLIC_SNAPSHOT.md](docs/PUBLIC_SNAPSHOT.md) describes those changes and the fresh verification of the public snapshot. The Lean sources and accepted upload bytes are unchanged.

## Credentials

No API key is needed to build or inspect the proof. Authenticated Prove2 operations optionally use a local `.env` file based on [.env.example](.env.example). `.env` and `tmp/prove2-token.json` are ignored. The pre-commit guard scans actual staged content and ZIP members for credentials and personal metadata, including matches against locally configured credential values, without printing those values.

GitHub login and remote creation are intentionally left to the repository owner; see [docs/GITHUB.md](docs/GITHUB.md).
