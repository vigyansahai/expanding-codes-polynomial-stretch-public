# Public snapshot provenance

This repository preserves the Lean development, agent task records, and Prove2 publication workflow. Historical metadata has been edited for public distribution:

- Workstation-specific paths use relative paths or `$HOME`.
- API account identifiers and reviewer usernames use `[REDACTED_ACCOUNT]`. Theorem, definition, and submission identifiers remain available to connect the proof records.
- Source PDFs, extracted paper text, credentials, authentication caches, and private recovery files are excluded.
- The public Git history begins with a neutral author identity.

Historical API receipts and compiler logs are redacted records, rather than exact raw response bytes. Submitted Lean sources, their hashes, the exact mission statement, and the platform acceptance statuses are unchanged. All Lean source files are byte-identical to the pre-redaction snapshot, including the 14 accepted upload archives. The original standalone proof ZIP also remains byte-identical and contains no redacted personal metadata.

`harness/runs/final-source-manifest.json` retains the original 174 source/configuration hashes. Its `public_metadata_overrides` separately identifies the current hashes of `AGENTS.md` and `harness/engine.py`. The instructions now refer to portable paths and public source references. The engine passes its temporary audit filenames to Lean relative to the project directory, preventing workstation paths from entering future receipts; its proof checks are unchanged.

After these metadata changes, the coordinator compared all 511 Lean source files against the pre-redaction snapshot, then ran a fresh serialized Lean audit of all 54 registered declarations using the existing compiled modules. It checked their exact types and transitive axioms, and used that real compiler output to refresh the graph's metadata/source receipts. The invocation and result are in `harness/runs/public-snapshot-verification.log`. No new clean build was performed; the earlier full clean build remains documented in its original final verification records. The standard `harness/engine.py verify` commands still rebuild the dependency graph before checking proofs.

`tools/check_saved_workflow.py` checks the documented source hashes, preserved accepted upload bytes, and saved acceptance evidence. `tools/check_secrets.py` scans the actual Git index and nested ZIP members for credentials and common personal-metadata patterns. These are publication guards, not a substitute for Lean verification or a guarantee that arbitrary future content is safe to publish.
