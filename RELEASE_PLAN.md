# Release Plan (v0.1x)

## Objective

Publish a focused repository that contains only:
- Lean linter implementation
- Lean tests
- Batch runner
- Dataset format docs
- Minimal CI/docs for users and agents

This release intentionally excludes prompt sets and prompt pipelines.
Release repo name: `atp-checkers`.
Internal Lean namespace remains `AtpLinter` for v0.1x.

## Scope Contract

In:
- `/src`, `/test`, `Main.lean`, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`
- `/runner`
- `/datasets`
- `README.md`, `AGENTS.md`, `llm.txt`
- `.github/workflows/lean.yml`

Out:
- `/prompts`
- Prompt-generation scripts
- Prompt-evaluation harness

## Status

Completed:
- [x] Created isolated release directory
- [x] Copied Lean package and tests
- [x] Copied runner package
- [x] Added docs (`README.md`, `AGENTS.md`, this plan)
- [x] Added dataset docs/examples
- [x] Added Lean CI workflow
- [x] Renamed release cut to `atp-checkers-v0.1x`
- [x] Updated package/exe identity to `atp-checkers`
- [x] Updated publish commands for `atp-checkers` repo

Pending:
- [ ] Quality gate sweep (tests + output schema checks)
- [ ] GitHub publish
- [ ] Initial dataset run sprint

## Quality Gates (Before Publish)

1. Build/test gates:
- `lake build`
- `lake build AtpLinterTest`
- `lake build AtpLinterDemo` (optional)

2. Runner gates:
- `python -m runner --help`
- smoke run on `datasets/examples/minimal.jsonl`
- validate emitted findings include `confidence` and `provedBy`

3. Docs gates:
- `README.md` commands are copy-paste runnable
- `datasets/FORMATS.md` clearly marks supported formats
- explicit note: prompt set excluded in v0.1x

## Publish Sequence

From this directory:

```bash
cd /Users/paws/personal/atp-eval/release/atp-checkers-v0.1x
git init
git add .
git commit -m "v0.1x: standalone ATP checkers + runner release cut"
gh repo create atp-checkers --private --source . --push
```

Then tag:

```bash
git tag -a v0.1.0 -m "ATP checkers v0.1.0"
git push origin v0.1.0
```

## Dataset Run Sprint (Immediately After Publish)

1. Prepare one output directory per dataset:
- `out/<dataset_name>/results.jsonl`
- `out/<dataset_name>/errors.jsonl` (if produced)

2. Run:
- `python -m runner <dataset.jsonl> --workspace . --output out/<dataset_name> --workers 4`

3. Capture metrics:
- total problems
- findings count by category
- compile/infra failure counts
- `confidence = proven|maybe` distribution

## v0.1x Exit Criteria

- CI green for Lean build/test
- Runner executes at least 2 real datasets end-to-end
- Output schema stable with `confidence` and `provedBy`
- Release docs accurately describe supported dataset formats

## Handoff To Next Agent

Primary path:
- `/Users/paws/personal/atp-eval/release/atp-checkers-v0.1x`

Do next:
1. Run quality gates in this directory (`lake build`, `lake build AtpLinterTest`, runner smoke run).
2. Fix any breakage from environment-specific dependency resolution.
3. Initialize/push GitHub repo `atp-checkers`.
4. Start the first 2 dataset runs and record metrics in a short run log.
