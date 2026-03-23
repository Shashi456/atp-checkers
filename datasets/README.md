# Datasets

This directory documents dataset formats supported by the runner.

## Canonical Internal Contract

Each JSONL row must provide:
- `id`
- `lean_code`

All other keys are preserved as metadata in output records.

## Minimal Example

See `datasets/examples/minimal.jsonl`.

## Validation Behavior

The loader reports parse errors for:
- invalid JSON
- missing `id`
- missing `lean_code`
- non-string `lean_code`

Invalid rows are skipped by default and emitted as infra errors in results.

## Next Step

As new external formats are integrated, add adapter notes and examples in `FORMATS.md`.

## Upstream Sources

| Family | Variant | Upstream URL |
|--------|---------|--------------|
| CombiBench | hf | `https://huggingface.co/datasets/AI-MO/CombiBench` |
| CombiBench | github | `https://github.com/MoonshotAI/CombiBench` |
| ProofNet | sharp | `https://huggingface.co/datasets/PAug/ProofNetSharp` |
| ProofNet | deepseek-port | `https://github.com/deepseek-ai/DeepSeek-Prover-V1.5/blob/main/datasets/proofnet.jsonl` |
| miniF2F | ai-mo-test | `https://huggingface.co/datasets/AI-MO/minif2f_test` |
| miniF2F | harmonic | `https://github.com/harmonic-ai/datasets/tree/main/minif2f` |
| miniF2F | justincasher | `https://github.com/justincasher/miniF2F` |
| miniF2F | yangky11 | `https://github.com/yangky11/miniF2F-lean4` |
| FormalMATH | all | `https://huggingface.co/datasets/SphereLab/FormalMATH-All` |
| FormalMATH | lite | `https://huggingface.co/datasets/SphereLab/FormalMATH-Lite` |
| FormalMATH | project | `https://github.com/Sphere-AI-Lab/FormalMATH-Bench` |
| TaoBench | taobench | `https://huggingface.co/datasets/uclanlp/TaoBench` |
| PutnamBench | lean4 | `https://github.com/trishullab/PutnamBench` |
| PutnamBench | project | `https://trishullab.github.io/PutnamBench/` |
| ProverBenchMath | deepseek | `https://huggingface.co/datasets/deepseek-ai/DeepSeek-ProverBench` |
| MathOlympiadBench | goedel | `https://huggingface.co/datasets/Goedel-LM/MathOlympiadBench` |
| IneqBench | ineq-comp-hf | `https://huggingface.co/datasets/zzzzzhy/Ineq-Comp` |
| IneqBench | ineq-comp-github | `https://github.com/haoyuzhao123/LeanIneqComp` |
| compfiles | default | `https://github.com/dwrensha/compfiles` |
| compfiles | site | `https://dwrensha.github.io/compfiles/` |
| IMOSLLean4 | default | `https://github.com/mortarsanjaya/IMOSLLean4` |
| IMOSLLean4 | site | `https://mortarsanjaya.github.io/IMOSLLean4/` |
