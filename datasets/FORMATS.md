# Dataset Format Status

## Implemented

| Format | Status | Notes |
|---|---|---|
| JSONL (`id`, `lean_code`, metadata...) | done | Native loader support in `runner/loader.py` |

## Planned

| Format | Status | Plan |
|---|---|---|
| JSON array objects | planned | add converter to canonical JSONL |
| CSV + code column | planned | add preprocessor script to canonical JSONL |
| benchmark-specific schemas | planned | adapter modules mapping to canonical fields |

## Design Rule

All adapters must map into canonical internal rows:
- `id: str`
- `lean_code: str`
- `metadata: dict`
