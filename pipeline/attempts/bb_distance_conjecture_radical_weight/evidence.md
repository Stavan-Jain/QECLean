# Evidence — corpus sweep + Bravyi table

## Corpus sweep (3894 labeled rows, primary conjecture)

| metric | value |
|---|:---:|
| Tested | 3 894 |
| Vacuous (no joint vanishing orbit) | 0 |
| **Violations** | **3 319 (85.2%)** |
| Tight (bound = d) | 213 |
| Loose (bound < d) | 362 |
| Mean gap (loose) | 0.18 |

## Per-c breakdown

| c | total | violations | tight | loose | tightness rate |
|:---:|:---:|:---:|:---:|:---:|:---:|
| 1 | 3 245 | **3 148** | 97 | 0 | 3.0% |
| 2 | 575 | 171 | 83 | 321 | 14.4% |
| 3 | 61 | **0** | 32 | 29 | **52.5%** |
| 4 | 8 | 0 | 0 | 8 | 0% |
| 5 | 1 | 0 | 1 | 0 | 100% |
| 6 | 4 | 0 | 0 | 4 | 0% |

## Alternative formulations

| formulation | violations | tight | loose |
|:---|:---:|:---:|:---:|
| primary | 3 319 | 213 | 362 |
| any-orbit | 3 319 | 213 | 362 |
| multi-mu | 3 133 | 176 | 585 |
| sum | gross-violating | — | — |
| geometric | 3 614 | 192 | 88 |

## Bravyi table (HANDOFF_C2 §C-v2.4)

| code | G | n | k | d | c | primary | multi-mu | verdict |
|---|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| bb_72_12_6 | Z₆×Z₆ | 72 | 12 | 6 | 3 | **6** | 3 | ✓ tight |
| bb_90_8_10 | Z₁₅×Z₃ | 90 | 8 | 10 | 3 | **10** | 10 | ✓ tight |
| bb_108_8_10 | **Z₉×Z₆** | 108 | 8 | 10 | 3 | 12 | 12 | ✗ **VIOLATES** (12 > 10) |
| gross | Z₁₂×Z₆ | 144 | 12 | 12 | 3 | **12** | 6 | ✓ tight |
| bb_288_12_18 | Z₁₂×Z₁₂ | 288 | 12 | 18 | 3 | **18** | 5 | ✓ tight |

**4 of 5 Bravyi instances tight, 1 violates.**

## Sample corpus violations

| instance | group | d | bound | c | A | B |
|---|---|:---:|:---:|:---:|---|---|
| 5ae76cea | Z₃×Z₅ | 2 | 8 | 1 | 1+x+x² | 1+x+x² |
| 8296ddb0 | Z₃×Z₆ | 2 | 12 | 1 | 1+y+y² | 1+y+y² |
| fdf42d8e | Z₃×Z₆ | 4 | 12 | 1 | 1+y+y² | 1+y+x |
| 95626828 | Z₃×Z₆ | 4 | 12 | 1 | 1+y+y² | 1+y+x·y |

## Reproduction

From `experiments/bb_lab/`:

```
uv run python scripts/cv2_corpus_sweep.py
uv run python -c "
import yaml
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.radical_weight import bb_radical_bound, joint_support_subgroup_index
for inst in yaml.safe_load(open('instances/bravyi_table.yaml'))['instances']:
    G = ZmZn(inst['group']['ell'], inst['group']['m'])
    A = Poly.from_string(inst['polynomials']['A'], G)
    B = Poly.from_string(inst['polynomials']['B'], G)
    d = inst['parameters']['d']
    c = joint_support_subgroup_index(A, B, G)
    b = bb_radical_bound(A, B, G)
    print(f\"{inst['code_id']:<20} d={d:>2} c={c} bound={b} {'OK' if b<=d else 'VIOLATES'}\")
"
```

Expected: cv2_corpus_sweep.py prints exactly the table above; the
Bravyi check returns one VIOLATES line (bb_108_8_10).
