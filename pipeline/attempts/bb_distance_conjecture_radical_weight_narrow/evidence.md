# Evidence — narrowed conjecture survives

## Corpus sweep (3 894 labeled rows, restricted to hypothesis)

```
$ uv run python scripts/cv3_restricted_sweep.py
```

| classifier | rows | violations | tight | tightness |
|:---|:---:|:---:|:---:|:---:|
| loose elem-ab G_odd ALL | 3 894 | 3 319 | 213 | 5.5% |
| loose elem-ab ∧ c = 3 | 61 | **0** | 32 | 52.5% |
| loose elem-ab ∧ c = 4 | 8 | 0 | 0 | 0% |
| loose elem-ab ∧ c = 5 | 1 | 0 | 1 | 100% |
| loose elem-ab ∧ c = 6 | 4 | 0 | 0 | 0% |
| **loose elem-ab ∧ c ≥ 3 (TOTAL)** | **74** | **0** | **33** | **44.6%** |

**No corpus violations on the hypothesis domain.**

For comparison, what gets filtered out:

| filtered-out | violations | tight rate |
|:---|:---:|:---:|
| elem-ab ∧ c = 1 | 3 148 / 3 245 (97%) | 3.0% |
| elem-ab ∧ c = 2 | 171 / 575 (30%) | 14.4% |
| NOT elem-ab | (corpus has 0 in this case — all labeled rows are elem-ab) | n/a |

## Per G_odd decomposition

| decomp | rows | violations | tight | tightness |
|:---|:---:|:---:|:---:|:---:|
| `(3,)` rank-1 | 179 | 55 | 93 | 52.0% |
| `(3, 3)` rank-2 same prime | 990 | 763 | 62 | 6.3% |
| `(3, 5)` rank-2 multi-prime | 2 725 | 2 501 | 58 | 2.1% |

Single-prime rank-1 is the highest tightness rate among G_odd
families. The narrowed conjecture's c ≥ 3 condition cuts most of the
rank-2 violations (which are dominated by c=1 cases with A ≅ B).

## Bravyi table

```
$ uv run python -c "
import yaml
from bb_lab.group import ZmZn
from bb_lab.poly import Poly
from bb_lab.radical_weight import bb_radical_bound, joint_support_subgroup_index
from bb_lab.degeneracy import is_g_odd_elementary_abelian
for inst in yaml.safe_load(open('instances/bravyi_table.yaml'))['instances']:
    G = ZmZn(inst['group']['ell'], inst['group']['m'])
    A = Poly.from_string(inst['polynomials']['A'], G)
    B = Poly.from_string(inst['polynomials']['B'], G)
    elem_ab = is_g_odd_elementary_abelian(G)
    c = joint_support_subgroup_index(A, B, G)
    bound = bb_radical_bound(A, B, G)
    d = inst['parameters']['d']
    print(f'{inst[\"code_id\"]:<20} elem-ab={elem_ab} c={c} bound={bound} d={d}')
"
```

| code | G | elem-ab | c | bound | d | in domain? | verdict |
|---|---|:---:|:---:|:---:|:---:|:---:|:---:|
| bb_72_12_6 | Z₆×Z₆ | ✓ | 3 | 6 | 6 | ✓ | **tight** |
| bb_90_8_10 | Z₁₅×Z₃ | ✓ | 3 | 10 | 10 | ✓ | **tight** |
| bb_108_8_10 | Z₉×Z₆ | ✗ | 3 | 12 | 10 | excluded | (n/a — not in hypothesis) |
| gross | Z₁₂×Z₆ | ✓ | 3 | 12 | 12 | ✓ | **tight** |
| bb_288_12_18 | Z₁₂×Z₁₂ | ✓ | 3 | 18 | 18 | ✓ | **tight** |

**All 4 Bravyi codes in the hypothesis domain are tight.** bb_108_8_10
is properly excluded by the elem-ab condition.

## Z_4 × Z_6 anomaly resolution

C-v2 flagged Z_4 × Z_6 as showing 65% tightness — investigated in
detail in [`Cv3_z4xz6_anomaly.md`](../../experiments/bb_lab/notes/Cv3_z4xz6_anomaly.md).
**Resolution: it's the same conjecture (rank-1 G_odd).** The 65%
empirical tightness includes c=1 cases that the c ≥ 3 condition
excludes (correctly). The hypothesis-domain rows on Z_4 × Z_6 are
not many (the c distribution shows almost all Z_4 × Z_6 rows are
c ∈ {1, 2}); they're consistent with the narrowed conjecture.

## Reproducibility commands

From `experiments/bb_lab/`:

```
uv run pytest tests/test_degeneracy.py -v   # 19 passed (10 existing + 9 new C-v3)
uv run python scripts/cv3_restricted_sweep.py  # ~9 seconds
```

## Implementation summary

- `degeneracy.g_odd_decomposition(G)`: primary cyclic factors of G_odd.
- `degeneracy.is_g_odd_elementary_abelian(G)`: True iff each prime-part
  of G_odd is elementary abelian (loose definition; bb_90 qualifies).
- `degeneracy.g_odd_elementary_prime(G)`: single-prime version
  (returns None for multi-prime cases like bb_90).
- `radical_weight.bb_radical_bound(A, B, G)`: from C-v2; unchanged.

The hypothesis-domain check in callers:
```python
from bb_lab.degeneracy import is_g_odd_elementary_abelian
from bb_lab.radical_weight import joint_support_subgroup_index, bb_radical_bound

def is_narrowed_hypothesis_applicable(A, B, G):
    return is_g_odd_elementary_abelian(G) and joint_support_subgroup_index(A, B, G) >= 3

def narrowed_bound(A, B, G):
    if not is_narrowed_hypothesis_applicable(A, B, G):
        return None  # conjecture not applicable
    return bb_radical_bound(A, B, G)
```
