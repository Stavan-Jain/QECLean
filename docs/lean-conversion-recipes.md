# Lean conversion recipes

One-time conversion patterns that come up only during linter sweeps or
mathlib-version bumps. Kept out of `CLAUDE.md` because they're situational
and code-heavy; pull them in when you hit the corresponding warning class.

## Converting nested `induction'` on `Fin L`

The legacy two-step pattern
```lean
induction' y with y ih
induction' y with y ih
```
(Fin destruct then Nat induction) has a clean modern equivalent:

```lean
obtain ⟨y, ih⟩ := y       -- destructure Fin → (y : ℕ, ih : y < L)
induction y with
| zero => ...
| succ y ih_step => ...   -- ih substitutes to `ih : y + 1 < L`
```

Key subtlety: in the `succ` case, the outer `ih : y < L` is preserved and
**substituted to `ih : y + 1 < L`** by `induction` (the tactic walks
through dependent hypotheses during case analysis). So any references
like `Nat.mod_eq_of_lt ih` in the original `induction'` body keep working
unchanged. The Nat induction's own IH gets a separate name (`ih_step`
above) to avoid the clash.

For closure-style induction principles, name cases by the principle:
- `Subgroup.closure_induction`: `| mem g hg | one | mul x y hx hy ihx ihy | inv x hx ih`
- `Finset.induction`: `| empty | insert a s has ih`

## Restructuring structure-builder `refine` chains (`linter.style.multiGoal`)

When a proof has
```lean
refine LinearEquiv.ofBijective ?_ ⟨?_, ?_⟩
refine { toFun := ?_, map_add' := ?_, map_smul' := ?_ }
refine fun x => ⟨?_, ?_⟩
refine { toFun := ..., map_add' := ?_, map_smul' := ?_ }
all_goals norm_num [...]
any_goals intros; ext; simp +decide [...]
...
```
each non-leading `refine` is flagged by `linter.style.multiGoal` for
leaving sibling goals untouched. The fix is **nested `·` bullets with the
broadcast tactics moved to the relevant level**:

```lean
refine LinearEquiv.ofBijective ?_ ⟨?_, ?_⟩
· refine { toFun := ?_, map_add' := ?_, map_smul' := ?_ }
  · refine fun x => ⟨?_, ?_⟩
    · refine { toFun := ..., map_add' := ?_, map_smul' := ?_ }
      all_goals norm_num [...]   -- closes the two innermost field goals
    · -- range-membership branch (uses x)
      ...
  all_goals norm_num [...]       -- closes the outer map_add' / map_smul'
  any_goals intros; ext; simp +decide [...]
all_goals norm_num [Function.Injective, Function.Surjective]
· -- injectivity
  ...
· -- surjectivity
  ...
```

`all_goals` / `any_goals` placed at a bullet's tail only sees the goals
that bullet has open. The proof's original broadcast tactics stay; they
just move from outer scope (where they applied to all 7 goals at once)
to specific nesting levels (where they apply to the relevant 2–3 goals).
See `toric_rank_boundary1_eq_rank_cutMap` in `ToricH1Dimension.lean` for
the worked example.

**What DOESN'T work**: combining all the `refine`s into one inline term
with metavariables across a `fun x => ...` binder — the metavars can't
be resolved from outer bullets because `x` isn't in their scope. Stick
to nested `·` focus.
