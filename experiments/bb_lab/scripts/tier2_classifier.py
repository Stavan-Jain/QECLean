"""Tier-2.1 — Tightness classifier for the textbook CSS bound.

For every corpus row with both `d_exact` and `min_wt_ker_{A,B}` filled
in, define::

    tight ≡ (d_exact == min(min_wt_ker_A, min_wt_ker_B))

The textbook CSS bound says `d_X ≤ min(d_A^⊥, d_B^⊥) = min(min_wt_ker_A,
min_wt_ker_B)`. The bound is tight 22.4% globally on this corpus but
per-group rates vary wildly — `Z4xZ6` is 90.6% tight, `Z5xZ6` is 10.7%.

The goal is to find a structural condition `C(G, A, B)` that predicts
tightness. To that end we train a small interpretable decision tree on
the available features and read the splits out by hand. Logistic
regression is a sanity-check secondary lens (linear feature importance).

Usage (from `experiments/bb_lab/`):

    uv run python scripts/tier2_classifier.py
    uv run python scripts/tier2_classifier.py --max-depth 5
    uv run python scripts/tier2_classifier.py --no-derived  # drop min_minwt etc.

Read-only — opens the corpus DuckDB via `Corpus(read_only=True)`.
"""

from __future__ import annotations

import argparse
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.linear_model import LogisticRegression
from sklearn.metrics import (
    accuracy_score,
    classification_report,
    confusion_matrix,
)
from sklearn.model_selection import StratifiedKFold, cross_val_score
from sklearn.preprocessing import StandardScaler
from sklearn.tree import DecisionTreeClassifier, export_text

from bb_lab.corpus import Corpus


# ---------- data loading -----------------------------------------------------


# Features available in the DB (group_struct will be one-hot encoded).
BASE_FEATURES = [
    "n", "k",
    "A_weight", "B_weight",
    "rank_HX", "rank_HZ",
    "dim_ker_A", "dim_ker_B",
    "orbit_size",
    "tanner_girth",
    "supp_diameter_A", "supp_diameter_B",
    "min_wt_ker_A", "min_wt_ker_B",
    "ell", "m",
]
# Derived "obvious" features — they are summaries of the two ker_min
# weights. Useful because the tree may want to split on them but can't
# combine raw columns mid-tree.
DERIVED_FEATURES = [
    "min_minwt",     # min(min_wt_ker_A, min_wt_ker_B)
    "max_minwt",     # max(min_wt_ker_A, min_wt_ker_B)
    "minwt_gap",     # max - min
    "minwt_eq",      # 1 iff min_wt_ker_A == min_wt_ker_B
]


def load_corpus_df(db_path: Path | None) -> pd.DataFrame:
    """Pull (d_exact, min_wt_ker_*) rows into a DataFrame.

    Adds a binary `tight` target and the derived feature columns.
    """
    c = Corpus(db_path=db_path) if db_path else Corpus()
    base = c.filter(
        d_exact_is_not_null=True,
        min_wt_ker_A_is_not_null=True,
        min_wt_ker_B_is_not_null=True,
    )
    df = base.to_pandas()
    minwts = df[["min_wt_ker_A", "min_wt_ker_B"]]
    df["min_minwt"] = minwts.min(axis=1)
    df["max_minwt"] = minwts.max(axis=1)
    df["minwt_gap"] = df["max_minwt"] - df["min_minwt"]
    df["minwt_eq"] = (df["min_wt_ker_A"] == df["min_wt_ker_B"]).astype(int)
    df["tight"] = (df["d_exact"] == df["min_minwt"]).astype(int)
    return df


def build_design_matrix(
    df: pd.DataFrame, include_derived: bool = True,
) -> tuple[pd.DataFrame, list[str]]:
    """Return (X, feature_names) with group_struct one-hot encoded."""
    cols = list(BASE_FEATURES)
    if include_derived:
        cols += DERIVED_FEATURES
    # Drop constant columns silently — sklearn handles them fine but they
    # clutter feature-importance plots.
    keep = [c for c in cols if df[c].nunique(dropna=True) > 1]
    X = df[keep].copy()
    # One-hot group_struct.
    group_dummies = pd.get_dummies(
        df["group_struct"], prefix="g", dtype=int,
    )
    X = pd.concat([X.reset_index(drop=True), group_dummies.reset_index(drop=True)], axis=1)
    return X, list(X.columns)


# ---------- classifier reports -----------------------------------------------


def fit_decision_tree(
    X: pd.DataFrame, y: pd.Series, max_depth: int,
) -> tuple[DecisionTreeClassifier, dict]:
    clf = DecisionTreeClassifier(
        max_depth=max_depth,
        criterion="gini",
        class_weight="balanced",
        random_state=42,
    )
    clf.fit(X, y)
    y_pred = clf.predict(X)
    # 5-fold CV for honest accuracy.
    cv = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)
    cv_scores = cross_val_score(clf, X, y, cv=cv, scoring="accuracy")
    report = {
        "train_accuracy": accuracy_score(y, y_pred),
        "cv_accuracy_mean": float(cv_scores.mean()),
        "cv_accuracy_std": float(cv_scores.std()),
        "confusion": confusion_matrix(y, y_pred).tolist(),
        "classification_report": classification_report(y, y_pred, digits=3),
    }
    return clf, report


def fit_logreg(
    X: pd.DataFrame, y: pd.Series,
) -> tuple[LogisticRegression, dict]:
    scaler = StandardScaler()
    Xs = scaler.fit_transform(X)
    clf = LogisticRegression(
        max_iter=5000, class_weight="balanced", random_state=42, solver="liblinear",
    )
    clf.fit(Xs, y)
    y_pred = clf.predict(Xs)
    cv = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)
    cv_scores = cross_val_score(clf, Xs, y, cv=cv, scoring="accuracy")
    report = {
        "train_accuracy": accuracy_score(y, y_pred),
        "cv_accuracy_mean": float(cv_scores.mean()),
        "cv_accuracy_std": float(cv_scores.std()),
        "confusion": confusion_matrix(y, y_pred).tolist(),
        "classification_report": classification_report(y, y_pred, digits=3),
    }
    return clf, report


def feature_importance_rows(
    feature_names: list[str], importances: np.ndarray, top_k: int = 10,
) -> list[tuple[str, float]]:
    order = np.argsort(importances)[::-1]
    return [(feature_names[i], float(importances[i])) for i in order[:top_k]]


# ---------- candidate condition evaluation -----------------------------------


def evaluate_condition(
    df: pd.DataFrame, mask: pd.Series, name: str,
) -> dict:
    """Return tightness statistics under a candidate condition."""
    sub = df[mask]
    pos = sub["tight"].sum()
    neg = len(sub) - pos
    return {
        "name": name,
        "applicable": int(len(sub)),
        "tight": int(pos),
        "loose": int(neg),
        "tight_rate": float(pos / max(len(sub), 1)),
        "per_group": (
            sub.groupby("group_struct")["tight"]
               .agg(["mean", "count"])
               .to_dict(orient="index")
        ),
    }


def report_candidates(df: pd.DataFrame) -> list[dict]:
    """Hand-crafted candidates suggested by the tree splits + EDA.

    Each candidate is a *condition* `C(row)` that predicts tightness.
    We report the empirical tightness rate among rows satisfying C.

    Top candidates discovered structurally from the EDA:

      C_A  min_minwt ≤ 4 AND n ≥ 4k         (the "low-rate small-dual" wedge)
      C_B  min_minwt ≤ 4                    (broader, weaker)
      C_C  min_minwt ≤ 6                    (broadest, weakest)

    The "min_minwt = 2 always tight" finding is trivial in this corpus
    (all `d_exact ≥ 2` and CSS bound gives ≤ 2, so they sandwich), so
    we don't promote it as a stand-alone candidate.
    """
    df = df.copy()
    df["n_over_k"] = df["n"] / df["k"]
    candidates: list[dict] = []
    candidates.append(evaluate_condition(
        df,
        (df["min_minwt"] <= 4) & (df["n_over_k"] >= 4),
        "C_A: min(d_A^⊥, d_B^⊥) ≤ 4 AND n ≥ 4k",
    ))
    candidates.append(evaluate_condition(
        df, df["min_minwt"] <= 4,
        "C_B: min(d_A^⊥, d_B^⊥) ≤ 4",
    ))
    candidates.append(evaluate_condition(
        df, df["min_minwt"] <= 6,
        "C_C: min(d_A^⊥, d_B^⊥) ≤ 6",
    ))
    candidates.append(evaluate_condition(
        df,
        (df["min_minwt"] <= 6) & (df["n_over_k"] >= 4),
        "C_D: min(d_A^⊥, d_B^⊥) ≤ 6 AND n ≥ 4k",
    ))
    candidates.append(evaluate_condition(
        df,
        (df["min_minwt"] <= 4) & (df["n"] >= 2 * df["k"]),
        "C_E: min(d_A^⊥, d_B^⊥) ≤ 4 AND n ≥ 2k",
    ))
    # the negation — useful for showing what "loose" looks like:
    candidates.append(evaluate_condition(
        df, df["min_minwt"] >= 8,
        "Cneg: min(d_A^⊥, d_B^⊥) ≥ 8  (sanity check: should be 0% tight)",
    ))
    return candidates


# ---------- entry point ------------------------------------------------------


def render_candidates(cands: list[dict]) -> str:
    out: list[str] = []
    for c in cands:
        out.append(f"  {c['name']}")
        out.append(
            f"    applicable: {c['applicable']}   tight: {c['tight']}   "
            f"tight_rate: {c['tight_rate']*100:.1f}%"
        )
        for g, info in sorted(c["per_group"].items()):
            out.append(
                f"      {g:10s}  tight {info['mean']*100:5.1f}%   "
                f"n = {int(info['count'])}"
            )
    return "\n".join(out)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n", 1)[0])
    ap.add_argument("--db", type=Path, default=None,
                    help="Path to a bb_instances.duckdb (default: lab's)")
    ap.add_argument("--max-depth", type=int, default=4,
                    help="Decision-tree depth (4 keeps splits readable)")
    ap.add_argument("--no-derived", action="store_true",
                    help="Don't add min_minwt / minwt_gap / minwt_eq features")
    args = ap.parse_args()

    df = load_corpus_df(args.db)
    print(f"corpus: {len(df)} rows with d_exact + min_wt_ker_{{A,B}}")
    print(f"target balance: tight={int(df['tight'].sum())} "
          f"loose={int((1-df['tight']).sum())} "
          f"baseline rate={df['tight'].mean()*100:.1f}%")
    print()

    print("=== per-group tightness rate ===")
    pg = df.groupby("group_struct")["tight"].agg(["mean", "count"]).sort_values("count", ascending=False)
    print(pg.to_string())
    print()

    X, feature_names = build_design_matrix(df, include_derived=not args.no_derived)
    y = df["tight"]

    # ---- decision tree (the primary lens) -----
    print(f"=== decision tree (max_depth={args.max_depth}, balanced classes) ===")
    tree, tree_report = fit_decision_tree(X, y, max_depth=args.max_depth)
    print(f"train acc: {tree_report['train_accuracy']:.3f}")
    print(f"5-fold CV acc: {tree_report['cv_accuracy_mean']:.3f}"
          f" ± {tree_report['cv_accuracy_std']:.3f}")
    print("confusion matrix (rows=true [loose, tight], cols=pred):")
    cm = np.array(tree_report["confusion"])
    print(f"  [[TN={cm[0,0]}  FP={cm[0,1]}]")
    print(f"   [FN={cm[1,0]}  TP={cm[1,1]}]]")
    print("classification report:")
    print(tree_report["classification_report"])
    print("top features by Gini importance:")
    for fname, imp in feature_importance_rows(feature_names, tree.feature_importances_, top_k=10):
        print(f"  {fname:30s}  {imp:.4f}")
    print()
    print("decision tree as text:")
    print(export_text(tree, feature_names=feature_names, max_depth=args.max_depth))

    # ---- logistic regression (secondary lens) -----
    print(f"=== logistic regression (balanced classes) ===")
    logreg, logreg_report = fit_logreg(X, y)
    print(f"train acc: {logreg_report['train_accuracy']:.3f}")
    print(f"5-fold CV acc: {logreg_report['cv_accuracy_mean']:.3f}"
          f" ± {logreg_report['cv_accuracy_std']:.3f}")
    coefs = logreg.coef_.ravel()
    # Rank by |coef|.
    order = np.argsort(np.abs(coefs))[::-1]
    print("top 10 standardized coefficients (|coef|):")
    for i in order[:10]:
        sign = "+" if coefs[i] >= 0 else "-"
        print(f"  {feature_names[i]:30s}  {sign}{abs(coefs[i]):.4f}")
    print()

    # ---- candidate condition evaluation ----
    print("=== candidate conditions C(row) ===")
    cands = report_candidates(df)
    print(render_candidates(cands))

    # ---- Z4xZ6 vs Z5xZ6 deep dive ----
    print()
    print("=== Z4xZ6 vs Z5xZ6 structural diff ===")
    for g in ("Z4xZ6", "Z5xZ6"):
        sub = df[df["group_struct"] == g]
        mm_counts = sub["min_minwt"].value_counts().sort_index().to_dict()
        print(f"  {g}: n={len(sub)}  tight_rate={sub['tight'].mean()*100:.1f}%")
        print(f"    min_minwt distribution: {mm_counts}")
        print(f"    tight rate by min_minwt:")
        for mm, rate in sub.groupby("min_minwt")["tight"].mean().items():
            count = int((sub["min_minwt"] == mm).sum())
            print(f"      min_minwt={int(mm):<3d}  tight={rate*100:5.1f}%  n={count}")


if __name__ == "__main__":
    main()
