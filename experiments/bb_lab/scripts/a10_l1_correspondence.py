"""A10 — constructive Lemma-L1 correspondence (the A11 cross-check).

The A11 session found that the ANCHORABLE presentations of hit2/hit5
have literal x-covers with d = 12, and inferred that a Fork-C negative
"can only be a statement about the stored presentations' descent
space".  Lemma L1 (A10 notes §R2.5) says otherwise: descent-cover
codes are invariant under presentation moves, classes permuted — so an
anchorable presentation's literal x-cover MUST appear in the stored
presentation's 4×64 descent screen at a computable (class, twist).

This script computes that row constructively:

  1. find the presentation move (swap?, σ ∈ Aut(H), translation g)
     carrying the stored pair to the anchorable pair;
  2. transport the anchorable literal x-cover (G₁ = Z₁₂×Z₆, π₁) back:
     π := σ⁻¹∘π₁ is a Z₂-extension of H presenting the SAME cover code
     over the STORED pair;
  3. classify its extension class c = (c₁, c₂) (generator-lift order
     test), build the explicit iso ψ : (G₁, π) → (G_c, π_c) over id_H
     (coboundary-correction η), and read the twist bits ε;
  4. verify: ψ transports the literal cover polynomials to a
     weight-preserving descent pair over G_c whose BB code is
     permutation-equivalent to the anchorable literal cover (exact
     matrix equality under ψ's index map), and report the screen row
     (c, εA, εB) — which must be / become a `rescue` row.

    uv run python scripts/a10_l1_correspondence.py
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

LAB_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LAB_ROOT / "src"))
sys.path.insert(0, str(LAB_ROOT / "scripts"))

from bb_lab.checks import bb_check_matrices
from bb_lab.group import AbelianGroup
from bb_lab.poly import Poly

from a5_cover_cascade import automorphisms, apply_auto
from a9_lean_target_screen import cover_group, lift_poly
from a10_descent_covers import CoverGroup, monomial_order

H = AbelianGroup((6, 6))

CASES = [
    # base_id, stored (A, B), anchorable (A', B') from the A11 message
    ("hit2", "y^3 + x + x^2", "1 + x*y^5 + x^2*y",
     "1 + x + x^2*y^3", "y^2 + x^3 + x^3*y"),
    ("hit5", "y^3 + x + x^2", "y^5 + x*y + x^2",
     "x^3 + x^4 + x^5*y^3", "x*y^2 + x^4 + x^4*y"),
]


def find_move(A, B, Ap, Bp):
    """(swapped, sigma, g) with  translate_g(apply_auto(pair, sigma))
    = (Ap, Bp), searching Aut × swap × translation."""
    for swapped, (P, Q) in ((False, (A, B)), (True, (B, A))):
        for sigma in automorphisms(6, 6):
            Ps = apply_auto(P, sigma, H)
            # candidate common translation from any support alignment
            for a0 in Ps.support:
                for a1 in Ap.support:
                    g = H.sub(a1, a0)
                    tP = frozenset(H.add(g, s) for s in Ps.support)
                    if tP != Ap.support:
                        continue
                    Qs = apply_auto(Q, sigma, H)
                    tQ = frozenset(H.add(g, s) for s in Qs.support)
                    if tQ == Bp.support:
                        return swapped, sigma, g
    return None


def sigma_matrix_inverse(sigma):
    """sigma as images of e1, e2; return the inverse automorphism as a
    callable on H (search: the inverse is also in Aut)."""
    e1, e2 = sigma

    def apply(h):
        return H.add(
            tuple((h[0] * c) % o for c, o in zip(e1, H.orders)),
            tuple((h[1] * c) % o for c, o in zip(e2, H.orders)),
        )

    for tau in automorphisms(6, 6):
        t1, t2 = tau

        def apply_t(h, t1=t1, t2=t2):
            return H.add(
                tuple((h[0] * c) % o for c, o in zip(t1, H.orders)),
                tuple((h[1] * c) % o for c, o in zip(t2, H.orders)),
            )

        if apply_t(apply((1, 0))) == (1, 0) and apply_t(apply((0, 1))) == (0, 1):
            return apply_t
    raise RuntimeError("no inverse found")


def main() -> None:
    G1 = cover_group(6, 6, "x")  # Z12 x Z6

    for base_id, A_str, B_str, Ap_str, Bp_str in CASES:
        A, B = Poly.from_string(A_str, H), Poly.from_string(B_str, H)
        Ap, Bp = Poly.from_string(Ap_str, H), Poly.from_string(Bp_str, H)
        move = find_move(A, B, Ap, Bp)
        if move is None:
            print(f"[{base_id}] NO Aut×swap×translation move found — "
                  "the anchorable pair is NOT in the stored pair's "
                  "presentation orbit; L1 does not apply to it!")
            continue
        swapped, sigma, g = move
        print(f"[{base_id}] move: swap={swapped} sigma(e1,e2)={sigma} translate={g}")
        inv = sigma_matrix_inverse(sigma)

        # π = translate-free: translations of H do not change π's class;
        # the cover of (A,B) is (G1, π, Ã, B̃) with π = inv ∘ π₁ and the
        # SAME literal cover polynomials (translated back by a lift of g;
        # a monomial translation of both cover polys is a cover-code
        # automorphism, so we drop it — weights and code unchanged).
        def pi(gc):
            return inv((gc[0] % 6, gc[1]))

        deck1 = None
        for cand in G1:
            if pi(cand) == (0, 0) and cand != (0, 0):
                deck1 = cand
        assert deck1 is not None
        # class test: minimal order of the two preimages of each generator
        def lift_order_doubles(h) -> int:
            pre = [gc for gc in G1 if pi(gc) == h]
            def order(gc):
                o, acc = 1, gc
                while acc != (0, 0):
                    acc = G1.add(acc, gc)
                    o += 1
                return o
            h_ord = 6
            return 1 if min(order(p) for p in pre) == 2 * h_ord else 0

        c1 = lift_order_doubles((1, 0))
        c2 = lift_order_doubles((0, 1))
        cls = (c1, c2)
        print(f"[{base_id}] transported extension class over stored pair: {cls}")

        # explicit iso ψ : (G1, π) -> (G_c, π_c) over id_H
        Gc = CoverGroup(6, 6, *cls)
        s1 = {}
        for h in H:
            s1[h] = next(gc for gc in G1 if pi(gc) == h and gc[0] < 6) \
                if any(pi(gc) == h and gc[0] < 6 for gc in G1) \
                else next(gc for gc in G1 if pi(gc) == h)
        def coc1(h, hp):  # cocycle of (G1, π, s1)
            return 0 if G1.add(s1[h], s1[hp]) == s1[H.add(h, hp)] else 1
        def cocc(h, hp):  # cocycle of (G_c, sec)
            return Gc.add(Gc.sec(h), Gc.sec(hp))[0]
        # solve dη = coc1 - cocc by BFS from 0 over generators
        eta = {(0, 0): 0}
        frontier = [(0, 0)]
        gens = [(1, 0), (0, 1)]
        eta_g = {}
        # generator values free — set 0
        for gen in gens:
            eta_g[gen] = 0
        while frontier:
            h = frontier.pop()
            for gen in gens:
                hp = H.add(h, gen)
                if hp in eta:
                    continue
                eta[hp] = (eta[h] + eta_g[gen] + coc1(h, gen) + cocc(h, gen)) % 2
                frontier.append(hp)
        # consistency check of η (class equality)
        bad = [
            (h, hp)
            for h in H
            for hp in H
            if (eta[H.add(h, hp)] + eta[h] + eta[hp]) % 2
            != (coc1(h, hp) + cocc(h, hp)) % 2
        ]
        print(f"[{base_id}] eta consistency violations: {len(bad)} (0 = classes equal)")
        if bad:
            continue

        def psi(gc):
            h = pi(gc)
            t = 0 if gc == s1[h] else 1
            base = Gc.sec(h)
            out = base if (t + eta[h]) % 2 == 0 else Gc.add(base, Gc.deck)
            return out

        # transport the literal cover polynomials (with the base translated
        # back: the anchorable pair = g + sigma(stored pair), so σ⁻¹ of the
        # translated-back anchorable = stored exactly)
        gi = inv(g)
        Ap_back = frozenset(H.sub(s, g) for s in Ap.support)
        Bp_back = frozenset(H.sub(s, g) for s in Bp.support)
        # literal lift on G1 of the anchorable polys, translated back on H first:
        # supports as elements of G1 (a<6 coordinates = the literal embed)
        At = frozenset(psi(s) for s in Ap_back)   # NB: Ap_back ⊂ H ⊂ G1 literally
        Bt = frozenset(psi(s) for s in Bp_back)
        if swapped:
            At, Bt = Bt, At
        # read off twist bits relative to my monomial order of the stored pair
        stored_A, stored_B = (A, B)
        def eps_of(cover_supp, P):
            eps = []
            for mon in monomial_order(P):
                fib = [gg for gg in cover_supp if (gg[1], gg[2]) == mon]
                assert len(fib) == 1, (mon, cover_supp)
                eps.append(fib[0][0])
            return tuple(eps)
        # ψ-image supports project correctly?
        projs_A = sorted((gg[1], gg[2]) for gg in At)
        assert projs_A == sorted(stored_A.support), (projs_A, sorted(stored_A.support))
        epsA = eps_of(At, stored_A)
        epsB = eps_of(Bt, stored_B)
        print(f"[{base_id}] ==> screen row: class={cls} "
              f"epsA={''.join(map(str, epsA))} epsB={''.join(map(str, epsB))}")

        # exact matrix-equality verification of the code identification
        Ac = Poly(support=At, group=Gc)
        Bc = Poly(support=Bt, group=Gc)
        checks_c = bb_check_matrices(Ac, Bc)
        lifted = bb_check_matrices(lift_poly(Poly(support=Ap_back, group=H), G1),
                                   lift_poly(Poly(support=Bp_back, group=H), G1))
        if swapped:
            n1 = G1.cardinality
            LX = np.concatenate([lifted.H_X[:, n1:], lifted.H_X[:, :n1]], axis=1)
            LZ = np.concatenate([lifted.H_Z[:, n1:], lifted.H_Z[:, :n1]], axis=1)
        else:
            LX, LZ = lifted.H_X, lifted.H_Z
        pi_idx = np.array([Gc.index(psi(gg)) for gg in G1], dtype=np.int64)
        n = G1.cardinality
        ok = True
        for Mc, Ml in ((checks_c.H_X, LX), (checks_c.H_Z, LZ)):
            left = np.zeros_like(Mc[:, :n]); right = np.zeros_like(Mc[:, n:])
            left[np.ix_(pi_idx, pi_idx)] = Ml[:, :n]
            right[np.ix_(pi_idx, pi_idx)] = Ml[:, n:]
            ok &= bool(np.array_equal(Mc[:, :n], left) and np.array_equal(Mc[:, n:], right))
        print(f"[{base_id}] exact matrix equality under psi: {ok}")

        # cross-reference against the screen JSONLs
        import glob
        for f in glob.glob(str(LAB_ROOT / "data" / "a10" / f"{base_id}_descent_screen*.jsonl")):
            for line in open(f):
                r = json.loads(line)
                if (tuple(r["cls"]), tuple(r["epsA"]), tuple(r["epsB"])) == (cls, epsA, epsB):
                    print(f"[{base_id}] screen JSONL row: verdict={r['verdict']} d={r.get('d')}")


if __name__ == "__main__":
    main()
