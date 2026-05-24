import QEC.Stabilizer.Codes.GOY.N

/-!
# Ganti-Onunkwo-Young codes

The parametric `[[6r, 2r, 2]]` Ganti-Onunkwo-Young code family for `r ≥ 1`.

The stabilizer group has `4r` generators: `2r − 1` weight-2 X-link
generators (`XLink i`, on adjacent x-qubits), one weight-`4r` all-X
generator (`XBig`, on all 0- and z-qubits), `2r − 1` weight-2 Z-link
generators (`ZLink i`, on adjacent z-qubits), and one weight-`4r` all-Z
generator (`ZBig`, on all x- and 0-qubits).

Introduced in [Ganti–Onunkwo–Young 2013, `arxiv:1309.1674`] for practical
scalable adiabatic quantum computation: every logical operator is weight 2,
and the planar connectivity graph has fixed degree.

- `N`: the parametric `[[6r, 2r, 2]]` formalization (this file's submodule)

The `r = 1` instance is also formalized separately in
`Codes/Small/SixQubit_6_2_2.lean` under Knill's C_6 presentation (4
weight-4 generators instead of GOY's 2 weight-2 + 2 weight-4 layout); the
two formalizations coexist as separate Lean objects (mirroring the
`Iceberg/N.lean` ↔ `FourQubit_4_2_2.lean` pattern).
-/
