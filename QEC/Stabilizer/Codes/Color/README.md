# Triangular honeycomb color codes

This directory formalizes the triangular color-code family described in
Ali Lavasani et al., *Quantum error correction well below the color code
threshold*, p. 1 and Fig. 1(a), [arXiv:2610.24077]. The parameters count data
qubits; syndrome-extraction ancillas are not part of the stabilizer code.

Import `QEC.Stabilizer.Codes.Color`. The namespace is
`Quantum.StabilizerGroup.ColorCode`.

## Interface

- `stabilizerCodeWithDistance r` has parameters
  `[[3*r*(r+1)+1, 1, 2*r+1]]` for every natural `r`.
- `codeOfOddDistance d hodd` has parameters
  `[[(3*d^2+1)/4, 1, d]]` for every odd natural `d`.
- `stabilizerCodeWithLogicals r` supplies the transversal X and Z pair.
- `has_code_distance r` proves the exact distance of the canonical
  `stabilizerCode r`, including arbitrary mixed Pauli logical operators.

The cases `r = 1, 2, 3` are `[[7,1,3]]`, `[[19,1,5]]`, and `[[37,1,7]]`.
The degenerate `r = 0` case is the `[[1,1,1]]` code with no stabilizer checks.

## Construction and proof

`Geometry` uses coordinates `0 ≤ column ≤ row ≤ 3*r`. Face centers have
`(row + column) % 3 = 2`; the other sites are qubits. Each face generates
both an X check and a Z check on its six neighboring positions, clipped
at the triangular boundary.

`FaceParity` and `Orthogonality` pair face sites and shared sites by
reflection. `Independence` uses an uppermost nonzero face coefficient to
prove independence of the checks. `Code` applies the reusable homological
presentation to derive the single canonical stabilizer group from its
generator list. The count of independent generators is `n - 1`.

`Logicals` proves that transversal X and Z commute with the checks and
anticommute with each other. `Boundary` constructs a nontrivial boundary
logical of weight `2*r+1`. `BinaryLogical` identifies the even cycles with
face boundaries, so every odd cycle is the all-ones chain plus a face
boundary.

The distance lower bound is a uniform induction on three-row shells:

1. `Spin` evaluates each qubit of the odd logical coset from its incident
   face labels. `SpinSum` groups its Hamming weight by shells.
2. `Energy` gives an eight-state potential whose local inequalities are
   proved by ordinary kernel-checked `decide`. Telescoping bounds each
   shell's energy relative to its inner and outer boundary labels.
3. `LowerBound` inducts on the number of shells. The external labels are
   zero, giving the lower bound `2*r+1` without a distance hypothesis.
4. `Distance` applies the existing CSS distance bridge and the boundary
   witness to package the exact `[[n,k,d]]` parameters.

Only the constant-size local inequalities use finite case checking. The
distance proof does not enumerate logical operators or bound `r`.

[arXiv:2610.24077]: https://arxiv.org/abs/2610.24077
