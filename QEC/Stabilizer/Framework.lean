module

public import QEC.Stabilizer.Framework.Core
public import QEC.Stabilizer.Framework.Symplectic
public import QEC.Stabilizer.Framework.Homological
public import QEC.Stabilizer.Framework.Concatenation
public import QEC.Stabilizer.Framework.FoldDouble

/-!
# Framework

The theory of stabilizer codes, independent of any particular code:

- `Core`: stabilizer groups and codes, the codespace, logical operators and
  gates, code distance, and CSS codes.
- `Symplectic`: stabilizer groups through their symplectic vectors;
  presentations of a code by independent generators.
- `Homological`: CSS codes as chain complexes, the correspondence between
  logical operators and homology, and bivariate bicycle codes.
- `Concatenation`: concatenation of CSS codes and its distance bound.
- `FoldDouble`: qubit pairings, the folded code and the fold-and-double
  distance theorem.
-/
