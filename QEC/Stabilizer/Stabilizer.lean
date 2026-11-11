/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import QEC.Stabilizer.Foundations
import QEC.Stabilizer.Framework
import QEC.Stabilizer.Geometry
import QEC.Stabilizer.Codes

/-!
# The stabilizer formalism

- `Foundations`: the Pauli groups and the binary symplectic representation.
- `Geometry`: lattice primitives shared by the lattice code families.
- `Framework`: stabilizer groups and codes, logical operators and distance,
  and the homological description of CSS codes.
- `Codes`: concrete codes and code families.

Each layer imports only the ones above it in this list.
-/
