import QEC.Stabilizer.Framework.Homological.Certificate.ParityFold
import QEC.Stabilizer.Framework.Homological.Certificate.BitsetTrie

namespace Quantum.Stabilizer.Homological.F2Mask

/-- A certificate branches on coordinates or prunes by disjoint odd parity constraints. -/
inductive ParitySearchTree where
  /-- An odd parity check has no remaining available coordinate. -/
  | zero (row : Nat)
  /-- Pairwise disjoint odd parity checks exceed the remaining weight budget. -/
  | pack (rows : List Nat)
  /-- No coordinate can remain, and the chosen word is in the candidate census. -/
  | done
  /-- Both choices of one available coordinate are certified. -/
  | split (coordinate : Nat) (chosen omitted : ParitySearchTree)

/-- The current picked disagrees with one required parity. -/
def parityResidual (k : Nat) (row : Nat → Nat) (target picked index : Nat) : Bool :=
  !(Nat.beq (parityFold k (row index &&& picked)) (if target.testBit index then 1 else 0))

/-- The selected parity rows have disjoint neighborhoods among the remaining coordinates. -/
def paritySeparated (row : Nat → Nat) (available : Nat) : List Nat → Bool
  | [] => true
  | r :: rest => rest.all (fun s => Nat.beq (row r &&& row s &&& available) 0) &&
      paritySeparated row available rest

/-- A small certificate checker for all bounded-weight solutions of a parity system. -/
def checkParitySearch (k : Nat) (row : Nat → Nat) (target : Nat) (valid : Nat → Bool) :
    ParitySearchTree → Nat → Nat → Nat → Bool
  | .zero r, available, picked, _ =>
      parityResidual k row target picked r && Nat.beq (row r &&& available) 0
  | .pack rows, available, picked, cap =>
      Nat.blt cap rows.length && rows.all (parityResidual k row target picked) &&
        paritySeparated row available rows
  | .done, available, picked, cap =>
      (Nat.beq cap 0 || Nat.beq available 0) && valid picked
  | .split q yes no, available, picked, cap =>
      Nat.blt q (2 ^ k) && available.testBit q &&
        (if Nat.beq cap 0 then true else
          checkParitySearch k row target valid yes (available ^^^ 2 ^ q)
            (picked ^^^ 2 ^ q) (cap - 1)) &&
        checkParitySearch k row target valid no (available ^^^ 2 ^ q) picked cap

end Quantum.Stabilizer.Homological.F2Mask
