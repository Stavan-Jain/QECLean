import QEC.Stabilizer.Foundations.BinarySymplectic.RankCertificate
import QEC.Stabilizer.Codes.Toric.StabilizerCode

/-!
# Rank certificates for concrete toric codes

Generator independence for the trimmed toric generator lists at `L = 4, 5, 6`
(`m = 30, 48, 70` generators on `n = 32, 50, 72` qubits), each closed by a
right inverse of the check matrix and `rankCertCheck` under
`decide +kernel`. The exhaustive `Decidable (rowsLinearIndependent L)`
instance would enumerate `2 ^ m` coefficient vectors (`2 ^ 30` already at
`L = 4`), so it is out of reach here.

These duplicate the parametric `rowsLinearIndependent_generatorsListPackaged`
(`StabilizerCode.lean`), which stays the source of the toric presentation:
they are concrete instances of the certificate route at sizes the exhaustive
search cannot reach.

The certificate literals below are emitted by
`lake env lean --run scripts/RankCertificateGen.lean toric4 toric5 toric6`.
Regenerate them with the script rather than editing them by hand.
-/

namespace Quantum
namespace StabilizerGroup
namespace ToricCodeN

open NQubitPauliGroupElement

local instance : Fact (0 < 4) := ⟨by decide⟩
local instance : Fact (0 < 5) := ⟨by decide⟩
local instance : Fact (0 < 6) := ⟨by decide⟩

/-- Rank certificate for the trimmed `L = 4` toric generators
(m = 30, n = 32; emitted by
`scripts/RankCertificateGen.lean`). -/
def rankCert4 : List ℕ :=
  [0x1000000000000, 0x11000000000000, 0x111000000000000, 0x100000000, 0x1001000000000,
   0x11010000000000, 0x111100000000000, 0x300000000, 0x1003000000000, 0x11030000000000,
   0x111300000000000, 0x700000000, 0x1007000000000, 0x11070000000000, 0x111700000000000, 0x10,
   0x110, 0x1, 0x20000, 0x20020, 0x20220, 0x20002, 0x60000, 0x60040, 0x60440, 0x60004, 0x10000,
   0x10080, 0x10880, 0x10008]

/-- Rank certificate for the trimmed `L = 5` toric generators
(m = 48, n = 50; emitted by
`scripts/RankCertificateGen.lean`). -/
def rankCert5 : List ℕ :=
  [0x8000000000000000000, 0x108000000000000000000, 0x2108000000000000000000,
   0x42108000000000000000000, 0x4000000000000, 0x8000080000000000000, 0x108001000000000000000,
   0x2108020000000000000000, 0x42108400000000000000000, 0xc000000000000, 0x8000180000000000000,
   0x108003000000000000000, 0x2108060000000000000000, 0x42108c00000000000000000, 0x1c000000000000,
   0x8000380000000000000, 0x108007000000000000000, 0x21080e0000000000000000,
   0x42109c00000000000000000, 0x3c000000000000, 0x8000780000000000000, 0x10800f000000000000000,
   0x21081e0000000000000000, 0x4210bc00000000000000000, 0x20, 0x420, 0x8420, 0x1, 0x4000000,
   0x4000040, 0x4000840, 0x4010840, 0x4000002, 0xc000000, 0xc000080, 0xc001080, 0xc021080,
   0xc000004, 0x1c000000, 0x1c000100, 0x1c002100, 0x1c042100, 0x1c000008, 0x2000000, 0x2000200,
   0x2004200, 0x2084200, 0x2000010]

/-- Rank certificate for the trimmed `L = 6` toric generators
(m = 70, n = 72; emitted by
`scripts/RankCertificateGen.lean`). -/
def rankCert6 : List ℕ :=
  [0x1000000000000000000000000000, 0x41000000000000000000000000000,
   0x1041000000000000000000000000000, 0x41041000000000000000000000000000,
   0x1041041000000000000000000000000000, 0x1000000000000000000, 0x1000000040000000000000000000,
   0x41000001000000000000000000000, 0x1041000040000000000000000000000,
   0x41041001000000000000000000000000, 0x1041041040000000000000000000000000, 0x3000000000000000000,
   0x10000000c0000000000000000000, 0x41000003000000000000000000000,
   0x10410000c0000000000000000000000, 0x41041003000000000000000000000000,
   0x10410410c0000000000000000000000000, 0x7000000000000000000, 0x10000001c0000000000000000000,
   0x41000007000000000000000000000, 0x10410001c0000000000000000000000,
   0x41041007000000000000000000000000, 0x10410411c0000000000000000000000000, 0xf000000000000000000,
   0x10000003c0000000000000000000, 0x4100000f000000000000000000000,
   0x10410003c0000000000000000000000, 0x4104100f000000000000000000000000,
   0x10410413c0000000000000000000000000, 0x1f000000000000000000, 0x10000007c0000000000000000000,
   0x4100001f000000000000000000000, 0x10410007c0000000000000000000000,
   0x4104101f000000000000000000000000, 0x10410417c0000000000000000000000000, 0x40, 0x1040, 0x41040,
   0x1041040, 0x1, 0x2000000000, 0x2000000080, 0x2000002080, 0x2000082080, 0x2002082080,
   0x2000000002, 0x6000000000, 0x6000000100, 0x6000004100, 0x6000104100, 0x6004104100,
   0x6000000004, 0xe000000000, 0xe000000200, 0xe000008200, 0xe000208200, 0xe008208200,
   0xe000000008, 0x1e000000000, 0x1e000000400, 0x1e000010400, 0x1e000410400, 0x1e010410400,
   0x1e000000010, 0x1000000000, 0x1000000800, 0x1000020800, 0x1000820800, 0x1020820800,
   0x1000000020]

/-- The 30 trimmed generators of the `L = 4` toric code are independent. -/
theorem rowsLinearIndependent_generatorsListPackaged_four :
    rowsLinearIndependent (generatorsListPackaged 4) :=
  rowsLinearIndependent_of_rankCertCheck _ rankCert4 (by decide +kernel)

/-- The 48 trimmed generators of the `L = 5` toric code are independent. -/
theorem rowsLinearIndependent_generatorsListPackaged_five :
    rowsLinearIndependent (generatorsListPackaged 5) :=
  rowsLinearIndependent_of_rankCertCheck _ rankCert5 (by decide +kernel)

/-- The 70 trimmed generators of the `L = 6` toric code are independent. -/
theorem rowsLinearIndependent_generatorsListPackaged_six :
    rowsLinearIndependent (generatorsListPackaged 6) :=
  rowsLinearIndependent_of_rankCertCheck _ rankCert6 (by decide +kernel)

end ToricCodeN
end StabilizerGroup
end Quantum
