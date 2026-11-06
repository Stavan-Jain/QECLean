/-
GENERATED FILE — DO NOT HAND-EDIT
Generator: qec-lab:experiments/bb_lab/scripts/mitten_kernel/generate_sweeps.py
Data source: QEC/Stabilizer/Codes/Mitten/M150/FloorData.lean
Regenerate: python3 experiments/bb_lab/scripts/mitten_kernel/generate_sweeps.py
  --root /path/to/QECLean --all --force
  --splits-per-module 16
All candidate coverage and packed computations are checked by Lean's kernel.
-/

import QEC.Stabilizer.Codes.Mitten.M150.FloorData
import QEC.Stabilizer.Codes.Mitten.M150.PackedClassification

namespace Quantum.Stabilizer.Homological.LP.M150
open PackedDigits F2Mask
-- Synchronous certificate elaboration bounds live proof state.
set_option Elab.async false
set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def X0M0LeftColumns : List (Nat × Nat) := [
  (0, 470161665),
  (1, 338198698),
  (2, 545669413),
  (3, 554467355),
  (4, 18884018),
  (5, 642009376),
  (6, 143674437),
  (7, 18877085),
  (8, 325059880),
  (9, 615962),
  (10, 336743457),
  (11, 689969159),
  (12, 705892420),
  (13, 172750),
  (14, 335627658),
  (15, 22643344),
  (16, 43189540),
  (17, 537266270),
  (18, 851712064),
  (19, 11055312),
  (20, 5333424),
  (21, 123773448),
  (22, 448873536),
  (23, 8526545),
  (24, 153891330),
  (25, 106456576),
  (26, 1011945728),
  (27, 143045124),
  (28, 387547168),
  (29, 682393665)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M0Left_columns_bound. -/
theorem X0M0Left_columns_bound : ∀ p ∈ X0M0LeftColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M0Left_eq. -/
theorem X0M0Left_eq : ∀ x < 2 ^ 30, reconX X0M0LeftColumns x = sweepLeft m4TX0 0 x := by
  apply sweepLeft_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M0Left_bound. -/
theorem X0M0Left_bound : ∀ x < 2 ^ 30, sweepLeft m4TX0 0 x < 2 ^ 30 := by
  intro x hx
  rw [← X0M0Left_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (X0M0Left_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def X0M0RightColumns : List (Nat × Nat) := [
  (0, 19424040),
  (1, 340985889),
  (2, 18400394),
  (3, 370215173),
  (4, 113378596),
  (5, 679741530),
  (6, 53551256),
  (7, 306332004),
  (8, 545525963),
  (9, 478233696),
  (10, 671226513),
  (11, 18917154),
  (12, 306717322),
  (13, 345003328),
  (14, 134494357),
  (15, 676402464),
  (16, 545696260),
  (17, 2737178),
  (18, 352887184),
  (19, 169169184),
  (20, 537797189),
  (21, 642075648),
  (22, 145393729),
  (23, 24183442),
  (24, 844383233),
  (25, 25729093),
  (26, 698486790),
  (27, 104899098),
  (28, 153489484),
  (29, 338199216)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M0Right_columns_bound. -/
theorem X0M0Right_columns_bound : ∀ p ∈ X0M0RightColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M0Right_eq. -/
theorem X0M0Right_eq : ∀ x < 2 ^ 30, reconX X0M0RightColumns x = sweepRight m4TX0 0 x := by
  apply sweepRight_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M0Right_bound. -/
theorem X0M0Right_bound : ∀ x < 2 ^ 30, sweepRight m4TX0 0 x < 2 ^ 30 := by
  intro x hx
  rw [← X0M0Right_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (X0M0Right_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M0_ann_bound. -/
theorem X0M0_ann_bound : ∀ a ∈ sweepAnn m4TX0 0, a < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def X0M1LeftColumns : List (Nat × Nat) := [
  (0, 945677631),
  (1, 262886727),
  (2, 662261717),
  (3, 200707565),
  (4, 970281086),
  (5, 915059389),
  (6, 391379566),
  (7, 1050899663),
  (8, 490929115),
  (9, 777265113),
  (10, 430747620),
  (11, 578641816),
  (12, 385783288),
  (13, 954022390),
  (14, 616494012),
  (15, 906492581),
  (16, 690746699),
  (17, 391637635),
  (18, 530937763),
  (19, 793673553),
  (20, 196931299),
  (21, 285125989),
  (22, 570251422),
  (23, 385524029),
  (24, 899668525),
  (25, 993768479),
  (26, 257305307),
  (27, 531122150),
  (28, 871173086),
  (29, 957478266)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M1Left_columns_bound. -/
theorem X0M1Left_columns_bound : ∀ p ∈ X0M1LeftColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M1Left_eq. -/
theorem X0M1Left_eq : ∀ x < 2 ^ 30, reconX X0M1LeftColumns x = sweepLeft m4TX0 1 x := by
  apply sweepLeft_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M1Left_bound. -/
theorem X0M1Left_bound : ∀ x < 2 ^ 30, sweepLeft m4TX0 1 x < 2 ^ 30 := by
  intro x hx
  rw [← X0M1Left_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (X0M1Left_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def X0M1RightColumns : List (Nat × Nat) := [
  (0, 117093564),
  (1, 449180853),
  (2, 531441378),
  (3, 777674704),
  (4, 1014835013),
  (5, 165600908),
  (6, 961131835),
  (7, 932706848),
  (8, 707523671),
  (9, 659151207),
  (10, 800563401),
  (11, 457950166),
  (12, 627920796),
  (13, 452889897),
  (14, 838670934),
  (15, 360078460),
  (16, 988297391),
  (17, 904983384),
  (18, 89385707),
  (19, 1067664775),
  (20, 256285531),
  (21, 110565355),
  (22, 1024339414),
  (23, 238869418),
  (24, 953248126),
  (25, 883348157),
  (26, 562789241),
  (27, 859235507),
  (28, 146059239),
  (29, 314126111)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M1Right_columns_bound. -/
theorem X0M1Right_columns_bound : ∀ p ∈ X0M1RightColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M1Right_eq. -/
theorem X0M1Right_eq : ∀ x < 2 ^ 30, reconX X0M1RightColumns x = sweepRight m4TX0 1 x := by
  apply sweepRight_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M1Right_bound. -/
theorem X0M1Right_bound : ∀ x < 2 ^ 30, sweepRight m4TX0 1 x < 2 ^ 30 := by
  intro x hx
  rw [← X0M1Right_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (X0M1Right_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M1_ann_bound. -/
theorem X0M1_ann_bound : ∀ a ∈ sweepAnn m4TX0 1, a < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def X0M2LeftColumns : List (Nat × Nat) := [
  (0, 181022646),
  (1, 424721310),
  (2, 11091190),
  (3, 408872141),
  (4, 453785982),
  (5, 168886173),
  (6, 196510044),
  (7, 297460259),
  (8, 443784881),
  (9, 155270016),
  (10, 22120413),
  (11, 293513890),
  (12, 49233554),
  (13, 39861072),
  (14, 35505134),
  (15, 426523310),
  (16, 181729917),
  (17, 166075044),
  (18, 442213346),
  (19, 414964403),
  (20, 408026513),
  (21, 405569405),
  (22, 138233123),
  (23, 410828963),
  (24, 412664335),
  (25, 310708204),
  (26, 272572686),
  (27, 332022271),
  (28, 325123201),
  (29, 333236323)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M2Left_columns_bound. -/
theorem X0M2Left_columns_bound : ∀ p ∈ X0M2LeftColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M2Left_eq. -/
theorem X0M2Left_eq : ∀ x < 2 ^ 30, reconX X0M2LeftColumns x = sweepLeft m4TX0 2 x := by
  apply sweepLeft_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M2Left_bound. -/
theorem X0M2Left_bound : ∀ x < 2 ^ 30, sweepLeft m4TX0 2 x < 2 ^ 30 := by
  intro x hx
  rw [← X0M2Left_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (X0M2Left_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def X0M2RightColumns : List (Nat × Nat) := [
  (0, 420356382),
  (1, 27656045),
  (2, 317073088),
  (3, 36829916),
  (4, 176579521),
  (5, 50046734),
  (6, 272415154),
  (7, 425704322),
  (8, 48006698),
  (9, 14130268),
  (10, 324847715),
  (11, 446421603),
  (12, 183949661),
  (13, 320112113),
  (14, 414549344),
  (15, 158536496),
  (16, 461839788),
  (17, 174147331),
  (18, 146112801),
  (19, 419462733),
  (20, 305019226),
  (21, 468065452),
  (22, 195625168),
  (23, 11248894),
  (24, 294142939),
  (25, 326624413),
  (26, 170809107),
  (27, 46677906),
  (28, 292364862),
  (29, 323181999)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M2Right_columns_bound. -/
theorem X0M2Right_columns_bound : ∀ p ∈ X0M2RightColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M2Right_eq. -/
theorem X0M2Right_eq : ∀ x < 2 ^ 30, reconX X0M2RightColumns x = sweepRight m4TX0 2 x := by
  apply sweepRight_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M2Right_bound. -/
theorem X0M2Right_bound : ∀ x < 2 ^ 30, sweepRight m4TX0 2 x < 2 ^ 30 := by
  intro x hx
  rw [← X0M2Right_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (X0M2Right_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X0M2_ann_bound. -/
theorem X0M2_ann_bound : ∀ a ∈ sweepAnn m4TX0 2, a < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def X1M0LeftColumns : List (Nat × Nat) := [
  (0, 470161665),
  (1, 338198698),
  (2, 545669413),
  (3, 554467355),
  (4, 18884018),
  (5, 642009376),
  (6, 143674437),
  (7, 18877085),
  (8, 325059880),
  (9, 615962),
  (10, 336743457),
  (11, 689969159),
  (12, 705892420),
  (13, 172750),
  (14, 335627658),
  (15, 22643344),
  (16, 43189540),
  (17, 537266270),
  (18, 851712064),
  (19, 11055312),
  (20, 5333424),
  (21, 123773448),
  (22, 448873536),
  (23, 8526545),
  (24, 153891330),
  (25, 106456576),
  (26, 1011945728),
  (27, 143045124),
  (28, 387547168),
  (29, 682393665)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M0Left_columns_bound. -/
theorem X1M0Left_columns_bound : ∀ p ∈ X1M0LeftColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M0Left_eq. -/
theorem X1M0Left_eq : ∀ x < 2 ^ 30, reconX X1M0LeftColumns x = sweepLeft m4TX1 0 x := by
  apply sweepLeft_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M0Left_bound. -/
theorem X1M0Left_bound : ∀ x < 2 ^ 30, sweepLeft m4TX1 0 x < 2 ^ 30 := by
  intro x hx
  rw [← X1M0Left_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (X1M0Left_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def X1M0RightColumns : List (Nat × Nat) := [
  (0, 545263681),
  (1, 52002818),
  (2, 134486020),
  (3, 7962632),
  (4, 325058584),
  (5, 306717216),
  (6, 537264193),
  (7, 123732098),
  (8, 104899328),
  (9, 335545226),
  (10, 352879872),
  (11, 142870592),
  (12, 8394757),
  (13, 335552570),
  (14, 338214944),
  (15, 57776),
  (16, 18956584),
  (17, 671223809),
  (18, 134611012),
  (19, 526256),
  (20, 19924258),
  (21, 3696128),
  (22, 5260426),
  (23, 545523716),
  (24, 16901632),
  (25, 33637402),
  (26, 101785744),
  (27, 134350913),
  (28, 273744528),
  (29, 545394692)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M0Right_columns_bound. -/
theorem X1M0Right_columns_bound : ∀ p ∈ X1M0RightColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M0Right_eq. -/
theorem X1M0Right_eq : ∀ x < 2 ^ 30, reconX X1M0RightColumns x = sweepRight m4TX1 0 x := by
  apply sweepRight_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M0Right_bound. -/
theorem X1M0Right_bound : ∀ x < 2 ^ 30, sweepRight m4TX1 0 x < 2 ^ 30 := by
  intro x hx
  rw [← X1M0Right_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (X1M0Right_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M0_ann_bound. -/
theorem X1M0_ann_bound : ∀ a ∈ sweepAnn m4TX1 0, a < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def X1M1LeftColumns : List (Nat × Nat) := [
  (0, 170264855),
  (1, 308348680),
  (2, 813843031),
  (3, 628259121),
  (4, 339853698),
  (5, 487410207),
  (6, 143694676),
  (7, 111037998),
  (8, 272146594),
  (9, 74473776),
  (10, 559055869),
  (11, 805492999),
  (12, 707187264),
  (13, 462652657),
  (14, 52962578),
  (15, 102254114),
  (16, 111214284),
  (17, 11946324),
  (18, 817141763),
  (19, 987838220),
  (20, 285819418),
  (21, 319915056),
  (22, 406827234),
  (23, 177361475),
  (24, 1011730882),
  (25, 22053784),
  (26, 602682643),
  (27, 982814740),
  (28, 102818440),
  (29, 975440705)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M1Left_columns_bound. -/
theorem X1M1Left_columns_bound : ∀ p ∈ X1M1LeftColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M1Left_eq. -/
theorem X1M1Left_eq : ∀ x < 2 ^ 30, reconX X1M1LeftColumns x = sweepLeft m4TX1 1 x := by
  apply sweepLeft_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M1Left_bound. -/
theorem X1M1Left_bound : ∀ x < 2 ^ 30, sweepLeft m4TX1 1 x < 2 ^ 30 := by
  intro x hx
  rw [← X1M1Left_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (X1M1Left_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def X1M1RightColumns : List (Nat × Nat) := [
  (0, 679608384),
  (1, 123789858),
  (2, 679483392),
  (3, 325592840),
  (4, 339248186),
  (5, 343507106),
  (6, 671483904),
  (7, 352960906),
  (8, 387547416),
  (9, 52496306),
  (10, 123741490),
  (11, 8654916),
  (12, 545392641),
  (13, 24142264),
  (14, 325075880),
  (15, 272754202),
  (16, 336152122),
  (17, 134484033),
  (18, 142739460),
  (19, 102262410),
  (20, 336651658),
  (21, 75072400),
  (22, 22120368),
  (23, 537137157),
  (24, 320446640),
  (25, 37314992),
  (26, 107079176),
  (27, 264261),
  (28, 324560386),
  (29, 135237)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M1Right_columns_bound. -/
theorem X1M1Right_columns_bound : ∀ p ∈ X1M1RightColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M1Right_eq. -/
theorem X1M1Right_eq : ∀ x < 2 ^ 30, reconX X1M1RightColumns x = sweepRight m4TX1 1 x := by
  apply sweepRight_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M1Right_bound. -/
theorem X1M1Right_bound : ∀ x < 2 ^ 30, sweepRight m4TX1 1 x < 2 ^ 30 := by
  intro x hx
  rw [← X1M1Right_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (X1M1Right_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M1_ann_bound. -/
theorem X1M1_ann_bound : ∀ a ∈ sweepAnn m4TX1 1, a < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def X1M2LeftColumns : List (Nat × Nat) := [
  (0, 181022646),
  (1, 424721310),
  (2, 11091190),
  (3, 408872141),
  (4, 453785982),
  (5, 168886173),
  (6, 196510044),
  (7, 297460259),
  (8, 443784881),
  (9, 155270016),
  (10, 22120413),
  (11, 293513890),
  (12, 49233554),
  (13, 39861072),
  (14, 35505134),
  (15, 426523310),
  (16, 181729917),
  (17, 166075044),
  (18, 442213346),
  (19, 414964403),
  (20, 408026513),
  (21, 405569405),
  (22, 138233123),
  (23, 410828963),
  (24, 412664335),
  (25, 310708204),
  (26, 272572686),
  (27, 332022271),
  (28, 325123201),
  (29, 333236323)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M2Left_columns_bound. -/
theorem X1M2Left_columns_bound : ∀ p ∈ X1M2LeftColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M2Left_eq. -/
theorem X1M2Left_eq : ∀ x < 2 ^ 30, reconX X1M2LeftColumns x = sweepLeft m4TX1 2 x := by
  apply sweepLeft_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M2Left_bound. -/
theorem X1M2Left_bound : ∀ x < 2 ^ 30, sweepLeft m4TX1 2 x < 2 ^ 30 := by
  intro x hx
  rw [← X1M2Left_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (X1M2Left_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def X1M2RightColumns : List (Nat × Nat) := [
  (0, 137599160),
  (1, 2070924),
  (2, 447302363),
  (3, 454900066),
  (4, 171892367),
  (5, 273849264),
  (6, 18735055),
  (7, 47810318),
  (8, 45729550),
  (9, 14271950),
  (10, 20113137),
  (11, 186976576),
  (12, 26101715),
  (13, 288194415),
  (14, 313097884),
  (15, 63207521),
  (16, 4194560),
  (17, 30769692),
  (18, 191382803),
  (19, 176086175),
  (20, 277290380),
  (21, 279649468),
  (22, 60047857),
  (23, 2899318),
  (24, 55395903),
  (25, 18866063),
  (26, 417972483),
  (27, 170811155),
  (28, 170876563),
  (29, 4096)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M2Right_columns_bound. -/
theorem X1M2Right_columns_bound : ∀ p ∈ X1M2RightColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M2Right_eq. -/
theorem X1M2Right_eq : ∀ x < 2 ^ 30, reconX X1M2RightColumns x = sweepRight m4TX1 2 x := by
  apply sweepRight_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M2Right_bound. -/
theorem X1M2Right_bound : ∀ x < 2 ^ 30, sweepRight m4TX1 2 x < 2 ^ 30 := by
  intro x hx
  rw [← X1M2Right_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (X1M2Right_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for X1M2_ann_bound. -/
theorem X1M2_ann_bound : ∀ a ∈ sweepAnn m4TX1 2, a < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def Z0M0LeftColumns : List (Nat × Nat) := [
  (0, 358646690),
  (1, 621550665),
  (2, 69264698),
  (3, 950323203),
  (4, 17242285),
  (5, 842404099),
  (6, 3753650),
  (7, 674367767),
  (8, 759498796),
  (9, 12985549),
  (10, 310659351),
  (11, 388505912),
  (12, 55682578),
  (13, 578964054),
  (14, 608308457),
  (15, 210317509),
  (16, 403850069),
  (17, 285755306),
  (18, 376013336),
  (19, 412260944),
  (20, 75709604),
  (21, 692858980),
  (22, 579916612),
  (23, 17950104),
  (24, 715559680),
  (25, 147792992),
  (26, 439670848),
  (27, 41509512),
  (28, 768152577),
  (29, 391684226)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M0Left_columns_bound. -/
theorem Z0M0Left_columns_bound : ∀ p ∈ Z0M0LeftColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M0Left_eq. -/
theorem Z0M0Left_eq : ∀ x < 2 ^ 30, reconX Z0M0LeftColumns x = sweepLeft m4TZ0 0 x := by
  apply sweepLeft_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M0Left_bound. -/
theorem Z0M0Left_bound : ∀ x < 2 ^ 30, sweepLeft m4TZ0 0 x < 2 ^ 30 := by
  intro x hx
  rw [← Z0M0Left_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (Z0M0Left_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def Z0M0RightColumns : List (Nat × Nat) := [
  (0, 612641837),
  (1, 97831349),
  (2, 134941925),
  (3, 303629474),
  (4, 238184045),
  (5, 6334344),
  (6, 566441028),
  (7, 323036432),
  (8, 654986843),
  (9, 848925926),
  (10, 69853314),
  (11, 554109161),
  (12, 214767688),
  (13, 340345608),
  (14, 294886076),
  (15, 459619664),
  (16, 24649778),
  (17, 12729485),
  (18, 759566497),
  (19, 89178528),
  (20, 182888392),
  (21, 877613835),
  (22, 117966362),
  (23, 210706628),
  (24, 103834664),
  (25, 1017770115),
  (26, 285311672),
  (27, 700985441),
  (28, 696002870),
  (29, 755768332)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M0Right_columns_bound. -/
theorem Z0M0Right_columns_bound : ∀ p ∈ Z0M0RightColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M0Right_eq. -/
theorem Z0M0Right_eq : ∀ x < 2 ^ 30, reconX Z0M0RightColumns x = sweepRight m4TZ0 0 x := by
  apply sweepRight_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M0Right_bound. -/
theorem Z0M0Right_bound : ∀ x < 2 ^ 30, sweepRight m4TZ0 0 x < 2 ^ 30 := by
  intro x hx
  rw [← Z0M0Right_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (Z0M0Right_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M0_ann_bound. -/
theorem Z0M0_ann_bound : ∀ a ∈ sweepAnn m4TZ0 0, a < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def Z0M2LeftColumns : List (Nat × Nat) := [
  (0, 844999538),
  (1, 954809165),
  (2, 392879889),
  (3, 261536355),
  (4, 760142278),
  (5, 263312203),
  (6, 364364590),
  (7, 984519741),
  (8, 435764330),
  (9, 632715385),
  (10, 980734142),
  (11, 652059561),
  (12, 183551483),
  (13, 967118791),
  (14, 793712026),
  (15, 178134703),
  (16, 909389779),
  (17, 526970021),
  (18, 1043429014),
  (19, 675543391),
  (20, 902130361),
  (21, 998745301),
  (22, 302775095),
  (23, 893068654),
  (24, 620649172),
  (25, 207269805),
  (26, 301909844),
  (27, 63528442),
  (28, 665576676),
  (29, 492271256)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M2Left_columns_bound. -/
theorem Z0M2Left_columns_bound : ∀ p ∈ Z0M2LeftColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M2Left_eq. -/
theorem Z0M2Left_eq : ∀ x < 2 ^ 30, reconX Z0M2LeftColumns x = sweepLeft m4TZ0 2 x := by
  apply sweepLeft_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M2Left_bound. -/
theorem Z0M2Left_bound : ∀ x < 2 ^ 30, sweepLeft m4TZ0 2 x < 2 ^ 30 := by
  intro x hx
  rw [← Z0M2Left_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (Z0M2Left_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def Z0M2RightColumns : List (Nat × Nat) := [
  (0, 129991599),
  (1, 1045897683),
  (2, 467723519),
  (3, 935418873),
  (4, 919108405),
  (5, 699724921),
  (6, 1010382814),
  (7, 475463596),
  (8, 950894351),
  (9, 488558436),
  (10, 708648591),
  (11, 360361804),
  (12, 592313330),
  (13, 650110433),
  (14, 694143447),
  (15, 598988137),
  (16, 860334295),
  (17, 128700906),
  (18, 360644121),
  (19, 469335079),
  (20, 670202461),
  (21, 452287630),
  (22, 350894941),
  (23, 435451066),
  (24, 1063191902),
  (25, 513710830),
  (26, 227464166),
  (27, 773662619),
  (28, 1000781297),
  (29, 860482229)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M2Right_columns_bound. -/
theorem Z0M2Right_columns_bound : ∀ p ∈ Z0M2RightColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M2Right_eq. -/
theorem Z0M2Right_eq : ∀ x < 2 ^ 30, reconX Z0M2RightColumns x = sweepRight m4TZ0 2 x := by
  apply sweepRight_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M2Right_bound. -/
theorem Z0M2Right_bound : ∀ x < 2 ^ 30, sweepRight m4TZ0 2 x < 2 ^ 30 := by
  intro x hx
  rw [← Z0M2Right_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (Z0M2Right_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M2_ann_bound. -/
theorem Z0M2_ann_bound : ∀ a ∈ sweepAnn m4TZ0 2, a < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def Z0M3LeftColumns : List (Nat × Nat) := [
  (0, 97189296),
  (1, 153295668),
  (2, 102237438),
  (3, 31499661),
  (4, 112105585),
  (5, 50093028),
  (6, 248742737),
  (7, 265109773),
  (8, 103836781),
  (9, 74752902),
  (10, 176620279),
  (11, 52331092),
  (12, 251485032),
  (13, 84839092),
  (14, 204308612),
  (15, 227508901),
  (16, 10386444),
  (17, 227935787),
  (18, 256597487),
  (19, 38176682),
  (20, 82599835),
  (21, 260635222),
  (22, 142287106),
  (23, 252574533),
  (24, 19927589),
  (25, 89432482),
  (26, 165895484),
  (27, 42432738),
  (28, 241903404),
  (29, 115908723)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M3Left_columns_bound. -/
theorem Z0M3Left_columns_bound : ∀ p ∈ Z0M3LeftColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M3Left_eq. -/
theorem Z0M3Left_eq : ∀ x < 2 ^ 30, reconX Z0M3LeftColumns x = sweepLeft m4TZ0 3 x := by
  apply sweepLeft_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M3Left_bound. -/
theorem Z0M3Left_bound : ∀ x < 2 ^ 30, sweepLeft m4TZ0 3 x < 2 ^ 30 := by
  intro x hx
  rw [← Z0M3Left_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (Z0M3Left_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def Z0M3RightColumns : List (Nat × Nat) := [
  (0, 111861875),
  (1, 107636731),
  (2, 204071042),
  (3, 132916697),
  (4, 524290),
  (5, 87482919),
  (6, 257113372),
  (7, 14403342),
  (8, 93388468),
  (9, 48505299),
  (10, 153085609),
  (11, 126417494),
  (12, 244418737),
  (13, 72786438),
  (14, 41739645),
  (15, 161055907),
  (16, 93452982),
  (17, 117966362),
  (18, 37547133),
  (19, 219144871),
  (20, 152027813),
  (21, 88750386),
  (22, 31048878),
  (23, 255268570),
  (24, 126941766),
  (25, 75291573),
  (26, 81151502),
  (27, 20716084),
  (28, 259368306),
  (29, 189121886)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M3Right_columns_bound. -/
theorem Z0M3Right_columns_bound : ∀ p ∈ Z0M3RightColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M3Right_eq. -/
theorem Z0M3Right_eq : ∀ x < 2 ^ 30, reconX Z0M3RightColumns x = sweepRight m4TZ0 3 x := by
  apply sweepRight_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M3Right_bound. -/
theorem Z0M3Right_bound : ∀ x < 2 ^ 30, sweepRight m4TZ0 3 x < 2 ^ 30 := by
  intro x hx
  rw [← Z0M3Right_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (Z0M3Right_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z0M3_ann_bound. -/
theorem Z0M3_ann_bound : ∀ a ∈ sweepAnn m4TZ0 3, a < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def Z1M0LeftColumns : List (Nat × Nat) := [
  (0, 358646690),
  (1, 621550665),
  (2, 69264698),
  (3, 950323203),
  (4, 17242285),
  (5, 842404099),
  (6, 3753650),
  (7, 674367767),
  (8, 759498796),
  (9, 12985549),
  (10, 310659351),
  (11, 388505912),
  (12, 55682578),
  (13, 578964054),
  (14, 608308457),
  (15, 210317509),
  (16, 403850069),
  (17, 285755306),
  (18, 376013336),
  (19, 412260944),
  (20, 75709604),
  (21, 692858980),
  (22, 579916612),
  (23, 17950104),
  (24, 715559680),
  (25, 147792992),
  (26, 439670848),
  (27, 41509512),
  (28, 768152577),
  (29, 391684226)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M0Left_columns_bound. -/
theorem Z1M0Left_columns_bound : ∀ p ∈ Z1M0LeftColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M0Left_eq. -/
theorem Z1M0Left_eq : ∀ x < 2 ^ 30, reconX Z1M0LeftColumns x = sweepLeft m4TZ1 0 x := by
  apply sweepLeft_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M0Left_bound. -/
theorem Z1M0Left_bound : ∀ x < 2 ^ 30, sweepLeft m4TZ1 0 x < 2 ^ 30 := by
  intro x hx
  rw [← Z1M0Left_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (Z1M0Left_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def Z1M0RightColumns : List (Nat × Nat) := [
  (0, 679612416),
  (1, 270108338),
  (2, 679741440),
  (3, 68805016),
  (4, 56731408),
  (5, 54617650),
  (6, 671221761),
  (7, 58221216),
  (8, 40920968),
  (9, 342475274),
  (10, 341411352),
  (11, 134484036),
  (12, 545392644),
  (13, 387490826),
  (14, 370794626),
  (15, 91259314),
  (16, 123831200),
  (17, 537137217),
  (18, 142739520),
  (19, 321454520),
  (20, 326639920),
  (21, 102786618),
  (22, 341894186),
  (23, 268293),
  (24, 289433482),
  (25, 386418442),
  (26, 70845874),
  (27, 393285),
  (28, 286376376),
  (29, 8392773)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M0Right_columns_bound. -/
theorem Z1M0Right_columns_bound : ∀ p ∈ Z1M0RightColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M0Right_eq. -/
theorem Z1M0Right_eq : ∀ x < 2 ^ 30, reconX Z1M0RightColumns x = sweepRight m4TZ1 0 x := by
  apply sweepRight_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M0Right_bound. -/
theorem Z1M0Right_bound : ∀ x < 2 ^ 30, sweepRight m4TZ1 0 x < 2 ^ 30 := by
  intro x hx
  rw [← Z1M0Right_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (Z1M0Right_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M0_ann_bound. -/
theorem Z1M0_ann_bound : ∀ a ∈ sweepAnn m4TZ1 0, a < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def Z1M2LeftColumns : List (Nat × Nat) := [
  (0, 844999538),
  (1, 954809165),
  (2, 392879889),
  (3, 261536355),
  (4, 760142278),
  (5, 263312203),
  (6, 364364590),
  (7, 984519741),
  (8, 435764330),
  (9, 632715385),
  (10, 980734142),
  (11, 652059561),
  (12, 183551483),
  (13, 967118791),
  (14, 793712026),
  (15, 178134703),
  (16, 909389779),
  (17, 526970021),
  (18, 1043429014),
  (19, 675543391),
  (20, 902130361),
  (21, 998745301),
  (22, 302775095),
  (23, 893068654),
  (24, 620649172),
  (25, 207269805),
  (26, 301909844),
  (27, 63528442),
  (28, 665576676),
  (29, 492271256)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M2Left_columns_bound. -/
theorem Z1M2Left_columns_bound : ∀ p ∈ Z1M2LeftColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M2Left_eq. -/
theorem Z1M2Left_eq : ∀ x < 2 ^ 30, reconX Z1M2LeftColumns x = sweepLeft m4TZ1 2 x := by
  apply sweepLeft_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M2Left_bound. -/
theorem Z1M2Left_bound : ∀ x < 2 ^ 30, sweepLeft m4TZ1 2 x < 2 ^ 30 := by
  intro x hx
  rw [← Z1M2Left_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (Z1M2Left_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def Z1M2RightColumns : List (Nat × Nat) := [
  (0, 1044195154),
  (1, 972901188),
  (2, 860478259),
  (3, 666350689),
  (4, 793958731),
  (5, 530948807),
  (6, 360107804),
  (7, 451746863),
  (8, 905591384),
  (9, 917919932),
  (10, 946385279),
  (11, 903213736),
  (12, 112444395),
  (13, 1028064727),
  (14, 261004202),
  (15, 446050275),
  (16, 623665110),
  (17, 243051945),
  (18, 451998902),
  (19, 616659837),
  (20, 967238841),
  (21, 982250773),
  (22, 18348667),
  (23, 925590695),
  (24, 207544036),
  (25, 683224975),
  (26, 50239133),
  (27, 299445630),
  (28, 726395094),
  (29, 256595928)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M2Right_columns_bound. -/
theorem Z1M2Right_columns_bound : ∀ p ∈ Z1M2RightColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M2Right_eq. -/
theorem Z1M2Right_eq : ∀ x < 2 ^ 30, reconX Z1M2RightColumns x = sweepRight m4TZ1 2 x := by
  apply sweepRight_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M2Right_bound. -/
theorem Z1M2Right_bound : ∀ x < 2 ^ 30, sweepRight m4TZ1 2 x < 2 ^ 30 := by
  intro x hx
  rw [← Z1M2Right_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (Z1M2Right_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M2_ann_bound. -/
theorem Z1M2_ann_bound : ∀ a ∈ sweepAnn m4TZ1 2, a < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def Z1M3LeftColumns : List (Nat × Nat) := [
  (0, 55592202),
  (1, 209852708),
  (2, 370229400),
  (3, 402788709),
  (4, 679887968),
  (5, 537430675),
  (6, 307241888),
  (7, 545543492),
  (8, 829593),
  (9, 680598529),
  (10, 19048980),
  (11, 39928874),
  (12, 369681664),
  (13, 135616577),
  (14, 19538565),
  (15, 709298180),
  (16, 11174474),
  (17, 340853906),
  (18, 288964896),
  (19, 576065541),
  (20, 25731150),
  (21, 885131329),
  (22, 161517714),
  (23, 104932144),
  (24, 377751621),
  (25, 153620696),
  (26, 673456666),
  (27, 340313632),
  (28, 553923210),
  (29, 87131424)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M3Left_columns_bound. -/
theorem Z1M3Left_columns_bound : ∀ p ∈ Z1M3LeftColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M3Left_eq. -/
theorem Z1M3Left_eq : ∀ x < 2 ^ 30, reconX Z1M3LeftColumns x = sweepLeft m4TZ1 3 x := by
  apply sweepLeft_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M3Left_bound. -/
theorem Z1M3Left_bound : ∀ x < 2 ^ 30, sweepLeft m4TZ1 3 x < 2 ^ 30 := by
  intro x hx
  rw [← Z1M3Left_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (Z1M3Left_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Columns of the split reconstruction map. -/
def Z1M3RightColumns : List (Nat × Nat) := [
  (0, 134352961),
  (1, 38806146),
  (2, 545525764),
  (3, 37823000),
  (4, 369664016),
  (5, 1695776),
  (6, 134481985),
  (7, 340296320),
  (8, 1672960),
  (9, 287834912),
  (10, 58196992),
  (11, 142612484),
  (12, 537006085),
  (13, 86024480),
  (14, 56737792),
  (15, 16827658),
  (16, 385941514),
  (17, 671481920),
  (18, 8652868),
  (19, 2638890),
  (20, 342884362),
  (21, 3227800),
  (22, 272630200),
  (23, 545265665),
  (24, 17892498),
  (25, 100663730),
  (26, 67135360),
  (27, 134612996),
  (28, 268461616),
  (29, 545390657)
]

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M3Right_columns_bound. -/
theorem Z1M3Right_columns_bound : ∀ p ∈ Z1M3RightColumns, p.1 < 32 ∧ p.2 < 2 ^ 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M3Right_eq. -/
theorem Z1M3Right_eq : ∀ x < 2 ^ 30, reconX Z1M3RightColumns x = sweepRight m4TZ1 3 x := by
  apply sweepRight_eq_recon
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M3Right_bound. -/
theorem Z1M3Right_bound : ∀ x < 2 ^ 30, sweepRight m4TZ1 3 x < 2 ^ 30 := by
  intro x hx
  rw [← Z1M3Right_eq x hx]
  exact reconX_lt _ _ _ (fun p hp => (Z1M3Right_columns_bound p hp).2)

set_option maxHeartbeats 0 in
-- Elaborating this generated certificate can exceed the default
-- heartbeat budget.
/-- Kernel-checked certificate for Z1M3_ann_bound. -/
theorem Z1M3_ann_bound : ∀ a ∈ sweepAnn m4TZ1 3, a < 2 ^ 30 := by
  decide +kernel

end Quantum.Stabilizer.Homological.LP.M150
