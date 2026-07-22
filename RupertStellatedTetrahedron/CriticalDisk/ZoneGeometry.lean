import RupertStellatedTetrahedron.CriticalDisk.Constants

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

/-!
## Abstract critical-disk zone geometry

This file formalizes the bookkeeping split used in the conditional Lemma 6' assembly.  The
coordinates are normalized blow-up quantities; the actual maps from rotations/translations into
these quantities are supplied by the analytic part of the proof.
-/

/-- Normalized coordinates used by the critical-disk pentachotomy. -/
structure CriticalDiskPoint where
  /-- Distance to the normalized first-order feasible set `D_hat(phi)`. -/
  distToD : ℝ
  /-- Planar distance to the diagonal corner. -/
  piNorm : ℝ
  /-- Planar distance to the reflection-sheet corner. -/
  piSheetDist : ℝ
  /-- Norm of the normalized spin/translation block. -/
  transverseNorm : ℝ
  /-- Full normalized size. -/
  totalNorm : ℝ

/-- Zone 0: large normalized size, handled by frozen `u*` epsilon-slack. -/
def CriticalDiskZone0 (x : CriticalDiskPoint) : Prop :=
  criticalDiskXD + criticalDiskNu < x.totalNorm

/-- Zone A: near the Zone-0 size range but away from the first-order feasible set. -/
def CriticalDiskZoneA (x : CriticalDiskPoint) : Prop :=
  ¬ CriticalDiskZone0 x ∧ criticalDiskNu ≤ x.distToD

/-- Zone B: near `D_hat(phi)` and inside the diagonal-corner ball. -/
def CriticalDiskZoneB (x : CriticalDiskPoint) : Prop :=
  ¬ CriticalDiskZone0 x ∧ x.distToD < criticalDiskNu ∧ x.piNorm ≤ criticalDiskRb

/-- Zone C: near `D_hat(phi)` and inside the reflection-sheet corner ball. -/
def CriticalDiskZoneC (x : CriticalDiskPoint) : Prop :=
  ¬ CriticalDiskZone0 x ∧ x.distToD < criticalDiskNu ∧
    criticalDiskRb < x.piNorm ∧ x.piSheetDist ≤ criticalDiskRb

/-- Zone D: near `D_hat(phi)` but outside both corner balls. -/
def CriticalDiskZoneD (x : CriticalDiskPoint) : Prop :=
  ¬ CriticalDiskZone0 x ∧ x.distToD < criticalDiskNu ∧
    criticalDiskRb < x.piNorm ∧ criticalDiskRb < x.piSheetDist

theorem CriticalDiskZoneA.notZone0 {x : CriticalDiskPoint}
    (h : CriticalDiskZoneA x) : ¬ CriticalDiskZone0 x :=
  h.1

theorem CriticalDiskZoneA.dist_ge {x : CriticalDiskPoint}
    (h : CriticalDiskZoneA x) : criticalDiskNu ≤ x.distToD :=
  h.2

theorem CriticalDiskZoneB.notZone0 {x : CriticalDiskPoint}
    (h : CriticalDiskZoneB x) : ¬ CriticalDiskZone0 x :=
  h.1

theorem CriticalDiskZoneB.dist_lt {x : CriticalDiskPoint}
    (h : CriticalDiskZoneB x) : x.distToD < criticalDiskNu :=
  h.2.1

theorem CriticalDiskZoneB.piNorm_le {x : CriticalDiskPoint}
    (h : CriticalDiskZoneB x) : x.piNorm ≤ criticalDiskRb :=
  h.2.2

theorem CriticalDiskZoneC.notZone0 {x : CriticalDiskPoint}
    (h : CriticalDiskZoneC x) : ¬ CriticalDiskZone0 x :=
  h.1

theorem CriticalDiskZoneC.dist_lt {x : CriticalDiskPoint}
    (h : CriticalDiskZoneC x) : x.distToD < criticalDiskNu :=
  h.2.1

theorem CriticalDiskZoneC.piNorm_gt {x : CriticalDiskPoint}
    (h : CriticalDiskZoneC x) : criticalDiskRb < x.piNorm :=
  h.2.2.1

theorem CriticalDiskZoneC.piSheetDist_le {x : CriticalDiskPoint}
    (h : CriticalDiskZoneC x) : x.piSheetDist ≤ criticalDiskRb :=
  h.2.2.2

theorem CriticalDiskZoneD.notZone0 {x : CriticalDiskPoint}
    (h : CriticalDiskZoneD x) : ¬ CriticalDiskZone0 x :=
  h.1

theorem CriticalDiskZoneD.dist_lt {x : CriticalDiskPoint}
    (h : CriticalDiskZoneD x) : x.distToD < criticalDiskNu :=
  h.2.1

theorem CriticalDiskZoneD.piNorm_gt {x : CriticalDiskPoint}
    (h : CriticalDiskZoneD x) : criticalDiskRb < x.piNorm :=
  h.2.2.1

theorem CriticalDiskZoneD.piSheetDist_gt {x : CriticalDiskPoint}
    (h : CriticalDiskZoneD x) : criticalDiskRb < x.piSheetDist :=
  h.2.2.2

/-- The normalized critical disk is covered by the five assembly zones. -/
theorem criticalDisk_zone_pentachotomy (x : CriticalDiskPoint) :
    CriticalDiskZone0 x ∨ CriticalDiskZoneA x ∨ CriticalDiskZoneB x ∨
      CriticalDiskZoneC x ∨ CriticalDiskZoneD x := by
  by_cases h0 : CriticalDiskZone0 x
  · exact Or.inl h0
  · right
    by_cases hdist : criticalDiskNu ≤ x.distToD
    · exact Or.inl ⟨h0, hdist⟩
    · right
      have hdist_lt : x.distToD < criticalDiskNu := lt_of_not_ge hdist
      by_cases hpi : x.piNorm ≤ criticalDiskRb
      · exact Or.inl ⟨h0, hdist_lt, hpi⟩
      · right
        have hpi_lt : criticalDiskRb < x.piNorm := lt_of_not_ge hpi
        by_cases hsheet : x.piSheetDist ≤ criticalDiskRb
        · exact Or.inl ⟨h0, hdist_lt, hpi_lt, hsheet⟩
        · right
          exact ⟨h0, hdist_lt, hpi_lt, lt_of_not_ge hsheet⟩

end RupertStellatedTetrahedron
