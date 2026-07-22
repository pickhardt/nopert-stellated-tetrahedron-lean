import RupertStellatedTetrahedron.CriticalDisk.AngleBounds
import RupertStellatedTetrahedron.Stellated.Vertices

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

open DepthCylinderTheorem

/-!
## Critical-disk exclusion statement

This module gives Lemma 6' a concrete Lean target while keeping the certificate-dependent
geometric facts as hypotheses in later modules.
-/

/-- Data of a candidate passage in one critical disk. -/
structure CriticalDiskCandidate where
  R₁ : Matrix.specialOrthogonalGroup (Fin 3) ℝ
  R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ
  t : V2
  /-- Distance of the outer direction from the critical direction. -/
  delta : ℝ
  /-- Relative rotation angle, or an upper-bound proxy for it. -/
  relAngle : ℝ
  /-- Normalized blow-up coordinates used by the zone split. -/
  point : CriticalDiskPoint

def CriticalDiskCandidate.config (cand : CriticalDiskCandidate) :
    Config stellatedVertices where
  R₁ := cand.R₁
  R₂ := cand.R₂
  t := cand.t

/-- The analytic side conditions of Lemma 6'. -/
structure CriticalDiskHypotheses (cand : CriticalDiskCandidate) : Prop where
  delta_pos : 0 < cand.delta
  delta_le_rho0 : ∀ rhoF rhoB : ℝ,
    cand.delta ≤ criticalDiskRho0 rhoF rhoB
  angle_pos : 0 < cand.relAngle
  angle_le_sigma0 : cand.relAngle ≤ criticalDiskSigma0

theorem CriticalDiskHypotheses.delta_le_rhoCap
    {cand : CriticalDiskCandidate}
    (hcand : CriticalDiskHypotheses cand) (rhoF rhoB : ℝ) :
    cand.delta ≤ criticalDiskRhoCap :=
  le_trans (hcand.delta_le_rho0 rhoF rhoB) (criticalDiskRho0_le_cap rhoF rhoB)

theorem CriticalDiskHypotheses.delta_le_rhoF
    {cand : CriticalDiskCandidate}
    (hcand : CriticalDiskHypotheses cand) (rhoF rhoB : ℝ) :
    cand.delta ≤ rhoF :=
  le_trans (hcand.delta_le_rho0 rhoF rhoB) (criticalDiskRho0_le_rhoF rhoF rhoB)

theorem CriticalDiskHypotheses.delta_le_rhoB
    {cand : CriticalDiskCandidate}
    (hcand : CriticalDiskHypotheses cand) (rhoF rhoB : ℝ) :
    cand.delta ≤ rhoB :=
  le_trans (hcand.delta_le_rho0 rhoF rhoB) (criticalDiskRho0_le_rhoB rhoF rhoB)

theorem CriticalDiskHypotheses.delta_le_sigma0
    {cand : CriticalDiskCandidate}
    (hcand : CriticalDiskHypotheses cand) (rhoF rhoB : ℝ) :
    cand.delta ≤ criticalDiskSigma0 :=
  le_trans (hcand.delta_le_rho0 rhoF rhoB) (criticalDiskRho0_le_sigma0 rhoF rhoB)

theorem CriticalDiskHypotheses.rho0_pos
    {cand : CriticalDiskCandidate}
    (hcand : CriticalDiskHypotheses cand) (rhoF rhoB : ℝ) :
    0 < criticalDiskRho0 rhoF rhoB :=
  lt_of_lt_of_le hcand.delta_pos (hcand.delta_le_rho0 rhoF rhoB)

/-- The concrete exclusion conclusion for the stellated tetrahedron in a critical disk. -/
def CriticalDiskExclusion (cand : CriticalDiskCandidate) : Prop :=
  ¬ RupertContainment stellatedVertices cand.config

/-- Named form of conditional Lemma 6' for one candidate. -/
def CriticalDiskLemma6PrimeStatement (cand : CriticalDiskCandidate) : Prop :=
  CriticalDiskHypotheses cand → CriticalDiskExclusion cand

theorem criticalDisk_exclusion_of_not_containment (cand : CriticalDiskCandidate)
    (h : ¬ RupertContainment stellatedVertices cand.config) :
    CriticalDiskExclusion cand := h

theorem criticalDisk_lemma6prime_of_exclusion (cand : CriticalDiskCandidate)
    (h : CriticalDiskExclusion cand) :
    CriticalDiskLemma6PrimeStatement cand := by
  intro _hcand
  exact h

end RupertStellatedTetrahedron
