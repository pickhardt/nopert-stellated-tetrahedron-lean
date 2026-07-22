import RupertStellatedTetrahedron.CriticalDisk.Statement
import RupertStellatedTetrahedron.Stellated.MarginalReduction

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

/-!
## Critical-disk transport along marginal sheets

The marginal-reduction theorem identifies the strict-containment system after replacing the inner
rotation by `N R₁ m`, for any improper symmetry `m` of the stellated vertex set.  This module
packages that algebra at the `CriticalDiskCandidate` level.
-/

def CriticalDiskCandidate.iotaInner
    (cand : CriticalDiskCandidate)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskCandidate :=
  { cand with R₁ := S.iota cand.R₁ }

theorem criticalDiskHypotheses_iotaInner_iff
    (cand : CriticalDiskCandidate)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskHypotheses (cand.iotaInner S) ↔ CriticalDiskHypotheses cand := by
  constructor
  · intro h
    exact
      { delta_pos := h.delta_pos
        delta_le_rho0 := h.delta_le_rho0
        angle_pos := h.angle_pos
        angle_le_sigma0 := h.angle_le_sigma0 }
  · intro h
    exact
      { delta_pos := h.delta_pos
        delta_le_rho0 := h.delta_le_rho0
        angle_pos := h.angle_pos
        angle_le_sigma0 := h.angle_le_sigma0 }

theorem criticalDiskExclusion_iotaInner_iff
    (cand : CriticalDiskCandidate)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskExclusion (cand.iotaInner S) ↔ CriticalDiskExclusion cand := by
  constructor
  · intro hiota hcontain
    exact hiota ((S.iota_containment_iff cand.R₁ cand.R₂ cand.t).mpr hcontain)
  · intro horig hcontain
    exact horig ((S.iota_containment_iff cand.R₁ cand.R₂ cand.t).mp hcontain)

theorem criticalDiskExclusion_swapXY_iotaInner_iff
    (cand : CriticalDiskCandidate) :
    CriticalDiskExclusion (cand.iotaInner swapXYImproperVertexSymmetry) ↔
      CriticalDiskExclusion cand :=
  criticalDiskExclusion_iotaInner_iff cand swapXYImproperVertexSymmetry

theorem criticalDiskExclusion_swapXZ_iotaInner_iff
    (cand : CriticalDiskCandidate) :
    CriticalDiskExclusion (cand.iotaInner swapXZImproperVertexSymmetry) ↔
      CriticalDiskExclusion cand :=
  criticalDiskExclusion_iotaInner_iff cand swapXZImproperVertexSymmetry

theorem criticalDiskExclusion_swapYZ_iotaInner_iff
    (cand : CriticalDiskCandidate) :
    CriticalDiskExclusion (cand.iotaInner swapYZImproperVertexSymmetry) ↔
      CriticalDiskExclusion cand :=
  criticalDiskExclusion_iotaInner_iff cand swapYZImproperVertexSymmetry

theorem criticalDiskExclusion_negSwapXY_iotaInner_iff
    (cand : CriticalDiskCandidate) :
    CriticalDiskExclusion (cand.iotaInner negSwapXYImproperVertexSymmetry) ↔
      CriticalDiskExclusion cand :=
  criticalDiskExclusion_iotaInner_iff cand negSwapXYImproperVertexSymmetry

theorem criticalDiskExclusion_negSwapXZ_iotaInner_iff
    (cand : CriticalDiskCandidate) :
    CriticalDiskExclusion (cand.iotaInner negSwapXZImproperVertexSymmetry) ↔
      CriticalDiskExclusion cand :=
  criticalDiskExclusion_iotaInner_iff cand negSwapXZImproperVertexSymmetry

theorem criticalDiskExclusion_negSwapYZ_iotaInner_iff
    (cand : CriticalDiskCandidate) :
    CriticalDiskExclusion (cand.iotaInner negSwapYZImproperVertexSymmetry) ↔
      CriticalDiskExclusion cand :=
  criticalDiskExclusion_iotaInner_iff cand negSwapYZImproperVertexSymmetry

theorem criticalDiskExclusion_faceDiagonalReflection_iotaInner_iff
    (cand : CriticalDiskCandidate) (i : Fin 6) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) ↔
      CriticalDiskExclusion cand :=
  criticalDiskExclusion_iotaInner_iff cand (faceDiagonalReflectionSymmetry i)

theorem criticalDiskLemma6Prime_iotaInner_iff
    (cand : CriticalDiskCandidate)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLemma6PrimeStatement (cand.iotaInner S) ↔
      CriticalDiskLemma6PrimeStatement cand := by
  constructor
  · intro h hcand
    exact (criticalDiskExclusion_iotaInner_iff cand S).mp
      (h ((criticalDiskHypotheses_iotaInner_iff cand S).mpr hcand))
  · intro h hiota
    exact (criticalDiskExclusion_iotaInner_iff cand S).mpr
      (h ((criticalDiskHypotheses_iotaInner_iff cand S).mp hiota))

theorem criticalDiskLemma6Prime_swapXY_iotaInner_iff
    (cand : CriticalDiskCandidate) :
    CriticalDiskLemma6PrimeStatement
        (cand.iotaInner swapXYImproperVertexSymmetry) ↔
      CriticalDiskLemma6PrimeStatement cand :=
  criticalDiskLemma6Prime_iotaInner_iff cand swapXYImproperVertexSymmetry

theorem criticalDiskLemma6Prime_swapXZ_iotaInner_iff
    (cand : CriticalDiskCandidate) :
    CriticalDiskLemma6PrimeStatement
        (cand.iotaInner swapXZImproperVertexSymmetry) ↔
      CriticalDiskLemma6PrimeStatement cand :=
  criticalDiskLemma6Prime_iotaInner_iff cand swapXZImproperVertexSymmetry

theorem criticalDiskLemma6Prime_swapYZ_iotaInner_iff
    (cand : CriticalDiskCandidate) :
    CriticalDiskLemma6PrimeStatement
        (cand.iotaInner swapYZImproperVertexSymmetry) ↔
      CriticalDiskLemma6PrimeStatement cand :=
  criticalDiskLemma6Prime_iotaInner_iff cand swapYZImproperVertexSymmetry

theorem criticalDiskLemma6Prime_negSwapXY_iotaInner_iff
    (cand : CriticalDiskCandidate) :
    CriticalDiskLemma6PrimeStatement
        (cand.iotaInner negSwapXYImproperVertexSymmetry) ↔
      CriticalDiskLemma6PrimeStatement cand :=
  criticalDiskLemma6Prime_iotaInner_iff cand negSwapXYImproperVertexSymmetry

theorem criticalDiskLemma6Prime_negSwapXZ_iotaInner_iff
    (cand : CriticalDiskCandidate) :
    CriticalDiskLemma6PrimeStatement
        (cand.iotaInner negSwapXZImproperVertexSymmetry) ↔
      CriticalDiskLemma6PrimeStatement cand :=
  criticalDiskLemma6Prime_iotaInner_iff cand negSwapXZImproperVertexSymmetry

theorem criticalDiskLemma6Prime_negSwapYZ_iotaInner_iff
    (cand : CriticalDiskCandidate) :
    CriticalDiskLemma6PrimeStatement
        (cand.iotaInner negSwapYZImproperVertexSymmetry) ↔
      CriticalDiskLemma6PrimeStatement cand :=
  criticalDiskLemma6Prime_iotaInner_iff cand negSwapYZImproperVertexSymmetry

theorem criticalDiskLemma6Prime_faceDiagonalReflection_iotaInner_iff
    (cand : CriticalDiskCandidate) (i : Fin 6) :
    CriticalDiskLemma6PrimeStatement
        (cand.iotaInner (faceDiagonalReflectionSymmetry i)) ↔
      CriticalDiskLemma6PrimeStatement cand :=
  criticalDiskLemma6Prime_iotaInner_iff cand (faceDiagonalReflectionSymmetry i)

end RupertStellatedTetrahedron
