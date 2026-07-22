import RupertStellatedTetrahedron.CriticalDisk.ExactConstants

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

/-!
## Scalar depth-certificate failure

Draft §13.1 records that the earlier scalar lower bound with slope `g₁ = 1/40`
is incompatible with an audited depth-rate dip near the silhouette walls.  This
module formalizes the exact numerical comparison and gives the audited depth
computation a Lean boundary without asserting its semantic content here.
-/

/-- Recorded upper bound for the scalar depth-rate dip, `0.023938`. -/
def criticalDiskScalarFailureRate : ℝ := 11969 / 500000

/-- Exact `ℚ[√2]` encoding of the recorded scalar depth-rate dip. -/
def criticalDiskScalarFailureRateQ : Qsqrt2 :=
  Qsqrt2.ofRat (11969 / 500000)

lemma criticalDiskScalarFailureRateQ_toReal :
    criticalDiskScalarFailureRateQ.toReal = criticalDiskScalarFailureRate := by
  norm_num [criticalDiskScalarFailureRateQ, criticalDiskScalarFailureRate,
    Qsqrt2.ofRat, Qsqrt2.toReal]

lemma criticalDiskScalarFailureRate_pos :
    0 < criticalDiskScalarFailureRate := by
  norm_num [criticalDiskScalarFailureRate]

lemma criticalDiskScalarFailureRate_lt_G1 :
    criticalDiskScalarFailureRate < criticalDiskG1 := by
  norm_num [criticalDiskScalarFailureRate, criticalDiskG1]

lemma criticalDiskBoxBPi_lt_scalarFailureRate :
    criticalDiskBoxBPi < criticalDiskScalarFailureRate := by
  norm_num [criticalDiskBoxBPi, criticalDiskScalarFailureRate]

lemma criticalDiskScalarFailureRate_eq_boxBPi_mul :
    criticalDiskScalarFailureRate = (11969 / 8000 : ℝ) * criticalDiskBoxBPi := by
  norm_num [criticalDiskScalarFailureRate, criticalDiskBoxBPi]

lemma criticalDiskScalarFailureRate_lt_three_halves_boxBPi :
    criticalDiskScalarFailureRate < (3 / 2 : ℝ) * criticalDiskBoxBPi := by
  norm_num [criticalDiskScalarFailureRate, criticalDiskBoxBPi]

/-- A semantic boundary for the audited scalar-depth counterexample.

The relation parameter is intentionally supplied by the eventual checker.  Its intended meaning is
that at parameter `φ`, the diagonal depth-rate is at most the supplied value.  The current file only
records the exact numerical obstruction to the old uniform `g₁` lower bound.
-/
structure CriticalDiskScalarDepthFailure
    (depthRateAtMost : ℝ → ℝ → Prop) where
  phi : ℝ
  rateUpper : ℝ
  rateUpper_eq : rateUpper = criticalDiskScalarFailureRate
  depthRateAtMost_certified : depthRateAtMost phi rateUpper

def criticalDiskScalarDepthFailure_of_recorded_rate
    {depthRateAtMost : ℝ → ℝ → Prop} {φ : ℝ}
    (hφ : depthRateAtMost φ criticalDiskScalarFailureRate) :
    CriticalDiskScalarDepthFailure depthRateAtMost where
  phi := φ
  rateUpper := criticalDiskScalarFailureRate
  rateUpper_eq := rfl
  depthRateAtMost_certified := hφ

theorem CriticalDiskScalarDepthFailure.rateUpper_lt_G1
    {depthRateAtMost : ℝ → ℝ → Prop}
    (failure : CriticalDiskScalarDepthFailure depthRateAtMost) :
    failure.rateUpper < criticalDiskG1 := by
  rw [failure.rateUpper_eq]
  exact criticalDiskScalarFailureRate_lt_G1

/-- The recorded audited-rate upper bound is incompatible with any attempted scalar lower-bound
interface that would force every audited upper bound to be at least `g₁`. -/
theorem CriticalDiskScalarDepthFailure.not_uniform_G1_lower_at_audited_rates
    {depthRateAtMost : ℝ → ℝ → Prop}
    (failure : CriticalDiskScalarDepthFailure depthRateAtMost) :
    ¬ (∀ φ rate, depthRateAtMost φ rate → criticalDiskG1 ≤ rate) := by
  intro hlower
  exact not_lt_of_ge
    (hlower failure.phi failure.rateUpper failure.depthRateAtMost_certified)
    failure.rateUpper_lt_G1

end RupertStellatedTetrahedron
