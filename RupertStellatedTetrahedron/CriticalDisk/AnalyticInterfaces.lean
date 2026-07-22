import RupertStellatedTetrahedron.CriticalDisk.Statement
import RupertStellatedTetrahedron.DepthCylinderTheorem.BoxCylinder

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

open DepthCylinderTheorem

/-!
## Analytic interfaces for the critical disk

These definitions give precise Lean targets for the analytic parts of draft Sections 12 and 14:
first-order flatness, flag drift/deviation bookkeeping, and the unconditional localization theorem.
The long exact-arithmetic verifications still enter as proof-carrying fields, but their conclusions
are no longer arbitrary propositions.
-/

/-- The explicit conclusion of Theorem 14.3 in normalized coordinates. -/
def CriticalDiskLocalizationConclusion (cand : CriticalDiskCandidate) : Prop :=
  cand.point.distToD < criticalDiskLocalizationPlanarTube ∧
    cand.point.transverseNorm < criticalDiskLocalizationTransverseTube

theorem CriticalDiskLocalizationConclusion.planarTube
    {cand : CriticalDiskCandidate}
    (h : CriticalDiskLocalizationConclusion cand) :
    cand.point.distToD < criticalDiskLocalizationPlanarTube :=
  h.1

theorem CriticalDiskLocalizationConclusion.transverseTube
    {cand : CriticalDiskCandidate}
    (h : CriticalDiskLocalizationConclusion cand) :
    cand.point.transverseNorm < criticalDiskLocalizationTransverseTube :=
  h.2

/-- The combined local conclusion used in the critical-disk assembly:
the candidate is localized to the certified tube and excluded. -/
def CriticalDiskLocalizedExclusionStatement (cand : CriticalDiskCandidate) : Prop :=
  CriticalDiskHypotheses cand →
    CriticalDiskLocalizationConclusion cand ∧ CriticalDiskExclusion cand

/-- A normalized point lies on the limiting first-order feasible set. -/
def CriticalDiskOnLimitingSet (x : CriticalDiskPoint) : Prop :=
  x.distToD = 0

/-- Exact flatness of the limiting feasible set: points on it have no transverse component. -/
def CriticalDiskExactFlatness : Prop :=
  ∀ x : CriticalDiskPoint, CriticalDiskOnLimitingSet x → x.transverseNorm = 0

/-- The parallelogram/circumradius part of Theorem 12.2 in normalized coordinates. -/
def CriticalDiskParallelogramBound : Prop :=
  ∀ x : CriticalDiskPoint, CriticalDiskOnLimitingSet x → x.totalNorm ≤ criticalDiskXD

/-- The transverse kill constant is available with the exact draft value. -/
def CriticalDiskTransverseKillBound : Prop :=
  0 < criticalDiskCT

/-- The Hoffman constant is available with the lower bound used by the assembly. -/
def CriticalDiskHoffmanBound : Prop :=
  0 < criticalDiskHoffmanC1

/-- Lean-facing statement of the exact first-order structure from Theorem 12.2. -/
structure CriticalDiskFirstOrderStructure where
  exactFlatness : CriticalDiskExactFlatness
  parallelogramBound : CriticalDiskParallelogramBound
  transverseKill : CriticalDiskTransverseKillBound
  hoffmanBound : CriticalDiskHoffmanBound

def CriticalDiskFirstOrderStructure.certified (_s : CriticalDiskFirstOrderStructure) : Prop :=
  CriticalDiskExactFlatness ∧ CriticalDiskParallelogramBound ∧
    CriticalDiskTransverseKillBound ∧ CriticalDiskHoffmanBound

theorem CriticalDiskFirstOrderStructure.certified_of_fields
    (s : CriticalDiskFirstOrderStructure) :
    s.certified :=
  ⟨s.exactFlatness, s.parallelogramBound, s.transverseKill, s.hoffmanBound⟩

/-- Lemma 14.1 packaged as a numerical BCH/deviation budget. -/
structure CriticalDiskDeviationDictionary where
  bchConstant : ℝ
  bchConstant_eq : bchConstant = 11 / 20
  deviationBudget :
    ∀ sigma delta : ℝ, 0 ≤ sigma → 0 ≤ delta →
      0 ≤ bchConstant * (sigma + 2 * delta) * (2 * delta)

/-- Norm of the rotation block `(x₀,x₁,x₂)` of a five-dimensional flag difference. -/
def criticalDiskRotationBlockNorm (x : BoxFlag5) : ℝ :=
  Real.sqrt (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2)

lemma criticalDiskRotationBlockNorm_nonneg (x : BoxFlag5) :
    0 ≤ criticalDiskRotationBlockNorm x := by
  unfold criticalDiskRotationBlockNorm
  positivity

/-- The translation block consists of the last two flag coordinates. -/
def criticalDiskSameTranslationBlock (x y : BoxFlag5) : Prop :=
  x 3 = y 3 ∧ x 4 = y 4

/-- Lemma 14.2 packaged as the drift fact needed by the localization proof.

Each chart/index names one active form tracked along the critical disk.  The translation block is
exactly stable, while the rotation block has a linear-in-`δ` Lipschitz bound.
-/
structure CriticalDiskFlagDrift where
  chart : Type
  flagAt : chart → ℝ → BoxFlag5
  limitFlag : chart → BoxFlag5
  lipschitzConstant : chart → ℝ
  lipschitzConstant_nonneg : ∀ c, 0 ≤ lipschitzConstant c
  translationBlockStable :
    ∀ c δ, criticalDiskSameTranslationBlock (flagAt c δ) (limitFlag c)
  rotationBlockLipschitz :
    ∀ c δ, 0 ≤ δ → δ ≤ criticalDiskRhoCap →
      criticalDiskRotationBlockNorm (flagAt c δ - limitFlag c) ≤
        lipschitzConstant c * δ

theorem CriticalDiskFlagDrift.translation_three_eq
    (d : CriticalDiskFlagDrift) (c : d.chart) (δ : ℝ) :
    d.flagAt c δ 3 = d.limitFlag c 3 :=
  (d.translationBlockStable c δ).1

theorem CriticalDiskFlagDrift.translation_four_eq
    (d : CriticalDiskFlagDrift) (c : d.chart) (δ : ℝ) :
    d.flagAt c δ 4 = d.limitFlag c 4 :=
  (d.translationBlockStable c δ).2

/-- Analytic hypotheses needed before the two external certificates assemble Lemma 6'. -/
structure CriticalDiskAnalyticInputs where
  firstOrder : CriticalDiskFirstOrderStructure
  deviationDictionary : CriticalDiskDeviationDictionary
  flagDrift : CriticalDiskFlagDrift
  /-- Theorem 14.3: unconditional localization in the normalized disk. -/
  localization :
    ∀ cand : CriticalDiskCandidate,
      CriticalDiskHypotheses cand → CriticalDiskLocalizationConclusion cand

theorem criticalDisk_transverse_kill_constant_positive
    (s : CriticalDiskFirstOrderStructure) : 0 < criticalDiskCT :=
  s.transverseKill

theorem criticalDisk_hoffman_constant_positive
    (s : CriticalDiskFirstOrderStructure) : 0 < criticalDiskHoffmanC1 :=
  s.hoffmanBound

theorem criticalDisk_firstOrder_certified_from_analytic_inputs
    (inputs : CriticalDiskAnalyticInputs) :
    inputs.firstOrder.certified :=
  inputs.firstOrder.certified_of_fields

theorem criticalDisk_exact_flatness_from_analytic_inputs
    (inputs : CriticalDiskAnalyticInputs) :
    CriticalDiskExactFlatness :=
  inputs.firstOrder.exactFlatness

theorem criticalDisk_parallelogram_bound_from_analytic_inputs
    (inputs : CriticalDiskAnalyticInputs) :
    CriticalDiskParallelogramBound :=
  inputs.firstOrder.parallelogramBound

theorem criticalDisk_transverse_kill_constant_positive_from_analytic_inputs
    (inputs : CriticalDiskAnalyticInputs) :
    0 < criticalDiskCT :=
  inputs.firstOrder.transverseKill

theorem criticalDisk_hoffman_constant_positive_from_analytic_inputs
    (inputs : CriticalDiskAnalyticInputs) :
    0 < criticalDiskHoffmanC1 :=
  inputs.firstOrder.hoffmanBound

theorem criticalDisk_deviation_bchConstant_eq_from_analytic_inputs
    (inputs : CriticalDiskAnalyticInputs) :
    inputs.deviationDictionary.bchConstant = 11 / 20 :=
  inputs.deviationDictionary.bchConstant_eq

theorem criticalDisk_deviation_budget_from_analytic_inputs
    (inputs : CriticalDiskAnalyticInputs)
    (sigma delta : ℝ) (hsigma : 0 ≤ sigma) (hdelta : 0 ≤ delta) :
    0 ≤ inputs.deviationDictionary.bchConstant * (sigma + 2 * delta) * (2 * delta) :=
  inputs.deviationDictionary.deviationBudget sigma delta hsigma hdelta

theorem criticalDisk_flag_drift_translation_three_from_analytic_inputs
    (inputs : CriticalDiskAnalyticInputs)
    (c : inputs.flagDrift.chart) (δ : ℝ) :
    inputs.flagDrift.flagAt c δ 3 = inputs.flagDrift.limitFlag c 3 :=
  inputs.flagDrift.translation_three_eq c δ

theorem criticalDisk_flag_drift_translation_four_from_analytic_inputs
    (inputs : CriticalDiskAnalyticInputs)
    (c : inputs.flagDrift.chart) (δ : ℝ) :
    inputs.flagDrift.flagAt c δ 4 = inputs.flagDrift.limitFlag c 4 :=
  inputs.flagDrift.translation_four_eq c δ

theorem criticalDisk_flag_drift_translation_block_from_analytic_inputs
    (inputs : CriticalDiskAnalyticInputs)
    (c : inputs.flagDrift.chart) (δ : ℝ) :
    criticalDiskSameTranslationBlock
      (inputs.flagDrift.flagAt c δ) (inputs.flagDrift.limitFlag c) :=
  inputs.flagDrift.translationBlockStable c δ

theorem criticalDisk_flag_drift_lipschitz_constant_nonneg_from_analytic_inputs
    (inputs : CriticalDiskAnalyticInputs)
    (c : inputs.flagDrift.chart) :
    0 ≤ inputs.flagDrift.lipschitzConstant c :=
  inputs.flagDrift.lipschitzConstant_nonneg c

theorem criticalDisk_flag_drift_rotation_lipschitz_from_analytic_inputs
    (inputs : CriticalDiskAnalyticInputs)
    (c : inputs.flagDrift.chart) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδcap : δ ≤ criticalDiskRhoCap) :
    criticalDiskRotationBlockNorm
        (inputs.flagDrift.flagAt c δ - inputs.flagDrift.limitFlag c) ≤
      inputs.flagDrift.lipschitzConstant c * δ :=
  inputs.flagDrift.rotationBlockLipschitz c δ hδ0 hδcap

theorem criticalDisk_localization_from_analytic_inputs
    (inputs : CriticalDiskAnalyticInputs)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskLocalizationConclusion cand :=
  inputs.localization cand hcand

theorem criticalDisk_localization_planar_tube_from_analytic_inputs
    (inputs : CriticalDiskAnalyticInputs)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand) :
    cand.point.distToD < criticalDiskLocalizationPlanarTube :=
  (inputs.localization cand hcand).planarTube

theorem criticalDisk_localization_transverse_tube_from_analytic_inputs
    (inputs : CriticalDiskAnalyticInputs)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand) :
    cand.point.transverseNorm < criticalDiskLocalizationTransverseTube :=
  (inputs.localization cand hcand).transverseTube

theorem criticalDisk_localized_exclusion_from_analytic_inputs
    (inputs : CriticalDiskAnalyticInputs)
    {cand : CriticalDiskCandidate}
    (lemma6 : CriticalDiskLemma6PrimeStatement cand) :
    CriticalDiskLocalizedExclusionStatement cand := by
  intro hcand
  exact ⟨inputs.localization cand hcand, lemma6 hcand⟩

theorem CriticalDiskLocalizedExclusionStatement.localization
    {cand : CriticalDiskCandidate}
    (h : CriticalDiskLocalizedExclusionStatement cand)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskLocalizationConclusion cand :=
  (h hcand).1

theorem CriticalDiskLocalizedExclusionStatement.planarTube
    {cand : CriticalDiskCandidate}
    (h : CriticalDiskLocalizedExclusionStatement cand)
    (hcand : CriticalDiskHypotheses cand) :
    cand.point.distToD < criticalDiskLocalizationPlanarTube :=
  (h.localization hcand).planarTube

theorem CriticalDiskLocalizedExclusionStatement.transverseTube
    {cand : CriticalDiskCandidate}
    (h : CriticalDiskLocalizedExclusionStatement cand)
    (hcand : CriticalDiskHypotheses cand) :
    cand.point.transverseNorm < criticalDiskLocalizationTransverseTube :=
  (h.localization hcand).transverseTube

theorem CriticalDiskLocalizedExclusionStatement.exclusion
    {cand : CriticalDiskCandidate}
    (h : CriticalDiskLocalizedExclusionStatement cand)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  (h hcand).2

end RupertStellatedTetrahedron
