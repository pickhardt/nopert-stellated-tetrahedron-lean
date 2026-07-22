import RupertStellatedTetrahedron.CriticalDisk.TranslationKill

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

/-!
## Critical-disk assembly constants

These are the exact constants used by the conditional Lemma 6' assembly.  They are independent
of the external certificate payloads, so we can keep them checked in Lean while the certificate
format remains abstract.
-/

/-- Corner-ball radius `r_b = 0.012`. -/
def criticalDiskRb : ℝ := 3 / 250

/-- Transverse tolerance `ν = 0.014`. -/
def criticalDiskNu : ℝ := 7 / 500

/-- SF bulk target `Ψ_min = 0.06`. -/
def criticalDiskPsiMin : ℝ := 3 / 50

/-- SF corner-shell slope `0.3`. -/
def criticalDiskShellSlope : ℝ := 3 / 10

/-- Box-certificate tilt half-width `b_Π = 2/125`. -/
def criticalDiskBoxBPi : ℝ := 2 / 125

/-- Box-certificate spin half-width `b_γ = 1/25`. -/
def criticalDiskBoxBGamma : ℝ := 1 / 25

/-- Box-certificate translation half-width `b_t = 1/500`. -/
def criticalDiskBoxBT : ℝ := 1 / 500

/-- Diagonal-anchor slope `g₁ = 1/40`. -/
def criticalDiskG1 : ℝ := 1 / 40

/-- Sheet contact-depth lower bound `c_min = 1/50`. -/
def criticalDiskCMin : ℝ := 1 / 50

/-- Flatness allowance `κ_T = 10⁻³`. -/
def criticalDiskKappaT : ℝ := 1 / 1000

/-- Size bound `X_D = 323√2/198`. -/
def criticalDiskXD : ℝ := 323 * Real.sqrt 2 / 198

/-- Transverse kill rate `c_T = 9√2/√1123`. -/
def criticalDiskCT : ℝ := 9 * Real.sqrt 2 / Real.sqrt 1123

/-- Composite Hoffman constant lower bound `c₁ = 0.162`. -/
def criticalDiskHoffmanC1 : ℝ := 81 / 500

/-- Localization planar tube radius `0.08`. -/
def criticalDiskLocalizationPlanarTube : ℝ := 2 / 25

/-- Localization transverse tube radius `0.0285`. -/
def criticalDiskLocalizationTransverseTube : ℝ := 57 / 2000

/-- Relative rotation cap `σ₀ = 0.0427`. -/
def criticalDiskSigma0 : ℝ := 427 / 10000

/-- Critical-disk radius cap `ρ₀ = 10⁻³`, before intersecting certificate radii. -/
def criticalDiskRhoCap : ℝ := 1 / 1000

/-- Cylinder residual constant at `s₀ = 0.1`, namely `M₀ = √3(1/2+1/60)`. -/
def criticalDiskM : ℝ := 31 * Real.sqrt 3 / 60

/-- Tail/bulk split for the exact `(SB-box)` tail certificate, `10⁻⁵`. -/
def criticalDiskTailCut : ℝ := 1 / 100000

/-- Certified lower bound for the box reach used in the SB/SF handoff. -/
def criticalDiskBoxReachLower : ℝ := 17879 / 1000000

/-- Certified shell radius used in the SB/SF handoff. -/
def criticalDiskShellRadius : ℝ := 69 / 5000

lemma criticalDiskRb_pos : 0 < criticalDiskRb := by
  norm_num [criticalDiskRb]

lemma criticalDiskNu_pos : 0 < criticalDiskNu := by
  norm_num [criticalDiskNu]

lemma criticalDiskPsiMin_pos : 0 < criticalDiskPsiMin := by
  norm_num [criticalDiskPsiMin]

lemma criticalDiskShellSlope_pos : 0 < criticalDiskShellSlope := by
  norm_num [criticalDiskShellSlope]

lemma criticalDiskBoxBPi_pos : 0 < criticalDiskBoxBPi := by
  norm_num [criticalDiskBoxBPi]

lemma criticalDiskBoxBGamma_pos : 0 < criticalDiskBoxBGamma := by
  norm_num [criticalDiskBoxBGamma]

lemma criticalDiskBoxBT_pos : 0 < criticalDiskBoxBT := by
  norm_num [criticalDiskBoxBT]

lemma criticalDiskG1_pos : 0 < criticalDiskG1 := by
  norm_num [criticalDiskG1]

lemma criticalDiskCMin_pos : 0 < criticalDiskCMin := by
  norm_num [criticalDiskCMin]

lemma criticalDiskKappaT_pos : 0 < criticalDiskKappaT := by
  norm_num [criticalDiskKappaT]

lemma criticalDiskXD_pos : 0 < criticalDiskXD := by
  unfold criticalDiskXD
  positivity

lemma criticalDiskCT_pos : 0 < criticalDiskCT := by
  unfold criticalDiskCT
  positivity

lemma criticalDiskHoffmanC1_pos : 0 < criticalDiskHoffmanC1 := by
  norm_num [criticalDiskHoffmanC1]

lemma criticalDiskLocalizationPlanarTube_pos : 0 < criticalDiskLocalizationPlanarTube := by
  norm_num [criticalDiskLocalizationPlanarTube]

lemma criticalDiskLocalizationTransverseTube_pos :
    0 < criticalDiskLocalizationTransverseTube := by
  norm_num [criticalDiskLocalizationTransverseTube]

lemma criticalDiskSigma0_pos : 0 < criticalDiskSigma0 := by
  norm_num [criticalDiskSigma0]

lemma criticalDiskRhoCap_pos : 0 < criticalDiskRhoCap := by
  norm_num [criticalDiskRhoCap]

lemma criticalDiskM_pos : 0 < criticalDiskM := by
  unfold criticalDiskM
  positivity

lemma criticalDiskTailCut_pos : 0 < criticalDiskTailCut := by
  norm_num [criticalDiskTailCut]

lemma criticalDiskBoxReachLower_pos : 0 < criticalDiskBoxReachLower := by
  norm_num [criticalDiskBoxReachLower]

lemma criticalDiskShellRadius_pos : 0 < criticalDiskShellRadius := by
  norm_num [criticalDiskShellRadius]

lemma criticalDiskM_sq : criticalDiskM ^ 2 = 961 / 1200 := by
  unfold criticalDiskM
  have hsqrt : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  calc
    (31 * Real.sqrt 3 / 60) ^ 2 = 961 * Real.sqrt 3 ^ 2 / 3600 := by ring
    _ = 961 / 1200 := by rw [hsqrt]; norm_num

lemma criticalDiskRb_lt_shellRadius : criticalDiskRb < criticalDiskShellRadius := by
  norm_num [criticalDiskRb, criticalDiskShellRadius]

lemma criticalDiskShellRadius_lt_boxReachLower :
    criticalDiskShellRadius < criticalDiskBoxReachLower := by
  norm_num [criticalDiskShellRadius, criticalDiskBoxReachLower]

lemma criticalDiskBoxReachLower_lt_boxBPi_div_M :
    criticalDiskBoxReachLower < criticalDiskBoxBPi / criticalDiskM := by
  have hsq :
      (criticalDiskBoxReachLower * criticalDiskM) ^ 2 < criticalDiskBoxBPi ^ 2 := by
    rw [mul_pow, criticalDiskM_sq]
    norm_num [criticalDiskBoxReachLower, criticalDiskBoxBPi]
  have hreach_nonneg : 0 ≤ criticalDiskBoxReachLower * criticalDiskM :=
    mul_nonneg (le_of_lt criticalDiskBoxReachLower_pos) (le_of_lt criticalDiskM_pos)
  have htarget_nonneg : 0 ≤ criticalDiskBoxBPi :=
    le_of_lt criticalDiskBoxBPi_pos
  have hmul : criticalDiskBoxReachLower * criticalDiskM < criticalDiskBoxBPi :=
    (sq_lt_sq₀ hreach_nonneg htarget_nonneg).mp hsq
  exact (lt_div_iff₀ criticalDiskM_pos).mpr hmul

lemma criticalDiskCMin_lt_G1 : criticalDiskCMin < criticalDiskG1 := by
  norm_num [criticalDiskCMin, criticalDiskG1]

lemma criticalDiskSigma0_lt_half : criticalDiskSigma0 < (1 / 2 : ℝ) := by
  norm_num [criticalDiskSigma0]

lemma criticalDiskPsiMin_lt_one :
    criticalDiskPsiMin < (1 : ℝ) := by
  norm_num [criticalDiskPsiMin]

lemma criticalDiskRb_lt_CMin : criticalDiskRb < criticalDiskCMin := by
  norm_num [criticalDiskRb, criticalDiskCMin]

lemma criticalDiskNu_lt_G1 : criticalDiskNu < criticalDiskG1 := by
  norm_num [criticalDiskNu, criticalDiskG1]

lemma criticalDiskKappaT_lt_Nu : criticalDiskKappaT < criticalDiskNu := by
  norm_num [criticalDiskKappaT, criticalDiskNu]

lemma criticalDiskRhoCap_lt_one : criticalDiskRhoCap < (1 : ℝ) := by
  norm_num [criticalDiskRhoCap]

lemma criticalDiskRhoCap_le_sigma0 : criticalDiskRhoCap ≤ criticalDiskSigma0 := by
  norm_num [criticalDiskRhoCap, criticalDiskSigma0]

lemma criticalDiskTailCut_lt_rhoCap : criticalDiskTailCut < criticalDiskRhoCap := by
  norm_num [criticalDiskTailCut, criticalDiskRhoCap]

/-- The squared Zone-B/C transverse radius used in the assembly. -/
def criticalDiskAnchorRadiusSq : ℝ :=
  criticalDiskRb ^ 2 + (criticalDiskNu + criticalDiskKappaT) ^ 2

lemma criticalDiskAnchorRadiusSq_eq :
    criticalDiskAnchorRadiusSq = 369 / 1000000 := by
  norm_num [criticalDiskAnchorRadiusSq, criticalDiskRb, criticalDiskNu, criticalDiskKappaT]

lemma criticalDiskAnchorRadiusSq_pos : 0 < criticalDiskAnchorRadiusSq := by
  rw [criticalDiskAnchorRadiusSq_eq]
  norm_num

lemma criticalDiskAnchorRadiusSq_lt_CMin_sq :
    criticalDiskAnchorRadiusSq < criticalDiskCMin ^ 2 := by
  rw [criticalDiskAnchorRadiusSq_eq]
  norm_num [criticalDiskCMin]

lemma criticalDiskAnchorRadiusSq_lt_G1_sq :
    criticalDiskAnchorRadiusSq < criticalDiskG1 ^ 2 := by
  rw [criticalDiskAnchorRadiusSq_eq]
  norm_num [criticalDiskG1]

lemma criticalDiskAnchorRadiusSq_lt_CMin_div_M_sq :
    criticalDiskAnchorRadiusSq < (criticalDiskCMin / criticalDiskM) ^ 2 := by
  rw [criticalDiskAnchorRadiusSq_eq]
  rw [div_pow, criticalDiskM_sq]
  norm_num [criticalDiskCMin]

lemma criticalDiskAnchorRadius_lt_CMin_div_M :
    Real.sqrt criticalDiskAnchorRadiusSq < criticalDiskCMin / criticalDiskM := by
  have htarget_pos : 0 < criticalDiskCMin / criticalDiskM :=
    div_pos criticalDiskCMin_pos criticalDiskM_pos
  rw [Real.sqrt_lt' htarget_pos]
  exact criticalDiskAnchorRadiusSq_lt_CMin_div_M_sq

lemma criticalDiskCMin_div_M_lt_G1_div_M :
    criticalDiskCMin / criticalDiskM < criticalDiskG1 / criticalDiskM := by
  exact div_lt_div_of_pos_right criticalDiskCMin_lt_G1 criticalDiskM_pos

lemma criticalDiskAnchorRadius_lt_G1_div_M :
    Real.sqrt criticalDiskAnchorRadiusSq < criticalDiskG1 / criticalDiskM :=
  lt_trans criticalDiskAnchorRadius_lt_CMin_div_M criticalDiskCMin_div_M_lt_G1_div_M

/-- Critical-disk radius used by the two-certificate conditional assembly. -/
def criticalDiskRho0 (rhoF rhoB : ℝ) : ℝ :=
  min criticalDiskRhoCap (min rhoF rhoB)

lemma criticalDiskRho0_le_cap (rhoF rhoB : ℝ) :
    criticalDiskRho0 rhoF rhoB ≤ criticalDiskRhoCap := by
  unfold criticalDiskRho0
  exact min_le_left _ _

lemma criticalDiskRho0_le_rhoF (rhoF rhoB : ℝ) :
    criticalDiskRho0 rhoF rhoB ≤ rhoF := by
  unfold criticalDiskRho0
  exact le_trans (min_le_right _ _) (min_le_left _ _)

lemma criticalDiskRho0_le_rhoB (rhoF rhoB : ℝ) :
    criticalDiskRho0 rhoF rhoB ≤ rhoB := by
  unfold criticalDiskRho0
  exact le_trans (min_le_right _ _) (min_le_right _ _)

lemma criticalDiskRho0_pos {rhoF rhoB : ℝ}
    (hF : 0 < rhoF) (hB : 0 < rhoB) :
    0 < criticalDiskRho0 rhoF rhoB := by
  unfold criticalDiskRho0
  exact lt_min criticalDiskRhoCap_pos (lt_min hF hB)

lemma criticalDiskRho0_le_sigma0 (rhoF rhoB : ℝ) :
    criticalDiskRho0 rhoF rhoB ≤ criticalDiskSigma0 := by
  exact le_trans (criticalDiskRho0_le_cap rhoF rhoB) criticalDiskRhoCap_le_sigma0

lemma criticalDiskRho0_lt_one (rhoF rhoB : ℝ) :
    criticalDiskRho0 rhoF rhoB < (1 : ℝ) := by
  exact lt_of_le_of_lt (criticalDiskRho0_le_cap rhoF rhoB) criticalDiskRhoCap_lt_one

end RupertStellatedTetrahedron
