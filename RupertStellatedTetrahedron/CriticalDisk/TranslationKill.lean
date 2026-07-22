import RupertStellatedTetrahedron.Stellated.CriticalDirection
import RupertStellatedTetrahedron.DepthCylinderTheorem.Duality

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

open DepthCylinderTheorem

/-!
## Abstract translation kill

The critical-disk proof uses a finite family of transverse gradients whose convex hull contains a
ball around the origin.  This file records the exact dual consequence: every nonzero transverse
motion is killed linearly by one of those gradients.  The concrete `9√2/20` certificate can later be
plugged into `hcert`.
-/

abbrev TransverseSpace := EuclideanSpace ℝ (Fin 5)

def transverseCoord (ξ₃ : ℝ) (t : V2) : TransverseSpace :=
  WithLp.toLp 2 fun i : Fin 5 =>
    match i with
    | 0 => 0
    | 1 => 0
    | 2 => ξ₃
    | 3 => t 0
    | 4 => t 1

@[simp] lemma transverseCoord_apply_zero (ξ₃ : ℝ) (t : V2) :
    transverseCoord ξ₃ t 0 = 0 := by
  simp [transverseCoord]

@[simp] lemma transverseCoord_apply_one (ξ₃ : ℝ) (t : V2) :
    transverseCoord ξ₃ t 1 = 0 := by
  simp [transverseCoord]

@[simp] lemma transverseCoord_apply_two (ξ₃ : ℝ) (t : V2) :
    transverseCoord ξ₃ t 2 = ξ₃ := by
  simp [transverseCoord]

@[simp] lemma transverseCoord_apply_three (ξ₃ : ℝ) (t : V2) :
    transverseCoord ξ₃ t 3 = t 0 := by
  simp [transverseCoord]

@[simp] lemma transverseCoord_apply_four (ξ₃ : ℝ) (t : V2) :
    transverseCoord ξ₃ t 4 = t 1 := by
  simp [transverseCoord]

lemma transverseCoord_eq_zero_iff (ξ₃ : ℝ) (t : V2) :
    transverseCoord ξ₃ t = 0 ↔ ξ₃ = 0 ∧ t = 0 := by
  constructor
  · intro h
    constructor
    · have h2 := congrArg (fun y : TransverseSpace => y 2) h
      simpa using h2
    · ext i
      fin_cases i
      · have h3 := congrArg (fun y : TransverseSpace => y 3) h
        simpa using h3
      · have h4 := congrArg (fun y : TransverseSpace => y 4) h
        simpa using h4
  · rintro ⟨rfl, rfl⟩
    ext i
    fin_cases i <;> simp

lemma exists_transverse_flag_kill
    (A : Finset TransverseSpace)
    (r : ℝ) (hr : 0 < r)
    (hcert : Metric.closedBall (0 : TransverseSpace) r ⊆
      convexHull ℝ (A : Set TransverseSpace))
    (x : TransverseSpace) (hx : x ≠ 0) :
    ∃ a ∈ A, ⟪a, x⟫ ≤ -r * ‖x‖ := by
  classical
  let u : TransverseSpace := (‖x‖⁻¹ : ℝ) • x
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖u‖ = 1 := by
    rw [show u = (‖x‖⁻¹ : ℝ) • x from rfl, norm_smul]
    rw [norm_inv, Real.norm_of_nonneg (le_of_lt hxpos)]
    exact inv_mul_cancel₀ (ne_of_gt hxpos)
  obtain ⟨a, ha, hale⟩ := (depth_duality A r hr).mp hcert u hu
  refine ⟨a, ha, ?_⟩
  have hinner : ⟪a, u⟫ = ‖x‖⁻¹ * ⟪a, x⟫ := by
    rw [show u = (‖x‖⁻¹ : ℝ) • x from rfl, inner_smul_right]
  rw [hinner] at hale
  have hmul := mul_le_mul_of_nonneg_right hale (le_of_lt hxpos)
  have hneq : ‖x‖ ≠ 0 := ne_of_gt hxpos
  have hc : ‖x‖⁻¹ * ‖x‖ = 1 := inv_mul_cancel₀ hneq
  have heq : (‖x‖⁻¹ * ⟪a, x⟫) * ‖x‖ = ⟪a, x⟫ := by
    calc
      (‖x‖⁻¹ * ⟪a, x⟫) * ‖x‖ =
          (‖x‖⁻¹ * ‖x‖) * ⟪a, x⟫ := by ring
      _ = ⟪a, x⟫ := by rw [hc]; ring
  rw [heq] at hmul
  exact hmul

/-- Named form of the exact `9√2/20` translation-kill radius from Proposition 12.1. -/
def translationKillRadius : ℝ := 9 * Real.sqrt 2 / 20

lemma translationKillRadius_pos : 0 < translationKillRadius := by
  unfold translationKillRadius
  positivity

theorem translation_kill_of_positive_span
    (A : Finset TransverseSpace)
    (hcert : Metric.closedBall (0 : TransverseSpace) translationKillRadius ⊆
      convexHull ℝ (A : Set TransverseSpace))
    (ξ₃ : ℝ) (t : V2)
    (hmotion : transverseCoord ξ₃ t ≠ 0) :
    ∃ a ∈ A, ⟪a, transverseCoord ξ₃ t⟫ ≤
      -translationKillRadius * ‖transverseCoord ξ₃ t‖ := by
  exact exists_transverse_flag_kill A translationKillRadius translationKillRadius_pos hcert
    (transverseCoord ξ₃ t) hmotion

end RupertStellatedTetrahedron
