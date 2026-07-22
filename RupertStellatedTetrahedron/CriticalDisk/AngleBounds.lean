import RupertStellatedTetrahedron.CriticalDisk.ZoneGeometry

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

/-!
## Angle bounds for the critical-disk corner zones

The Zone B/C assembly uses the same numerical estimate twice: a normalized vector whose squared
norm is bounded by `r_b^2 + (ν + κ_T)^2` lies inside both cylinder radii.  This file isolates that
pure norm arithmetic from the certificate-dependent arguments.
-/

variable {E : Type*} [SeminormedAddCommGroup E]

lemma norm_lt_CMin_div_M_of_norm_sq_le_anchor (x : E)
    (h : ‖x‖ ^ 2 ≤ criticalDiskAnchorRadiusSq) :
    ‖x‖ < criticalDiskCMin / criticalDiskM := by
  have hsq : ‖x‖ ^ 2 < (criticalDiskCMin / criticalDiskM) ^ 2 :=
    lt_of_le_of_lt h criticalDiskAnchorRadiusSq_lt_CMin_div_M_sq
  exact (sq_lt_sq₀ (norm_nonneg x)
    (le_of_lt (div_pos criticalDiskCMin_pos criticalDiskM_pos))).mp hsq

lemma norm_lt_G1_div_M_of_norm_sq_le_anchor (x : E)
    (h : ‖x‖ ^ 2 ≤ criticalDiskAnchorRadiusSq) :
    ‖x‖ < criticalDiskG1 / criticalDiskM := by
  exact lt_trans (norm_lt_CMin_div_M_of_norm_sq_le_anchor x h)
    criticalDiskCMin_div_M_lt_G1_div_M

lemma scaled_norm_lt_CMin_delta_div_M_of_norm_sq_le_anchor
    (δ : ℝ) (hδ : 0 < δ) (x : E)
    (h : ‖x‖ ^ 2 ≤ criticalDiskAnchorRadiusSq) :
    δ * ‖x‖ < criticalDiskCMin * δ / criticalDiskM := by
  have hbase := norm_lt_CMin_div_M_of_norm_sq_le_anchor x h
  have hmul := mul_lt_mul_of_pos_left hbase hδ
  calc
    δ * ‖x‖ < δ * (criticalDiskCMin / criticalDiskM) := hmul
    _ = criticalDiskCMin * δ / criticalDiskM := by ring

lemma scaled_norm_lt_G1_delta_div_M_of_norm_sq_le_anchor
    (δ : ℝ) (hδ : 0 < δ) (x : E)
    (h : ‖x‖ ^ 2 ≤ criticalDiskAnchorRadiusSq) :
    δ * ‖x‖ < criticalDiskG1 * δ / criticalDiskM := by
  have hbase := norm_lt_G1_div_M_of_norm_sq_le_anchor x h
  have hmul := mul_lt_mul_of_pos_left hbase hδ
  calc
    δ * ‖x‖ < δ * (criticalDiskG1 / criticalDiskM) := hmul
    _ = criticalDiskG1 * δ / criticalDiskM := by ring

/-- Zone B angle estimate: the diagonal-anchor ball fits inside the SB cylinder radius. -/
theorem zoneB_angle_bound_of_norm_sq_le_anchor (δ : ℝ) (hδ : 0 < δ) (ξhat : E)
    (hξ : ‖ξhat‖ ^ 2 ≤ criticalDiskAnchorRadiusSq) :
    δ * ‖ξhat‖ < criticalDiskG1 * δ / criticalDiskM := by
  exact scaled_norm_lt_G1_delta_div_M_of_norm_sq_le_anchor δ hδ ξhat hξ

/-- Zone C angle estimate: the sheet-anchor ball fits inside the SC cylinder radius. -/
theorem zoneC_angle_bound_of_norm_sq_le_anchor (δ : ℝ) (hδ : 0 < δ) (ξhatDiff : E)
    (hξ : ‖ξhatDiff‖ ^ 2 ≤ criticalDiskAnchorRadiusSq) :
    δ * ‖ξhatDiff‖ < criticalDiskCMin * δ / criticalDiskM := by
  exact scaled_norm_lt_CMin_delta_div_M_of_norm_sq_le_anchor δ hδ ξhatDiff hξ

end RupertStellatedTetrahedron
