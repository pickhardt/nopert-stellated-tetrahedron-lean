import RupertStellatedTetrahedron.DepthCylinderTheorem.FrameReduction

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace DepthCylinderTheorem

lemma finite_flags_convexHull_closed (F : Finset (EuclideanSpace ℝ (Fin 5))) :
    IsClosed (convexHull ℝ (F : Set (EuclideanSpace ℝ (Fin 5)))) := by
  exact (Finset.finite_toSet F).isClosed_convexHull ℝ

lemma support_depth_nonempty (F : Finset (EuclideanSpace ℝ (Fin 5))) (d : ℝ)
    (hsupport : ∀ x : EuclideanSpace ℝ (Fin 5), ‖x‖ = 1 → ∃ r ∈ F, ⟪r, x⟫ ≤ -d) :
    F.Nonempty := by
  obtain ⟨r, hr, _⟩ :=
    hsupport (EuclideanSpace.single (0 : Fin 5) (1 : ℝ)) (by simp)
  exact ⟨r, hr⟩

lemma depth_duality_forward (F : Finset (EuclideanSpace ℝ (Fin 5))) (d : ℝ) (hd : 0 < d)
    (hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 5)) d ⊆ convexHull ℝ (F : Set _)) :
    ∀ x : EuclideanSpace ℝ (Fin 5), ‖x‖ = 1 → ∃ r ∈ F, ⟪r, x⟫ ≤ -d := by
  intro x hx
  let y : EuclideanSpace ℝ (Fin 5) := (-d) • x
  have hyball : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 5)) d := by
    rw [Metric.mem_closedBall, dist_zero_right]
    simp [y, norm_smul, hx, abs_of_pos hd]
  have hyconv : y ∈ convexHull ℝ (F : Set _) := hball hyball
  have hf : ConcaveOn ℝ Set.univ (fun r : EuclideanSpace ℝ (Fin 5) => ⟪x, r⟫) := by
    simpa using ((innerSL ℝ x).toLinearMap.concaveOn
      (convex_univ : Convex ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin 5)))))
  obtain ⟨r, hrSet, hrle⟩ := hf.exists_le_of_mem_convexHull (by intro z hz; simp) hyconv
  refine ⟨r, hrSet, ?_⟩
  have hyinner : ⟪x, y⟫ = -d := by
    rw [show y = (-d) • x from rfl, inner_smul_right, real_inner_self_eq_norm_sq, hx]
    ring
  rw [← real_inner_comm r x]
  exact le_trans hrle (le_of_eq hyinner)

lemma depth_duality_forward_set (F : Set (EuclideanSpace ℝ (Fin 5))) (d : ℝ) (hd : 0 < d)
    (hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 5)) d ⊆ convexHull ℝ F) :
    ∀ x : EuclideanSpace ℝ (Fin 5), ‖x‖ = 1 → ∃ r ∈ F, ⟪r, x⟫ ≤ -d := by
  intro x hx
  let y : EuclideanSpace ℝ (Fin 5) := (-d) • x
  have hyball : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 5)) d := by
    rw [Metric.mem_closedBall, dist_zero_right]
    simp [y, norm_smul, hx, abs_of_pos hd]
  have hyconv : y ∈ convexHull ℝ F := hball hyball
  have hf : ConcaveOn ℝ Set.univ (fun r : EuclideanSpace ℝ (Fin 5) => ⟪x, r⟫) := by
    simpa using ((innerSL ℝ x).toLinearMap.concaveOn
      (convex_univ : Convex ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin 5)))))
  obtain ⟨r, hrSet, hrle⟩ := hf.exists_le_of_mem_convexHull (by intro z hz; simp) hyconv
  refine ⟨r, hrSet, ?_⟩
  have hyinner : ⟪x, y⟫ = -d := by
    rw [show y = (-d) • x from rfl, inner_smul_right, real_inner_self_eq_norm_sq, hx]
    ring
  rw [← real_inner_comm r x]
  exact le_trans hrle (le_of_eq hyinner)

theorem depth_duality (F : Finset (EuclideanSpace ℝ (Fin 5))) (d : ℝ) (hd : 0 < d) :
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 5)) d ⊆ convexHull ℝ (F : Set _))
      ↔ ∀ x : EuclideanSpace ℝ (Fin 5), ‖x‖ = 1 → ∃ r ∈ F, ⟪r, x⟫ ≤ -d := by
  constructor
  · exact depth_duality_forward F d hd
  · intro hsupport y hy
    by_contra hyK
    obtain ⟨f, u, hfu, huy⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (F : Set (EuclideanSpace ℝ (Fin 5))))
      (finite_flags_convexHull_closed F) hyK
    let z : EuclideanSpace ℝ (Fin 5) := (InnerProductSpace.toDual ℝ
      (EuclideanSpace ℝ (Fin 5))).symm f
    have hf_apply : ∀ v : EuclideanSpace ℝ (Fin 5), f v = ⟪z, v⟫ := by
      intro v
      exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)
        (E := EuclideanSpace ℝ (Fin 5)) (x := v) (y := f)).symm
    obtain ⟨r0, hr0⟩ := support_depth_nonempty F d hsupport
    have hr0K : r0 ∈ convexHull ℝ (F : Set (EuclideanSpace ℝ (Fin 5))) :=
      (subset_convexHull ℝ (F : Set (EuclideanSpace ℝ (Fin 5)))) hr0
    have hr0_lt : f r0 < u := hfu r0 hr0K
    have hz_ne : z ≠ 0 := by
      intro hz0
      have fr0 : f r0 = 0 := by simp [hf_apply, hz0]
      have fy : f y = 0 := by simp [hf_apply, hz0]
      nlinarith
    let xdir : EuclideanSpace ℝ (Fin 5) := (-‖z‖⁻¹ : ℝ) • z
    have hxdir_norm : ‖xdir‖ = 1 := by
      have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
      rw [show xdir = (-‖z‖⁻¹ : ℝ) • z from rfl, norm_smul]
      rw [norm_neg, norm_inv, Real.norm_of_nonneg (le_of_lt hzpos)]
      exact inv_mul_cancel₀ (ne_of_gt hzpos)
    obtain ⟨r, hrF, hrle⟩ := hsupport xdir hxdir_norm
    have hrK : r ∈ convexHull ℝ (F : Set (EuclideanSpace ℝ (Fin 5))) :=
      (subset_convexHull ℝ (F : Set (EuclideanSpace ℝ (Fin 5)))) hrF
    have hfr_lt : f r < u := hfu r hrK
    have hinner_calc : ⟪r, xdir⟫ = -‖z‖⁻¹ * f r := by
      rw [show xdir = (-‖z‖⁻¹ : ℝ) • z from rfl, inner_smul_right]
      rw [real_inner_comm z r, ← hf_apply r]
    have hfr_ge : d * ‖z‖ ≤ f r := by
      rw [hinner_calc] at hrle
      have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
      have hmul := mul_le_mul_of_nonneg_right hrle (le_of_lt hzpos)
      have hzn : ‖z‖ ≠ 0 := ne_of_gt hzpos
      have hc : ‖z‖⁻¹ * ‖z‖ = 1 := inv_mul_cancel₀ hzn
      have heq : (-‖z‖⁻¹ * f r) * ‖z‖ = -f r := by
        calc
          (-‖z‖⁻¹ * f r) * ‖z‖ = -(‖z‖⁻¹ * ‖z‖) * f r := by ring
          _ = -f r := by rw [hc]; ring
      have hmulPrime : -f r ≤ -d * ‖z‖ := by
        rw [heq] at hmul
        exact hmul
      linarith
    have hynorm : ‖y‖ ≤ d := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hy
    have hfy_bound : f y ≤ ‖z‖ * d := by
      rw [hf_apply y]
      have hinner_le : ⟪z, y⟫ ≤ ‖z‖ * ‖y‖ :=
        le_trans (le_abs_self _)
          (by simpa [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) z y))
      have hmul : ‖z‖ * ‖y‖ ≤ ‖z‖ * d :=
        mul_le_mul_of_nonneg_left hynorm (norm_nonneg z)
      exact le_trans hinner_le hmul
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
    nlinarith

/-! ### Lemma 7.1 — `exp` surjective on `SO(3)` with `‖ξ‖ = angle`  (Euler + Rodrigues).
See `SO3AxisAngle.exp_surjective_SO3`. -/

end DepthCylinderTheorem
