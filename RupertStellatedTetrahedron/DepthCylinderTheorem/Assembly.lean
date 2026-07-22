import RupertStellatedTetrahedron.DepthCylinderTheorem.Duality
import RupertStellatedTetrahedron.DepthCylinderTheorem.SO3AxisAngle

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace DepthCylinderTheorem

lemma containment_imp_slack_pos {V : Finset V3} {c : Config V}
    (hcont : RupertContainment V c) (ξ : V3)
    (hξ : NormedSpace.exp (skewMatrix ξ) =
      ((c.R₁ * c.R₂⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ))
    (p : ActivePair V c.R₂) :
    0 < slack p ξ c.t := by
  exact p.strictOfContainment c.R₁ c.t hcont ξ hξ

/-- Depth-duality packaged for the full active-pair range: if the radius-`d` ball is contained in
    the convex hull of all active flags, then every nonzero direction is killed by some flag. -/
lemma exists_flag_kill {V : Finset V3} {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ}
    (d : ℝ) (hd : 0 < d)
    (hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 5)) d ⊆
      convexHull ℝ (Set.range (flagOf : ActivePair V R₂ → EuclideanSpace ℝ (Fin 5))))
    (x : EuclideanSpace ℝ (Fin 5)) (hx : x ≠ 0) :
    ∃ p : ActivePair V R₂, ⟪flagOf p, x⟫ ≤ -d * ‖x‖ := by
  let u : EuclideanSpace ℝ (Fin 5) := (‖x‖⁻¹ : ℝ) • x
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖u‖ = 1 := by
    rw [show u = (‖x‖⁻¹ : ℝ) • x from rfl, norm_smul]
    rw [norm_inv, Real.norm_of_nonneg (le_of_lt hxpos)]
    exact inv_mul_cancel₀ (ne_of_gt hxpos)
  obtain ⟨r, hr, hrle⟩ := depth_duality_forward_set
    (Set.range (flagOf : ActivePair V R₂ → EuclideanSpace ℝ (Fin 5))) d hd hball u hu
  obtain ⟨p, hpr⟩ := Set.mem_range.mp hr
  refine ⟨p, ?_⟩
  subst hpr
  have hinner : ⟪flagOf p, u⟫ = ‖x‖⁻¹ * ⟪flagOf p, x⟫ := by
    rw [show u = (‖x‖⁻¹ : ℝ) • x from rfl, inner_smul_right]
  rw [hinner] at hrle
  have hmul := mul_le_mul_of_nonneg_right hrle (le_of_lt hxpos)
  have hneq : ‖x‖ ≠ 0 := ne_of_gt hxpos
  have hc : ‖x‖⁻¹ * ‖x‖ = 1 := inv_mul_cancel₀ hneq
  have heq : (‖x‖⁻¹ * ⟪flagOf p, x⟫) * ‖x‖ = ⟪flagOf p, x⟫ := by
    calc
      (‖x‖⁻¹ * ⟪flagOf p, x⟫) * ‖x‖ =
          (‖x‖⁻¹ * ‖x‖) * ⟪flagOf p, x⟫ := by ring
      _ = ⟪flagOf p, x⟫ := by rw [hc]; ring
  rw [heq] at hmul
  exact hmul

lemma exists_cert_flag_kill {V : Finset V3} {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ}
    (cert : Finset (ActivePair V R₂))
    (d : ℝ) (hd : 0 < d)
    (hcert : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 5)) d ⊆
      convexHull ℝ (flagFinset cert : Set (EuclideanSpace ℝ (Fin 5))))
    (x : EuclideanSpace ℝ (Fin 5)) (hx : x ≠ 0) :
    ∃ p ∈ cert, ⟪flagOf p, x⟫ ≤ -d * ‖x‖ := by
  classical
  let u : EuclideanSpace ℝ (Fin 5) := (‖x‖⁻¹ : ℝ) • x
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖u‖ = 1 := by
    rw [show u = (‖x‖⁻¹ : ℝ) • x from rfl, norm_smul]
    rw [norm_inv, Real.norm_of_nonneg (le_of_lt hxpos)]
    exact inv_mul_cancel₀ (ne_of_gt hxpos)
  obtain ⟨r, hr, hrle⟩ := (depth_duality (flagFinset cert) d hd).mp hcert u hu
  obtain ⟨p, hp, hpr⟩ := by
    simpa [flagFinset] using (Finset.mem_image.mp hr)
  refine ⟨p, hp, ?_⟩
  subst hpr
  have hinner : ⟪flagOf p, u⟫ = ‖x‖⁻¹ * ⟪flagOf p, x⟫ := by
    rw [show u = (‖x‖⁻¹ : ℝ) • x from rfl, inner_smul_right]
  rw [hinner] at hrle
  have hmul := mul_le_mul_of_nonneg_right hrle (le_of_lt hxpos)
  have hneq : ‖x‖ ≠ 0 := ne_of_gt hxpos
  have hc : ‖x‖⁻¹ * ‖x‖ = 1 := inv_mul_cancel₀ hneq
  have heq : (‖x‖⁻¹ * ⟪flagOf p, x⟫) * ‖x‖ = ⟪flagOf p, x⟫ := by
    calc
      (‖x‖⁻¹ * ⟪flagOf p, x⟫) * ‖x‖ =
          (‖x‖⁻¹ * ‖x‖) * ⟪flagOf p, x⟫ := by ring
      _ = ⟪flagOf p, x⟫ := by rw [hc]; ring
  rw [heq] at hmul
  exact hmul

/-- Lemma 4.1 + 5.1 for one active pair: `slack = ⟪r,x⟫ + Q` with `|Q| ≤ ρ(1/2+‖ξ‖/6)‖ξ‖²`
    (uniform in `t`, since `Q` is `t`-independent). -/
lemma slack_decomp {V : Finset V3} {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ}
    (p : ActivePair V R₂) (ξ : V3) (t : V2) :
    ∃ Q : ℝ, slack p ξ t = ⟪flagOf p, relCoord ξ t⟫ + Q ∧
      |Q| ≤ circumradius V * (1/2 + ‖ξ‖/6) * ‖ξ‖ ^ 2 := by
  exact p.decompBound ξ t

/-! ## Theorem 8.1 — The Depth–Cylinder Theorem -/

/-- Certificate form of the Depth–Cylinder Theorem.

This is the executable assembly used by the paper's certificates: if a finite certified subset of
active flags contains the ball `B(0,d_lo)` in its convex hull, then every nonzero cylinder motion
with sufficiently small relative angle is excluded, uniformly over translations. -/
theorem depth_cylinder_theorem_cert_of_exp
    (V : Finset V3) (c : Config V)
    (cert : Finset (ActivePair V c.R₂))
    (s₀ d_lo : ℝ) (hd : 0 < d_lo)
    (hcert : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 5)) d_lo ⊆
      convexHull ℝ (flagFinset cert : Set (EuclideanSpace ℝ (Fin 5))))
    (M : ℝ) (hM : M = circumradius V * (1/2 + s₀/6)) (hMpos : 0 < M)
    (hangle : relAngle c.R₁ c.R₂ < min s₀ (d_lo / M))
    (hmotion : relAngle c.R₁ c.R₂ ≠ 0 ∨ c.t ≠ 0)
    (hexp : ∃ ξ : V3,
      NormedSpace.exp (skewMatrix ξ) =
        ((c.R₁ * c.R₂⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
          Matrix (Fin 3) (Fin 3) ℝ) ∧
      ‖ξ‖ = rotationAngleOf (c.R₁ * c.R₂⁻¹)) :
    ¬ RupertContainment V c := by
  rintro hcont
  set s := relAngle c.R₁ c.R₂ with hs_def
  obtain ⟨ξ, hξexp, hξnorm'⟩ := hexp
  have hξnorm : ‖ξ‖ = s := by
    rw [hξnorm', hs_def, relAngle]
  have hs_nonneg : 0 ≤ s := by
    rw [← hξnorm]
    exact norm_nonneg ξ
  set x := relCoord ξ c.t with hx_def
  have hxge : s ≤ ‖x‖ := hξnorm ▸ angle_le_relCoord_norm ξ c.t
  have hx0 : x ≠ 0 := by
    intro hx
    have hzt : ξ = 0 ∧ c.t = 0 := by
      exact (relCoord_eq_zero_iff ξ c.t).mp (by simpa [hx_def] using hx)
    rcases hzt with ⟨hξ0, ht0⟩
    have hs0 : s = 0 := by
      rw [← hξnorm, hξ0, norm_zero]
    rcases hmotion with hs_ne | ht_ne
    · exact hs_ne hs0
    · exact ht_ne ht0
  obtain ⟨p, _hpCert, hkill⟩ := exists_cert_flag_kill cert d_lo hd hcert x hx0
  obtain ⟨Q, hdecomp, hQbnd⟩ := slack_decomp p ξ c.t
  have hs_le_s₀ : s ≤ s₀ := le_of_lt (lt_of_lt_of_le hangle (min_le_left _ _))
  have hQ : |Q| ≤ M * s ^ 2 := by
    rw [hξnorm] at hQbnd
    rw [hM]
    have hρ : 0 ≤ circumradius V := circumradius_nonneg V
    have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
    have hfac : 1 / 2 + s / 6 ≤ 1 / 2 + s₀ / 6 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hfac hρ, hs2, hQbnd]
  have hneg : slack p ξ c.t < 0 := by
    have hQle : Q ≤ M * s ^ 2 := le_trans (le_abs_self Q) hQ
    have hstep_norm : slack p ξ c.t ≤ -d_lo * ‖x‖ + M * s ^ 2 := by
      rw [hdecomp]
      nlinarith [hkill, hQle]
    by_cases hs_zero : s = 0
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hquad : M * s ^ 2 = 0 := by rw [hs_zero]; ring
      nlinarith [hstep_norm, hxpos, hd, hquad]
    · have hs_pos : 0 < s := lt_of_le_of_ne hs_nonneg (Ne.symm hs_zero)
      have hxx : -d_lo * ‖x‖ ≤ -d_lo * s := by nlinarith [hxge, hd]
      have hstep : slack p ξ c.t ≤ -d_lo * s + M * s ^ 2 := by
        nlinarith [hstep_norm, hxx]
      have hMs : M * s ^ 2 < d_lo * s := by
        have hslt : s < d_lo / M := lt_of_lt_of_le hangle (min_le_right _ _)
        have h1 : M * s < d_lo := by
          rw [lt_div_iff₀ hMpos] at hslt
          nlinarith
        nlinarith
      nlinarith [hstep, hMs]
  have hpos : 0 < slack p ξ c.t := containment_imp_slack_pos hcont ξ hξexp p
  exact absurd hpos (not_lt.mpr (le_of_lt hneg))

theorem depth_cylinder_theorem_cert
    (V : Finset V3) (c : Config V)
    (cert : Finset (ActivePair V c.R₂))
    (s₀ d_lo : ℝ) (hd : 0 < d_lo)
    (hcert : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 5)) d_lo ⊆
      convexHull ℝ (flagFinset cert : Set (EuclideanSpace ℝ (Fin 5))))
    (M : ℝ) (hM : M = circumradius V * (1/2 + s₀/6)) (hMpos : 0 < M)
    (hangle : relAngle c.R₁ c.R₂ < min s₀ (d_lo / M))
    (hmotion : relAngle c.R₁ c.R₂ ≠ 0 ∨ c.t ≠ 0) :
    ¬ RupertContainment V c := by
  exact depth_cylinder_theorem_cert_of_exp V c cert s₀ d_lo hd hcert M hM hMpos hangle
    hmotion (exp_surjective_SO3 (c.R₁ * c.R₂⁻¹))

/-- If the outer flag system contains `B(0,d_lo)` in its convex hull, then for `M = ρ(1/2+s₀/6)` there is
NO strict Rupert containment for any inner rotation within relative angle `min(s₀, d_lo/M)` of the
outer rotation and ANY translation `t`. -/
theorem depth_cylinder_theorem
    (V : Finset V3) (c : Config V)
    (s₀ d_lo : ℝ) (hs₀ : 0 < s₀) (hd : 0 < d_lo)
    (hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 5)) d_lo ⊆
      convexHull ℝ (Set.range (flagOf : ActivePair V c.R₂ → EuclideanSpace ℝ (Fin 5))))
    (M : ℝ) (hM : M = circumradius V * (1/2 + s₀/6)) (hMpos : 0 < M)
    (hangle : relAngle c.R₁ c.R₂ < min s₀ (d_lo / M))
    (hmotion : relAngle c.R₁ c.R₂ ≠ 0 ∨ c.t ≠ 0) :
    ¬ RupertContainment V c := by
  rintro hcont
  -- s := relative angle, x := relCoord ξ t.
  set s := relAngle c.R₁ c.R₂ with hs_def
  -- (1) Lemma 7.1: write `R₁R₂ᵀ = exp[ξ]×` with `‖ξ‖ = s`.
  obtain ⟨ξ, hξexp, hξnorm'⟩ := exp_surjective_SO3 (c.R₁ * c.R₂⁻¹)
  have hξnorm : ‖ξ‖ = s := by
    rw [hξnorm', hs_def, relAngle]
  have hs_nonneg : 0 ≤ s := by
    rw [← hξnorm]
    exact norm_nonneg ξ
  set x := relCoord ξ c.t with hx_def
  -- (2) `‖ξ‖ ≤ ‖x‖`, and nonzero cylinder motion gives `x ≠ 0`.
  have hxge : s ≤ ‖x‖ := hξnorm ▸ angle_le_relCoord_norm ξ c.t
  have hx0 : x ≠ 0 := by
    intro hx
    have hzt : ξ = 0 ∧ c.t = 0 := by
      exact (relCoord_eq_zero_iff ξ c.t).mp (by simpa [hx_def] using hx)
    rcases hzt with ⟨hξ0, ht0⟩
    have hs0 : s = 0 := by
      rw [← hξnorm, hξ0, norm_zero]
    rcases hmotion with hs_ne | ht_ne
    · exact hs_ne hs0
    · exact ht_ne ht0
  -- (3) Lemma 6.1 (packaged): pick an active flag with `⟪r,x⟫ ≤ -d_lo‖x‖`.
  obtain ⟨p, hkill⟩ := exists_flag_kill d_lo hd hball x hx0
  -- (4) Lemma 4.1+5.1: `slack = ⟪r,x⟫ + Q`, `|Q| ≤ M·s²`  (using `‖ξ‖ = s ≤ s₀` for M-monotonicity).
  obtain ⟨Q, hdecomp, hQbnd⟩ := slack_decomp p ξ c.t
  have hs_le_s₀ : s ≤ s₀ := le_of_lt (lt_of_lt_of_le hangle (min_le_left _ _))
  have hQ : |Q| ≤ M * s ^ 2 := by
    -- `ρ(1/2+‖ξ‖/6)‖ξ‖² ≤ ρ(1/2+s₀/6)s² = M s²` since `‖ξ‖ = s ≤ s₀`
    rw [hξnorm] at hQbnd
    rw [hM]
    have hρ : 0 ≤ circumradius V := circumradius_nonneg V
    have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
    have hs₀_nonneg : 0 ≤ s₀ := le_of_lt hs₀
    have hfac : 1 / 2 + s / 6 ≤ 1 / 2 + s₀ / 6 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hfac hρ, hs2, hQbnd]
  -- (5) Combine to `slack p ξ t < 0`.
  have hneg : slack p ξ c.t < 0 := by
    have hQle : Q ≤ M * s ^ 2 := le_trans (le_abs_self Q) hQ
    have hstep_norm : slack p ξ c.t ≤ -d_lo * ‖x‖ + M * s ^ 2 := by
      rw [hdecomp]
      nlinarith [hkill, hQle]
    by_cases hs_zero : s = 0
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hquad : M * s ^ 2 = 0 := by rw [hs_zero]; ring
      nlinarith [hstep_norm, hxpos, hd, hquad]
    · have hs_pos : 0 < s := lt_of_le_of_ne hs_nonneg (Ne.symm hs_zero)
      have hxx : -d_lo * ‖x‖ ≤ -d_lo * s := by nlinarith [hxge, hd]
      have hstep : slack p ξ c.t ≤ -d_lo * s + M * s ^ 2 := by
        nlinarith [hstep_norm, hxx]
      -- `s < d_lo/M ⟹ M s² < d_lo s ⟹ -d_lo s + M s² < 0`
      have hMs : M * s ^ 2 < d_lo * s := by
        have hslt : s < d_lo / M := lt_of_lt_of_le hangle (min_le_right _ _)
        have h1 : M * s < d_lo := by
          rw [lt_div_iff₀ hMpos] at hslt
          nlinarith
        nlinarith
      nlinarith [hstep, hMs]
  -- (6) Contradiction with eq. (2.1): containment ⟹ `slack p ξ t > 0`.
  have hpos : 0 < slack p ξ c.t := containment_imp_slack_pos hcont ξ hξexp p
  exact absurd hpos (not_lt.mpr (le_of_lt hneg))

/-! ### Extensions

The ε-slack, contact-base, and support-offset variants are routed through this theorem in the
`RupertStellatedTetrahedron.Local` modules.
-/


end DepthCylinderTheorem
