import RupertStellatedTetrahedron.Local.EpsilonSlack

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace DepthCylinderTheorem

/-!
## The contact-base cylinder

This is the abstract certificate form of Theorem 9.2. A contact certificate is based at an
arbitrary weak-containment configuration `(W₁,t₀)` rather than the diagonal base `(R₂,0)`.
-/

structure ContactPair
    (V : Finset V3)
    (R₂ W₁ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (t₀ : V2) where
  flag : EuclideanSpace ℝ (Fin 5)
  slackFn : V3 → V2 → ℝ
  decompBound : ∀ ξ : V3, ∀ δt : V2, ∃ Q : ℝ,
    slackFn ξ δt = ⟪flag, relCoord ξ δt⟫ + Q ∧
      |Q| ≤ circumradius V * (1/2 + ‖ξ‖/6) * ‖ξ‖ ^ 2
  strictOfContainment :
    ∀ (R₁ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (t : V2),
      RupertContainment V ({ R₁ := R₁, R₂ := R₂, t := t } : Config V) →
      ∀ (ξ : V3) (δt : V2),
        NormedSpace.exp (skewMatrix ξ) =
          ((R₁ * W₁⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
            Matrix (Fin 3) (Fin 3) ℝ) →
        t = t₀ + δt →
        0 < slackFn ξ δt

def contactFlagOf {V R₂ W₁ t₀} (p : ContactPair V R₂ W₁ t₀) :
    EuclideanSpace ℝ (Fin 5) :=
  p.flag

def contactFlagFinset {V : Finset V3} {R₂ W₁ : Matrix.specialOrthogonalGroup (Fin 3) ℝ}
    {t₀ : V2} (cert : Finset (ContactPair V R₂ W₁ t₀)) :
    Finset (EuclideanSpace ℝ (Fin 5)) := by
  classical
  exact cert.image contactFlagOf

def contactSlack {V R₂ W₁ t₀} (p : ContactPair V R₂ W₁ t₀) (ξ : V3) (δt : V2) :
    ℝ :=
  p.slackFn ξ δt

lemma exists_contact_cert_flag_kill
    {V : Finset V3} {R₂ W₁ : Matrix.specialOrthogonalGroup (Fin 3) ℝ} {t₀ : V2}
    (cert : Finset (ContactPair V R₂ W₁ t₀))
    (d : ℝ) (hd : 0 < d)
    (hcert : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 5)) d ⊆
      convexHull ℝ (contactFlagFinset cert : Set (EuclideanSpace ℝ (Fin 5))))
    (x : EuclideanSpace ℝ (Fin 5)) (hx : x ≠ 0) :
    ∃ p ∈ cert, ⟪contactFlagOf p, x⟫ ≤ -d * ‖x‖ := by
  classical
  let u : EuclideanSpace ℝ (Fin 5) := (‖x‖⁻¹ : ℝ) • x
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖u‖ = 1 := by
    rw [show u = (‖x‖⁻¹ : ℝ) • x from rfl, norm_smul]
    rw [norm_inv, Real.norm_of_nonneg (le_of_lt hxpos)]
    exact inv_mul_cancel₀ (ne_of_gt hxpos)
  obtain ⟨r, hr, hrle⟩ := (depth_duality (contactFlagFinset cert) d hd).mp hcert u hu
  obtain ⟨p, hp, hpr⟩ := by
    simpa [contactFlagFinset] using (Finset.mem_image.mp hr)
  refine ⟨p, hp, ?_⟩
  subst hpr
  have hinner : ⟪contactFlagOf p, u⟫ = ‖x‖⁻¹ * ⟪contactFlagOf p, x⟫ := by
    rw [show u = (‖x‖⁻¹ : ℝ) • x from rfl, inner_smul_right]
  rw [hinner] at hrle
  have hmul := mul_le_mul_of_nonneg_right hrle (le_of_lt hxpos)
  have hneq : ‖x‖ ≠ 0 := ne_of_gt hxpos
  have hc : ‖x‖⁻¹ * ‖x‖ = 1 := inv_mul_cancel₀ hneq
  have heq : (‖x‖⁻¹ * ⟪contactFlagOf p, x⟫) * ‖x‖ = ⟪contactFlagOf p, x⟫ := by
    calc
      (‖x‖⁻¹ * ⟪contactFlagOf p, x⟫) * ‖x‖ =
          (‖x‖⁻¹ * ‖x‖) * ⟪contactFlagOf p, x⟫ := by ring
      _ = ⟪contactFlagOf p, x⟫ := by rw [hc]; ring
  rw [heq] at hmul
  exact hmul

/-- Contact-base cylinder theorem, explicit exponential-coordinate form.

The relative motion is measured from the contact base `(W₁,t₀)`: `R₁ = exp([ξ]×) W₁` and
`t = t₀ + δt`. If the contact flags contain a ball of radius `d`, then any nonzero relative
motion satisfying `d * ‖x‖ > M * ‖ξ‖²` is excluded.
-/
theorem contact_base_cylinder_theorem_of_exp
    (V : Finset V3) (c : Config V)
    (W₁ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (t₀ δt : V2)
    (cert : Finset (ContactPair V c.R₂ W₁ t₀))
    (s₀ d : ℝ) (hd : 0 < d)
    (hcert : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 5)) d ⊆
      convexHull ℝ (contactFlagFinset cert : Set (EuclideanSpace ℝ (Fin 5))))
    (M : ℝ) (hM : M = circumradius V * (1/2 + s₀/6))
    (ξ : V3)
    (hξexp : NormedSpace.exp (skewMatrix ξ) =
      ((c.R₁ * W₁⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ))
    (ht : c.t = t₀ + δt)
    (hs_le : ‖ξ‖ ≤ s₀)
    (hmotion : relCoord ξ δt ≠ 0)
    (hineq : M * ‖ξ‖ ^ 2 < d * ‖relCoord ξ δt‖) :
    ¬ RupertContainment V c := by
  rintro hcont
  set x := relCoord ξ δt with hx_def
  have hx0 : x ≠ 0 := by
    intro hx
    exact hmotion (by simpa [hx_def] using hx)
  obtain ⟨p, _hpCert, hkill⟩ := exists_contact_cert_flag_kill cert d hd hcert x hx0
  obtain ⟨Q, hdecomp, hQbnd⟩ := p.decompBound ξ δt
  have hQ : |Q| ≤ M * ‖ξ‖ ^ 2 := by
    rw [hM]
    have hρ : 0 ≤ circumradius V := circumradius_nonneg V
    have hs2 : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg ‖ξ‖
    have hfac : 1 / 2 + ‖ξ‖ / 6 ≤ 1 / 2 + s₀ / 6 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hfac hρ, hs2, hQbnd]
  have hQle : Q ≤ M * ‖ξ‖ ^ 2 := le_trans (le_abs_self Q) hQ
  have hneg : contactSlack p ξ δt < 0 := by
    have hdecomp' : p.slackFn ξ δt = ⟪p.flag, x⟫ + Q := by
      simpa [hx_def] using hdecomp
    have hkill' : ⟪p.flag, x⟫ ≤ -d * ‖x‖ := by
      simpa [contactFlagOf] using hkill
    have hstep : contactSlack p ξ δt ≤ -d * ‖relCoord ξ δt‖ + M * ‖ξ‖ ^ 2 := by
      dsimp [contactSlack]
      rw [← hx_def]
      nlinarith [hdecomp', hkill', hQle]
    nlinarith
  have hpos : 0 < contactSlack p ξ δt :=
    p.strictOfContainment c.R₁ c.t hcont ξ δt hξexp ht
  exact absurd hpos (not_lt.mpr (le_of_lt hneg))

/-- Contact-base cylinder theorem with the relative `SO(3)` logarithm supplied by
`exp_surjective_SO3`.  The caller still supplies the numerical inequalities for the selected
logarithm from the contact base. -/
theorem contact_base_cylinder_theorem
    (V : Finset V3) (c : Config V)
    (W₁ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (t₀ δt : V2)
    (cert : Finset (ContactPair V c.R₂ W₁ t₀))
    (s₀ d : ℝ) (hd : 0 < d)
    (hcert : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 5)) d ⊆
      convexHull ℝ (contactFlagFinset cert : Set (EuclideanSpace ℝ (Fin 5))))
    (M : ℝ) (hM : M = circumradius V * (1/2 + s₀/6))
    (ht : c.t = t₀ + δt)
    (hlog :
      ∀ ξ : V3,
        NormedSpace.exp (skewMatrix ξ) =
            ((c.R₁ * W₁⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
              Matrix (Fin 3) (Fin 3) ℝ) →
          ‖ξ‖ = rotationAngleOf (c.R₁ * W₁⁻¹) →
            ‖ξ‖ ≤ s₀ ∧ relCoord ξ δt ≠ 0 ∧
              M * ‖ξ‖ ^ 2 < d * ‖relCoord ξ δt‖) :
    ¬ RupertContainment V c := by
  obtain ⟨ξ, hξexp, hξnorm⟩ := exp_surjective_SO3 (c.R₁ * W₁⁻¹)
  obtain ⟨hs_le, hmotion, hineq⟩ := hlog ξ hξexp hξnorm
  exact contact_base_cylinder_theorem_of_exp V c W₁ t₀ δt cert s₀ d hd hcert M hM
    ξ hξexp ht hs_le hmotion hineq

end DepthCylinderTheorem
