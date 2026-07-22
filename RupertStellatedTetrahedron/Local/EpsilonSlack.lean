import RupertStellatedTetrahedron.DepthCylinderTheorem.Assembly

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace DepthCylinderTheorem

/-!
## The epsilon-slack cylinder

This is the abstract certificate form of Theorem 9.1. An epsilon pair is a proof-carrying
near-active flag: its base slack is not necessarily zero, but is bounded by `ε`.
-/

structure EpsilonPair (V : Finset V3) (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (ε : ℝ) where
  flag : EuclideanSpace ℝ (Fin 5)
  slackFn : V3 → V2 → ℝ
  baseSlackBound : ∀ ξ : V3, ∀ t : V2, ∃ Q : ℝ,
    slackFn ξ t ≤ ε + ⟪flag, relCoord ξ t⟫ + Q ∧
      |Q| ≤ circumradius V * (1/2 + ‖ξ‖/6) * ‖ξ‖ ^ 2
  strictOfContainment :
    ∀ (R₁ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (t : V2),
      RupertContainment V ({ R₁ := R₁, R₂ := R₂, t := t } : Config V) →
      ∀ ξ : V3,
        NormedSpace.exp (skewMatrix ξ) =
          ((R₁ * R₂⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
            Matrix (Fin 3) (Fin 3) ℝ) →
        0 < slackFn ξ t

def epsilonFlagOf {V R₂ ε} (p : EpsilonPair V R₂ ε) : EuclideanSpace ℝ (Fin 5) :=
  p.flag

def epsilonFlagFinset {V : Finset V3} {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ}
    {ε : ℝ} (cert : Finset (EpsilonPair V R₂ ε)) :
    Finset (EuclideanSpace ℝ (Fin 5)) := by
  classical
  exact cert.image epsilonFlagOf

def epsilonSlack {V R₂ ε} (p : EpsilonPair V R₂ ε) (ξ : V3) (t : V2) : ℝ :=
  p.slackFn ξ t

lemma exists_epsilon_cert_flag_kill
    {V : Finset V3} {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ} {ε : ℝ}
    (cert : Finset (EpsilonPair V R₂ ε))
    (d : ℝ) (hd : 0 < d)
    (hcert : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 5)) d ⊆
      convexHull ℝ (epsilonFlagFinset cert : Set (EuclideanSpace ℝ (Fin 5))))
    (x : EuclideanSpace ℝ (Fin 5)) (hx : x ≠ 0) :
    ∃ p ∈ cert, ⟪epsilonFlagOf p, x⟫ ≤ -d * ‖x‖ := by
  classical
  let u : EuclideanSpace ℝ (Fin 5) := (‖x‖⁻¹ : ℝ) • x
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖u‖ = 1 := by
    rw [show u = (‖x‖⁻¹ : ℝ) • x from rfl, norm_smul]
    rw [norm_inv, Real.norm_of_nonneg (le_of_lt hxpos)]
    exact inv_mul_cancel₀ (ne_of_gt hxpos)
  obtain ⟨r, hr, hrle⟩ := (depth_duality (epsilonFlagFinset cert) d hd).mp hcert u hu
  obtain ⟨p, hp, hpr⟩ := by
    simpa [epsilonFlagFinset] using (Finset.mem_image.mp hr)
  refine ⟨p, hp, ?_⟩
  subst hpr
  have hinner : ⟪epsilonFlagOf p, u⟫ = ‖x‖⁻¹ * ⟪epsilonFlagOf p, x⟫ := by
    rw [show u = (‖x‖⁻¹ : ℝ) • x from rfl, inner_smul_right]
  rw [hinner] at hrle
  have hmul := mul_le_mul_of_nonneg_right hrle (le_of_lt hxpos)
  have hneq : ‖x‖ ≠ 0 := ne_of_gt hxpos
  have hc : ‖x‖⁻¹ * ‖x‖ = 1 := inv_mul_cancel₀ hneq
  have heq : (‖x‖⁻¹ * ⟪epsilonFlagOf p, x⟫) * ‖x‖ = ⟪epsilonFlagOf p, x⟫ := by
    calc
      (‖x‖⁻¹ * ⟪epsilonFlagOf p, x⟫) * ‖x‖ =
          (‖x‖⁻¹ * ‖x‖) * ⟪epsilonFlagOf p, x⟫ := by ring
      _ = ⟪epsilonFlagOf p, x⟫ := by rw [hc]; ring
  rw [heq] at hmul
  exact hmul

/-- Epsilon-slack cylinder theorem, explicit exponential-coordinate form.

If the epsilon-active certificate contains a ball of radius `d`, then any motion satisfying
`d * ‖x‖ > ε + M * ‖ξ‖²` is excluded. This is uniform in translation because the residual bound is.
-/
theorem epsilon_slack_cylinder_theorem_of_exp
    (V : Finset V3) (c : Config V) (ε : ℝ)
    (cert : Finset (EpsilonPair V c.R₂ ε))
    (s₀ d : ℝ) (hd : 0 < d)
    (hcert : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 5)) d ⊆
      convexHull ℝ (epsilonFlagFinset cert : Set (EuclideanSpace ℝ (Fin 5))))
    (M : ℝ) (hM : M = circumradius V * (1/2 + s₀/6))
    (ξ : V3)
    (hξexp : NormedSpace.exp (skewMatrix ξ) =
      ((c.R₁ * c.R₂⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ))
    (hs_le : ‖ξ‖ ≤ s₀)
    (hmotion : relCoord ξ c.t ≠ 0)
    (hineq : ε + M * ‖ξ‖ ^ 2 < d * ‖relCoord ξ c.t‖) :
    ¬ RupertContainment V c := by
  rintro hcont
  set x := relCoord ξ c.t with hx_def
  have hx0 : x ≠ 0 := by
    intro hx
    exact hmotion (by simpa [hx_def] using hx)
  obtain ⟨p, _hpCert, hkill⟩ := exists_epsilon_cert_flag_kill cert d hd hcert x hx0
  obtain ⟨Q, hdecomp, hQbnd⟩ := p.baseSlackBound ξ c.t
  have hQ : |Q| ≤ M * ‖ξ‖ ^ 2 := by
    rw [hM]
    have hρ : 0 ≤ circumradius V := circumradius_nonneg V
    have hs2 : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg ‖ξ‖
    have hfac : 1 / 2 + ‖ξ‖ / 6 ≤ 1 / 2 + s₀ / 6 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hfac hρ, hs2, hQbnd]
  have hQle : Q ≤ M * ‖ξ‖ ^ 2 := le_trans (le_abs_self Q) hQ
  have hneg : epsilonSlack p ξ c.t < 0 := by
    have hdecomp' : p.slackFn ξ c.t ≤ ε + ⟪p.flag, x⟫ + Q := by
      simpa [hx_def] using hdecomp
    have hkill' : ⟪p.flag, x⟫ ≤ -d * ‖x‖ := by
      simpa [epsilonFlagOf] using hkill
    have hstep : epsilonSlack p ξ c.t ≤ ε - d * ‖relCoord ξ c.t‖ + M * ‖ξ‖ ^ 2 := by
      dsimp [epsilonSlack]
      rw [← hx_def]
      nlinarith [hdecomp', hkill', hQle]
    nlinarith
  have hpos : 0 < epsilonSlack p ξ c.t := p.strictOfContainment c.R₁ c.t hcont ξ hξexp
  exact absurd hpos (not_lt.mpr (le_of_lt hneg))

/-- Epsilon-slack cylinder theorem with the `SO(3)` logarithm supplied by
`exp_surjective_SO3`.  The caller still supplies the numerical inequalities for the selected
logarithm. -/
theorem epsilon_slack_cylinder_theorem
    (V : Finset V3) (c : Config V) (ε : ℝ)
    (cert : Finset (EpsilonPair V c.R₂ ε))
    (s₀ d : ℝ) (hd : 0 < d)
    (hcert : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 5)) d ⊆
      convexHull ℝ (epsilonFlagFinset cert : Set (EuclideanSpace ℝ (Fin 5))))
    (M : ℝ) (hM : M = circumradius V * (1/2 + s₀/6))
    (hlog :
      ∀ ξ : V3,
        NormedSpace.exp (skewMatrix ξ) =
            ((c.R₁ * c.R₂⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
              Matrix (Fin 3) (Fin 3) ℝ) →
          ‖ξ‖ = rotationAngleOf (c.R₁ * c.R₂⁻¹) →
            ‖ξ‖ ≤ s₀ ∧ relCoord ξ c.t ≠ 0 ∧
              ε + M * ‖ξ‖ ^ 2 < d * ‖relCoord ξ c.t‖) :
    ¬ RupertContainment V c := by
  obtain ⟨ξ, hξexp, hξnorm⟩ := exp_surjective_SO3 (c.R₁ * c.R₂⁻¹)
  obtain ⟨hs_le, hmotion, hineq⟩ := hlog ξ hξexp hξnorm
  exact epsilon_slack_cylinder_theorem_of_exp V c ε cert s₀ d hd hcert M hM
    ξ hξexp hs_le hmotion hineq

end DepthCylinderTheorem
