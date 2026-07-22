import RupertStellatedTetrahedron.Local.EpsilonSlack

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace DepthCylinderTheorem

/-!
## Support-offset certificates

This file records the Lean-facing interface for the support-offset version of the local
epsilon-slack argument. The concrete offsets are intended to be emitted by the external
certificate checker; until that format is fixed, the soundness conditions are explicit fields.
-/

/-- A supporting halfspace for the outer shadow, written in the convention used by slacks. -/
def supportHalfspace (n : V2) (offset : ℝ) : Set V2 :=
  {q | offset ≤ ⟪n, q⟫}

/-- The signed support slack of a planar point against a support offset. -/
def supportSlack (n : V2) (offset : ℝ) (q : V2) : ℝ :=
  n 0 * q 0 + n 1 * q 1 - offset

lemma mem_supportHalfspace_iff_supportSlack_nonneg (n : V2) (offset : ℝ) (q : V2) :
    q ∈ supportHalfspace n offset ↔ 0 ≤ supportSlack n offset q := by
  rw [supportHalfspace, supportSlack]
  change offset ≤ ⟪n, q⟫ ↔ 0 ≤ n 0 * q 0 + n 1 * q 1 - offset
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two]
  constructor <;> intro h <;> nlinarith

/-- Proof-carrying support offset for one outer shadow. -/
structure SupportOffset (V : Finset V3)
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) where
  normal : V2
  offset : ℝ
  supportsShadow : ∀ q ∈ shadow V R₂, q ∈ supportHalfspace normal offset

lemma shadow_subset_supportHalfspace {V : Finset V3}
    {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ} (s : SupportOffset V R₂) :
    shadow V R₂ ⊆ supportHalfspace s.normal s.offset := by
  intro q hq
  exact s.supportsShadow q hq

/-- Certificate form of the support-offset local pair. -/
structure SupportOffsetPair (V : Finset V3)
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (ε : ℝ) where
  support : SupportOffset V R₂
  vertex : V3
  vertex_mem : vertex ∈ V
  flag : EuclideanSpace ℝ (Fin 5)
  slackFn : V3 → V2 → ℝ
  baseSlackBound : ∀ ξ : V3, ∀ t : V2, ∃ Q : ℝ,
    slackFn ξ t ≤ ε + ⟪flag, relCoord ξ t⟫ + Q ∧
      |Q| ≤ circumradius V * (1/2 + ‖ξ‖/6) * ‖ξ‖ ^ 2
  slack_eq_supportSlack :
    ∀ (R₁ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (t : V2) (ξ : V3),
      NormedSpace.exp (skewMatrix ξ) =
        ((R₁ * R₂⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
          Matrix (Fin 3) (Fin 3) ℝ) →
      slackFn ξ t =
        supportSlack support.normal support.offset
          (proj (Matrix.toLpLin 2 2 (R₁ : Matrix (Fin 3) (Fin 3) ℝ) vertex) + t)
  strictInteriorSupport :
    ∀ q ∈ interior (shadow V R₂), 0 < supportSlack support.normal support.offset q

theorem SupportOffsetPair.supportSound {V : Finset V3}
    {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ} {ε : ℝ}
    (p : SupportOffsetPair V R₂ ε) :
    ∀ (R₁ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (t : V2),
      RupertContainment V ({ R₁ := R₁, R₂ := R₂, t := t } : Config V) →
      ∀ ξ : V3,
        NormedSpace.exp (skewMatrix ξ) =
          ((R₁ * R₂⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
            Matrix (Fin 3) (Fin 3) ℝ) →
        0 < p.slackFn ξ t := by
  intro R₁ t hcont ξ hξexp
  rw [p.slack_eq_supportSlack R₁ t ξ hξexp]
  exact p.strictInteriorSupport
    (proj (Matrix.toLpLin 2 2 (R₁ : Matrix (Fin 3) (Fin 3) ℝ) p.vertex) + t)
    (hcont p.vertex p.vertex_mem)

/-- A support-offset pair is the same local data expected by the epsilon-slack theorem. -/
def SupportOffsetPair.toEpsilonPair {V : Finset V3}
    {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ} {ε : ℝ}
    (p : SupportOffsetPair V R₂ ε) : EpsilonPair V R₂ ε where
  flag := p.flag
  slackFn := p.slackFn
  baseSlackBound := p.baseSlackBound
  strictOfContainment := p.supportSound

def supportOffsetToEpsilonCert {V : Finset V3}
    {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ} {ε : ℝ}
    (cert : Finset (SupportOffsetPair V R₂ ε)) :
    Finset (EpsilonPair V R₂ ε) := by
  classical
  exact cert.image SupportOffsetPair.toEpsilonPair

theorem supportOffsetPair_is_epsilonPair {V : Finset V3}
    {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ} {ε : ℝ}
    (p : SupportOffsetPair V R₂ ε) :
    (p.toEpsilonPair : EpsilonPair V R₂ ε).flag = p.flag := rfl

theorem supportOffsetToEpsilonCert_flags
    {V : Finset V3} {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ} {ε : ℝ}
    (cert : Finset (SupportOffsetPair V R₂ ε)) :
    epsilonFlagFinset (supportOffsetToEpsilonCert cert) =
      cert.image (fun p : SupportOffsetPair V R₂ ε => p.flag) := by
  classical
  ext r
  constructor
  · intro hr
    rw [epsilonFlagFinset, supportOffsetToEpsilonCert] at hr
    obtain ⟨pε, hpε, hpεr⟩ := Finset.mem_image.mp hr
    obtain ⟨p, hp, hp⟩ := Finset.mem_image.mp hpε
    subst hp
    have hflag : p.flag = r := by
      rw [← supportOffsetPair_is_epsilonPair p]
      simpa [epsilonFlagOf] using hpεr
    exact Finset.mem_image.mpr ⟨p, hp, hflag⟩
  · intro hr
    obtain ⟨p, hp, hpr⟩ := Finset.mem_image.mp hr
    rw [epsilonFlagFinset, supportOffsetToEpsilonCert]
    exact Finset.mem_image.mpr
      ⟨p.toEpsilonPair, Finset.mem_image.mpr ⟨p, hp, rfl⟩,
        by simpa [epsilonFlagOf, hpr]⟩

/-- Support-offset cylinder theorem, routed through the epsilon-slack theorem. -/
theorem support_offset_cylinder_theorem
    (V : Finset V3) (c : Config V) (ε : ℝ)
    (cert : Finset (SupportOffsetPair V c.R₂ ε))
    (s₀ d : ℝ) (hd : 0 < d)
    (hcert : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 5)) d ⊆
      convexHull ℝ
        ((cert.image (fun p : SupportOffsetPair V c.R₂ ε => p.flag)) :
          Set (EuclideanSpace ℝ (Fin 5))))
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
  apply epsilon_slack_cylinder_theorem V c ε (supportOffsetToEpsilonCert cert) s₀ d hd
  · rwa [supportOffsetToEpsilonCert_flags]
  · exact hM
  · exact hlog

end DepthCylinderTheorem
