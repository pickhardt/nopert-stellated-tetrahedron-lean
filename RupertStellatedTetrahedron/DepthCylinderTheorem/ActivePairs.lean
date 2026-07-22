import RupertStellatedTetrahedron.DepthCylinderTheorem.Core

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace DepthCylinderTheorem

/-! ### The active-flag / slack layer

An *active pair* is an edge/incident-vertex datum of the outer shadow. Here it is represented by the
two pieces of data consumed by the cylinder assembly: a five-dimensional flag and the corresponding
containment slack, together with the exact decomposition/remainder bound interface.
-/

structure ActivePair (V : Finset V3) (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) where
  flag : EuclideanSpace ℝ (Fin 5)
  slackFn : V3 → V2 → ℝ
  decompBound : ∀ (ξ : V3) (t : V2),
    ∃ Q : ℝ, slackFn ξ t = ⟪flag, relCoord ξ t⟫ + Q ∧
      |Q| ≤ circumradius V * (1/2 + ‖ξ‖/6) * ‖ξ‖ ^ 2
  strictOfContainment :
    ∀ (R₁ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (t : V2),
      RupertContainment V ({ R₁ := R₁, R₂ := R₂, t := t } : Config V) →
      ∀ ξ : V3,
        NormedSpace.exp (skewMatrix ξ) =
          ((R₁ * R₂⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
            Matrix (Fin 3) (Fin 3) ℝ) →
        0 < slackFn ξ t

/-- Flag vector `r_{i,j} ∈ ℝ⁵` of an active pair. -/
def flagOf {V R₂} (p : ActivePair V R₂) : EuclideanSpace ℝ (Fin 5) :=
  p.flag

/-- The finite set of flag vectors used by a depth certificate. -/
def flagFinset {V : Finset V3} {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ}
    (cert : Finset (ActivePair V R₂)) : Finset (EuclideanSpace ℝ (Fin 5)) := by
  classical
  exact cert.image flagOf

/-- Containment slack `h_{i,j}(ξ,t)` for inner motion `exp[ξ]×` and translation `t`. -/
def slack {V R₂} (p : ActivePair V R₂) (ξ : V3) (t : V2) : ℝ :=
  p.slackFn ξ t

/-- Depth: the largest `d` with `B(0,d) ⊆ conv {flagOf p}`. `depth > 0` is the Gordan-dual
    first-order rigidity certificate. -/
def depth (V : Finset V3) (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) : ℝ :=
  sSup {d : ℝ | Metric.closedBall (0 : EuclideanSpace ℝ (Fin 5)) d ⊆
    convexHull ℝ (Set.range (flagOf : ActivePair V R₂ → EuclideanSpace ℝ (Fin 5)))}

lemma proj_skewApply_relCoord_zero (ξ w : V3) :
    proj (skewApply ξ w) 0 = relCoord ξ 0 2 * w 0 + relCoord ξ 0 1 * w 2 := by
  simp [proj, skewApply, skewMatrix, relCoord, Matrix.toLpLin_apply, Matrix.mulVec,
    Matrix.mul_apply, dotProduct, Fin.sum_univ_three]

lemma proj_skewApply_relCoord_one (ξ w : V3) :
    proj (skewApply ξ w) 1 = relCoord ξ 0 2 * w 1 - relCoord ξ 0 0 * w 2 := by
  simp [proj, skewApply, skewMatrix, relCoord, Matrix.toLpLin_apply, Matrix.mulVec,
    Matrix.mul_apply, dotProduct, Fin.sum_univ_three]
  ring

/-- The concrete first-order flag attached to a planar normal `n` and lifted vertex `w`.

With the projection convention `proj w = (w₁, -w₀)`, this is the coordinate form of
`(z n, n · Jq, n)` from the paper. -/
def firstOrderFlag (n : V2) (w : V3) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 fun i : Fin 5 =>
    match i with
    | 0 => -w 2 * n 1
    | 1 => w 2 * n 0
    | 2 => n 0 * w 0 + n 1 * w 1
    | 3 => n 0
    | 4 => n 1

@[simp] lemma firstOrderFlag_apply_zero (n : V2) (w : V3) :
    firstOrderFlag n w 0 = -w 2 * n 1 := by
  simp [firstOrderFlag]

@[simp] lemma firstOrderFlag_apply_one (n : V2) (w : V3) :
    firstOrderFlag n w 1 = w 2 * n 0 := by
  simp [firstOrderFlag]

@[simp] lemma firstOrderFlag_apply_two (n : V2) (w : V3) :
    firstOrderFlag n w 2 = n 0 * w 0 + n 1 * w 1 := by
  simp [firstOrderFlag]

@[simp] lemma firstOrderFlag_apply_three (n : V2) (w : V3) :
    firstOrderFlag n w 3 = n 0 := by
  simp [firstOrderFlag]

@[simp] lemma firstOrderFlag_apply_four (n : V2) (w : V3) :
    firstOrderFlag n w 4 = n 1 := by
  simp [firstOrderFlag]

lemma firstOrderFlag_inner_relCoord (n : V2) (w ξ : V3) (t : V2) :
    ⟪firstOrderFlag n w, relCoord ξ t⟫ =
      n 0 * (proj (skewApply ξ w) 0 + t 0) +
        n 1 * (proj (skewApply ξ w) 1 + t 1) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_five]
  ring

/-- Apply a `3 × 3` matrix to a vector as an element of Euclidean space. -/
def matrixApply (A : Matrix (Fin 3) (Fin 3) ℝ) (w : V3) : V3 :=
  Matrix.toLpLin 2 2 A w

@[simp] lemma matrixApply_apply (A : Matrix (Fin 3) (Fin 3) ℝ) (w : V3) (i : Fin 3) :
    matrixApply A w i = (A.mulVec w) i := by
  simp [matrixApply, Matrix.toLpLin_apply]

@[simp] lemma matrixApply_one (w : V3) : matrixApply 1 w = w := by
  ext i
  simp [matrixApply]

@[simp] lemma matrixApply_skewMatrix (ξ w : V3) :
    matrixApply (skewMatrix ξ) w = skewApply ξ w := by
  rfl

/-- Half-plane slack for a moved point `A w`, with inward normal `n` and offset `c`. -/
def affineSlack (n : V2) (c : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) (w : V3) (t : V2) : ℝ :=
  n 0 * (proj (matrixApply A w) 0 + t 0) +
    n 1 * (proj (matrixApply A w) 1 + t 1) - c

/-- The exact non-linear remainder vector `(A - I - [ξ]×) w`. -/
def remainderApply (A : Matrix (Fin 3) (Fin 3) ℝ) (ξ w : V3) : V3 :=
  matrixApply (A - 1 - skewMatrix ξ) w

/-- Exact algebraic decomposition of one half-plane slack.

This is Lemma 4.1 without specializing `A` to `exp [ξ]×` and without estimating the residual. -/
lemma affineSlack_decomp (n : V2) (c : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (w ξ : V3) (t₀ δt : V2) :
    affineSlack n c A w (t₀ + δt) =
      affineSlack n c 1 w t₀ + ⟪firstOrderFlag n w, relCoord ξ δt⟫ +
        (n 0 * proj (remainderApply A ξ w) 0 +
          n 1 * proj (remainderApply A ξ w) 1) := by
  rw [firstOrderFlag_inner_relCoord]
  simp [affineSlack, remainderApply, matrixApply, proj, Matrix.toLpLin_apply, Matrix.mulVec,
    Matrix.mul_apply, dotProduct, Fin.sum_univ_three, skewMatrix]
  ring_nf

/-- The exponential residual `(exp [ξ]× - I - [ξ]×) w`. -/
def expRemainderApply (ξ w : V3) : V3 :=
  remainderApply (NormedSpace.exp (skewMatrix ξ)) ξ w

lemma affineSlack_exp_decomp (n : V2) (c : ℝ) (w ξ : V3) (t₀ δt : V2) :
    affineSlack n c (NormedSpace.exp (skewMatrix ξ)) w (t₀ + δt) =
      affineSlack n c 1 w t₀ + ⟪firstOrderFlag n w, relCoord ξ δt⟫ +
        (n 0 * proj (expRemainderApply ξ w) 0 +
          n 1 * proj (expRemainderApply ξ w) 1) := by
  simpa [expRemainderApply] using
    affineSlack_decomp n c (NormedSpace.exp (skewMatrix ξ)) w ξ t₀ δt

lemma affineSlack_residual_eq_expRemainder (n : V2) (c : ℝ) (w ξ : V3) (t₀ δt : V2) :
    affineSlack n c (NormedSpace.exp (skewMatrix ξ)) w (t₀ + δt) -
        affineSlack n c 1 w t₀ - ⟪firstOrderFlag n w, relCoord ξ δt⟫ =
      n 0 * proj (expRemainderApply ξ w) 0 +
        n 1 * proj (expRemainderApply ξ w) 1 := by
  have h := affineSlack_exp_decomp n c w ξ t₀ δt
  rw [h]
  ring

lemma affineSlack_residual_t_independent (n : V2) (c : ℝ) (w ξ : V3)
    (t₀ δt δt' : V2) :
    affineSlack n c (NormedSpace.exp (skewMatrix ξ)) w (t₀ + δt) -
        affineSlack n c 1 w t₀ - ⟪firstOrderFlag n w, relCoord ξ δt⟫ =
      affineSlack n c (NormedSpace.exp (skewMatrix ξ)) w (t₀ + δt') -
        affineSlack n c 1 w t₀ - ⟪firstOrderFlag n w, relCoord ξ δt'⟫ := by
  rw [affineSlack_residual_eq_expRemainder n c w ξ t₀ δt,
    affineSlack_residual_eq_expRemainder n c w ξ t₀ δt']

/-- Concrete active pair data generated by a supporting half-plane and a lifted vertex. -/
def geometricActivePair {V : Finset V3} {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ}
    (n : V2) (c : ℝ) (w : V3) (hactive : affineSlack n c 1 w 0 = 0)
    (hbound : ∀ ξ : V3,
      |n 0 * proj (expRemainderApply ξ w) 0 + n 1 * proj (expRemainderApply ξ w) 1| ≤
        circumradius V * (1/2 + ‖ξ‖/6) * ‖ξ‖ ^ 2)
    (hstrict :
      ∀ (R₁ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (t : V2),
        RupertContainment V ({ R₁ := R₁, R₂ := R₂, t := t } : Config V) →
        ∀ ξ : V3,
          NormedSpace.exp (skewMatrix ξ) =
            ((R₁ * R₂⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
              Matrix (Fin 3) (Fin 3) ℝ) →
          0 < affineSlack n c (NormedSpace.exp (skewMatrix ξ)) w t) :
    ActivePair V R₂ where
  flag := firstOrderFlag n w
  slackFn ξ t := affineSlack n c (NormedSpace.exp (skewMatrix ξ)) w t
  decompBound := by
    intro ξ t
    refine ⟨n 0 * proj (expRemainderApply ξ w) 0 +
      n 1 * proj (expRemainderApply ξ w) 1, ?_, hbound ξ⟩
    have h := affineSlack_exp_decomp n c w ξ (0 : V2) t
    simpa [hactive, add_assoc] using h
  strictOfContainment := by
    intro R₁ t hcont ξ hξ
    exact hstrict R₁ t hcont ξ hξ

@[simp] lemma flagOf_geometricActivePair {V : Finset V3}
    {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ} (n : V2) (c : ℝ) (w : V3)
    (hactive hbound hstrict) :
    flagOf (geometricActivePair (V := V) (R₂ := R₂) n c w hactive hbound hstrict) =
      firstOrderFlag n w := by
  rfl

@[simp] lemma slack_geometricActivePair {V : Finset V3}
    {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ} (n : V2) (c : ℝ) (w : V3)
    (hactive hbound hstrict) (ξ : V3) (t : V2) :
    slack (geometricActivePair (V := V) (R₂ := R₂) n c w hactive hbound hstrict) ξ t =
      affineSlack n c (NormedSpace.exp (skewMatrix ξ)) w t := by
  rfl

lemma geometricActivePair_slack_decomp_exact {V : Finset V3}
    {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ} (n : V2) (c : ℝ) (w ξ : V3)
    (t : V2) (hactive hbound hstrict) :
    ∃ Q : ℝ,
      slack (geometricActivePair (V := V) (R₂ := R₂) n c w hactive hbound hstrict) ξ t =
        ⟪flagOf (geometricActivePair (V := V) (R₂ := R₂) n c w hactive hbound hstrict),
          relCoord ξ t⟫ + Q ∧
      Q = n 0 * proj (expRemainderApply ξ w) 0 +
        n 1 * proj (expRemainderApply ξ w) 1 := by
  refine ⟨n 0 * proj (expRemainderApply ξ w) 0 +
      n 1 * proj (expRemainderApply ξ w) 1, ?_, rfl⟩
  have h := affineSlack_exp_decomp n c w ξ (0 : V2) t
  simpa [hactive, add_assoc] using h

end DepthCylinderTheorem
