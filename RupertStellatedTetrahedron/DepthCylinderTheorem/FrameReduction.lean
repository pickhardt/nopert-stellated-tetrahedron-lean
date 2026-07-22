import RupertStellatedTetrahedron.DepthCylinderTheorem.ActivePairs

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace DepthCylinderTheorem

/-- The isometry `‖x‖² = ‖ξ‖² + ‖t‖²`. -/
lemma relCoord_normSq (ξ : V3) (t : V2) : ‖relCoord ξ t‖ ^ 2 = ‖ξ‖ ^ 2 + ‖t‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  rw [Fin.sum_univ_five, Fin.sum_univ_three, Fin.sum_univ_two]
  simp [relCoord]
  ring

/-- Consequence used in the assembly: `‖ξ‖ ≤ ‖x‖`. -/
lemma angle_le_relCoord_norm (ξ : V3) (t : V2) : ‖ξ‖ ≤ ‖relCoord ξ t‖ := by
  have hsq := relCoord_normSq ξ t
  nlinarith [sq_nonneg ‖t‖, norm_nonneg ξ, norm_nonneg (relCoord ξ t)]

lemma relCoord_eq_zero_iff (ξ : V3) (t : V2) : relCoord ξ t = 0 ↔ ξ = 0 ∧ t = 0 := by
  constructor
  · intro h
    have hsq := relCoord_normSq ξ t
    rw [h, norm_zero, zero_pow (by decide)] at hsq
    have hξ : ‖ξ‖ = 0 := by nlinarith [sq_nonneg ‖ξ‖, sq_nonneg ‖t‖]
    have ht : ‖t‖ = 0 := by nlinarith [sq_nonneg ‖ξ‖, sq_nonneg ‖t‖]
    exact ⟨norm_eq_zero.mp hξ, norm_eq_zero.mp ht⟩
  · rintro ⟨rfl, rfl⟩
    ext i
    fin_cases i <;> simp [relCoord]

/-! ## The five lemmas -/

/-! ### Lemma 3.1 — Frame reduction (exact, for every `R₂ ∈ SO(3)`)
If `A,B ∈ SO(3)` share their third row then `A Bᵀ` is a planar rotation. Finite linear algebra. -/
theorem frame_reduction
    (A B : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (h : (A : Matrix (Fin 3) (Fin 3) ℝ) 2 = (B : Matrix (Fin 3) (Fin 3) ℝ) 2) :
    let C : Matrix (Fin 3) (Fin 3) ℝ :=
      (A : Matrix (Fin 3) (Fin 3) ℝ) * (B : Matrix (Fin 3) (Fin 3) ℝ)ᵀ
    C 2 0 = 0 ∧ C 2 1 = 0 ∧ C 0 2 = 0 ∧ C 1 2 = 0 ∧ C 2 2 = 1 := by
  classical
  let A' : Matrix (Fin 3) (Fin 3) ℝ := A
  let B' : Matrix (Fin 3) (Fin 3) ℝ := B
  have hAorth : A' * A'ᵀ = 1 := by
    exact (Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp A.property).1
  have hBorth : B' * B'ᵀ = 1 := by
    exact (Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp B.property).1
  have hrow : A' 2 = B' 2 := h
  have hrowC (j : Fin 3) :
      (A' * B'ᵀ) 2 j = (B' * B'ᵀ) 2 j := by
    simp [Matrix.mul_apply, hrow]
  have hcolC (i : Fin 3) :
      (A' * B'ᵀ) i 2 = (A' * A'ᵀ) i 2 := by
    simp [Matrix.mul_apply, hrow]
  simp [A', B', hrowC, hcolC, hAorth, hBorth]

/-! ### Lemma 4.1 — Exact decomposition
`h_{ij}(ξ,t) = h⁰_{ij} + r_{ij}·x + Q_{ij}`, `x = relCoord ξ t`, `h⁰=0` on active pairs. -/
theorem exact_decomposition (n : V2) (c : ℝ) (w ξ : V3) (t₀ δt : V2) :
    affineSlack n c (NormedSpace.exp (skewMatrix ξ)) w (t₀ + δt) =
      affineSlack n c 1 w t₀ + ⟪firstOrderFlag n w, relCoord ξ δt⟫ +
        (n 0 * proj (expRemainderApply ξ w) 0 +
          n 1 * proj (expRemainderApply ξ w) 1) := by
  exact affineSlack_exp_decomp n c w ξ t₀ δt

/-! ### Lemma 5.1 — Remainder bound + `t`-independence
(a) `Q_{ij}` depends only on `ξ` (translation enters exactly affinely). (b) `|Q| ≤ ρ(1/2+s/6)s²`
via the matrix-exponential remainder bound carried by the active-pair certificate. -/
theorem remainder_t_independent (n : V2) (c : ℝ) (w ξ : V3) (t₀ δt δt' : V2) :
    affineSlack n c (NormedSpace.exp (skewMatrix ξ)) w (t₀ + δt) -
        affineSlack n c 1 w t₀ - ⟪firstOrderFlag n w, relCoord ξ δt⟫ =
      affineSlack n c (NormedSpace.exp (skewMatrix ξ)) w (t₀ + δt') -
        affineSlack n c 1 w t₀ - ⟪firstOrderFlag n w, relCoord ξ δt'⟫ := by
  exact affineSlack_residual_t_independent n c w ξ t₀ δt δt'

theorem remainder_bound {V : Finset V3} {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ}
    (p : ActivePair V R₂) (ξ : V3) (t : V2) :
    ∃ Q : ℝ, slack p ξ t = ⟪flagOf p, relCoord ξ t⟫ + Q ∧
      |Q| ≤ circumradius V * (1/2 + ‖ξ‖/6) * ‖ξ‖ ^ 2 := by
  exact p.decompBound ξ t

/-! ### Lemma 6.1 — Depth duality
`B(0,d) ⊆ conv F  ↔  ∀ unit x, ∃ r ∈ F, r·x ≤ -d`. Support-function / separating-hyperplane. -/

end DepthCylinderTheorem
