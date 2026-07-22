import RupertStellatedTetrahedron.Stellated.ReflectionSheets

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

open DepthCylinderTheorem

/-!
## Sheet collision and pinch: reflection-product algebra

The geometric pinch theorem uses the elementary fact that the product of two plane reflections in
`R^3`, with unit normals `p` and `q`, has trace `-1 + 4 (p · q)^2`. This file proves that exact
finite-dimensional identity. The subsequent angle statement can consume this trace identity together
with the trace/arccos definition of `rotationAngleOf`.
-/

/-- Dot product on `Fin 3 → ℝ`, used for compact matrix formulas. -/
def dot3 (p q : Fin 3 → ℝ) : ℝ :=
  ∑ i, p i * q i

/-- Plane reflection with unit normal `p`: `x ↦ x - 2(p·x)p`. -/
def planeReflection (p : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  1 - (2 : ℝ) • Matrix.vecMulVec p p

@[simp] lemma planeReflection_apply (p : Fin 3 → ℝ) (i j : Fin 3) :
    planeReflection p i j = (if i = j then 1 else 0) - 2 * p i * p j := by
  by_cases hij : i = j <;>
    simp [planeReflection, Matrix.vecMulVec, hij] <;> ring

lemma trace_planeReflection_mul_planeReflection
    (p q : Fin 3 → ℝ)
    (hp : dot3 p p = 1)
    (hq : dot3 q q = 1) :
    Matrix.trace (planeReflection p * planeReflection q) =
      -1 + 4 * (dot3 p q) ^ 2 := by
  rw [Matrix.trace, Fin.sum_univ_three]
  simp [Matrix.mul_apply, Fin.sum_univ_three, planeReflection_apply, dot3] at hp hq ⊢
  ring_nf at hp hq ⊢
  nlinarith

lemma trace_planeReflection_mul_planeReflection_v3
    (p q : V3)
    (hp : ‖p‖ = 1)
    (hq : ‖q‖ = 1) :
    Matrix.trace (planeReflection p * planeReflection q) =
      -1 + 4 * (dot3 p q) ^ 2 := by
  apply trace_planeReflection_mul_planeReflection
  · change ∑ i, (p : Fin 3 → ℝ) i * (p : Fin 3 → ℝ) i = 1
    rw [EuclideanSpace.norm_eq] at hp
    have hp2 := congrArg (fun x : ℝ => x ^ 2) hp
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hp2
    simpa [Fin.sum_univ_three, pow_two] using hp2
  · change ∑ i, (q : Fin 3 → ℝ) i * (q : Fin 3 → ℝ) i = 1
    rw [EuclideanSpace.norm_eq] at hq
    have hq2 := congrArg (fun x : ℝ => x ^ 2) hq
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hq2
    simpa [Fin.sum_univ_three, pow_two] using hq2

lemma two_mul_arccos_abs_le_pi {c : ℝ} (_hc : |c| ≤ 1) :
    2 * Real.arccos |c| ≤ Real.pi := by
  have habs_nonneg : 0 ≤ |c| := abs_nonneg c
  have hle : Real.arccos |c| ≤ Real.pi / 2 :=
    (Real.arccos_le_pi_div_two).mpr habs_nonneg
  nlinarith

lemma cos_two_arccos_abs {c : ℝ} (hc : |c| ≤ 1) :
    Real.cos (2 * Real.arccos |c|) = 2 * c ^ 2 - 1 := by
  rw [Real.cos_two_mul, Real.cos_arccos (by nlinarith [abs_nonneg c]) hc]
  rw [sq_abs]

/-- Trace-to-angle bridge used by the collision theorem.

If an `SO(3)` element has trace `-1 + 4 c²`, with `|c| ≤ 1`, then its trace/arccos
rotation angle is `2 arccos |c|`.  This is the exact arccos step in Theorem 10.3.
-/
lemma rotationAngleOf_eq_two_arccos_abs_of_trace
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (c : ℝ) (hc : |c| ≤ 1)
    (htrace : Matrix.trace (R : Matrix (Fin 3) (Fin 3) ℝ) = -1 + 4 * c ^ 2) :
    rotationAngleOf R = 2 * Real.arccos |c| := by
  have harg :
      (Matrix.trace (R : Matrix (Fin 3) (Fin 3) ℝ) - 1) / 2 =
        Real.cos (2 * Real.arccos |c|) := by
    rw [htrace, cos_two_arccos_abs hc]
    ring
  rw [rotationAngleOf, harg]
  exact Real.arccos_cos
    (by nlinarith [Real.arccos_nonneg |c|])
    (two_mul_arccos_abs_le_pi hc)

/-- Product-of-reflections angle theorem.

This is the angle form of the pinch algebra: any `SO(3)` element whose matrix is the product of
the two plane reflections with unit normals `p` and `q` has rotation angle
`2 arccos |p · q|`.
-/
theorem rotationAngleOf_planeReflection_product
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (p q : Fin 3 → ℝ)
    (hp : dot3 p p = 1)
    (hq : dot3 q q = 1)
    (hdot : |dot3 p q| ≤ 1)
    (hR : (R : Matrix (Fin 3) (Fin 3) ℝ) = planeReflection p * planeReflection q) :
    rotationAngleOf R = 2 * Real.arccos |dot3 p q| := by
  apply rotationAngleOf_eq_two_arccos_abs_of_trace R (dot3 p q) hdot
  rw [hR]
  exact trace_planeReflection_mul_planeReflection p q hp hq

theorem rotationAngleOf_planeReflection_product_v3
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (p q : V3)
    (hp : ‖p‖ = 1)
    (hq : ‖q‖ = 1)
    (hdot : |dot3 p q| ≤ 1)
    (hR : (R : Matrix (Fin 3) (Fin 3) ℝ) = planeReflection p * planeReflection q) :
    rotationAngleOf R = 2 * Real.arccos |dot3 p q| := by
  apply rotationAngleOf_eq_two_arccos_abs_of_trace R (dot3 p q) hdot
  rw [hR]
  exact trace_planeReflection_mul_planeReflection_v3 p q hp hq

/-- Collision-angle theorem for a reflection-sheet relative rotation, in product-reflection form.

In the geometric application, `p` is the projection-axis normal and `q` is the transported normal
of the tetrahedral reflection plane.  The hypothesis `hrel` is exactly the algebraic identification
`R₁ R₂⁻¹ = (reflection through p⊥) (reflection through q⊥)`.  Under that identification the
relative angle is `2 arccos |p · q|`.
-/
theorem reflection_sheet_collision_angle_of_product
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (p q : V3)
    (hp : ‖p‖ = 1)
    (hq : ‖q‖ = 1)
    (hdot : |dot3 p q| ≤ 1)
    (hrel : ((R₁ * R₂⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ) = planeReflection p * planeReflection q) :
    relAngle R₁ R₂ = 2 * Real.arccos |dot3 p q| := by
  exact rotationAngleOf_planeReflection_product_v3 (R₁ * R₂⁻¹) p q hp hq hdot hrel

/-- Reflection-sheet specialization of `reflection_sheet_collision_angle_of_product`.

The remaining geometric work for a concrete reflection `m` is exactly the matrix identity `hrel`;
for a plane reflection with normal `ν`, this identity is the formal version of
`N R₂ m R₂ᵀ = (reflection through e₃⊥)(reflection through (R₂ν)⊥)`.
-/
theorem reflectionSheetInner_collision_angle_of_product
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (m : Matrix (Fin 3) (Fin 3) ℝ)
    (hmOrth : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hmDet : Matrix.det m = (-1 : ℝ))
    (p q : V3)
    (hp : ‖p‖ = 1)
    (hq : ‖q‖ = 1)
    (hdot : |dot3 p q| ≤ 1)
    (hrel :
      (reflectionSheetMatrix R₂ m * (R₂⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ) = planeReflection p * planeReflection q) :
    relAngle (reflectionSheetInner R₂ m hmOrth hmDet) R₂ =
      2 * Real.arccos |dot3 p q| := by
  apply reflection_sheet_collision_angle_of_product
    (R₁ := reflectionSheetInner R₂ m hmOrth hmDet) (R₂ := R₂)
    (p := p) (q := q) hp hq hdot
  simpa [reflectionSheetInner] using hrel

lemma reflection_sheet_collision_angle_zero_of_abs_dot_eq_one
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (p q : V3)
    (hp : ‖p‖ = 1)
    (hq : ‖q‖ = 1)
    (hdot : |dot3 p q| ≤ 1)
    (hrel : ((R₁ * R₂⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ) = planeReflection p * planeReflection q)
    (habs : |dot3 p q| = 1) :
    relAngle R₁ R₂ = 0 := by
  rw [reflection_sheet_collision_angle_of_product R₁ R₂ p q hp hq hdot hrel, habs,
    Real.arccos_one]
  ring

lemma zReflection_eq_planeReflection_e3 :
    zReflection = planeReflection (WithLp.toLp 2 ![(0 : ℝ), 0, 1] : V3) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [zReflection, planeReflection, Matrix.vecMulVec]

lemma specialOrthogonalGroup_inv_coe_eq_transpose
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ((R⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
      Matrix (Fin 3) (Fin 3) ℝ) =
      (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := R
  let B : Matrix (Fin 3) (Fin 3) ℝ :=
    ((R⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
      Matrix (Fin 3) (Fin 3) ℝ)
  have horth : A * Aᵀ = 1 := by
    have h := specialOrthogonalGroup_orthogonal R
    rw [Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ] at h
    exact h
  have hBA : B * A = 1 := by
    change (((R⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) * R :
      Matrix.specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = 1
    simp
  calc
    B = B * 1 := by simp
    _ = B * (A * Aᵀ) := by rw [horth]
    _ = (B * A) * Aᵀ := by rw [Matrix.mul_assoc]
    _ = Aᵀ := by rw [hBA]; simp

lemma planeReflection_conj_specialOrthogonal
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (ν : V3) :
    (R : Matrix (Fin 3) (Fin 3) ℝ) * planeReflection ν *
        ((R⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
          Matrix (Fin 3) (Fin 3) ℝ) =
      planeReflection (matrixAction (R : Matrix (Fin 3) (Fin 3) ℝ) ν) := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := R
  have horth : A * Aᵀ = 1 := by
    have h := specialOrthogonalGroup_orthogonal R
    rw [Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ] at h
    exact h
  rw [specialOrthogonalGroup_inv_coe_eq_transpose]
  calc
    A * planeReflection ν * Aᵀ =
        A * (1 - (2 : ℝ) • Matrix.vecMulVec ν ν) * Aᵀ := by rfl
    _ = A * 1 * Aᵀ - (2 : ℝ) • (A * Matrix.vecMulVec ν ν * Aᵀ) := by
      simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    _ = A * Aᵀ - (2 : ℝ) • (A * Matrix.vecMulVec ν ν * Aᵀ) := by
      simp
    _ = 1 - (2 : ℝ) •
        Matrix.vecMulVec (A *ᵥ ν) ((ν : Fin 3 → ℝ) ᵥ* Aᵀ) := by
      rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, horth]
    _ = planeReflection (matrixAction (R : Matrix (Fin 3) (Fin 3) ℝ) ν) := by
      rw [Matrix.vecMul_transpose]
      rfl

theorem reflectionSheetInner_collision_angle_of_planeReflection
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (ν : V3)
    (hmOrth : planeReflection ν ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hmDet : Matrix.det (planeReflection ν) = (-1 : ℝ))
    (hp : ‖(WithLp.toLp 2 ![(0 : ℝ), 0, 1] : V3)‖ = 1)
    (hq : ‖matrixAction (R₂ : Matrix (Fin 3) (Fin 3) ℝ) ν‖ = 1)
    (hdot : |dot3 (WithLp.toLp 2 ![(0 : ℝ), 0, 1] : V3)
        (matrixAction (R₂ : Matrix (Fin 3) (Fin 3) ℝ) ν)| ≤ 1) :
    relAngle (reflectionSheetInner R₂ (planeReflection ν) hmOrth hmDet) R₂ =
      2 * Real.arccos |dot3 (WithLp.toLp 2 ![(0 : ℝ), 0, 1] : V3)
        (matrixAction (R₂ : Matrix (Fin 3) (Fin 3) ℝ) ν)| := by
  apply reflectionSheetInner_collision_angle_of_product
    (R₂ := R₂) (m := planeReflection ν) (hmOrth := hmOrth) (hmDet := hmDet)
    (p := (WithLp.toLp 2 ![(0 : ℝ), 0, 1] : V3))
    (q := matrixAction (R₂ : Matrix (Fin 3) (Fin 3) ℝ) ν)
    hp hq hdot
  rw [reflectionSheetMatrix, zReflection_eq_planeReflection_e3]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (R₂ : Matrix (Fin 3) (Fin 3) ℝ) (planeReflection ν)
    ((R₂⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)]
  rw [planeReflection_conj_specialOrthogonal]

/-- Order-theoretic pinch consequence.

In the geometric use, `hnot` is obtained because a reflection-sheet weak-containment exists at
relative angle `2δ`; if the depth-cylinder radius `d / M` were larger than `2δ`, that sheet point
would be excluded.  Therefore the certified depth must satisfy `d ≤ 2Mδ`.
-/
lemma depth_le_two_mul_M_delta_of_not_lt_radius
    {d M δ : ℝ} (hM : 0 < M) (hnot : ¬ 2 * δ < d / M) :
    d ≤ 2 * M * δ := by
  have hle : d / M ≤ 2 * δ := le_of_not_gt hnot
  have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt hM)
  rw [div_mul_cancel₀ d (ne_of_gt hM)] at hmul
  linarith

end RupertStellatedTetrahedron
