import RupertStellatedTetrahedron.DepthCylinderTheorem.Core

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

open DepthCylinderTheorem

/-!
## Reflection sheets

This file formalizes the algebraic core of the Reflection Sheet Theorem.

If `m` is an improper symmetry of the vertex set and `N = diag(1,1,-1)`, then
`R₁ = N R₂ m` is proper orthogonal and has the same projected vertex set as `R₂`.
The project uses the `proj` convention from the depth-cylinder theorem,
`proj (x,y,z) = (y,-x)`, so `N` is still invisible to projection.
-/

/-- The reflection through the projection plane. -/
def zReflection : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![(1 : ℝ), 1, -1]

/-- Matrix action on `V3`, using the same convention as the depth-cylinder theorem. -/
def matrixAction (A : Matrix (Fin 3) (Fin 3) ℝ) (v : V3) : V3 :=
  Matrix.toLpLin 2 2 A v

@[simp] lemma matrixAction_apply (A : Matrix (Fin 3) (Fin 3) ℝ) (v : V3) (i : Fin 3) :
    matrixAction A v i = (A *ᵥ v) i := by
  simp [matrixAction, Matrix.toLpLin_apply]

@[simp] lemma matrixAction_mul (A B : Matrix (Fin 3) (Fin 3) ℝ) (v : V3) :
    matrixAction (A * B) v = matrixAction A (matrixAction B v) := by
  ext i
  simp [matrixAction, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

@[simp] lemma matrixAction_one (v : V3) :
    matrixAction (1 : Matrix (Fin 3) (Fin 3) ℝ) v = v := by
  ext i
  simp [matrixAction]

@[simp] lemma zReflection_apply_zero (v : V3) : matrixAction zReflection v 0 = v 0 := by
  change (zReflection *ᵥ v.ofLp) 0 = v.ofLp 0
  change ((Matrix.diagonal ![(1 : ℝ), 1, -1]) *ᵥ v.ofLp) 0 = v.ofLp 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma zReflection_apply_one (v : V3) : matrixAction zReflection v 1 = v 1 := by
  change (zReflection *ᵥ v.ofLp) 1 = v.ofLp 1
  change ((Matrix.diagonal ![(1 : ℝ), 1, -1]) *ᵥ v.ofLp) 1 = v.ofLp 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma zReflection_apply_two (v : V3) : matrixAction zReflection v 2 = -v 2 := by
  change (zReflection *ᵥ v.ofLp) 2 = -v.ofLp 2
  change ((Matrix.diagonal ![(1 : ℝ), 1, -1]) *ᵥ v.ofLp) 2 = -v.ofLp 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The projection discards the reflected coordinate, so `N` is invisible to shadows. -/
@[simp] lemma proj_zReflection (v : V3) :
    proj (matrixAction zReflection v) = proj v := by
  ext i
  fin_cases i <;>
    simp [proj, matrixAction, zReflection, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

lemma zReflection_transpose :
    zReflectionᵀ = zReflection := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zReflection]

lemma zReflection_orthogonal :
    zReflection ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zReflection, Matrix.mul_apply, Fin.sum_univ_three]

lemma zReflection_det :
    zReflection.det = (-1 : ℝ) := by
  simp [zReflection, Matrix.det_diagonal, Fin.prod_univ_three]

lemma orthogonal_mul {A B : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hB : B ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    A * B ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ] at hA hB ⊢
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc B Bᵀ Aᵀ, hB]
  simp [hA]

lemma specialOrthogonalGroup_orthogonal
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    (R : Matrix (Fin 3) (Fin 3) ℝ) ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
  (Matrix.mem_specialOrthogonalGroup_iff.mp R.property).1

lemma specialOrthogonalGroup_det
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    Matrix.det (R : Matrix (Fin 3) (Fin 3) ℝ) = (1 : ℝ) :=
  (Matrix.mem_specialOrthogonalGroup_iff.mp R.property).2

/-- The matrix on the reflection sheet, before packaging it as an `SO(3)` element. -/
def reflectionSheetMatrix
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (m : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  zReflection * (R₂ : Matrix (Fin 3) (Fin 3) ℝ) * m

lemma reflectionSheetMatrix_orthogonal
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (m : Matrix (Fin 3) (Fin 3) ℝ)
    (hmOrth : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    reflectionSheetMatrix R₂ m ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  exact orthogonal_mul
    (orthogonal_mul zReflection_orthogonal (specialOrthogonalGroup_orthogonal R₂))
    hmOrth

lemma reflectionSheetMatrix_det
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (m : Matrix (Fin 3) (Fin 3) ℝ)
    (hmDet : Matrix.det m = (-1 : ℝ)) :
    Matrix.det (reflectionSheetMatrix R₂ m) = (1 : ℝ) := by
  simp [reflectionSheetMatrix, Matrix.det_mul, zReflection_det,
    specialOrthogonalGroup_det R₂, hmDet]

lemma reflectionSheetMatrix_mem_specialOrthogonalGroup
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (m : Matrix (Fin 3) (Fin 3) ℝ)
    (hmOrth : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hmDet : Matrix.det m = (-1 : ℝ)) :
    reflectionSheetMatrix R₂ m ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  exact (Matrix.mem_specialOrthogonalGroup_iff).mpr
    ⟨reflectionSheetMatrix_orthogonal R₂ m hmOrth,
      reflectionSheetMatrix_det R₂ m hmDet⟩

/-- Package the inner rotation on a reflection sheet as an element of `SO(3)`. -/
def reflectionSheetInner
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (m : Matrix (Fin 3) (Fin 3) ℝ)
    (hmOrth : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hmDet : Matrix.det m = (-1 : ℝ)) :
    Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨reflectionSheetMatrix R₂ m,
    reflectionSheetMatrix_mem_specialOrthogonalGroup R₂ m hmOrth hmDet⟩

/-- Applying the reflection-sheet inner matrix is the same, after projection, as applying `R₂ m`. -/
lemma proj_reflectionSheetMatrix
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (m : Matrix (Fin 3) (Fin 3) ℝ)
    (v : V3) :
    proj (matrixAction (reflectionSheetMatrix R₂ m) v) =
      proj (matrixAction (R₂ : Matrix (Fin 3) (Fin 3) ℝ) (matrixAction m v)) := by
  simp [reflectionSheetMatrix, Matrix.mul_assoc]

lemma image_comp_eq_of_mapsTo
    {α β : Type*} {s : Set α} {f : α → α} {g : α → β}
    (hf : Set.MapsTo f s s) (hsurj : ∀ y ∈ s, ∃ x ∈ s, f x = y) :
    (fun x => g (f x)) '' s = g '' s := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, hf hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rcases hsurj x hx with ⟨x', hx', hx'eq⟩
    exact ⟨x', hx', by simp [hx'eq]⟩

/-- The algebraic core of the Reflection Sheet Theorem.

If `m` is an improper orthogonal symmetry of `V`, then for every outer rotation `R₂`, the
inner rotation `N R₂ m` is in `SO(3)` and gives exactly the same projected vertex set.
-/
theorem reflection_sheet_theorem
    (V : Set V3)
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (m : Matrix (Fin 3) (Fin 3) ℝ)
    (hmOrth : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hmDet : Matrix.det m = (-1 : ℝ))
    (hmMaps : Set.MapsTo (matrixAction m) V V)
    (hmSurj : ∀ y ∈ V, ∃ x ∈ V, matrixAction m x = y) :
    let R₁ := reflectionSheetInner R₂ m hmOrth hmDet
    (R₁ : Matrix (Fin 3) (Fin 3) ℝ) = reflectionSheetMatrix R₂ m ∧
      ((fun v : V3 => proj (matrixAction (R₁ : Matrix (Fin 3) (Fin 3) ℝ) v)) '' V =
        (fun v : V3 => proj (matrixAction (R₂ : Matrix (Fin 3) (Fin 3) ℝ) v)) '' V) := by
  intro R₁
  constructor
  · rfl
  · change
      ((fun v : V3 => proj (matrixAction (reflectionSheetMatrix R₂ m) v)) '' V =
        (fun v : V3 => proj (matrixAction (R₂ : Matrix (Fin 3) (Fin 3) ℝ) v)) '' V)
    rw [show
        (fun v : V3 => proj (matrixAction (reflectionSheetMatrix R₂ m) v)) =
          fun v : V3 =>
            proj (matrixAction (R₂ : Matrix (Fin 3) (Fin 3) ℝ) (matrixAction m v)) by
      funext v
      exact proj_reflectionSheetMatrix R₂ m v]
    simpa using image_comp_eq_of_mapsTo (s := V) (f := matrixAction m)
      (g := fun v : V3 => proj (matrixAction (R₂ : Matrix (Fin 3) (Fin 3) ℝ) v))
      hmMaps hmSurj

/-- Finset-shadow form of the Reflection Sheet Theorem.

For a finite vertex set preserved by an improper orthogonal symmetry `m`, the inner rotation
`N R₂ m` and the outer rotation `R₂` have equal shadows. This is the exact formal counterpart of
`π(N R₂ m V) = π(R₂ V)`.
-/
theorem reflection_sheet_shadow_eq
    (V : Finset V3)
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (m : Matrix (Fin 3) (Fin 3) ℝ)
    (hmOrth : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hmDet : Matrix.det m = (-1 : ℝ))
    (hmMaps : Set.MapsTo (matrixAction m) (V : Set V3) (V : Set V3))
    (hmSurj : ∀ y ∈ (V : Set V3), ∃ x ∈ (V : Set V3), matrixAction m x = y) :
    shadow V (reflectionSheetInner R₂ m hmOrth hmDet) = shadow V R₂ := by
  unfold shadow
  congr 1
  exact (reflection_sheet_theorem (V : Set V3) R₂ m hmOrth hmDet hmMaps hmSurj).2

end RupertStellatedTetrahedron
