import RupertStellatedTetrahedron.Stellated.Vertices

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

open DepthCylinderTheorem

/-!
## Concrete symmetries of `P_{11/20}`

This starts the `T_d` formalization with the reflection swapping the first two coordinates.  It is
one of the six reflection symmetries; combined with coordinate permutations/sign changes it is the
local model used by the reflection-sheet and critical-direction arguments.
-/

/-- Reflection in the plane `x = y`, written as the coordinate swap `(x,y,z) ↦ (y,x,z)`. -/
def swapXY : Matrix (Fin 3) (Fin 3) ℝ
  | 0, 1 => 1
  | 1, 0 => 1
  | 2, 2 => 1
  | _, _ => 0

/-- Reflection in the plane `x = z`, written as the coordinate swap `(x,y,z) ↦ (z,y,x)`. -/
def swapXZ : Matrix (Fin 3) (Fin 3) ℝ
  | 0, 2 => 1
  | 1, 1 => 1
  | 2, 0 => 1
  | _, _ => 0

/-- Reflection in the plane `y = z`, written as the coordinate swap `(x,y,z) ↦ (x,z,y)`. -/
def swapYZ : Matrix (Fin 3) (Fin 3) ℝ
  | 0, 0 => 1
  | 1, 2 => 1
  | 2, 1 => 1
  | _, _ => 0

/-- Reflection in the plane `x = -y`, written as `(x,y,z) ↦ (-y,-x,z)`. -/
def negSwapXY : Matrix (Fin 3) (Fin 3) ℝ
  | 0, 1 => -1
  | 1, 0 => -1
  | 2, 2 => 1
  | _, _ => 0

/-- Reflection in the plane `x = -z`, written as `(x,y,z) ↦ (-z,y,-x)`. -/
def negSwapXZ : Matrix (Fin 3) (Fin 3) ℝ
  | 0, 2 => -1
  | 1, 1 => 1
  | 2, 0 => -1
  | _, _ => 0

/-- Reflection in the plane `y = -z`, written as `(x,y,z) ↦ (x,-z,-y)`. -/
def negSwapYZ : Matrix (Fin 3) (Fin 3) ℝ
  | 0, 0 => 1
  | 1, 2 => -1
  | 2, 1 => -1
  | _, _ => 0

@[simp] lemma swapXY_apply (i j : Fin 3) :
    swapXY i j =
      if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 2) then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [swapXY]

@[simp] lemma swapXZ_apply (i j : Fin 3) :
    swapXZ i j =
      if (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 1) ∨ (i = 2 ∧ j = 0) then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [swapXZ]

@[simp] lemma swapYZ_apply (i j : Fin 3) :
    swapYZ i j =
      if (i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [swapYZ]

@[simp] lemma negSwapXY_apply (i j : Fin 3) :
    negSwapXY i j =
      if i = 0 ∧ j = 1 then -1
      else if i = 1 ∧ j = 0 then -1
      else if i = 2 ∧ j = 2 then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [negSwapXY]

@[simp] lemma negSwapXZ_apply (i j : Fin 3) :
    negSwapXZ i j =
      if i = 0 ∧ j = 2 then -1
      else if i = 1 ∧ j = 1 then 1
      else if i = 2 ∧ j = 0 then -1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [negSwapXZ]

@[simp] lemma negSwapYZ_apply (i j : Fin 3) :
    negSwapYZ i j =
      if i = 0 ∧ j = 0 then 1
      else if i = 1 ∧ j = 2 then -1
      else if i = 2 ∧ j = 1 then -1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [negSwapYZ]

@[simp] lemma matrixAction_swapXY_apply_zero (v : V3) :
    matrixAction swapXY v 0 = v 1 := by
  simp [matrixAction, swapXY, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXY_apply_one (v : V3) :
    matrixAction swapXY v 1 = v 0 := by
  simp [matrixAction, swapXY, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXY_apply_two (v : V3) :
    matrixAction swapXY v 2 = v 2 := by
  simp [matrixAction, swapXY, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXZ_apply_zero (v : V3) :
    matrixAction swapXZ v 0 = v 2 := by
  simp [matrixAction, swapXZ, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXZ_apply_one (v : V3) :
    matrixAction swapXZ v 1 = v 1 := by
  simp [matrixAction, swapXZ, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXZ_apply_two (v : V3) :
    matrixAction swapXZ v 2 = v 0 := by
  simp [matrixAction, swapXZ, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapYZ_apply_zero (v : V3) :
    matrixAction swapYZ v 0 = v 0 := by
  simp [matrixAction, swapYZ, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapYZ_apply_one (v : V3) :
    matrixAction swapYZ v 1 = v 2 := by
  simp [matrixAction, swapYZ, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapYZ_apply_two (v : V3) :
    matrixAction swapYZ v 2 = v 1 := by
  simp [matrixAction, swapYZ, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXY_apply_zero (v : V3) :
    matrixAction negSwapXY v 0 = -v 1 := by
  simp [matrixAction, negSwapXY, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXY_apply_one (v : V3) :
    matrixAction negSwapXY v 1 = -v 0 := by
  simp [matrixAction, negSwapXY, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXY_apply_two (v : V3) :
    matrixAction negSwapXY v 2 = v 2 := by
  simp [matrixAction, negSwapXY, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXZ_apply_zero (v : V3) :
    matrixAction negSwapXZ v 0 = -v 2 := by
  simp [matrixAction, negSwapXZ, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXZ_apply_one (v : V3) :
    matrixAction negSwapXZ v 1 = v 1 := by
  simp [matrixAction, negSwapXZ, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXZ_apply_two (v : V3) :
    matrixAction negSwapXZ v 2 = -v 0 := by
  simp [matrixAction, negSwapXZ, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapYZ_apply_zero (v : V3) :
    matrixAction negSwapYZ v 0 = v 0 := by
  simp [matrixAction, negSwapYZ, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapYZ_apply_one (v : V3) :
    matrixAction negSwapYZ v 1 = -v 2 := by
  simp [matrixAction, negSwapYZ, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapYZ_apply_two (v : V3) :
    matrixAction negSwapYZ v 2 = -v 1 := by
  simp [matrixAction, negSwapYZ, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

lemma swapXY_orthogonal :
    swapXY ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapXY, Matrix.mul_apply, Fin.sum_univ_three]

lemma swapXZ_orthogonal :
    swapXZ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapXZ, Matrix.mul_apply, Fin.sum_univ_three]

lemma swapYZ_orthogonal :
    swapYZ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapYZ, Matrix.mul_apply, Fin.sum_univ_three]

lemma negSwapXY_orthogonal :
    negSwapXY ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [negSwapXY, Matrix.mul_apply, Fin.sum_univ_three]

lemma negSwapXZ_orthogonal :
    negSwapXZ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [negSwapXZ, Matrix.mul_apply, Fin.sum_univ_three]

lemma negSwapYZ_orthogonal :
    negSwapYZ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [negSwapYZ, Matrix.mul_apply, Fin.sum_univ_three]

@[simp] lemma swapXY_mul_self :
    swapXY * swapXY = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

@[simp] lemma swapXZ_mul_self :
    swapXZ * swapXZ = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

@[simp] lemma swapYZ_mul_self :
    swapYZ * swapYZ = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

@[simp] lemma negSwapXY_mul_self :
    negSwapXY * negSwapXY = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

@[simp] lemma negSwapXZ_mul_self :
    negSwapXZ * negSwapXZ = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

@[simp] lemma negSwapYZ_mul_self :
    negSwapYZ * negSwapYZ = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

lemma swapXY_det : swapXY.det = (-1 : ℝ) := by
  rw [Matrix.det_fin_three]
  simp [swapXY]

lemma swapXZ_det : swapXZ.det = (-1 : ℝ) := by
  rw [Matrix.det_fin_three]
  simp [swapXZ]

lemma swapYZ_det : swapYZ.det = (-1 : ℝ) := by
  rw [Matrix.det_fin_three]
  simp [swapYZ]

lemma negSwapXY_det : negSwapXY.det = (-1 : ℝ) := by
  rw [Matrix.det_fin_three]
  simp [negSwapXY]

lemma negSwapXZ_det : negSwapXZ.det = (-1 : ℝ) := by
  rw [Matrix.det_fin_three]
  simp [negSwapXZ]

lemma negSwapYZ_det : negSwapYZ.det = (-1 : ℝ) := by
  rw [Matrix.det_fin_three]
  simp [negSwapYZ]

@[simp] lemma matrixAction_swapXY_tetraVertex_zero :
    matrixAction swapXY (tetraVertex 0) = tetraVertex 0 := by
  ext i
  fin_cases i
  · change matrixAction swapXY (tetraVertex 0) 0 = tetraVertex 0 0
    simp [tetraVertex, matrixAction, swapXY, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · change matrixAction swapXY (tetraVertex 0) 1 = tetraVertex 0 1
    simp [tetraVertex, matrixAction, swapXY, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · change matrixAction swapXY (tetraVertex 0) 2 = tetraVertex 0 2
    simp [tetraVertex, matrixAction, swapXY, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXY_tetraVertex_one :
    matrixAction swapXY (tetraVertex 1) = tetraVertex 2 := by
  ext i
  fin_cases i
  · change matrixAction swapXY (tetraVertex 1) 0 = tetraVertex 2 0
    simp [tetraVertex, matrixAction, swapXY, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · change matrixAction swapXY (tetraVertex 1) 1 = tetraVertex 2 1
    simp [tetraVertex, matrixAction, swapXY, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · change matrixAction swapXY (tetraVertex 1) 2 = tetraVertex 2 2
    simp [tetraVertex, matrixAction, swapXY, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXY_tetraVertex_two :
    matrixAction swapXY (tetraVertex 2) = tetraVertex 1 := by
  ext i
  fin_cases i
  · change matrixAction swapXY (tetraVertex 2) 0 = tetraVertex 1 0
    simp [tetraVertex, matrixAction, swapXY, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · change matrixAction swapXY (tetraVertex 2) 1 = tetraVertex 1 1
    simp [tetraVertex, matrixAction, swapXY, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · change matrixAction swapXY (tetraVertex 2) 2 = tetraVertex 1 2
    simp [tetraVertex, matrixAction, swapXY, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXY_tetraVertex_three :
    matrixAction swapXY (tetraVertex 3) = tetraVertex 3 := by
  ext i
  fin_cases i
  · change matrixAction swapXY (tetraVertex 3) 0 = tetraVertex 3 0
    simp [tetraVertex, matrixAction, swapXY, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · change matrixAction swapXY (tetraVertex 3) 1 = tetraVertex 3 1
    simp [tetraVertex, matrixAction, swapXY, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · change matrixAction swapXY (tetraVertex 3) 2 = tetraVertex 3 2
    simp [tetraVertex, matrixAction, swapXY, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXY_stellatedApex_zero :
    matrixAction swapXY (stellatedApex 0) = stellatedApex 0 := by
  ext i
  fin_cases i <;>
    simp [stellatedApex, tetraVertex, matrixAction, swapXY, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXY_stellatedApex_one :
    matrixAction swapXY (stellatedApex 1) = stellatedApex 2 := by
  ext i
  fin_cases i <;>
    simp [stellatedApex, tetraVertex, matrixAction, swapXY, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXY_stellatedApex_two :
    matrixAction swapXY (stellatedApex 2) = stellatedApex 1 := by
  ext i
  fin_cases i <;>
    simp [stellatedApex, tetraVertex, matrixAction, swapXY, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXY_stellatedApex_three :
    matrixAction swapXY (stellatedApex 3) = stellatedApex 3 := by
  ext i
  fin_cases i <;>
    simp [stellatedApex, tetraVertex, matrixAction, swapXY, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXY_stellatedVertex_zero :
    matrixAction swapXY (stellatedVertex 0) = stellatedVertex 0 := by
  simpa [stellatedVertex] using matrixAction_swapXY_tetraVertex_zero

@[simp] lemma matrixAction_swapXY_stellatedVertex_one :
    matrixAction swapXY (stellatedVertex 1) = stellatedVertex 2 := by
  simpa [stellatedVertex] using matrixAction_swapXY_tetraVertex_one

@[simp] lemma matrixAction_swapXY_stellatedVertex_two :
    matrixAction swapXY (stellatedVertex 2) = stellatedVertex 1 := by
  simpa [stellatedVertex] using matrixAction_swapXY_tetraVertex_two

@[simp] lemma matrixAction_swapXY_stellatedVertex_three :
    matrixAction swapXY (stellatedVertex 3) = stellatedVertex 3 := by
  simpa [stellatedVertex] using matrixAction_swapXY_tetraVertex_three

@[simp] lemma matrixAction_swapXY_stellatedVertex_four :
    matrixAction swapXY (stellatedVertex 4) = stellatedVertex 4 := by
  simp [stellatedVertex]

@[simp] lemma matrixAction_swapXY_stellatedVertex_five :
    matrixAction swapXY (stellatedVertex 5) = stellatedVertex 6 := by
  simp [stellatedVertex]

@[simp] lemma matrixAction_swapXY_stellatedVertex_six :
    matrixAction swapXY (stellatedVertex 6) = stellatedVertex 5 := by
  simp [stellatedVertex]

@[simp] lemma matrixAction_swapXY_stellatedVertex_seven :
    matrixAction swapXY (stellatedVertex 7) = stellatedVertex 7 := by
  simp [stellatedVertex]

@[simp] lemma matrixAction_swapXZ_stellatedVertex_zero :
    matrixAction swapXZ (stellatedVertex 0) = stellatedVertex 0 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, swapXZ, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXZ_stellatedVertex_one :
    matrixAction swapXZ (stellatedVertex 1) = stellatedVertex 3 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, swapXZ, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXZ_stellatedVertex_two :
    matrixAction swapXZ (stellatedVertex 2) = stellatedVertex 2 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, swapXZ, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXZ_stellatedVertex_three :
    matrixAction swapXZ (stellatedVertex 3) = stellatedVertex 1 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, swapXZ, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXZ_stellatedVertex_four :
    matrixAction swapXZ (stellatedVertex 4) = stellatedVertex 4 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, swapXZ,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXZ_stellatedVertex_five :
    matrixAction swapXZ (stellatedVertex 5) = stellatedVertex 7 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, swapXZ,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXZ_stellatedVertex_six :
    matrixAction swapXZ (stellatedVertex 6) = stellatedVertex 6 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, swapXZ,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapXZ_stellatedVertex_seven :
    matrixAction swapXZ (stellatedVertex 7) = stellatedVertex 5 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, swapXZ,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapYZ_stellatedVertex_zero :
    matrixAction swapYZ (stellatedVertex 0) = stellatedVertex 0 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, swapYZ, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapYZ_stellatedVertex_one :
    matrixAction swapYZ (stellatedVertex 1) = stellatedVertex 1 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, swapYZ, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapYZ_stellatedVertex_two :
    matrixAction swapYZ (stellatedVertex 2) = stellatedVertex 3 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, swapYZ, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapYZ_stellatedVertex_three :
    matrixAction swapYZ (stellatedVertex 3) = stellatedVertex 2 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, swapYZ, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapYZ_stellatedVertex_four :
    matrixAction swapYZ (stellatedVertex 4) = stellatedVertex 4 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, swapYZ,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapYZ_stellatedVertex_five :
    matrixAction swapYZ (stellatedVertex 5) = stellatedVertex 5 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, swapYZ,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapYZ_stellatedVertex_six :
    matrixAction swapYZ (stellatedVertex 6) = stellatedVertex 7 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, swapYZ,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_swapYZ_stellatedVertex_seven :
    matrixAction swapYZ (stellatedVertex 7) = stellatedVertex 6 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, swapYZ,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXY_stellatedVertex_zero :
    matrixAction negSwapXY (stellatedVertex 0) = stellatedVertex 3 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, negSwapXY, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXY_stellatedVertex_one :
    matrixAction negSwapXY (stellatedVertex 1) = stellatedVertex 1 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, negSwapXY, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXY_stellatedVertex_two :
    matrixAction negSwapXY (stellatedVertex 2) = stellatedVertex 2 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, negSwapXY, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXY_stellatedVertex_three :
    matrixAction negSwapXY (stellatedVertex 3) = stellatedVertex 0 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, negSwapXY, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXY_stellatedVertex_four :
    matrixAction negSwapXY (stellatedVertex 4) = stellatedVertex 7 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, negSwapXY,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXY_stellatedVertex_five :
    matrixAction negSwapXY (stellatedVertex 5) = stellatedVertex 5 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, negSwapXY,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXY_stellatedVertex_six :
    matrixAction negSwapXY (stellatedVertex 6) = stellatedVertex 6 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, negSwapXY,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXY_stellatedVertex_seven :
    matrixAction negSwapXY (stellatedVertex 7) = stellatedVertex 4 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, negSwapXY,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXZ_stellatedVertex_zero :
    matrixAction negSwapXZ (stellatedVertex 0) = stellatedVertex 2 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, negSwapXZ, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXZ_stellatedVertex_one :
    matrixAction negSwapXZ (stellatedVertex 1) = stellatedVertex 1 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, negSwapXZ, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXZ_stellatedVertex_two :
    matrixAction negSwapXZ (stellatedVertex 2) = stellatedVertex 0 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, negSwapXZ, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXZ_stellatedVertex_three :
    matrixAction negSwapXZ (stellatedVertex 3) = stellatedVertex 3 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, negSwapXZ, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXZ_stellatedVertex_four :
    matrixAction negSwapXZ (stellatedVertex 4) = stellatedVertex 6 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, negSwapXZ,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXZ_stellatedVertex_five :
    matrixAction negSwapXZ (stellatedVertex 5) = stellatedVertex 5 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, negSwapXZ,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXZ_stellatedVertex_six :
    matrixAction negSwapXZ (stellatedVertex 6) = stellatedVertex 4 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, negSwapXZ,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapXZ_stellatedVertex_seven :
    matrixAction negSwapXZ (stellatedVertex 7) = stellatedVertex 7 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, negSwapXZ,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapYZ_stellatedVertex_zero :
    matrixAction negSwapYZ (stellatedVertex 0) = stellatedVertex 1 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, negSwapYZ, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapYZ_stellatedVertex_one :
    matrixAction negSwapYZ (stellatedVertex 1) = stellatedVertex 0 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, negSwapYZ, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapYZ_stellatedVertex_two :
    matrixAction negSwapYZ (stellatedVertex 2) = stellatedVertex 2 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, negSwapYZ, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapYZ_stellatedVertex_three :
    matrixAction negSwapYZ (stellatedVertex 3) = stellatedVertex 3 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, tetraVertex, matrixAction, negSwapYZ, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapYZ_stellatedVertex_four :
    matrixAction negSwapYZ (stellatedVertex 4) = stellatedVertex 5 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, negSwapYZ,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapYZ_stellatedVertex_five :
    matrixAction negSwapYZ (stellatedVertex 5) = stellatedVertex 4 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, negSwapYZ,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapYZ_stellatedVertex_six :
    matrixAction negSwapYZ (stellatedVertex 6) = stellatedVertex 6 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, negSwapYZ,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma matrixAction_negSwapYZ_stellatedVertex_seven :
    matrixAction negSwapYZ (stellatedVertex 7) = stellatedVertex 7 := by
  ext i
  fin_cases i <;>
    simp [stellatedVertex, stellatedApex, tetraVertex, matrixAction, negSwapYZ,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

lemma swapXY_maps_stellatedVertices :
    Set.MapsTo (matrixAction swapXY) (stellatedVertices : Set V3) (stellatedVertices : Set V3) := by
  classical
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
  fin_cases i <;> simp [stellatedVertices]

lemma swapXZ_maps_stellatedVertices :
    Set.MapsTo (matrixAction swapXZ) (stellatedVertices : Set V3) (stellatedVertices : Set V3) := by
  classical
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
  fin_cases i <;> simp [stellatedVertices]

lemma swapYZ_maps_stellatedVertices :
    Set.MapsTo (matrixAction swapYZ) (stellatedVertices : Set V3) (stellatedVertices : Set V3) := by
  classical
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
  fin_cases i <;> simp [stellatedVertices]

lemma negSwapXY_maps_stellatedVertices :
    Set.MapsTo (matrixAction negSwapXY) (stellatedVertices : Set V3)
      (stellatedVertices : Set V3) := by
  classical
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
  fin_cases i <;> simp [stellatedVertices]

lemma negSwapXZ_maps_stellatedVertices :
    Set.MapsTo (matrixAction negSwapXZ) (stellatedVertices : Set V3)
      (stellatedVertices : Set V3) := by
  classical
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
  fin_cases i <;> simp [stellatedVertices]

lemma negSwapYZ_maps_stellatedVertices :
    Set.MapsTo (matrixAction negSwapYZ) (stellatedVertices : Set V3)
      (stellatedVertices : Set V3) := by
  classical
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
  fin_cases i <;> simp [stellatedVertices]

@[simp] lemma matrixAction_swapXY_swapXY (v : V3) :
    matrixAction swapXY (matrixAction swapXY v) = v := by
  simpa using (matrixAction_mul swapXY swapXY v).symm

@[simp] lemma matrixAction_swapXZ_swapXZ (v : V3) :
    matrixAction swapXZ (matrixAction swapXZ v) = v := by
  simpa using (matrixAction_mul swapXZ swapXZ v).symm

@[simp] lemma matrixAction_swapYZ_swapYZ (v : V3) :
    matrixAction swapYZ (matrixAction swapYZ v) = v := by
  simpa using (matrixAction_mul swapYZ swapYZ v).symm

@[simp] lemma matrixAction_negSwapXY_negSwapXY (v : V3) :
    matrixAction negSwapXY (matrixAction negSwapXY v) = v := by
  simpa using (matrixAction_mul negSwapXY negSwapXY v).symm

@[simp] lemma matrixAction_negSwapXZ_negSwapXZ (v : V3) :
    matrixAction negSwapXZ (matrixAction negSwapXZ v) = v := by
  simpa using (matrixAction_mul negSwapXZ negSwapXZ v).symm

@[simp] lemma matrixAction_negSwapYZ_negSwapYZ (v : V3) :
    matrixAction negSwapYZ (matrixAction negSwapYZ v) = v := by
  simpa using (matrixAction_mul negSwapYZ negSwapYZ v).symm

lemma swapXY_surj_stellatedVertices :
    ∀ y ∈ (stellatedVertices : Set V3), ∃ x ∈ (stellatedVertices : Set V3),
      matrixAction swapXY x = y := by
  intro y hy
  refine ⟨matrixAction swapXY y, swapXY_maps_stellatedVertices hy, ?_⟩
  simp

lemma swapXZ_surj_stellatedVertices :
    ∀ y ∈ (stellatedVertices : Set V3), ∃ x ∈ (stellatedVertices : Set V3),
      matrixAction swapXZ x = y := by
  intro y hy
  refine ⟨matrixAction swapXZ y, swapXZ_maps_stellatedVertices hy, ?_⟩
  simp

lemma swapYZ_surj_stellatedVertices :
    ∀ y ∈ (stellatedVertices : Set V3), ∃ x ∈ (stellatedVertices : Set V3),
      matrixAction swapYZ x = y := by
  intro y hy
  refine ⟨matrixAction swapYZ y, swapYZ_maps_stellatedVertices hy, ?_⟩
  simp

lemma negSwapXY_surj_stellatedVertices :
    ∀ y ∈ (stellatedVertices : Set V3), ∃ x ∈ (stellatedVertices : Set V3),
      matrixAction negSwapXY x = y := by
  intro y hy
  refine ⟨matrixAction negSwapXY y, negSwapXY_maps_stellatedVertices hy, ?_⟩
  simp

lemma negSwapXZ_surj_stellatedVertices :
    ∀ y ∈ (stellatedVertices : Set V3), ∃ x ∈ (stellatedVertices : Set V3),
      matrixAction negSwapXZ x = y := by
  intro y hy
  refine ⟨matrixAction negSwapXZ y, negSwapXZ_maps_stellatedVertices hy, ?_⟩
  simp

lemma negSwapYZ_surj_stellatedVertices :
    ∀ y ∈ (stellatedVertices : Set V3), ∃ x ∈ (stellatedVertices : Set V3),
      matrixAction negSwapYZ x = y := by
  intro y hy
  refine ⟨matrixAction negSwapYZ y, negSwapYZ_maps_stellatedVertices hy, ?_⟩
  simp

/-- A proof-carrying improper symmetry of a finite vertex set. -/
structure ImproperVertexSymmetry (V : Finset V3) where
  matrix : Matrix (Fin 3) (Fin 3) ℝ
  orthogonal : matrix ∈ Matrix.orthogonalGroup (Fin 3) ℝ
  det_neg : Matrix.det matrix = (-1 : ℝ)
  maps : Set.MapsTo (matrixAction matrix) (V : Set V3) (V : Set V3)
  surj : ∀ y ∈ (V : Set V3), ∃ x ∈ (V : Set V3), matrixAction matrix x = y

/-- Any proof-carrying improper symmetry gives a reflection-sheet shadow equality. -/
theorem improperVertexSymmetry_reflection_sheet_shadow_eq
    (V : Finset V3)
    (S : ImproperVertexSymmetry V)
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    shadow V (reflectionSheetInner R₂ S.matrix S.orthogonal S.det_neg) = shadow V R₂ := by
  exact reflection_sheet_shadow_eq V R₂ S.matrix S.orthogonal S.det_neg S.maps S.surj

def swapXYImproperVertexSymmetry : ImproperVertexSymmetry stellatedVertices where
  matrix := swapXY
  orthogonal := swapXY_orthogonal
  det_neg := swapXY_det
  maps := swapXY_maps_stellatedVertices
  surj := swapXY_surj_stellatedVertices

def swapXZImproperVertexSymmetry : ImproperVertexSymmetry stellatedVertices where
  matrix := swapXZ
  orthogonal := swapXZ_orthogonal
  det_neg := swapXZ_det
  maps := swapXZ_maps_stellatedVertices
  surj := swapXZ_surj_stellatedVertices

def swapYZImproperVertexSymmetry : ImproperVertexSymmetry stellatedVertices where
  matrix := swapYZ
  orthogonal := swapYZ_orthogonal
  det_neg := swapYZ_det
  maps := swapYZ_maps_stellatedVertices
  surj := swapYZ_surj_stellatedVertices

def negSwapXYImproperVertexSymmetry : ImproperVertexSymmetry stellatedVertices where
  matrix := negSwapXY
  orthogonal := negSwapXY_orthogonal
  det_neg := negSwapXY_det
  maps := negSwapXY_maps_stellatedVertices
  surj := negSwapXY_surj_stellatedVertices

def negSwapXZImproperVertexSymmetry : ImproperVertexSymmetry stellatedVertices where
  matrix := negSwapXZ
  orthogonal := negSwapXZ_orthogonal
  det_neg := negSwapXZ_det
  maps := negSwapXZ_maps_stellatedVertices
  surj := negSwapXZ_surj_stellatedVertices

def negSwapYZImproperVertexSymmetry : ImproperVertexSymmetry stellatedVertices where
  matrix := negSwapYZ
  orthogonal := negSwapYZ_orthogonal
  det_neg := negSwapYZ_det
  maps := negSwapYZ_maps_stellatedVertices
  surj := negSwapYZ_surj_stellatedVertices

/-- The six face-diagonal reflections, indexed compatibly with `criticalDirection`:
`x=y`, `x=-y`, `x=z`, `x=-z`, `y=z`, `y=-z`. -/
def faceDiagonalReflectionSymmetry : Fin 6 → ImproperVertexSymmetry stellatedVertices
  | 0 => swapXYImproperVertexSymmetry
  | 1 => negSwapXYImproperVertexSymmetry
  | 2 => swapXZImproperVertexSymmetry
  | 3 => negSwapXZImproperVertexSymmetry
  | 4 => swapYZImproperVertexSymmetry
  | 5 => negSwapYZImproperVertexSymmetry

theorem swapXY_reflection_sheet_shadow_eq
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    shadow stellatedVertices
        (reflectionSheetInner R₂ swapXY swapXY_orthogonal swapXY_det) =
      shadow stellatedVertices R₂ := by
  exact improperVertexSymmetry_reflection_sheet_shadow_eq stellatedVertices
    swapXYImproperVertexSymmetry R₂

theorem swapXZ_reflection_sheet_shadow_eq
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    shadow stellatedVertices
        (reflectionSheetInner R₂ swapXZ swapXZ_orthogonal swapXZ_det) =
      shadow stellatedVertices R₂ := by
  exact improperVertexSymmetry_reflection_sheet_shadow_eq stellatedVertices
    swapXZImproperVertexSymmetry R₂

theorem swapYZ_reflection_sheet_shadow_eq
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    shadow stellatedVertices
        (reflectionSheetInner R₂ swapYZ swapYZ_orthogonal swapYZ_det) =
      shadow stellatedVertices R₂ := by
  exact improperVertexSymmetry_reflection_sheet_shadow_eq stellatedVertices
    swapYZImproperVertexSymmetry R₂

theorem negSwapXY_reflection_sheet_shadow_eq
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    shadow stellatedVertices
        (reflectionSheetInner R₂ negSwapXY negSwapXY_orthogonal negSwapXY_det) =
      shadow stellatedVertices R₂ := by
  exact improperVertexSymmetry_reflection_sheet_shadow_eq stellatedVertices
    negSwapXYImproperVertexSymmetry R₂

theorem negSwapXZ_reflection_sheet_shadow_eq
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    shadow stellatedVertices
        (reflectionSheetInner R₂ negSwapXZ negSwapXZ_orthogonal negSwapXZ_det) =
      shadow stellatedVertices R₂ := by
  exact improperVertexSymmetry_reflection_sheet_shadow_eq stellatedVertices
    negSwapXZImproperVertexSymmetry R₂

theorem negSwapYZ_reflection_sheet_shadow_eq
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    shadow stellatedVertices
        (reflectionSheetInner R₂ negSwapYZ negSwapYZ_orthogonal negSwapYZ_det) =
      shadow stellatedVertices R₂ := by
  exact improperVertexSymmetry_reflection_sheet_shadow_eq stellatedVertices
    negSwapYZImproperVertexSymmetry R₂

end RupertStellatedTetrahedron
