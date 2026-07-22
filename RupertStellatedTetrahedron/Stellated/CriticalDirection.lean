import RupertStellatedTetrahedron.Stellated.Symmetry

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

open DepthCylinderTheorem

/-!
## Face-diagonal critical directions

The six unoriented critical directions are the normals to the reflection planes
`x = ± y`, `x = ± z`, and `y = ± z`.
-/

def criticalDirection : Fin 6 → V3
  | 0 => (Real.sqrt 2 / 2 : ℝ) • WithLp.toLp 2 ![(1 : ℝ), -1, 0]
  | 1 => (Real.sqrt 2 / 2 : ℝ) • WithLp.toLp 2 ![(1 : ℝ), 1, 0]
  | 2 => (Real.sqrt 2 / 2 : ℝ) • WithLp.toLp 2 ![(1 : ℝ), 0, -1]
  | 3 => (Real.sqrt 2 / 2 : ℝ) • WithLp.toLp 2 ![(1 : ℝ), 0, 1]
  | 4 => (Real.sqrt 2 / 2 : ℝ) • WithLp.toLp 2 ![(0 : ℝ), 1, -1]
  | 5 => (Real.sqrt 2 / 2 : ℝ) • WithLp.toLp 2 ![(0 : ℝ), 1, 1]

/-- The paper's base critical direction `u* = (1,-1,0)/sqrt 2`. -/
def uStar : V3 := criticalDirection 0

@[simp] lemma uStar_apply_zero : uStar 0 = Real.sqrt 2 / 2 := by
  simp [uStar, criticalDirection]

@[simp] lemma uStar_apply_one : uStar 1 = -Real.sqrt 2 / 2 := by
  simp [uStar, criticalDirection]
  ring

@[simp] lemma uStar_apply_two : uStar 2 = 0 := by
  simp [uStar, criticalDirection]

lemma norm_criticalDirection (i : Fin 6) :
    ‖criticalDirection i‖ = 1 := by
  have hsqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  fin_cases i <;>
    simp [criticalDirection.eq_def, norm_smul,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 2 / 2),
      EuclideanSpace.norm_eq, Fin.sum_univ_three, pow_two] <;>
    nlinarith

lemma norm_uStar : ‖uStar‖ = 1 := by
  simpa [uStar] using norm_criticalDirection 0

lemma swapXY_neg_uStar :
    matrixAction swapXY uStar = -uStar := by
  ext i
  fin_cases i
  · simp [uStar, criticalDirection, matrixAction, swapXY, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]
  · simp [uStar, criticalDirection, matrixAction, swapXY, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]
  · simp [uStar, criticalDirection, matrixAction, swapXY, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]

lemma swapXZ_uStar_eq_neg_criticalDirection_four :
    matrixAction swapXZ uStar = -criticalDirection 4 := by
  ext i
  fin_cases i
  · simp [uStar, criticalDirection, matrixAction, swapXZ, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]
  · simp [uStar, criticalDirection, matrixAction, swapXZ, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]
  · simp [uStar, criticalDirection, matrixAction, swapXZ, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]

lemma swapYZ_uStar_eq_criticalDirection_two :
    matrixAction swapYZ uStar = criticalDirection 2 := by
  ext i
  fin_cases i
  · simp [uStar, criticalDirection, matrixAction, swapYZ, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]
  · simp [uStar, criticalDirection, matrixAction, swapYZ, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]
  · simp [uStar, criticalDirection, matrixAction, swapYZ, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]

theorem faceDiagonalReflection_flips_criticalDirection (i : Fin 6) :
    matrixAction (faceDiagonalReflectionSymmetry i).matrix (criticalDirection i) =
      -criticalDirection i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [faceDiagonalReflectionSymmetry, swapXYImproperVertexSymmetry,
      negSwapXYImproperVertexSymmetry, swapXZImproperVertexSymmetry,
      negSwapXZImproperVertexSymmetry, swapYZImproperVertexSymmetry,
      negSwapYZImproperVertexSymmetry, criticalDirection, matrixAction, swapXY, negSwapXY,
      swapXZ, negSwapXZ, swapYZ, negSwapYZ, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]

end RupertStellatedTetrahedron
