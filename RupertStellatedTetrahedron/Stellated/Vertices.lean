import RupertStellatedTetrahedron.Stellated.ReflectionSheets

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

open DepthCylinderTheorem

/-!
## The eight vertices of `P_{11/20}`

The stellated tetrahedron used in the Rupert program is
`conv ({v₁, …, v₄} ∪ {-(11/20) v₁, …, -(11/20) v₄})`, where the tetrahedron vertices are
the four even sign vectors.
-/

/-- The four vertices of the regular tetrahedron, indexed as in the paper. -/
def tetraVertex : Fin 4 → V3
  | 0 => WithLp.toLp 2 ![(1 : ℝ), 1, 1]
  | 1 => WithLp.toLp 2 ![(1 : ℝ), -1, -1]
  | 2 => WithLp.toLp 2 ![(-1 : ℝ), 1, -1]
  | 3 => WithLp.toLp 2 ![(-1 : ℝ), -1, 1]

/-- The stellated partner `pᵢ = -(11/20) vᵢ`. -/
def stellatedApex (i : Fin 4) : V3 :=
  (-(11 / 20 : ℝ)) • tetraVertex i

/-- The eight vertices of `P_{11/20}` as an indexed family. -/
def stellatedVertex : Fin 8 → V3
  | ⟨n, h⟩ =>
      if h4 : n < 4 then
        tetraVertex ⟨n, h4⟩
      else
        stellatedApex ⟨n - 4, by omega⟩

/-- The finite vertex set of `P_{11/20}`. -/
def stellatedVertices : Finset V3 := by
  classical
  exact Finset.univ.image stellatedVertex

@[simp] lemma tetraVertex_zero : tetraVertex 0 = WithLp.toLp 2 ![(1 : ℝ), 1, 1] := rfl
@[simp] lemma tetraVertex_one : tetraVertex 1 = WithLp.toLp 2 ![(1 : ℝ), -1, -1] := rfl
@[simp] lemma tetraVertex_two : tetraVertex 2 = WithLp.toLp 2 ![(-1 : ℝ), 1, -1] := rfl
@[simp] lemma tetraVertex_three : tetraVertex 3 = WithLp.toLp 2 ![(-1 : ℝ), -1, 1] := rfl

@[simp] lemma stellatedVertex_tetra (i : Fin 4) :
    stellatedVertex ⟨i.val, by omega⟩ = tetraVertex i := by
  fin_cases i <;> rfl

@[simp] lemma stellatedVertex_apex (i : Fin 4) :
    stellatedVertex ⟨i.val + 4, by omega⟩ = stellatedApex i := by
  fin_cases i <;> rfl

lemma mem_stellatedVertices_of_index (i : Fin 8) :
    stellatedVertex i ∈ stellatedVertices := by
  classical
  exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩

lemma tetraVertex_mem_stellatedVertices (i : Fin 4) :
    tetraVertex i ∈ stellatedVertices := by
  simpa using mem_stellatedVertices_of_index ⟨i.val, by omega⟩

lemma stellatedApex_mem_stellatedVertices (i : Fin 4) :
    stellatedApex i ∈ stellatedVertices := by
  simpa using mem_stellatedVertices_of_index ⟨i.val + 4, by omega⟩

@[simp] lemma norm_sq_tetraVertex (i : Fin 4) :
    ‖tetraVertex i‖ ^ 2 = (3 : ℝ) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
  · fin_cases i <;> simp [tetraVertex, Fin.sum_univ_three, pow_two] <;> norm_num
  · fin_cases i <;> simp [tetraVertex, Fin.sum_univ_three, pow_two] <;> norm_num

lemma norm_tetraVertex (i : Fin 4) :
    ‖tetraVertex i‖ = Real.sqrt 3 := by
  have h := norm_sq_tetraVertex i
  have hnorm : 0 ≤ ‖tetraVertex i‖ := norm_nonneg _
  have hsqrt : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

lemma norm_stellatedApex (i : Fin 4) :
    ‖stellatedApex i‖ = (11 / 20 : ℝ) * Real.sqrt 3 := by
  have habs : ‖-(11 / 20 : ℝ)‖ = (11 / 20 : ℝ) := by norm_num
  rw [stellatedApex, norm_smul,
    habs, norm_tetraVertex]

lemma norm_stellatedApex_le_tetra (i : Fin 4) :
    ‖stellatedApex i‖ ≤ Real.sqrt 3 := by
  rw [norm_stellatedApex]
  have hsqrt : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
  nlinarith

end RupertStellatedTetrahedron
