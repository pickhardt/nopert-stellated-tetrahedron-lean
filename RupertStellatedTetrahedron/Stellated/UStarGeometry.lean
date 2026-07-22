import RupertStellatedTetrahedron.Stellated.CriticalDirection
import RupertStellatedTetrahedron.Stellated.Vertices

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

open DepthCylinderTheorem

/-!
## Geometry in the `u*` frame

The coordinates here isolate the face-diagonal critical direction
`u* = (1,-1,0)/sqrt 2`. They are deliberately lightweight: the exact active inequalities and
weights will live in the certificate files built on top of these definitions.
-/

def uStarA (v : V3) : ℝ := v 2

def uStarB (v : V3) : ℝ := -((v 0 + v 1) / Real.sqrt 2)

def uStarHeight (v : V3) : ℝ := (v 0 - v 1) / Real.sqrt 2

def uStarProj (v : V3) : V2 :=
  WithLp.toLp 2 ![uStarA v, uStarB v]

lemma two_div_sqrt_two : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hs]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

lemma inv_sqrt_two_mul_two : (Real.sqrt 2)⁻¹ * (2 : ℝ) = Real.sqrt 2 := by
  rw [← div_eq_inv_mul, two_div_sqrt_two]

lemma neg_two_div_sqrt_two : (-2 : ℝ) / Real.sqrt 2 = -Real.sqrt 2 := by
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, neg_div, two_div_sqrt_two]

@[simp] lemma uStarA_smul (a : ℝ) (v : V3) :
    uStarA (a • v) = a * uStarA v := by
  simp [uStarA]

@[simp] lemma uStarB_smul (a : ℝ) (v : V3) :
    uStarB (a • v) = a * uStarB v := by
  simp [uStarB]
  ring

@[simp] lemma uStarHeight_smul (a : ℝ) (v : V3) :
    uStarHeight (a • v) = a * uStarHeight v := by
  simp [uStarHeight]
  ring

@[simp] lemma uStarProj_apply_zero (v : V3) :
    uStarProj v 0 = uStarA v := by
  simp [uStarProj]

@[simp] lemma uStarProj_apply_one (v : V3) :
    uStarProj v 1 = uStarB v := by
  simp [uStarProj]

@[simp] lemma uStarA_tetraVertex_zero :
    uStarA (tetraVertex 0) = 1 := by
  simp [uStarA, tetraVertex]

@[simp] lemma uStarA_tetraVertex_one :
    uStarA (tetraVertex 1) = -1 := by
  simp [uStarA, tetraVertex]

@[simp] lemma uStarA_tetraVertex_two :
    uStarA (tetraVertex 2) = -1 := by
  simp [uStarA, tetraVertex]

@[simp] lemma uStarA_tetraVertex_three :
    uStarA (tetraVertex 3) = 1 := by
  simp [uStarA, tetraVertex]

@[simp] lemma uStarB_tetraVertex_zero :
    uStarB (tetraVertex 0) = -Real.sqrt 2 := by
  simp [uStarB, tetraVertex]
  norm_num

@[simp] lemma uStarB_tetraVertex_one :
    uStarB (tetraVertex 1) = 0 := by
  simp [uStarB, tetraVertex]

@[simp] lemma uStarB_tetraVertex_two :
    uStarB (tetraVertex 2) = 0 := by
  simp [uStarB, tetraVertex]

@[simp] lemma uStarB_tetraVertex_three :
    uStarB (tetraVertex 3) = Real.sqrt 2 := by
  simp [uStarB, tetraVertex]
  rw [show ((-1 : ℝ) + -1) = -2 by norm_num]
  rw [neg_two_div_sqrt_two]
  ring

@[simp] lemma uStarHeight_tetraVertex_zero :
    uStarHeight (tetraVertex 0) = 0 := by
  simp [uStarHeight, tetraVertex]

@[simp] lemma uStarHeight_tetraVertex_one :
    uStarHeight (tetraVertex 1) = Real.sqrt 2 := by
  simp [uStarHeight, tetraVertex]
  norm_num

@[simp] lemma uStarHeight_tetraVertex_two :
    uStarHeight (tetraVertex 2) = -Real.sqrt 2 := by
  simp [uStarHeight, tetraVertex]
  rw [show ((-1 : ℝ) - 1) = -2 by norm_num]
  exact neg_two_div_sqrt_two

@[simp] lemma uStarHeight_tetraVertex_three :
    uStarHeight (tetraVertex 3) = 0 := by
  simp [uStarHeight, tetraVertex]

@[simp] lemma uStarA_stellatedApex (i : Fin 4) :
    uStarA (stellatedApex i) = -(11 / 20 : ℝ) * uStarA (tetraVertex i) := by
  unfold stellatedApex
  rw [uStarA_smul]

@[simp] lemma uStarB_stellatedApex (i : Fin 4) :
    uStarB (stellatedApex i) = -(11 / 20 : ℝ) * uStarB (tetraVertex i) := by
  unfold stellatedApex
  rw [uStarB_smul]

@[simp] lemma uStarHeight_stellatedApex (i : Fin 4) :
    uStarHeight (stellatedApex i) = -(11 / 20 : ℝ) * uStarHeight (tetraVertex i) := by
  unfold stellatedApex
  rw [uStarHeight_smul]

@[simp] lemma uStarA_stellatedApex_zero :
    uStarA (stellatedApex 0) = -(11 / 20 : ℝ) := by
  rw [uStarA_stellatedApex, uStarA_tetraVertex_zero]
  ring

@[simp] lemma uStarA_stellatedApex_one :
    uStarA (stellatedApex 1) = 11 / 20 := by
  rw [uStarA_stellatedApex, uStarA_tetraVertex_one]
  ring

@[simp] lemma uStarA_stellatedApex_two :
    uStarA (stellatedApex 2) = 11 / 20 := by
  rw [uStarA_stellatedApex, uStarA_tetraVertex_two]
  ring

@[simp] lemma uStarA_stellatedApex_three :
    uStarA (stellatedApex 3) = -(11 / 20 : ℝ) := by
  rw [uStarA_stellatedApex, uStarA_tetraVertex_three]
  ring

@[simp] lemma uStarB_stellatedApex_zero :
    uStarB (stellatedApex 0) = (11 / 20 : ℝ) * Real.sqrt 2 := by
  rw [uStarB_stellatedApex, uStarB_tetraVertex_zero]
  ring

@[simp] lemma uStarB_stellatedApex_one :
    uStarB (stellatedApex 1) = 0 := by
  rw [uStarB_stellatedApex, uStarB_tetraVertex_one]
  ring

@[simp] lemma uStarB_stellatedApex_two :
    uStarB (stellatedApex 2) = 0 := by
  rw [uStarB_stellatedApex, uStarB_tetraVertex_two]
  ring

@[simp] lemma uStarB_stellatedApex_three :
    uStarB (stellatedApex 3) = -(11 / 20 : ℝ) * Real.sqrt 2 := by
  rw [uStarB_stellatedApex, uStarB_tetraVertex_three]

@[simp] lemma uStarHeight_stellatedApex_zero :
    uStarHeight (stellatedApex 0) = 0 := by
  rw [uStarHeight_stellatedApex, uStarHeight_tetraVertex_zero]
  ring

@[simp] lemma uStarHeight_stellatedApex_one :
    uStarHeight (stellatedApex 1) = -(11 / 20 : ℝ) * Real.sqrt 2 := by
  rw [uStarHeight_stellatedApex, uStarHeight_tetraVertex_one]

@[simp] lemma uStarHeight_stellatedApex_two :
    uStarHeight (stellatedApex 2) = (11 / 20 : ℝ) * Real.sqrt 2 := by
  rw [uStarHeight_stellatedApex, uStarHeight_tetraVertex_two]
  ring

@[simp] lemma uStarHeight_stellatedApex_three :
    uStarHeight (stellatedApex 3) = 0 := by
  rw [uStarHeight_stellatedApex, uStarHeight_tetraVertex_three]
  ring

lemma uStarProj_tetraVertex_one_eq_two :
    uStarProj (tetraVertex 1) = uStarProj (tetraVertex 2) := by
  ext i
  fin_cases i <;> simp [uStarProj, uStarA, uStarB, tetraVertex]

lemma uStarHeight_tetraVertex_one_eq_neg_two :
    uStarHeight (tetraVertex 1) = -uStarHeight (tetraVertex 2) := by
  rw [uStarHeight_tetraVertex_one, uStarHeight_tetraVertex_two]
  ring

lemma uStarProj_stellatedApex_one_eq_two :
    uStarProj (stellatedApex 1) = uStarProj (stellatedApex 2) := by
  ext i
  fin_cases i <;> simp [uStarProj, uStarA, uStarB, stellatedApex, tetraVertex]

/-- The diagonal corner in the `u*` planar coordinates. -/
def uStarDiagonalCorner : V2 := 0

/-- The coincident tetrahedron vertex corner in the `u*` planar coordinates. -/
def uStarCoincidentTetraCorner : V2 := uStarProj (tetraVertex 1)

lemma uStarCoincidentTetraCorner_eq :
    uStarCoincidentTetraCorner = WithLp.toLp 2 ![(-1 : ℝ), 0] := by
  ext i
  fin_cases i <;> simp [uStarCoincidentTetraCorner, uStarProj, uStarA, uStarB, tetraVertex]

lemma uStarProj_tetraVertex_two_eq_coincident_corner :
    uStarProj (tetraVertex 2) = uStarCoincidentTetraCorner := by
  rw [← uStarProj_tetraVertex_one_eq_two]
  rfl

/-- The twelve active incidences at `u*`.

The doubled projected corner contributes both tetrahedron vertices on each adjacent edge, so the
two edges adjacent to that corner have three metric active flags rather than two.
-/
inductive UStarActiveFlagIndex
  | edgeV4P1_v4
  | edgeV4P1_p1
  | edgeP1D_p1
  | edgeP1D_v2
  | edgeP1D_v3
  | edgeDP4_v2
  | edgeDP4_v3
  | edgeDP4_p4
  | edgeP4V1_p4
  | edgeP4V1_v1
  | edgeV1V4_v1
  | edgeV1V4_v4
  deriving DecidableEq, Fintype, Repr

/-- The vertex carrying a named active incidence. -/
def UStarActiveFlagIndex.vertex : UStarActiveFlagIndex → V3
  | .edgeV4P1_v4 => tetraVertex 3
  | .edgeV4P1_p1 => stellatedApex 0
  | .edgeP1D_p1 => stellatedApex 0
  | .edgeP1D_v2 => tetraVertex 1
  | .edgeP1D_v3 => tetraVertex 2
  | .edgeDP4_v2 => tetraVertex 1
  | .edgeDP4_v3 => tetraVertex 2
  | .edgeDP4_p4 => stellatedApex 3
  | .edgeP4V1_p4 => stellatedApex 3
  | .edgeP4V1_v1 => tetraVertex 0
  | .edgeV1V4_v1 => tetraVertex 0
  | .edgeV1V4_v4 => tetraVertex 3

/-- First endpoint of the active shadow edge associated with an incidence. -/
def UStarActiveFlagIndex.edgeStart : UStarActiveFlagIndex → V2
  | .edgeV4P1_v4 => uStarProj (tetraVertex 3)
  | .edgeV4P1_p1 => uStarProj (tetraVertex 3)
  | .edgeP1D_p1 => uStarProj (stellatedApex 0)
  | .edgeP1D_v2 => uStarProj (stellatedApex 0)
  | .edgeP1D_v3 => uStarProj (stellatedApex 0)
  | .edgeDP4_v2 => uStarCoincidentTetraCorner
  | .edgeDP4_v3 => uStarCoincidentTetraCorner
  | .edgeDP4_p4 => uStarCoincidentTetraCorner
  | .edgeP4V1_p4 => uStarProj (stellatedApex 3)
  | .edgeP4V1_v1 => uStarProj (stellatedApex 3)
  | .edgeV1V4_v1 => uStarProj (tetraVertex 0)
  | .edgeV1V4_v4 => uStarProj (tetraVertex 0)

/-- Second endpoint of the active shadow edge associated with an incidence. -/
def UStarActiveFlagIndex.edgeEnd : UStarActiveFlagIndex → V2
  | .edgeV4P1_v4 => uStarProj (stellatedApex 0)
  | .edgeV4P1_p1 => uStarProj (stellatedApex 0)
  | .edgeP1D_p1 => uStarCoincidentTetraCorner
  | .edgeP1D_v2 => uStarCoincidentTetraCorner
  | .edgeP1D_v3 => uStarCoincidentTetraCorner
  | .edgeDP4_v2 => uStarProj (stellatedApex 3)
  | .edgeDP4_v3 => uStarProj (stellatedApex 3)
  | .edgeDP4_p4 => uStarProj (stellatedApex 3)
  | .edgeP4V1_p4 => uStarProj (tetraVertex 0)
  | .edgeP4V1_v1 => uStarProj (tetraVertex 0)
  | .edgeV1V4_v1 => uStarProj (tetraVertex 3)
  | .edgeV1V4_v4 => uStarProj (tetraVertex 3)

lemma UStarActiveFlagIndex.card :
    Fintype.card UStarActiveFlagIndex = 12 := by
  native_decide

end RupertStellatedTetrahedron
