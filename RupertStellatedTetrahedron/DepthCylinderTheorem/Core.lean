/-
# The Depth–Cylinder Theorem — formal blueprint

A finite local theorem, *with the translation term*, for Rupert exclusions.

This file is a formalization-in-progress. Statements mirror the paper (`../paper.pdf`, draft
`draft_round_11.md`). The low-level projection, circumradius, relative-coordinate, norm/isometry,
finite proof-carrying flag/slack certificate interface, exact slack decomposition algebra, and depth
duality are now checked against Mathlib. SO(3) exponential surjectivity with the trace-angle norm
is checked in `SO3AxisAngle`. The analytic residual bound and strict half-plane semantics are proof
obligations carried by concrete `ActivePair` certificates.

Paper → Lean map:
  Lemma 3.1 (frame reduction, all R₂)      → `frame_reduction`
  Lemma 4.1 (exact decomposition)          → `exact_decomposition`, `slack_decomp`
  Lemma 5.1 (remainder bound, t-indep.)    → `remainder_bound`, `remainder_t_independent`
  Lemma 6.1 (depth duality)                → `depth_duality`, `exists_flag_kill`
  Lemma 7.1 (exp surjective on SO(3))      → `exp_surjective_SO3`
  eq. (2.1)  (containment ⇒ slacks > 0)     → `containment_imp_slack_pos`
  Theorem 8.1 (Depth–Cylinder Theorem)     → `depth_cylinder_theorem`

Fill-in checklist:
  [x] proj                                                   -- fixed projection `Z`
  [x] circumradius                                          -- finite max norm
  [x] relAngle                                              -- trace/arccos angle on relative SO(3)
  [x] flags, depth                                          -- abstract flags + supremal depth
  [x] ActivePair / flagOf / slack                          -- proof-carrying active flag/slack data
  [x] relCoord + relCoord_normSq + angle_le_relCoord_norm  -- the ℝ⁵ coordinate & isometry
  [x] frame_reduction (3.1)  [x] exact_decomposition (4.1) [x] remainder_bound (certificate form)
  [x] remainder_t_independent (5.1a)
  [x] depth_duality (6.1)    [x] exp_surjective_SO3 (7.1)
  [x] exists_flag_kill  [x] slack_decomp  [x] containment_imp_slack_pos
  [x] depth_cylinder_theorem_cert_of_exp                   -- certificate assembly, explicit exp witness
  [x] depth_cylinder_theorem                               -- certificate assembly using `exp_surjective_SO3`
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.RingTheory.Complex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace DepthCylinderTheorem

/-! ## Setup -/

/-- Ambient 3-space and the projection plane. -/
abbrev V3 := EuclideanSpace ℝ (Fin 3)
abbrev V2 := EuclideanSpace ℝ (Fin 2)

/-- Orthogonal projection `ℝ³ → ℝ²` used for the shadow (the map `Z` of the paper). -/
def proj : V3 →ₗ[ℝ] V2 :=
  Matrix.toLpLin 2 2 ![![0, 1, 0], ![-1, 0, 0]]

@[simp] lemma proj_apply_zero (v : V3) : proj v 0 = v 1 := by
  simp [proj, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] lemma proj_apply_one (v : V3) : proj v 1 = -v 0 := by
  simp [proj, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- A configuration: vertex set `V`, outer/inner rotations `R₂,R₁ ∈ SO(3)`, translation `t`. -/
structure Config (V : Finset V3) where
  R₁ : Matrix.specialOrthogonalGroup (Fin 3) ℝ
  R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ
  t  : V2

/-- Outer shadow `K = conv (proj (R₂ • V))`. -/
def shadow (V : Finset V3) (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) : Set V2 :=
  convexHull ℝ ((fun v => proj (Matrix.toLpLin 2 2 (R₂ : Matrix (Fin 3) (Fin 3) ℝ) v))
    '' (V : Set V3))

/-- Strict Rupert containment: every inner vertex lands in the interior of the outer shadow. -/
def RupertContainment (V : Finset V3) (c : Config V) : Prop :=
  ∀ v ∈ V, proj (Matrix.toLpLin 2 2 (c.R₁ : Matrix (Fin 3) (Fin 3) ℝ) v) + c.t ∈
    interior (shadow V c.R₂)

private def listMaxNorm : List V3 → ℝ
  | [] => 0
  | v :: vs => max ‖v‖ (listMaxNorm vs)

private lemma listMaxNorm_nonneg : ∀ vs : List V3, 0 ≤ listMaxNorm vs
  | [] => by simp [listMaxNorm]
  | v :: vs => by
      simp [listMaxNorm, listMaxNorm_nonneg vs, norm_nonneg v]

private lemma norm_le_listMaxNorm : ∀ {vs : List V3} {v : V3}, v ∈ vs → ‖v‖ ≤ listMaxNorm vs
  | [], _, hv => by cases hv
  | w :: vs, v, hv => by
      rw [listMaxNorm]
      rcases List.mem_cons.mp hv with h | h
      · subst h
        exact le_max_left _ _
      · exact le_trans (norm_le_listMaxNorm h) (le_max_right _ _)

/-- Circumradius of the vertex set (the `ρ` of the constant `M`). -/
def circumradius (V : Finset V3) : ℝ := listMaxNorm V.toList

lemma circumradius_nonneg (V : Finset V3) : 0 ≤ circumradius V :=
  listMaxNorm_nonneg V.toList

lemma norm_le_circumradius {V : Finset V3} {v : V3} (hv : v ∈ V) : ‖v‖ ≤ circumradius V :=
  norm_le_listMaxNorm (Finset.mem_toList.mpr hv)

/-- The skew-symmetric cross-product matrix `[ξ]×`. -/
def skewMatrix (ξ : V3) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![0, -ξ 2, ξ 1],
    ![ξ 2, 0, -ξ 0],
    ![-ξ 1, ξ 0, 0]]

lemma skewMatrix_smul (a : ℝ) (ξ : V3) :
    skewMatrix (a • ξ) = a • skewMatrix ξ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewMatrix]

@[simp] lemma skewMatrix_transpose (ξ : V3) : (skewMatrix ξ)ᵀ = -skewMatrix ξ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewMatrix]

@[simp] lemma skewMatrix_trace (ξ : V3) : Matrix.trace (skewMatrix ξ) = 0 := by
  simp [skewMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_three]

lemma skewMatrix_eq_zero_iff (ξ : V3) :
    skewMatrix ξ = (0 : Matrix (Fin 3) (Fin 3) ℝ) ↔ ξ = 0 := by
  constructor
  · intro h
    ext i
    fin_cases i
    · have hij := congr_fun (congr_fun h 1) 2
      simpa [skewMatrix] using hij
    · have hij := congr_fun (congr_fun h 0) 2
      simpa [skewMatrix] using hij
    · have hij := congr_fun (congr_fun h 1) 0
      simpa [skewMatrix] using hij
  · rintro rfl
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skewMatrix]

def skewVectorOfMatrix (A : Matrix (Fin 3) (Fin 3) ℝ) : V3 :=
  WithLp.toLp 2 ![-A 1 2, A 0 2, -A 0 1]

lemma skewMatrix_skewVectorOfMatrix {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : Aᵀ = -A) : skewMatrix (skewVectorOfMatrix A) = A := by
  have h10 : A 1 0 = -A 0 1 := by
    have h := congr_fun (congr_fun hA 0) 1
    simpa using h
  have h20 : A 2 0 = -A 0 2 := by
    have h := congr_fun (congr_fun hA 0) 2
    simpa using h
  have h21 : A 2 1 = -A 1 2 := by
    have h := congr_fun (congr_fun hA 1) 2
    simpa using h
  have h00 : A 0 0 = 0 := by
    have h : A 0 0 = -A 0 0 := by
      have h' := congr_fun (congr_fun hA 0) 0
      simpa using h'
    linarith
  have h11 : A 1 1 = 0 := by
    have h : A 1 1 = -A 1 1 := by
      have h' := congr_fun (congr_fun hA 1) 1
      simpa using h'
    linarith
  have h22 : A 2 2 = 0 := by
    have h : A 2 2 = -A 2 2 := by
      have h' := congr_fun (congr_fun hA 2) 2
      simpa using h'
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewMatrix, skewVectorOfMatrix, h00, h11, h22, h10, h20, h21]

@[simp] lemma skewVectorOfMatrix_skewMatrix (ξ : V3) :
    skewVectorOfMatrix (skewMatrix ξ) = ξ := by
  ext i
  fin_cases i <;> simp [skewVectorOfMatrix, skewMatrix]

/-- The linear action of `[ξ]×` on a vector, as an element of `EuclideanSpace`. -/
def skewApply (ξ w : V3) : V3 :=
  Matrix.toLpLin 2 2 (skewMatrix ξ) w

lemma skewApply_eq_crossProduct (ξ w : V3) :
    skewApply ξ w = WithLp.toLp 2 ((ξ : Fin 3 → ℝ) ⨯₃ (w : Fin 3 → ℝ)) := by
  ext i
  fin_cases i <;>
    simp [skewApply, skewMatrix, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, cross_apply] <;> ring

@[simp] lemma skewApply_apply_zero (ξ w : V3) :
    skewApply ξ w 0 = -ξ 2 * w 1 + ξ 1 * w 2 := by
  simp [skewApply, skewMatrix, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

@[simp] lemma skewApply_apply_one (ξ w : V3) :
    skewApply ξ w 1 = ξ 2 * w 0 - ξ 0 * w 2 := by
  simp [skewApply, skewMatrix, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]
  ring

@[simp] lemma skewApply_apply_two (ξ w : V3) :
    skewApply ξ w 2 = -ξ 1 * w 0 + ξ 0 * w 1 := by
  simp [skewApply, skewMatrix, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

@[simp] lemma proj_skewApply_apply_zero (ξ w : V3) :
    proj (skewApply ξ w) 0 = ξ 2 * w 0 - ξ 0 * w 2 := by
  simp [proj, skewApply, skewMatrix, Matrix.toLpLin_apply, Matrix.mulVec, Matrix.mul_apply,
    dotProduct, Fin.sum_univ_three]
  ring

@[simp] lemma proj_skewApply_apply_one (ξ w : V3) :
    proj (skewApply ξ w) 1 = ξ 2 * w 1 - ξ 1 * w 2 := by
  simp [proj, skewApply, skewMatrix, Matrix.toLpLin_apply, Matrix.mulVec, Matrix.mul_apply,
    dotProduct, Fin.sum_univ_three]
  ring

/-- Rotation angle of an element of `SO(3)`, via the standard trace formula. -/
def rotationAngleOf (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) : ℝ :=
  Real.arccos ((Matrix.trace (R : Matrix (Fin 3) (Fin 3) ℝ) - 1) / 2)

/-- Rotation angle of `R₁ R₂ᵀ ∈ SO(3)`. -/
def relAngle (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) : ℝ :=
  rotationAngleOf (R₁ * R₂⁻¹)

/-- The relative coordinate `x = ((ξ₂,−ξ₁), ξ₃, t) ∈ ℝ⁵` bundling rotation and translation. -/
def relCoord (ξ : V3) (t : V2) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 fun i : Fin 5 =>
    match i with
    | 0 => ξ 1
    | 1 => -ξ 0
    | 2 => ξ 2
    | 3 => t 0
    | 4 => t 1

@[simp] lemma relCoord_apply_zero (ξ : V3) (t : V2) : relCoord ξ t 0 = ξ 1 := by
  simp [relCoord]

@[simp] lemma relCoord_apply_one (ξ : V3) (t : V2) : relCoord ξ t 1 = -ξ 0 := by
  simp [relCoord]

@[simp] lemma relCoord_apply_two (ξ : V3) (t : V2) : relCoord ξ t 2 = ξ 2 := by
  simp [relCoord]

@[simp] lemma relCoord_apply_three (ξ : V3) (t : V2) : relCoord ξ t 3 = t 0 := by
  simp [relCoord]

@[simp] lemma relCoord_apply_four (ξ : V3) (t : V2) : relCoord ξ t 4 = t 1 := by
  simp [relCoord]

end DepthCylinderTheorem
