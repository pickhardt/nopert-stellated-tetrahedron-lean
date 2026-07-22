import RupertStellatedTetrahedron.DepthCylinderTheorem.Core
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.NoncommRing

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace DepthCylinderTheorem

lemma exp_skewMatrix_zero :
    NormedSpace.exp (skewMatrix (0 : V3)) = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have h0 : skewMatrix (0 : V3) = (0 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skewMatrix]
  rw [h0, NormedSpace.exp_zero]

lemma rotationAngleOf_one :
    rotationAngleOf (1 : Matrix.specialOrthogonalGroup (Fin 3) ℝ) = 0 := by
  have harg :
      (Matrix.trace ((1 : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
          Matrix (Fin 3) (Fin 3) ℝ) - 1) / 2 = (1 : ℝ) := by
    norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  rw [rotationAngleOf, harg, Real.arccos_one]

lemma exp_surjective_SO3_one :
    ∃ ξ : V3,
      NormedSpace.exp (skewMatrix ξ) =
        ((1 : Matrix.specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) ∧
      ‖ξ‖ = rotationAngleOf (1 : Matrix.specialOrthogonalGroup (Fin 3) ℝ) := by
  refine ⟨0, ?_, ?_⟩
  · exact exp_skewMatrix_zero
  · simp [rotationAngleOf_one]

lemma exp_skewMatrix_transpose (ξ : V3) :
    (NormedSpace.exp (skewMatrix ξ))ᵀ = (NormedSpace.exp (skewMatrix ξ))⁻¹ := by
  rw [← Matrix.exp_transpose, skewMatrix_transpose, Matrix.exp_neg]

lemma exp_skewMatrix_mem_orthogonalGroup (ξ : V3) :
    NormedSpace.exp (skewMatrix ξ) ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ]
  rw [exp_skewMatrix_transpose]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _))

lemma exp_skewMatrix_det_sq (ξ : V3) :
    (NormedSpace.exp (skewMatrix ξ)).det ^ 2 = (1 : ℝ) := by
  have horth := (Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ).mp
    (exp_skewMatrix_mem_orthogonalGroup ξ)
  have hdet := congrArg Matrix.det horth
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  rw [sq]
  exact hdet

lemma exp_skewMatrix_det (ξ : V3) :
    (NormedSpace.exp (skewMatrix ξ)).det = (1 : ℝ) := by
  let f : ℝ → ℝ := fun t => (NormedSpace.exp (skewMatrix (t • ξ))).det
  have hskew_cont : Continuous (fun t : ℝ => skewMatrix (t • ξ)) := by
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j <;> simp [skewMatrix] <;> fun_prop
  have hexp_cont : Continuous (fun t : ℝ => NormedSpace.exp (skewMatrix (t • ξ))) := by
    exact (NormedSpace.exp_continuous (𝔸 := Matrix (Fin 3) (Fin 3) ℝ)).comp hskew_cont
  have hfcont : ContinuousOn f Set.univ := by
    exact hexp_cont.matrix_det.continuousOn
  have hsq : Set.EqOn (f ^ 2) (1 : ℝ → ℝ) Set.univ := by
    intro t ht
    change f t ^ 2 = (1 : ℝ)
    exact exp_skewMatrix_det_sq (t • ξ)
  rcases isPreconnected_univ.eq_one_or_eq_neg_one_of_sq_eq hfcont hsq with h | h
  · simpa [f] using h (x := 1) trivial
  · have h0 := h (x := 0) trivial
    have hf0 : f 0 = (1 : ℝ) := by
      simp [f, exp_skewMatrix_zero]
    rw [hf0] at h0
    norm_num at h0

lemma exp_skewMatrix_mem_specialOrthogonalGroup (ξ : V3) :
    NormedSpace.exp (skewMatrix ξ) ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  exact (Matrix.mem_specialOrthogonalGroup_iff).mpr
    ⟨exp_skewMatrix_mem_orthogonalGroup ξ, exp_skewMatrix_det ξ⟩

lemma exp_surjective_SO3_of_skew_log (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : Aᵀ = -A)
    (hExp : NormedSpace.exp A = (R : Matrix (Fin 3) (Fin 3) ℝ))
    (hNorm : ‖skewVectorOfMatrix A‖ = rotationAngleOf R) :
    ∃ ξ : V3, NormedSpace.exp (skewMatrix ξ) = (R : Matrix (Fin 3) (Fin 3) ℝ) ∧
      ‖ξ‖ = rotationAngleOf R := by
  refine ⟨skewVectorOfMatrix A, ?_, hNorm⟩
  rw [skewMatrix_skewVectorOfMatrix hA]
  exact hExp

def zAxisVec (θ : ℝ) : V3 := WithLp.toLp 2 ![(0 : ℝ), 0, θ]

lemma skewMatrix_zAxisVec (θ : ℝ) :
    skewMatrix (zAxisVec θ) = !![(0 : ℝ), -θ, 0; θ, 0, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zAxisVec, skewMatrix]

lemma norm_zAxisVec_of_nonneg {θ : ℝ} (hθ : 0 ≤ θ) :
    ‖zAxisVec θ‖ = θ := by
  rw [EuclideanSpace.norm_eq]
  simp [zAxisVec, Fin.sum_univ_three, hθ]

abbrev axisBlockSize : Bool → Type
  | false => Fin 2
  | true => Fin 1

instance axisBlockSizeFintype (b : Bool) : Fintype (axisBlockSize b) := by
  cases b <;> infer_instance

instance axisBlockSizeDecEq (b : Bool) : DecidableEq (axisBlockSize b) := by
  cases b <;> infer_instance

def axisSkewBlocks (θ : ℝ) : (b : Bool) → Matrix (axisBlockSize b) (axisBlockSize b) ℝ
  | false => !![(0 : ℝ), -θ; θ, 0]
  | true => 0

def axisRotBlocks (θ : ℝ) : (b : Bool) → Matrix (axisBlockSize b) (axisBlockSize b) ℝ
  | false => !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]
  | true => 1

lemma exists_angle_of_sq_add_sq_eq_one {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = a ∧ Real.sin θ = b := by
  let z : Circle := ⟨(a : ℂ) + (b : ℂ) * Complex.I, by
    rw [Submonoid.unitSphere]
    exact mem_sphere_zero_iff_norm.2 (by
      rw [Complex.norm_def, Complex.normSq_add_mul_I, h, Real.sqrt_one])⟩
  rcases Circle.exp_surjective z with ⟨θ, hθ⟩
  refine ⟨θ, ?_, ?_⟩
  · have hc := congrArg (fun w : Circle => (w : ℂ).re) hθ
    simpa [z, Circle.coe_exp, Complex.exp_ofReal_mul_I_re] using hc
  · have hs := congrArg (fun w : Circle => (w : ℂ).im) hθ
    simpa [z, Circle.coe_exp, Complex.exp_ofReal_mul_I_im] using hs

lemma exists_angle_of_SO2 {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hM : M ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    ∃ θ : ℝ, M = !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := by
  obtain ⟨h00, h01, hsq⟩ := (Matrix.mem_specialOrthogonalGroup_fin_two_iff).mp hM
  have hsq' : M 0 0 ^ 2 + (-M 0 1) ^ 2 = 1 := by
    simpa [sq] using hsq
  obtain ⟨θ, hcos, hsin⟩ := exists_angle_of_sq_add_sq_eq_one hsq'
  refine ⟨θ, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hcos, hsin, h00, h01]

lemma leftMulMatrix_complex_continuous :
    Continuous (Algebra.leftMulMatrix Complex.basisOneI : ℂ → Matrix (Fin 2) (Fin 2) ℝ) := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Algebra.leftMulMatrix_complex] <;> fun_prop

set_option backward.isDefEq.respectTransparency false in
lemma exp_planar_skew (θ : ℝ) :
    NormedSpace.exp (!![(0 : ℝ), -θ; θ, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := by
  have hmap := NormedSpace.map_exp
    (Algebra.leftMulMatrix Complex.basisOneI)
    leftMulMatrix_complex_continuous (θ * Complex.I)
  rw [← Complex.exp_eq_exp_ℂ] at hmap
  rw [Algebra.leftMulMatrix_complex] at hmap
  have h := hmap.symm
  ext i j
  have hij := congr_fun (congr_fun h i) j
  fin_cases i <;> fin_cases j <;>
    simpa [Complex.exp_ofReal_mul_I, Algebra.leftMulMatrix_complex,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re] using hij

lemma exp_surjective_SO2 (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : M ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    ∃ θ : ℝ, NormedSpace.exp (!![(0 : ℝ), -θ; θ, 0] : Matrix (Fin 2) (Fin 2) ℝ) = M := by
  obtain ⟨θ, hθ⟩ := exists_angle_of_SO2 hM
  refine ⟨θ, ?_⟩
  rw [exp_planar_skew, hθ]

set_option backward.isDefEq.respectTransparency false in
lemma exp_axis_blocks (θ : ℝ) :
    NormedSpace.exp (Matrix.blockDiagonal' (axisSkewBlocks θ)) =
      Matrix.blockDiagonal' (axisRotBlocks θ) := by
  rw [Matrix.exp_blockDiagonal']
  rw [Matrix.blockDiagonal'_inj]
  funext b
  cases b
  · simpa [axisSkewBlocks, axisRotBlocks] using exp_planar_skew θ
  · ext i j
    fin_cases i
    fin_cases j
    simp [axisSkewBlocks, axisRotBlocks, NormedSpace.exp_zero]

def axisBlockEquivFin3 : Sigma axisBlockSize ≃ Fin 3 where
  toFun
    | ⟨false, i⟩ => Fin.castAdd 1 i
    | ⟨true, i⟩ => Fin.natAdd 2 i
  invFun
    | 0 => ⟨false, (0 : Fin 2)⟩
    | 1 => ⟨false, (1 : Fin 2)⟩
    | 2 => ⟨true, (0 : Fin 1)⟩
  left_inv := by
    rintro ⟨b, i⟩
    cases b
    · fin_cases i <;> rfl
    · fin_cases i
      rfl
  right_inv := by
    intro k
    fin_cases k <;> rfl

lemma axis_skew_reindex (θ : ℝ) :
    Matrix.reindex axisBlockEquivFin3 axisBlockEquivFin3
      (Matrix.blockDiagonal' (axisSkewBlocks θ)) =
      !![(0 : ℝ), -θ, 0; θ, 0, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindex_apply, Matrix.blockDiagonal'_apply, axisBlockEquivFin3, axisSkewBlocks]

lemma axis_rot_reindex (θ : ℝ) :
    Matrix.reindex axisBlockEquivFin3 axisBlockEquivFin3
      (Matrix.blockDiagonal' (axisRotBlocks θ)) =
      !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindex_apply, Matrix.blockDiagonal'_apply, axisBlockEquivFin3, axisRotBlocks];
    rfl

lemma reindexAxisBlock_continuous :
    Continuous
      (Matrix.reindexAlgEquiv ℝ ℝ axisBlockEquivFin3 :
        Matrix (Sigma axisBlockSize) (Sigma axisBlockSize) ℝ ≃ₐ[ℝ]
          Matrix (Fin 3) (Fin 3) ℝ) := by
  apply continuous_matrix
  intro i j
  simp [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  fun_prop

lemma exp_zAxisVec (θ : ℝ) :
    NormedSpace.exp (skewMatrix (zAxisVec θ)) =
      !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1] := by
  have hmap := NormedSpace.map_exp
    (Matrix.reindexAlgEquiv ℝ ℝ axisBlockEquivFin3)
    reindexAxisBlock_continuous
    (Matrix.blockDiagonal' (axisSkewBlocks θ))
  rw [Matrix.coe_reindexAlgEquiv] at hmap
  have hleft :
      Matrix.reindex axisBlockEquivFin3 axisBlockEquivFin3
        (NormedSpace.exp (Matrix.blockDiagonal' (axisSkewBlocks θ))) =
      Matrix.reindex axisBlockEquivFin3 axisBlockEquivFin3
        (Matrix.blockDiagonal' (axisRotBlocks θ)) := by
    exact congrArg (Matrix.reindex axisBlockEquivFin3 axisBlockEquivFin3) (exp_axis_blocks θ)
  have htarget := hmap.symm.trans hleft
  rw [axis_rot_reindex, axis_skew_reindex] at htarget
  rw [skewMatrix_zAxisVec]
  exact htarget

lemma trace_axisRotationMatrix (θ : ℝ) :
    Matrix.trace (!![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) ℝ) = 2 * Real.cos θ + 1 := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  ring

lemma rotationAngleOf_axisRotation {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    {R : Matrix.specialOrthogonalGroup (Fin 3) ℝ}
    (hR : (R : Matrix (Fin 3) (Fin 3) ℝ) =
      !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]) :
    rotationAngleOf R = θ := by
  have harg :
      (Matrix.trace (R : Matrix (Fin 3) (Fin 3) ℝ) - 1) / 2 = Real.cos θ := by
    rw [hR, trace_axisRotationMatrix]
    ring
  rw [rotationAngleOf, harg, Real.arccos_cos hθ0 hθπ]

lemma exp_surjective_SO3_axisRotation {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hR : (R : Matrix (Fin 3) (Fin 3) ℝ) =
      !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]) :
    ∃ ξ : V3, NormedSpace.exp (skewMatrix ξ) = (R : Matrix (Fin 3) (Fin 3) ℝ) ∧
      ‖ξ‖ = rotationAngleOf R := by
  refine ⟨zAxisVec θ, ?_, ?_⟩
  · rw [exp_zAxisVec, ← hR]
  · rw [norm_zAxisVec_of_nonneg hθ0, rotationAngleOf_axisRotation hθ0 hθπ hR]

lemma exp_matrix_conj (P A : Matrix (Fin 3) (Fin 3) ℝ) (hP : IsUnit P.det) :
    NormedSpace.exp (P * A * P⁻¹) = P * NormedSpace.exp A * P⁻¹ := by
  exact (NormedSpace.exp_units_conj (Matrix.nonsingInvUnit (A := P) hP) A)

def axisRotationMatrix (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]

def axisSkewConj (P : Matrix (Fin 3) (Fin 3) ℝ) (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  P * skewMatrix (zAxisVec θ) * P⁻¹

@[simp] lemma axisSkewConj_one (θ : ℝ) :
    axisSkewConj (1 : Matrix (Fin 3) (Fin 3) ℝ) θ = skewMatrix (zAxisVec θ) := by
  simp [axisSkewConj]

lemma axisSkewConj_one_norm {θ : ℝ} (hθ : 0 ≤ θ) :
    ‖skewVectorOfMatrix (axisSkewConj (1 : Matrix (Fin 3) (Fin 3) ℝ) θ)‖ = θ := by
  simp [norm_zAxisVec_of_nonneg hθ]

lemma axisSkewConj_transpose_of_inv_eq_transpose (P : Matrix (Fin 3) (Fin 3) ℝ) (θ : ℝ)
    (hPinv : P⁻¹ = Pᵀ) :
    (axisSkewConj P θ)ᵀ = -axisSkewConj P θ := by
  have hPinvT : (P⁻¹)ᵀ = P := by
    simpa using congrArg Matrix.transpose hPinv
  rw [axisSkewConj, Matrix.transpose_mul, Matrix.transpose_mul, skewMatrix_transpose,
    hPinvT, hPinv]
  noncomm_ring

lemma inv_eq_transpose_of_mem_orthogonal (P : Matrix (Fin 3) (Fin 3) ℝ)
    (hP : P ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    P⁻¹ = Pᵀ :=
  Matrix.inv_eq_right_inv ((Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ).mp hP)

lemma specialOrthogonal_inv_eq_transpose (P : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ((P : Matrix (Fin 3) (Fin 3) ℝ)⁻¹) =
      ((P : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) := by
  exact inv_eq_transpose_of_mem_orthogonal (P : Matrix (Fin 3) (Fin 3) ℝ)
    (Matrix.mem_specialOrthogonalGroup_iff.mp P.property).1

lemma axisRotationMatrix_eq (θ : ℝ) :
    axisRotationMatrix θ =
      !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1] := rfl

lemma rotationAngleOf_conj_axisRotation {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (P : Matrix (Fin 3) (Fin 3) ℝ) (hP : IsUnit P.det)
    {R : Matrix.specialOrthogonalGroup (Fin 3) ℝ}
    (hR : (R : Matrix (Fin 3) (Fin 3) ℝ) = P * axisRotationMatrix θ * P⁻¹) :
    rotationAngleOf R = θ := by
  have htrace :
      Matrix.trace (R : Matrix (Fin 3) (Fin 3) ℝ) = 2 * Real.cos θ + 1 := by
    rw [hR, Matrix.trace_conj ((Matrix.isUnit_iff_isUnit_det P).mpr hP),
      axisRotationMatrix_eq, trace_axisRotationMatrix]
  have harg :
      (Matrix.trace (R : Matrix (Fin 3) (Fin 3) ℝ) - 1) / 2 = Real.cos θ := by
    rw [htrace]
    ring
  rw [rotationAngleOf, harg, Real.arccos_cos hθ0 hθπ]

lemma exp_surjective_SO3_of_conj_axisRotation {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (P : Matrix (Fin 3) (Fin 3) ℝ) (hP : IsUnit P.det)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hR : (R : Matrix (Fin 3) (Fin 3) ℝ) = P * axisRotationMatrix θ * P⁻¹)
    (hPinv : P⁻¹ = Pᵀ)
    (hNorm : ‖skewVectorOfMatrix (axisSkewConj P θ)‖ = θ) :
    ∃ ξ : V3, NormedSpace.exp (skewMatrix ξ) = (R : Matrix (Fin 3) (Fin 3) ℝ) ∧
      ‖ξ‖ = rotationAngleOf R := by
  refine exp_surjective_SO3_of_skew_log R (axisSkewConj P θ)
    (axisSkewConj_transpose_of_inv_eq_transpose P θ hPinv) ?_ ?_
  · rw [axisSkewConj, exp_matrix_conj P (skewMatrix (zAxisVec θ)) hP, exp_zAxisVec,
      ← axisRotationMatrix_eq, ← hR]
  · rw [hNorm, rotationAngleOf_conj_axisRotation hθ0 hθπ P hP hR]

lemma exp_surjective_SO3_of_conj_axisRotation_SO {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθπ : θ ≤ Real.pi)
    (P : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hR : (R : Matrix (Fin 3) (Fin 3) ℝ) =
      (P : Matrix (Fin 3) (Fin 3) ℝ) * axisRotationMatrix θ *
        ((P : Matrix (Fin 3) (Fin 3) ℝ)⁻¹))
    (hNorm : ‖skewVectorOfMatrix (axisSkewConj (P : Matrix (Fin 3) (Fin 3) ℝ) θ)‖ = θ) :
    ∃ ξ : V3, NormedSpace.exp (skewMatrix ξ) = (R : Matrix (Fin 3) (Fin 3) ℝ) ∧
      ‖ξ‖ = rotationAngleOf R := by
  have hPdet : IsUnit (P : Matrix (Fin 3) (Fin 3) ℝ).det := by
    rw [(Matrix.mem_specialOrthogonalGroup_iff.mp P.property).2]
    exact isUnit_one
  exact exp_surjective_SO3_of_conj_axisRotation hθ0 hθπ
    (P : Matrix (Fin 3) (Fin 3) ℝ) hPdet R hR
    (specialOrthogonal_inv_eq_transpose P) hNorm

structure SO3AxisAngleData (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) where
  θ : ℝ
  hθ0 : 0 ≤ θ
  hθπ : θ ≤ Real.pi
  P : Matrix.specialOrthogonalGroup (Fin 3) ℝ
  hR : (R : Matrix (Fin 3) (Fin 3) ℝ) =
    (P : Matrix (Fin 3) (Fin 3) ℝ) * axisRotationMatrix θ *
      ((P : Matrix (Fin 3) (Fin 3) ℝ)⁻¹)
  hNorm : ‖skewVectorOfMatrix (axisSkewConj (P : Matrix (Fin 3) (Fin 3) ℝ) θ)‖ = θ

lemma exp_surjective_SO3_of_axisAngleData
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (d : SO3AxisAngleData R) :
    ∃ ξ : V3, NormedSpace.exp (skewMatrix ξ) = (R : Matrix (Fin 3) (Fin 3) ℝ) ∧
      ‖ξ‖ = rotationAngleOf R := by
  exact exp_surjective_SO3_of_conj_axisRotation_SO d.hθ0 d.hθπ d.P R d.hR d.hNorm

end DepthCylinderTheorem
