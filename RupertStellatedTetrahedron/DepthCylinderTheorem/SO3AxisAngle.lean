import RupertStellatedTetrahedron.DepthCylinderTheorem.SO3Exp

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace DepthCylinderTheorem

/-!
## Axis-angle decomposition for `SO(3)`

`SO3Exp` proves that any matrix already presented as a conjugate of a standard axis rotation
has the required exponential logarithm with the trace-angle norm. This file supplies the
geometric input: every non-identity element of `SO(3)` admits such an axis-angle presentation.
-/

lemma exists_mulVec_eq_zero_of_det_eq_zero
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hdet : A.det = 0) :
    ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ A *ᵥ v = 0 := by
  have hker : LinearMap.ker (Matrix.toLin' A) ≠ ⊥ := by
    rw [← LinearMap.det_eq_zero_iff_ker_ne_bot]
    rwa [LinearMap.det_toLin']
  obtain ⟨v, hvker, hv0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨v, hv0, hvker⟩

lemma det_sub_one_eq_zero_of_mem_SO3
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ((R : Matrix (Fin 3) (Fin 3) ℝ) - 1).det = 0 := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := R
  have hdetA : A.det = 1 := (Matrix.mem_specialOrthogonalGroup_iff.mp R.property).2
  have hunitA : IsUnit A.det := by
    rw [hdetA]
    exact isUnit_one
  have hAinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hunitA
  have hPinv : A⁻¹ = Aᵀ := specialOrthogonal_inv_eq_transpose R
  have htranspose :
      (A - 1).det = (Aᵀ - 1).det := by
    rw [← Matrix.det_transpose]
    simp [Matrix.transpose_sub]
  have hfactor : A⁻¹ - 1 = A⁻¹ * (1 - A) := by
    rw [Matrix.mul_sub, Matrix.mul_one, hAinv]
  have hdetInv : A⁻¹.det = 1 := by
    rw [Matrix.det_nonsing_inv, hdetA]
    norm_num
  have hneg : (1 - A).det = -((A - 1).det) := by
    calc
      (1 - A).det = (-(A - 1)).det := by
        congr 1
        abel
      _ = (-1 : ℝ) ^ Fintype.card (Fin 3) * (A - 1).det := Matrix.det_neg (A - 1)
      _ = -((A - 1).det) := by norm_num
  have hmain : (A - 1).det = -((A - 1).det) := by
    calc
      (A - 1).det = (Aᵀ - 1).det := htranspose
      _ = (A⁻¹ - 1).det := by rw [hPinv]
      _ = (A⁻¹ * (1 - A)).det := by rw [hfactor]
      _ = A⁻¹.det * (1 - A).det := Matrix.det_mul _ _
      _ = -((A - 1).det) := by rw [hdetInv, hneg]; ring
  linarith

lemma exists_fixed_vector_of_mem_SO3
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ (R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v = v := by
  obtain ⟨v, hv0, hvker⟩ :=
    exists_mulVec_eq_zero_of_det_eq_zero
      ((R : Matrix (Fin 3) (Fin 3) ℝ) - 1)
      (det_sub_one_eq_zero_of_mem_SO3 R)
  refine ⟨v, hv0, ?_⟩
  ext i
  have hi := congr_fun hvker i
  have hi' : ((R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) i - v i = 0 := by
    simpa [Matrix.sub_mulVec, Matrix.one_mulVec] using hi
  linarith

lemma dotProduct_mulVec_of_mem_SO3
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (u v : Fin 3 → ℝ) :
    ((R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u) ⬝ᵥ
      ((R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) = u ⬝ᵥ v := by
  have horth :
      ((R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) * (R : Matrix (Fin 3) (Fin 3) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := Fin 3) ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp R.property).1
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, horth,
    Matrix.vecMul_one]

lemma dotProduct_mulVec_self_of_mem_SO3
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    ((R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ⬝ᵥ
      ((R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) = v ⬝ᵥ v :=
  dotProduct_mulVec_of_mem_SO3 R v v

lemma fixed_axis_orthogonal_plane_invariant
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) {v w : Fin 3 → ℝ}
    (hvfix : (R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v = v)
    (hw : w ⬝ᵥ v = 0) :
    ((R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w) ⬝ᵥ v = 0 := by
  rw [← hvfix, dotProduct_mulVec_of_mem_SO3 R w v, hw]

lemma exists_fixed_axis_of_mem_SO3
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ v : V3, v ≠ 0 ∧
      Matrix.toLpLin 2 2 (R : Matrix (Fin 3) (Fin 3) ℝ) v = v := by
  obtain ⟨v, hv0, hvfix⟩ := exists_fixed_vector_of_mem_SO3 R
  refine ⟨WithLp.toLp 2 v, ?_, ?_⟩
  · intro hv
    apply hv0
    simpa using congrArg (WithLp.ofLp) hv
  · rw [Matrix.toLpLin_toLp]
    simpa [Matrix.toLin'_apply] using congrArg (WithLp.toLp 2) hvfix

lemma exists_unit_fixed_axis_of_mem_SO3
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ u : V3, u ≠ 0 ∧ ‖u‖ = 1 ∧
      Matrix.toLpLin 2 2 (R : Matrix (Fin 3) (Fin 3) ℝ) u = u := by
  obtain ⟨v, hv0, hvfix⟩ := exists_fixed_axis_of_mem_SO3 R
  let u : V3 := (‖v‖)⁻¹ • v
  have hvnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hunorm : ‖u‖ = 1 := by
    change ‖(‖v‖)⁻¹ • v‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvnorm_pos),
      inv_mul_cancel₀ hvnorm_pos.ne']
  refine ⟨u, ?_, hunorm, ?_⟩
  · exact fun hu0 => by
      have : ‖u‖ = 0 := by simp [hu0]
      linarith
  · change Matrix.toLpLin 2 2 (R : Matrix (Fin 3) (Fin 3) ℝ) ((‖v‖)⁻¹ • v) =
      (‖v‖)⁻¹ • v
    rw [map_smul, hvfix]

lemma finrank_V3 : Module.finrank ℝ V3 = 3 := by
  simp

lemma exists_orthonormalBasis_with_axis
    (u : V3) (hu : ‖u‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ V3, b 2 = u := by
  let v : Fin 3 → V3 := Function.update (fun _ : Fin 3 => 0) 2 u
  let s : Set (Fin 3) := {i | i = 2}
  have hv : Orthonormal ℝ (({i : Fin 3 | i = 2} : Set (Fin 3)).restrict v) := by
    constructor
    · intro i
      have hi : (i : Fin 3) = 2 := i.property
      simp [Set.restrict, v, hi, hu]
    · intro i j hij
      have hi : (i : Fin 3) = 2 := i.property
      have hj : (j : Fin 3) = 2 := j.property
      exfalso
      apply hij
      exact Subtype.ext (hi.trans hj.symm)
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℝ) (E := V3) (ι := Fin 3) (by
        rw [finrank_V3]
        simp) hv
  refine ⟨b, ?_⟩
  exact hb 2 (by simp)

def onbMatrix (b : OrthonormalBasis (Fin 3) ℝ V3) : Matrix (Fin 3) (Fin 3) ℝ :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.toMatrix b

lemma onbMatrix_apply (b : OrthonormalBasis (Fin 3) ℝ V3) (i j : Fin 3) :
    onbMatrix b i j = b j i := by
  simp [onbMatrix, Module.Basis.toMatrix_apply, EuclideanSpace.basisFun_repr]

lemma onbMatrix_mem_orthogonalGroup (b : OrthonormalBasis (Fin 3) ℝ V3) :
    onbMatrix b ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  simpa [onbMatrix] using
    (EuclideanSpace.basisFun (Fin 3) ℝ).toMatrix_orthonormalBasis_mem_orthogonal b

lemma onbMatrix_column (b : OrthonormalBasis (Fin 3) ℝ V3) (j : Fin 3) :
    (fun i : Fin 3 => onbMatrix b i j) = b j := by
  ext i
  exact onbMatrix_apply b i j

lemma exists_orthogonal_matrix_with_axis
    (u : V3) (hu : ‖u‖ = 1) :
    ∃ P : Matrix (Fin 3) (Fin 3) ℝ,
      P ∈ Matrix.orthogonalGroup (Fin 3) ℝ ∧
      (fun i : Fin 3 => P i 2) = u := by
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_with_axis u hu
  refine ⟨onbMatrix b, onbMatrix_mem_orthogonalGroup b, ?_⟩
  rw [onbMatrix_column, hb]

def flip0Matrix : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal (fun j : Fin 3 => if j = 0 then -(1 : ℝ) else 1)

lemma flip0Matrix_mem_orthogonalGroup :
    flip0Matrix ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flip0Matrix, Matrix.mul_apply, Fin.sum_univ_three]

lemma flip0Matrix_det :
    flip0Matrix.det = -(1 : ℝ) := by
  simp [flip0Matrix, Matrix.det_diagonal]

lemma mul_flip0Matrix_column_two (P : Matrix (Fin 3) (Fin 3) ℝ) :
    (fun i : Fin 3 => (P * flip0Matrix) i 2) =
      (fun i : Fin 3 => P i 2) := by
  ext i
  fin_cases i <;> simp [flip0Matrix, Matrix.mul_apply, Fin.sum_univ_three]

lemma det_sq_of_mem_orthogonal
    {P : Matrix (Fin 3) (Fin 3) ℝ}
    (hP : P ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    P.det ^ 2 = (1 : ℝ) := by
  have horth := (Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ).mp hP
  have hdet := congrArg Matrix.det horth
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  simpa [sq] using hdet

lemma exists_specialOrthogonal_matrix_with_axis
    (u : V3) (hu : ‖u‖ = 1) :
    ∃ P : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      (fun i : Fin 3 => (P : Matrix (Fin 3) (Fin 3) ℝ) i 2) = u := by
  obtain ⟨P, hPorth, hPcol⟩ := exists_orthogonal_matrix_with_axis u hu
  have hdet_cases : P.det = 1 ∨ P.det = -(1 : ℝ) :=
    sq_eq_one_iff.mp (det_sq_of_mem_orthogonal hPorth)
  rcases hdet_cases with hdet | hdet
  · refine ⟨⟨P, ?_⟩, hPcol⟩
    exact (Matrix.mem_specialOrthogonalGroup_iff).mpr ⟨hPorth, hdet⟩
  · let Q : Matrix (Fin 3) (Fin 3) ℝ := P * flip0Matrix
    have hQorth : Q ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
      exact (Matrix.orthogonalGroup (Fin 3) ℝ).mul_mem hPorth
        (show flip0Matrix ∈ Matrix.orthogonalGroup (Fin 3) ℝ from flip0Matrix_mem_orthogonalGroup)
    have hQdet : Q.det = 1 := by
      change (P * flip0Matrix).det = 1
      rw [Matrix.det_mul, flip0Matrix_det, hdet]
      norm_num
    refine ⟨⟨Q, ?_⟩, ?_⟩
    · exact (Matrix.mem_specialOrthogonalGroup_iff).mpr ⟨hQorth, hQdet⟩
    · change (fun i : Fin 3 => (P * flip0Matrix) i 2) = u
      rw [mul_flip0Matrix_column_two, hPcol]

lemma column_two_sq_sum_of_mem_SO3
    (P : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    (∑ i : Fin 3, (P : Matrix (Fin 3) (Fin 3) ℝ) i 2 ^ 2) = 1 := by
  have horth :
      ((P : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) * (P : Matrix (Fin 3) (Fin 3) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := Fin 3) ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp P.property).1
  have h22 := congr_fun (congr_fun horth 2) 2
  simpa [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, sq] using h22

lemma norm_column_two_of_mem_SO3
    (P : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ‖(WithLp.toLp 2 fun i : Fin 3 =>
      (P : Matrix (Fin 3) (Fin 3) ℝ) i 2 : V3)‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hsum :
      (∑ i : Fin 3, (P : Matrix (Fin 3) (Fin 3) ℝ) i 2 ^ 2) = 1 := by
    exact column_two_sq_sum_of_mem_SO3 P
  have hsum_norm :
      (∑ i : Fin 3, ‖((WithLp.toLp 2 fun i : Fin 3 =>
        (P : Matrix (Fin 3) (Fin 3) ℝ) i 2 : V3).ofLp i)‖ ^ 2) = 1 := by
    simpa [Real.norm_eq_abs, sq_abs] using hsum
  rw [hsum_norm, Real.sqrt_one]

lemma dotProduct_column_column_of_mem_SO3
    (P : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (i j : Fin 3) :
    (fun k : Fin 3 => (P : Matrix (Fin 3) (Fin 3) ℝ) k i) ⬝ᵥ
      (fun k : Fin 3 => (P : Matrix (Fin 3) (Fin 3) ℝ) k j) =
        if i = j then 1 else 0 := by
  have horth :
      ((P : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) * (P : Matrix (Fin 3) (Fin 3) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := Fin 3) ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp P.property).1
  have hij := congr_fun (congr_fun horth i) j
  simpa [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.one_apply] using hij

lemma conjugated_fixed_axis_row_two
    (P R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hfix :
      (R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        (fun i : Fin 3 => (P : Matrix (Fin 3) (Fin 3) ℝ) i 2) =
          (fun i : Fin 3 => (P : Matrix (Fin 3) (Fin 3) ℝ) i 2))
    (j : Fin 3) :
    (((P : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) *
        (R : Matrix (Fin 3) (Fin 3) ℝ) *
        (P : Matrix (Fin 3) (Fin 3) ℝ)) 2 j =
      if j = 2 then 1 else 0 := by
  let col2 : Fin 3 → ℝ := fun i => (P : Matrix (Fin 3) (Fin 3) ℝ) i 2
  let colj : Fin 3 → ℝ := fun i => (P : Matrix (Fin 3) (Fin 3) ℝ) i j
  have hfix_col2 : (R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ col2 = col2 := by
    simpa [col2] using hfix
  have hentry :
      (((P : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) *
          (R : Matrix (Fin 3) (Fin 3) ℝ) *
          (P : Matrix (Fin 3) (Fin 3) ℝ)) 2 j =
        col2 ⬝ᵥ ((R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ colj) := by
    simp [col2, colj, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  rw [hentry]
  calc
    col2 ⬝ᵥ ((R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ colj) =
        ((R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ col2) ⬝ᵥ
          ((R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ colj) := by rw [hfix_col2]
    _ = col2 ⬝ᵥ colj := dotProduct_mulVec_of_mem_SO3 R col2 colj
    _ = if j = 2 then 1 else 0 := by
      simpa [col2, colj, eq_comm] using dotProduct_column_column_of_mem_SO3 P 2 j

lemma conjugated_fixed_axis_col_two
    (P R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hfix :
      (R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        (fun i : Fin 3 => (P : Matrix (Fin 3) (Fin 3) ℝ) i 2) =
          (fun i : Fin 3 => (P : Matrix (Fin 3) (Fin 3) ℝ) i 2))
    (i : Fin 3) :
    (((P : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) *
        (R : Matrix (Fin 3) (Fin 3) ℝ) *
        (P : Matrix (Fin 3) (Fin 3) ℝ)) i 2 =
      if i = 2 then 1 else 0 := by
  let coli : Fin 3 → ℝ := fun k => (P : Matrix (Fin 3) (Fin 3) ℝ) k i
  let col2 : Fin 3 → ℝ := fun k => (P : Matrix (Fin 3) (Fin 3) ℝ) k 2
  have hfix_col2 : (R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ col2 = col2 := by
    simpa [col2] using hfix
  have hentry :
      (((P : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) *
          (R : Matrix (Fin 3) (Fin 3) ℝ) *
          (P : Matrix (Fin 3) (Fin 3) ℝ)) i 2 =
        coli ⬝ᵥ ((R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ col2) := by
    simp [coli, col2, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  rw [hentry, hfix_col2]
  exact dotProduct_column_column_of_mem_SO3 P i 2

def fin2ToFin3 : Fin 2 → Fin 3
  | 0 => 0
  | 1 => 1

def topLeftSO2Block (B : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => B (fin2ToFin3 i) (fin2ToFin3 j)

lemma topLeftSO2Block_mem_orthogonalGroup_of_fixed_axis
    (B : Matrix (Fin 3) (Fin 3) ℝ)
    (horth : B ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (_hrow : ∀ j : Fin 3, B 2 j = if j = 2 then 1 else 0)
    (hcol : ∀ i : Fin 3, B i 2 = if i = 2 then 1 else 0) :
    topLeftSO2Block B ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff (n := Fin 2) ℝ]
  have horth' :
      B * Bᵀ = (1 : Matrix (Fin 3) (Fin 3) ℝ) :=
    (Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ).mp horth
  ext i j
  have hij := congr_fun (congr_fun horth' (fin2ToFin3 i)) (fin2ToFin3 j)
  fin_cases i <;> fin_cases j <;>
    simpa [topLeftSO2Block, fin2ToFin3, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_three, hcol] using hij

lemma topLeftSO2Block_det_of_fixed_axis
    (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hrow : ∀ j : Fin 3, B 2 j = if j = 2 then 1 else 0)
    (hcol : ∀ i : Fin 3, B i 2 = if i = 2 then 1 else 0) :
    (topLeftSO2Block B).det = B.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_three]
  simp [topLeftSO2Block, fin2ToFin3, hrow, hcol]

lemma topLeftSO2Block_mem_specialOrthogonalGroup_of_fixed_axis
    (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hSO : B ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hrow : ∀ j : Fin 3, B 2 j = if j = 2 then 1 else 0)
    (hcol : ∀ i : Fin 3, B i 2 = if i = 2 then 1 else 0) :
    topLeftSO2Block B ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  refine (Matrix.mem_specialOrthogonalGroup_iff).mpr ⟨?_, ?_⟩
  · exact topLeftSO2Block_mem_orthogonalGroup_of_fixed_axis B
      (Matrix.mem_specialOrthogonalGroup_iff.mp hSO).1 hrow hcol
  · rw [topLeftSO2Block_det_of_fixed_axis B hrow hcol]
    exact (Matrix.mem_specialOrthogonalGroup_iff.mp hSO).2

lemma matrix_eq_axisRotationMatrix_of_topLeftSO2Block
    (B : Matrix (Fin 3) (Fin 3) ℝ) (θ : ℝ)
    (hblock : topLeftSO2Block B =
      !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ])
    (hrow : ∀ j : Fin 3, B 2 j = if j = 2 then 1 else 0)
    (hcol : ∀ i : Fin 3, B i 2 = if i = 2 then 1 else 0) :
    B = axisRotationMatrix θ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    try simp [axisRotationMatrix, hrow, hcol]
  · have h := congr_fun (congr_fun hblock 0) 0
    simpa [topLeftSO2Block, fin2ToFin3, axisRotationMatrix] using h
  · have h := congr_fun (congr_fun hblock 0) 1
    simpa [topLeftSO2Block, fin2ToFin3, axisRotationMatrix] using h
  · have h := congr_fun (congr_fun hblock 1) 0
    simpa [topLeftSO2Block, fin2ToFin3, axisRotationMatrix] using h
  · have h := congr_fun (congr_fun hblock 1) 1
    simpa [topLeftSO2Block, fin2ToFin3, axisRotationMatrix] using h

lemma conjugated_mem_specialOrthogonalGroup
    (P R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ((P : Matrix (Fin 3) (Fin 3) ℝ)ᵀ *
        (R : Matrix (Fin 3) (Fin 3) ℝ) *
        (P : Matrix (Fin 3) (Fin 3) ℝ)) ∈
      Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  have hPinvCoe :
      ((P⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ) =
        (P : Matrix (Fin 3) (Fin 3) ℝ)ᵀ := rfl
  have hmem := ((P⁻¹ * R * P : Matrix.specialOrthogonalGroup (Fin 3) ℝ).property)
  change (((P⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
      Matrix (Fin 3) (Fin 3) ℝ) *
        (R : Matrix (Fin 3) (Fin 3) ℝ) *
        (P : Matrix (Fin 3) (Fin 3) ℝ)) ∈
      Matrix.specialOrthogonalGroup (Fin 3) ℝ at hmem
  simpa [hPinvCoe, Matrix.mul_assoc] using hmem

lemma exists_axisRotationMatrix_eq_conjugated_of_fixed_axis
    (P R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hfix :
      (R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        (fun i : Fin 3 => (P : Matrix (Fin 3) (Fin 3) ℝ) i 2) =
          (fun i : Fin 3 => (P : Matrix (Fin 3) (Fin 3) ℝ) i 2)) :
    ∃ θ : ℝ,
      ((P : Matrix (Fin 3) (Fin 3) ℝ)ᵀ *
          (R : Matrix (Fin 3) (Fin 3) ℝ) *
          (P : Matrix (Fin 3) (Fin 3) ℝ)) =
        axisRotationMatrix θ := by
  let B : Matrix (Fin 3) (Fin 3) ℝ :=
    (P : Matrix (Fin 3) (Fin 3) ℝ)ᵀ *
      (R : Matrix (Fin 3) (Fin 3) ℝ) *
      (P : Matrix (Fin 3) (Fin 3) ℝ)
  have hrow : ∀ j : Fin 3, B 2 j = if j = 2 then 1 else 0 := by
    intro j
    exact conjugated_fixed_axis_row_two P R hfix j
  have hcol : ∀ i : Fin 3, B i 2 = if i = 2 then 1 else 0 := by
    intro i
    exact conjugated_fixed_axis_col_two P R hfix i
  have hSO : B ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    conjugated_mem_specialOrthogonalGroup P R
  have hblockSO :
      topLeftSO2Block B ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
    topLeftSO2Block_mem_specialOrthogonalGroup_of_fixed_axis B hSO hrow hcol
  obtain ⟨θ, hθ⟩ := exists_angle_of_SO2 hblockSO
  refine ⟨θ, ?_⟩
  exact matrix_eq_axisRotationMatrix_of_topLeftSO2Block B θ hθ hrow hcol

lemma eq_conj_axisRotation_of_conjugated_eq
    (P R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (θ : ℝ)
    (h :
      ((P : Matrix (Fin 3) (Fin 3) ℝ)ᵀ *
          (R : Matrix (Fin 3) (Fin 3) ℝ) *
          (P : Matrix (Fin 3) (Fin 3) ℝ)) =
        axisRotationMatrix θ) :
    (R : Matrix (Fin 3) (Fin 3) ℝ) =
      (P : Matrix (Fin 3) (Fin 3) ℝ) * axisRotationMatrix θ *
        ((P : Matrix (Fin 3) (Fin 3) ℝ)⁻¹) := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := P
  let B : Matrix (Fin 3) (Fin 3) ℝ := R
  have hPinv : A⁻¹ = Aᵀ := specialOrthogonal_inv_eq_transpose P
  have hPdet : IsUnit A.det := by
    rw [(Matrix.mem_specialOrthogonalGroup_iff.mp P.property).2]
    exact isUnit_one
  have hleft : A * Aᵀ = 1 := by
    exact (Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp P.property).1
  have hright : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hPdet
  change B = A * axisRotationMatrix θ * A⁻¹
  rw [← h]
  change B = A * (Aᵀ * B * A) * A⁻¹
  rw [← hPinv, Matrix.mul_assoc]
  calc
    B = (1 : Matrix (Fin 3) (Fin 3) ℝ) * B * 1 := by simp
    _ = (A * A⁻¹) * B * (A * A⁻¹) := by rw [hright]
    _ = A * (A⁻¹ * B * A * A⁻¹) := by simp [Matrix.mul_assoc]

lemma adjugate_eq_transpose_of_mem_SO3
    (P : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    Matrix.adjugate (P : Matrix (Fin 3) (Fin 3) ℝ) =
      (P : Matrix (Fin 3) (Fin 3) ℝ)ᵀ := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := P
  have hdet : A.det = 1 := (Matrix.mem_specialOrthogonalGroup_iff.mp P.property).2
  have hinv : A⁻¹ = A.adjugate := by
    rw [Matrix.inv_def, hdet]
    simp
  have hPinv : A⁻¹ = Aᵀ := specialOrthogonal_inv_eq_transpose P
  exact hinv.symm.trans hPinv

lemma cofactor_two_zero_eq_column_two_of_mem_SO3
    (P : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    (P : Matrix (Fin 3) (Fin 3) ℝ) 1 0 * (P : Matrix (Fin 3) (Fin 3) ℝ) 2 1 -
      (P : Matrix (Fin 3) (Fin 3) ℝ) 1 1 * (P : Matrix (Fin 3) (Fin 3) ℝ) 2 0 =
        (P : Matrix (Fin 3) (Fin 3) ℝ) 0 2 := by
  have h := congr_fun (congr_fun (adjugate_eq_transpose_of_mem_SO3 P) 2) 0
  simpa [Matrix.adjugate_fin_three, Matrix.transpose_apply] using h

lemma cofactor_two_one_eq_column_two_of_mem_SO3
    (P : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    (P : Matrix (Fin 3) (Fin 3) ℝ) 0 1 * (P : Matrix (Fin 3) (Fin 3) ℝ) 2 0 -
      (P : Matrix (Fin 3) (Fin 3) ℝ) 0 0 * (P : Matrix (Fin 3) (Fin 3) ℝ) 2 1 =
        (P : Matrix (Fin 3) (Fin 3) ℝ) 1 2 := by
  have h := congr_fun (congr_fun (adjugate_eq_transpose_of_mem_SO3 P) 2) 1
  have h' :
      -((P : Matrix (Fin 3) (Fin 3) ℝ) 0 0 * (P : Matrix (Fin 3) (Fin 3) ℝ) 2 1) +
        (P : Matrix (Fin 3) (Fin 3) ℝ) 0 1 * (P : Matrix (Fin 3) (Fin 3) ℝ) 2 0 =
          (P : Matrix (Fin 3) (Fin 3) ℝ) 1 2 := by
    simpa [Matrix.adjugate_fin_three, Matrix.transpose_apply] using h
  linarith

lemma cofactor_two_two_eq_column_two_of_mem_SO3
    (P : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    (P : Matrix (Fin 3) (Fin 3) ℝ) 0 0 * (P : Matrix (Fin 3) (Fin 3) ℝ) 1 1 -
      (P : Matrix (Fin 3) (Fin 3) ℝ) 0 1 * (P : Matrix (Fin 3) (Fin 3) ℝ) 1 0 =
        (P : Matrix (Fin 3) (Fin 3) ℝ) 2 2 := by
  have h := congr_fun (congr_fun (adjugate_eq_transpose_of_mem_SO3 P) 2) 2
  simpa [Matrix.adjugate_fin_three, Matrix.transpose_apply] using h

lemma skewVector_axisSkewConj_of_mem_SO3
    (P : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (θ : ℝ) :
    skewVectorOfMatrix (axisSkewConj (P : Matrix (Fin 3) (Fin 3) ℝ) θ) =
      θ • (WithLp.toLp 2 fun i : Fin 3 =>
        (P : Matrix (Fin 3) (Fin 3) ℝ) i 2 : V3) := by
  ext i
  fin_cases i
  · have hcof := cofactor_two_zero_eq_column_two_of_mem_SO3 P
    have hscaled := congrArg (fun x : ℝ => θ * x) hcof
    simp [axisSkewConj, skewVectorOfMatrix, skewMatrix_zAxisVec, Matrix.mul_apply,
      specialOrthogonal_inv_eq_transpose P, Matrix.transpose_apply, Fin.sum_univ_three]
    ring_nf at hscaled ⊢
    exact hscaled
  · have hcof := cofactor_two_one_eq_column_two_of_mem_SO3 P
    have hscaled := congrArg (fun x : ℝ => θ * x) hcof
    simp [axisSkewConj, skewVectorOfMatrix, skewMatrix_zAxisVec, Matrix.mul_apply,
      specialOrthogonal_inv_eq_transpose P, Matrix.transpose_apply, Fin.sum_univ_three]
    ring_nf at hscaled ⊢
    exact hscaled
  · have hcof := cofactor_two_two_eq_column_two_of_mem_SO3 P
    have hscaled := congrArg (fun x : ℝ => θ * x) hcof
    simp [axisSkewConj, skewVectorOfMatrix, skewMatrix_zAxisVec, Matrix.mul_apply,
      specialOrthogonal_inv_eq_transpose P, Matrix.transpose_apply, Fin.sum_univ_three]
    ring_nf at hscaled ⊢
    exact hscaled

lemma axisSkewConj_norm_of_mem_SO3 {θ : ℝ} (hθ : 0 ≤ θ)
    (P : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ‖skewVectorOfMatrix (axisSkewConj (P : Matrix (Fin 3) (Fin 3) ℝ) θ)‖ = θ := by
  rw [skewVector_axisSkewConj_of_mem_SO3 P θ, norm_smul,
    norm_column_two_of_mem_SO3 P, Real.norm_eq_abs, abs_of_nonneg hθ]
  ring

lemma axisRotationMatrix_mem_orthogonalGroup (θ : ℝ) :
    axisRotationMatrix θ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisRotationMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;> ring_nf <;>
      simp [add_comm]

lemma axisRotationMatrix_det (θ : ℝ) :
    (axisRotationMatrix θ).det = (1 : ℝ) := by
  rw [axisRotationMatrix_eq]
  simp [Matrix.det_fin_three]
  ring_nf
  simp

lemma axisRotationMatrix_mem_specialOrthogonalGroup (θ : ℝ) :
    axisRotationMatrix θ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  (Matrix.mem_specialOrthogonalGroup_iff).mpr
    ⟨axisRotationMatrix_mem_orthogonalGroup θ, axisRotationMatrix_det θ⟩

def axisRotationSO3 (θ : ℝ) : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨axisRotationMatrix θ, axisRotationMatrix_mem_specialOrthogonalGroup θ⟩

@[simp] lemma axisRotationMatrix_zero :
    axisRotationMatrix 0 = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [axisRotationMatrix]

@[simp] lemma axisRotationSO3_zero :
    axisRotationSO3 0 = (1 : Matrix.specialOrthogonalGroup (Fin 3) ℝ) := by
  ext i j
  simp [axisRotationSO3]

lemma axisRotationMatrix_eq_one_iff {θ : ℝ} :
    axisRotationMatrix θ = (1 : Matrix (Fin 3) (Fin 3) ℝ) ↔
      Real.cos θ = 1 ∧ Real.sin θ = 0 := by
  constructor
  · intro h
    constructor
    · have h00 := congr_fun (congr_fun h 0) 0
      simpa [axisRotationMatrix] using h00
    · have h10 := congr_fun (congr_fun h 1) 0
      simpa [axisRotationMatrix] using h10
  · rintro ⟨hcos, hsin⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [axisRotationMatrix, hcos, hsin]

lemma axisRotationMatrix_eq_one_iff_of_mem_Icc {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    axisRotationMatrix θ = (1 : Matrix (Fin 3) (Fin 3) ℝ) ↔ θ = 0 := by
  constructor
  · intro h
    have hcos : Real.cos θ = 1 := (axisRotationMatrix_eq_one_iff.mp h).1
    have hlt_left : -(2 * Real.pi) < θ := by
      have hpi : 0 < Real.pi := Real.pi_pos
      linarith
    have hlt_right : θ < 2 * Real.pi := by
      have hpi : 0 < Real.pi := Real.pi_pos
      linarith
    exact (Real.cos_eq_one_iff_of_lt_of_lt hlt_left hlt_right).mp hcos
  · rintro rfl
    exact axisRotationMatrix_zero

lemma axisRotationSO3_eq_one_iff_of_mem_Icc {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    axisRotationSO3 θ = (1 : Matrix.specialOrthogonalGroup (Fin 3) ℝ) ↔ θ = 0 := by
  constructor
  · intro h
    exact (axisRotationMatrix_eq_one_iff_of_mem_Icc hθ0 hθπ).mp
      (Subtype.ext_iff.mp h)
  · rintro rfl
    exact axisRotationSO3_zero

lemma cos_arccos_cos (θ : ℝ) :
    Real.cos (Real.arccos (Real.cos θ)) = Real.cos θ := by
  exact Real.cos_arccos (abs_le.mp (Real.abs_cos_le_one θ)).1
    (abs_le.mp (Real.abs_cos_le_one θ)).2

lemma sin_arccos_cos_of_sin_nonneg {θ : ℝ} (hθ : 0 ≤ Real.sin θ) :
    Real.sin (Real.arccos (Real.cos θ)) = Real.sin θ := by
  rw [Real.sin_arccos]
  have hsq : 1 - Real.cos θ ^ 2 = Real.sin θ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hθ]

lemma axisRotationMatrix_arccos_cos_of_sin_nonneg {θ : ℝ}
    (hθ : 0 ≤ Real.sin θ) :
    axisRotationMatrix θ = axisRotationMatrix (Real.arccos (Real.cos θ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisRotationMatrix, cos_arccos_cos θ, sin_arccos_cos_of_sin_nonneg hθ]

lemma sin_arccos_cos_of_sin_nonpos {θ : ℝ} (hθ : Real.sin θ ≤ 0) :
    Real.sin (Real.arccos (Real.cos θ)) = -Real.sin θ := by
  rw [Real.sin_arccos]
  have hsq : 1 - Real.cos θ ^ 2 = Real.sin θ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonpos hθ]

def axisFlipMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal (fun j : Fin 3 => if j = 0 then (1 : ℝ) else -1)

lemma axisFlipMatrix_mem_specialOrthogonalGroup :
    axisFlipMatrix ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  refine (Matrix.mem_specialOrthogonalGroup_iff).mpr ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [axisFlipMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [axisFlipMatrix, Matrix.det_diagonal, Fin.prod_univ_three]

def axisFlipSO3 : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨axisFlipMatrix, axisFlipMatrix_mem_specialOrthogonalGroup⟩

lemma axisFlipMatrix_inv :
    axisFlipMatrix⁻¹ = axisFlipMatrix := by
  have horth : axisFlipMatrix * axisFlipMatrix = 1 := by
    have h := (Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp axisFlipMatrix_mem_specialOrthogonalGroup).1
    simpa [axisFlipMatrix] using h
  exact Matrix.inv_eq_right_inv horth

lemma axisFlip_conj_axisRotation (φ : ℝ) :
    axisFlipMatrix * axisRotationMatrix φ * axisFlipMatrix⁻¹ =
      axisRotationMatrix (-φ) := by
  rw [axisFlipMatrix_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisFlipMatrix, axisRotationMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      Real.cos_neg, Real.sin_neg]

lemma axisRotationMatrix_eq_axisFlip_conj_arccos_of_sin_nonpos {θ : ℝ}
    (hθ : Real.sin θ ≤ 0) :
    axisRotationMatrix θ =
      axisFlipMatrix * axisRotationMatrix (Real.arccos (Real.cos θ)) * axisFlipMatrix⁻¹ := by
  rw [axisFlip_conj_axisRotation]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisRotationMatrix, cos_arccos_cos θ, sin_arccos_cos_of_sin_nonpos hθ,
      Real.cos_neg, Real.sin_neg]

def SO3AxisAngleData.axisRotation {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    SO3AxisAngleData (axisRotationSO3 θ) where
  θ := θ
  hθ0 := hθ0
  hθπ := hθπ
  P := 1
  hR := by simp [axisRotationSO3]
  hNorm := axisSkewConj_one_norm hθ0

def SO3AxisAngleData.of_conj_axisRotation {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (P : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hR : (R : Matrix (Fin 3) (Fin 3) ℝ) =
      (P : Matrix (Fin 3) (Fin 3) ℝ) * axisRotationMatrix θ *
        ((P : Matrix (Fin 3) (Fin 3) ℝ)⁻¹))
    (hNorm : ‖skewVectorOfMatrix (axisSkewConj (P : Matrix (Fin 3) (Fin 3) ℝ) θ)‖ = θ) :
    SO3AxisAngleData R where
  θ := θ
  hθ0 := hθ0
  hθπ := hθπ
  P := P
  hR := hR
  hNorm := hNorm

def SO3AxisAngleData.of_conj_axisRotation_SO {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (P : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hR : (R : Matrix (Fin 3) (Fin 3) ℝ) =
      (P : Matrix (Fin 3) (Fin 3) ℝ) * axisRotationMatrix θ *
        ((P : Matrix (Fin 3) (Fin 3) ℝ)⁻¹)) :
    SO3AxisAngleData R :=
  SO3AxisAngleData.of_conj_axisRotation hθ0 hθπ P R hR
    (axisSkewConj_norm_of_mem_SO3 hθ0 P)

lemma matrix_eq_one_of_conj_axisRotation_zero
    (P : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hR : (R : Matrix (Fin 3) (Fin 3) ℝ) =
      (P : Matrix (Fin 3) (Fin 3) ℝ) * axisRotationMatrix 0 *
        ((P : Matrix (Fin 3) (Fin 3) ℝ)⁻¹)) :
    (R : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  have hPdet : IsUnit (P : Matrix (Fin 3) (Fin 3) ℝ).det := by
    rw [(Matrix.mem_specialOrthogonalGroup_iff.mp P.property).2]
    exact isUnit_one
  rw [hR, axisRotationMatrix_zero, Matrix.mul_one, Matrix.mul_nonsing_inv _ hPdet]

lemma angle_ne_zero_of_conj_axisRotation_ne_one {θ : ℝ} (_hθ0 : 0 ≤ θ)
    (_hθπ : θ ≤ Real.pi)
    (P : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hR : (R : Matrix (Fin 3) (Fin 3) ℝ) =
      (P : Matrix (Fin 3) (Fin 3) ℝ) * axisRotationMatrix θ *
        ((P : Matrix (Fin 3) (Fin 3) ℝ)⁻¹))
    (hne : R ≠ 1) :
    θ ≠ 0 := by
  intro hθ
  apply hne
  ext i j
  have hR0 : (R : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    apply matrix_eq_one_of_conj_axisRotation_zero P R
    simpa [hθ] using hR
  exact congr_fun (congr_fun hR0 i) j

lemma exists_SO3AxisAngleData_of_conj_axisRotation {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθπ : θ ≤ Real.pi)
    (P : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hR : (R : Matrix (Fin 3) (Fin 3) ℝ) =
      (P : Matrix (Fin 3) (Fin 3) ℝ) * axisRotationMatrix θ *
        ((P : Matrix (Fin 3) (Fin 3) ℝ)⁻¹))
    (hne : R ≠ 1) :
    ∃ d : SO3AxisAngleData R, d.θ ≠ 0 := by
  refine ⟨SO3AxisAngleData.of_conj_axisRotation_SO hθ0 hθπ P R hR, ?_⟩
  exact angle_ne_zero_of_conj_axisRotation_ne_one hθ0 hθπ P R hR hne

/-- Axis-angle normal form data for non-identity elements of `SO(3)`.

The intended proof is the classical one: find a fixed unit axis from the odd-dimensional
orientation-preserving orthogonal matrix, extend it to a positively oriented orthonormal basis of
`ℝ³`, and read the restriction to the orthogonal plane as a member of `SO(2)`. -/
theorem exists_SO3AxisAngleData_of_ne_one
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (hR : R ≠ 1) :
    ∃ d : SO3AxisAngleData R, d.θ ≠ 0 := by
  obtain ⟨u, hu0, hunorm, hufix⟩ := exists_unit_fixed_axis_of_mem_SO3 R
  obtain ⟨P, hPcol⟩ := exists_specialOrthogonal_matrix_with_axis u hunorm
  have hfix :
      (R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        (fun i : Fin 3 => (P : Matrix (Fin 3) (Fin 3) ℝ) i 2) =
          (fun i : Fin 3 => (P : Matrix (Fin 3) (Fin 3) ℝ) i 2) := by
    rw [hPcol]
    exact congrArg (WithLp.ofLp) hufix
  obtain ⟨θ, hθ⟩ := exists_axisRotationMatrix_eq_conjugated_of_fixed_axis P R hfix
  have hRθ :
      (R : Matrix (Fin 3) (Fin 3) ℝ) =
        (P : Matrix (Fin 3) (Fin 3) ℝ) * axisRotationMatrix θ *
          ((P : Matrix (Fin 3) (Fin 3) ℝ)⁻¹) :=
    eq_conj_axisRotation_of_conjugated_eq P R θ hθ
  by_cases hsin : 0 ≤ Real.sin θ
  · let φ : ℝ := Real.arccos (Real.cos θ)
    have hφ0 : 0 ≤ φ := by
      exact Real.arccos_nonneg _
    have hφπ : φ ≤ Real.pi := by
      exact Real.arccos_le_pi _
    have hrot : axisRotationMatrix θ = axisRotationMatrix φ := by
      simpa [φ] using axisRotationMatrix_arccos_cos_of_sin_nonneg hsin
    have hRφ :
        (R : Matrix (Fin 3) (Fin 3) ℝ) =
          (P : Matrix (Fin 3) (Fin 3) ℝ) * axisRotationMatrix φ *
            ((P : Matrix (Fin 3) (Fin 3) ℝ)⁻¹) := by
      simpa [hrot] using hRθ
    exact exists_SO3AxisAngleData_of_conj_axisRotation hφ0 hφπ P R hRφ hR
  · have hsin_nonpos : Real.sin θ ≤ 0 := le_of_not_ge hsin
    let φ : ℝ := Real.arccos (Real.cos θ)
    let F : Matrix.specialOrthogonalGroup (Fin 3) ℝ := axisFlipSO3
    let P' : Matrix.specialOrthogonalGroup (Fin 3) ℝ := P * F
    have hφ0 : 0 ≤ φ := by
      exact Real.arccos_nonneg _
    have hφπ : φ ≤ Real.pi := by
      exact Real.arccos_le_pi _
    have hrot :
        axisRotationMatrix θ =
          axisFlipMatrix * axisRotationMatrix φ * axisFlipMatrix⁻¹ := by
      simpa [φ] using axisRotationMatrix_eq_axisFlip_conj_arccos_of_sin_nonpos hsin_nonpos
    have hRφ :
        (R : Matrix (Fin 3) (Fin 3) ℝ) =
          (P' : Matrix (Fin 3) (Fin 3) ℝ) * axisRotationMatrix φ *
            ((P' : Matrix (Fin 3) (Fin 3) ℝ)⁻¹) := by
      change (R : Matrix (Fin 3) (Fin 3) ℝ) =
        ((P : Matrix (Fin 3) (Fin 3) ℝ) * axisFlipMatrix) *
          axisRotationMatrix φ *
          (((P : Matrix (Fin 3) (Fin 3) ℝ) * axisFlipMatrix)⁻¹)
      rw [hRθ, hrot, Matrix.mul_inv_rev]
      simp [Matrix.mul_assoc]
    exact exists_SO3AxisAngleData_of_conj_axisRotation hφ0 hφπ P' R hRφ hR

def SO3AxisAngleData.of_ne_one
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (hR : R ≠ 1) :
    SO3AxisAngleData R :=
  (exists_SO3AxisAngleData_of_ne_one R hR).choose

lemma SO3AxisAngleData.of_ne_one_angle_ne_zero
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (hR : R ≠ 1) :
    (SO3AxisAngleData.of_ne_one R hR).θ ≠ 0 :=
  (exists_SO3AxisAngleData_of_ne_one R hR).choose_spec

theorem exp_surjective_SO3 (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ ξ : V3, NormedSpace.exp (skewMatrix ξ) = (R : Matrix (Fin 3) (Fin 3) ℝ) ∧
      ‖ξ‖ = rotationAngleOf R := by
  by_cases hR : R = 1
  · subst hR
    exact exp_surjective_SO3_one
  · exact exp_surjective_SO3_of_axisAngleData R (SO3AxisAngleData.of_ne_one R hR)

end DepthCylinderTheorem
