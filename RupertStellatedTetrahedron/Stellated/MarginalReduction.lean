import RupertStellatedTetrahedron.Stellated.Pinch
import RupertStellatedTetrahedron.Stellated.Symmetry

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

open DepthCylinderTheorem

/-!
## Marginal reduction interface

The reflection-sheet theorem gives the map `R ↦ N R m` for an improper vertex symmetry `m`.
This file records the Lean-facing transport facts used by the critical-disk assembly.
-/

/-- The paper's involution-like map `ι_m(R) = N R m`, packaged in `SO(3)`. -/
def marginalIota
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (m : Matrix (Fin 3) (Fin 3) ℝ)
    (hmOrth : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hmDet : Matrix.det m = (-1 : ℝ)) :
    Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  reflectionSheetInner R m hmOrth hmDet

@[simp] lemma marginalIota_coe
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (m : Matrix (Fin 3) (Fin 3) ℝ)
    (hmOrth : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hmDet : Matrix.det m = (-1 : ℝ)) :
    ((marginalIota R m hmOrth hmDet) : Matrix (Fin 3) (Fin 3) ℝ) =
      zReflection * (R : Matrix (Fin 3) (Fin 3) ℝ) * m := rfl

/-- Projection-level identity behind the containment-system transport. -/
theorem marginalIota_projected_vertex
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (m : Matrix (Fin 3) (Fin 3) ℝ)
    (hmOrth : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hmDet : Matrix.det m = (-1 : ℝ))
    (v : V3) :
    proj (matrixAction ((marginalIota R m hmOrth hmDet) :
        Matrix (Fin 3) (Fin 3) ℝ) v) =
      proj (matrixAction (R : Matrix (Fin 3) (Fin 3) ℝ) (matrixAction m v)) := by
  exact proj_reflectionSheetMatrix R m v

/-- Shadow equality for the marginal-reduction map when `m` is an improper vertex symmetry. -/
theorem marginalIota_shadow_eq
    (V : Finset V3)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (m : Matrix (Fin 3) (Fin 3) ℝ)
    (hmOrth : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hmDet : Matrix.det m = (-1 : ℝ))
    (hmMaps : Set.MapsTo (matrixAction m) (V : Set V3) (V : Set V3))
    (hmSurj : ∀ y ∈ (V : Set V3), ∃ x ∈ (V : Set V3), matrixAction m x = y) :
    shadow V (marginalIota R m hmOrth hmDet) = shadow V R := by
  exact reflection_sheet_shadow_eq V R m hmOrth hmDet hmMaps hmSurj

lemma rotationAngleOf_eq_of_trace
    (R S : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (htrace : Matrix.trace (R : Matrix (Fin 3) (Fin 3) ℝ) =
      Matrix.trace (S : Matrix (Fin 3) (Fin 3) ℝ)) :
    rotationAngleOf R = rotationAngleOf S := by
  simp [rotationAngleOf, htrace]

lemma orthogonal_inv_eq_transpose
    (m : Matrix (Fin 3) (Fin 3) ℝ)
    (hmOrth : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    m⁻¹ = mᵀ := by
  have hm : m * mᵀ = 1 := by
    rw [Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ] at hmOrth
    exact hmOrth
  exact Matrix.inv_eq_right_inv hm

lemma zReflection_mul_self :
    zReflection * zReflection = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have h := zReflection_orthogonal
  rw [Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ] at h
  simpa [zReflection_transpose] using h

lemma marginalIota_relative_trace
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (m : Matrix (Fin 3) (Fin 3) ℝ)
    (hmOrth : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hmDet : Matrix.det m = (-1 : ℝ)) :
    Matrix.trace (((marginalIota R₁ m hmOrth hmDet) *
        (marginalIota R₂ m hmOrth hmDet)⁻¹ :
          Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
          Matrix (Fin 3) (Fin 3) ℝ) =
      Matrix.trace ((R₁ * R₂⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
          Matrix (Fin 3) (Fin 3) ℝ) := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := R₁
  let B : Matrix (Fin 3) (Fin 3) ℝ := R₂
  let N : Matrix (Fin 3) (Fin 3) ℝ := zReflection
  have hmInv : m⁻¹ = mᵀ := orthogonal_inv_eq_transpose m hmOrth
  have hmRight : m * mᵀ = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [Matrix.mem_orthogonalGroup_iff (n := Fin 3) ℝ] at hmOrth
    exact hmOrth
  have hN : N * N = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    simpa [N] using zReflection_mul_self
  have hR₂inv :
      (((R₂⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ)) = Bᵀ := by
    simpa [B] using specialOrthogonalGroup_inv_coe_eq_transpose R₂
  have hIotaInv :
      (((marginalIota R₂ m hmOrth hmDet)⁻¹ :
          Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
          Matrix (Fin 3) (Fin 3) ℝ) = mᵀ * Bᵀ * N := by
    rw [specialOrthogonalGroup_inv_coe_eq_transpose]
    simp [marginalIota, reflectionSheetInner, reflectionSheetMatrix, Matrix.transpose_mul,
      zReflection_transpose, B, N]
    rw [Matrix.mul_assoc]
  calc
    Matrix.trace (((marginalIota R₁ m hmOrth hmDet) *
        (marginalIota R₂ m hmOrth hmDet)⁻¹ :
          Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
          Matrix (Fin 3) (Fin 3) ℝ) =
        Matrix.trace (N * (A * Bᵀ) * N) := by
      change Matrix.trace (((marginalIota R₁ m hmOrth hmDet) :
          Matrix (Fin 3) (Fin 3) ℝ) *
        (((marginalIota R₂ m hmOrth hmDet)⁻¹ :
          Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
          Matrix (Fin 3) (Fin 3) ℝ)) =
        Matrix.trace (N * (A * Bᵀ) * N)
      rw [hIotaInv]
      simp only [marginalIota, reflectionSheetInner, reflectionSheetMatrix, A, B, N]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc m mᵀ (((R₂ : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) * zReflection),
        hmRight]
      simp
    _ = Matrix.trace ((N * N) * (A * Bᵀ)) := by
      rw [Matrix.trace_mul_cycle N (A * Bᵀ) N]
    _ = Matrix.trace (A * Bᵀ) := by
      rw [hN]
      simp
    _ = Matrix.trace ((R₁ * R₂⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
          Matrix (Fin 3) (Fin 3) ℝ) := by
      simp [A, B, hR₂inv]

/-- Angle-isometry target for `ι_m`, reduced to the corresponding trace-conjugation identity. -/
theorem marginalIota_relAngle_eq_of_trace
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (m : Matrix (Fin 3) (Fin 3) ℝ)
    (hmOrth : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hmDet : Matrix.det m = (-1 : ℝ))
    (htrace :
      Matrix.trace (((marginalIota R₁ m hmOrth hmDet) *
          (marginalIota R₂ m hmOrth hmDet)⁻¹ :
            Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
            Matrix (Fin 3) (Fin 3) ℝ) =
        Matrix.trace ((R₁ * R₂⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
            Matrix (Fin 3) (Fin 3) ℝ)) :
    relAngle (marginalIota R₁ m hmOrth hmDet) (marginalIota R₂ m hmOrth hmDet) =
      relAngle R₁ R₂ := by
  exact rotationAngleOf_eq_of_trace
    ((marginalIota R₁ m hmOrth hmDet) * (marginalIota R₂ m hmOrth hmDet)⁻¹)
    (R₁ * R₂⁻¹) htrace

/-- The marginal map `ι_m(R)=NRm` preserves relative rotation angle. -/
theorem marginalIota_relAngle_eq
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (m : Matrix (Fin 3) (Fin 3) ℝ)
    (hmOrth : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hmDet : Matrix.det m = (-1 : ℝ)) :
    relAngle (marginalIota R₁ m hmOrth hmDet) (marginalIota R₂ m hmOrth hmDet) =
      relAngle R₁ R₂ := by
  exact marginalIota_relAngle_eq_of_trace R₁ R₂ m hmOrth hmDet
    (marginalIota_relative_trace R₁ R₂ m hmOrth hmDet)

/-- Strict-containment systems are identical after applying `ι_m` to the inner rotation. -/
theorem marginalIota_containment_iff
    (V : Finset V3)
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (m : Matrix (Fin 3) (Fin 3) ℝ)
    (hmOrth : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hmDet : Matrix.det m = (-1 : ℝ))
    (hmMaps : Set.MapsTo (matrixAction m) (V : Set V3) (V : Set V3))
    (hmSurj : ∀ y ∈ (V : Set V3), ∃ x ∈ (V : Set V3), matrixAction m x = y)
    (t : V2) :
    RupertContainment V
        ({ R₁ := marginalIota R₁ m hmOrth hmDet, R₂ := R₂, t := t } : Config V) ↔
      RupertContainment V ({ R₁ := R₁, R₂ := R₂, t := t } : Config V) := by
  constructor
  · intro h v hv
    obtain ⟨u, hu, hmu⟩ := hmSurj v hv
    have hucont := h u hu
    have hproj :
        proj (matrixAction ((marginalIota R₁ m hmOrth hmDet) :
            Matrix (Fin 3) (Fin 3) ℝ) u) =
          proj (matrixAction (R₁ : Matrix (Fin 3) (Fin 3) ℝ) v) := by
      rw [marginalIota_projected_vertex R₁ m hmOrth hmDet u, hmu]
    change proj (matrixAction (R₁ : Matrix (Fin 3) (Fin 3) ℝ) v) + t ∈
      interior (shadow V R₂)
    rw [← hproj]
    simpa [RupertContainment, matrixAction] using hucont
  · intro h v hv
    have hmv : matrixAction m v ∈ (V : Set V3) := hmMaps hv
    have hvcont := h (matrixAction m v) hmv
    have hproj :
        proj (matrixAction ((marginalIota R₁ m hmOrth hmDet) :
            Matrix (Fin 3) (Fin 3) ℝ) v) =
          proj (matrixAction (R₁ : Matrix (Fin 3) (Fin 3) ℝ) (matrixAction m v)) := by
      exact marginalIota_projected_vertex R₁ m hmOrth hmDet v
    change proj (matrixAction ((marginalIota R₁ m hmOrth hmDet) :
        Matrix (Fin 3) (Fin 3) ℝ) v) + t ∈ interior (shadow V R₂)
    rw [hproj]
    simpa [RupertContainment, matrixAction] using hvcont

/-- Marginal-reduction map attached to a proof-carrying improper vertex symmetry. -/
def ImproperVertexSymmetry.iota
    {V : Finset V3} (S : ImproperVertexSymmetry V)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  marginalIota R S.matrix S.orthogonal S.det_neg

@[simp] lemma ImproperVertexSymmetry.iota_coe
    {V : Finset V3} (S : ImproperVertexSymmetry V)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ((S.iota R) : Matrix (Fin 3) (Fin 3) ℝ) =
      zReflection * (R : Matrix (Fin 3) (Fin 3) ℝ) * S.matrix := rfl

/-- A proof-carrying improper vertex symmetry gives exact shadow equality for its sheet. -/
theorem ImproperVertexSymmetry.iota_shadow_eq
    {V : Finset V3} (S : ImproperVertexSymmetry V)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    shadow V (S.iota R) = shadow V R :=
  marginalIota_shadow_eq V R S.matrix S.orthogonal S.det_neg S.maps S.surj

/-- The marginal-reduction map attached to an improper symmetry preserves relative angle. -/
theorem ImproperVertexSymmetry.iota_relAngle_eq
    {V : Finset V3} (S : ImproperVertexSymmetry V)
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    relAngle (S.iota R₁) (S.iota R₂) = relAngle R₁ R₂ :=
  marginalIota_relAngle_eq R₁ R₂ S.matrix S.orthogonal S.det_neg

/-- The strict-containment system is unchanged by the marginal-reduction map attached to an
improper vertex symmetry. -/
theorem ImproperVertexSymmetry.iota_containment_iff
    {V : Finset V3} (S : ImproperVertexSymmetry V)
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (t : V2) :
    RupertContainment V
        ({ R₁ := S.iota R₁, R₂ := R₂, t := t } : Config V) ↔
      RupertContainment V ({ R₁ := R₁, R₂ := R₂, t := t } : Config V) :=
  marginalIota_containment_iff V R₁ R₂ S.matrix S.orthogonal S.det_neg S.maps S.surj t

theorem swapXY_iota_relAngle_eq
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    relAngle (swapXYImproperVertexSymmetry.iota R₁)
        (swapXYImproperVertexSymmetry.iota R₂) =
      relAngle R₁ R₂ :=
  swapXYImproperVertexSymmetry.iota_relAngle_eq R₁ R₂

theorem swapXY_iota_containment_iff
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (t : V2) :
    RupertContainment stellatedVertices
        ({ R₁ := swapXYImproperVertexSymmetry.iota R₁, R₂ := R₂, t := t } :
          Config stellatedVertices) ↔
      RupertContainment stellatedVertices
        ({ R₁ := R₁, R₂ := R₂, t := t } : Config stellatedVertices) :=
  swapXYImproperVertexSymmetry.iota_containment_iff R₁ R₂ t

theorem swapXZ_iota_relAngle_eq
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    relAngle (swapXZImproperVertexSymmetry.iota R₁)
        (swapXZImproperVertexSymmetry.iota R₂) =
      relAngle R₁ R₂ :=
  swapXZImproperVertexSymmetry.iota_relAngle_eq R₁ R₂

theorem swapXZ_iota_containment_iff
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (t : V2) :
    RupertContainment stellatedVertices
        ({ R₁ := swapXZImproperVertexSymmetry.iota R₁, R₂ := R₂, t := t } :
          Config stellatedVertices) ↔
      RupertContainment stellatedVertices
        ({ R₁ := R₁, R₂ := R₂, t := t } : Config stellatedVertices) :=
  swapXZImproperVertexSymmetry.iota_containment_iff R₁ R₂ t

theorem swapYZ_iota_relAngle_eq
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    relAngle (swapYZImproperVertexSymmetry.iota R₁)
        (swapYZImproperVertexSymmetry.iota R₂) =
      relAngle R₁ R₂ :=
  swapYZImproperVertexSymmetry.iota_relAngle_eq R₁ R₂

theorem swapYZ_iota_containment_iff
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (t : V2) :
    RupertContainment stellatedVertices
        ({ R₁ := swapYZImproperVertexSymmetry.iota R₁, R₂ := R₂, t := t } :
          Config stellatedVertices) ↔
      RupertContainment stellatedVertices
        ({ R₁ := R₁, R₂ := R₂, t := t } : Config stellatedVertices) :=
  swapYZImproperVertexSymmetry.iota_containment_iff R₁ R₂ t

theorem negSwapXY_iota_relAngle_eq
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    relAngle (negSwapXYImproperVertexSymmetry.iota R₁)
        (negSwapXYImproperVertexSymmetry.iota R₂) =
      relAngle R₁ R₂ :=
  negSwapXYImproperVertexSymmetry.iota_relAngle_eq R₁ R₂

theorem negSwapXY_iota_containment_iff
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (t : V2) :
    RupertContainment stellatedVertices
        ({ R₁ := negSwapXYImproperVertexSymmetry.iota R₁, R₂ := R₂, t := t } :
          Config stellatedVertices) ↔
      RupertContainment stellatedVertices
        ({ R₁ := R₁, R₂ := R₂, t := t } : Config stellatedVertices) :=
  negSwapXYImproperVertexSymmetry.iota_containment_iff R₁ R₂ t

theorem negSwapXZ_iota_relAngle_eq
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    relAngle (negSwapXZImproperVertexSymmetry.iota R₁)
        (negSwapXZImproperVertexSymmetry.iota R₂) =
      relAngle R₁ R₂ :=
  negSwapXZImproperVertexSymmetry.iota_relAngle_eq R₁ R₂

theorem negSwapXZ_iota_containment_iff
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (t : V2) :
    RupertContainment stellatedVertices
        ({ R₁ := negSwapXZImproperVertexSymmetry.iota R₁, R₂ := R₂, t := t } :
          Config stellatedVertices) ↔
      RupertContainment stellatedVertices
        ({ R₁ := R₁, R₂ := R₂, t := t } : Config stellatedVertices) :=
  negSwapXZImproperVertexSymmetry.iota_containment_iff R₁ R₂ t

theorem negSwapYZ_iota_relAngle_eq
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    relAngle (negSwapYZImproperVertexSymmetry.iota R₁)
        (negSwapYZImproperVertexSymmetry.iota R₂) =
      relAngle R₁ R₂ :=
  negSwapYZImproperVertexSymmetry.iota_relAngle_eq R₁ R₂

theorem negSwapYZ_iota_containment_iff
    (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (t : V2) :
    RupertContainment stellatedVertices
        ({ R₁ := negSwapYZImproperVertexSymmetry.iota R₁, R₂ := R₂, t := t } :
          Config stellatedVertices) ↔
      RupertContainment stellatedVertices
        ({ R₁ := R₁, R₂ := R₂, t := t } : Config stellatedVertices) :=
  negSwapYZImproperVertexSymmetry.iota_containment_iff R₁ R₂ t

theorem faceDiagonalReflection_iota_relAngle_eq
    (i : Fin 6) (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    relAngle ((faceDiagonalReflectionSymmetry i).iota R₁)
        ((faceDiagonalReflectionSymmetry i).iota R₂) =
      relAngle R₁ R₂ :=
  (faceDiagonalReflectionSymmetry i).iota_relAngle_eq R₁ R₂

theorem faceDiagonalReflection_iota_containment_iff
    (i : Fin 6) (R₁ R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (t : V2) :
    RupertContainment stellatedVertices
        ({ R₁ := (faceDiagonalReflectionSymmetry i).iota R₁, R₂ := R₂, t := t } :
          Config stellatedVertices) ↔
      RupertContainment stellatedVertices
        ({ R₁ := R₁, R₂ := R₂, t := t } : Config stellatedVertices) :=
  (faceDiagonalReflectionSymmetry i).iota_containment_iff R₁ R₂ t

end RupertStellatedTetrahedron
