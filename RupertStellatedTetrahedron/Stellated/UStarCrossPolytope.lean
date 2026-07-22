import RupertStellatedTetrahedron.Stellated.UStarCertifiedInput

/-!
Exact cross-polytope witnesses inside the `u*` active-flag hull.

The ten vertices are
`±(√2/4)e₀`, `±(1/4)e₁`, `±(1/4)e₂`, `±(√2/4)e₃`, and `±(1/4)e₄`.
Each is recorded as an exact convex combination of the twelve active `u*` flags.
-/

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

namespace UStarCrossPolytope

private def ratWeight (q : ℚ) : Qsqrt2 :=
  ⟨q, 0⟩

private def term (idx : Nat) (q : ℚ) : ConvexComboTerm where
  flagIndex := idx
  weight := ratWeight q

private def coarseSqrt2Bounds : Qsqrt2.Sqrt2Bounds where
  lo := 0
  hi := 2
  lo_nonneg := by norm_num
  lo_sq_le_two := by norm_num
  hi_nonneg := by norm_num
  two_le_hi_sq := by norm_num

private def ratWeight_nonnegCert (q : ℚ) (hq : 0 ≤ q) :
    Qsqrt2.NonnegCert (ratWeight q) where
  bounds := coarseSqrt2Bounds
  nonneg := by
    simpa [ratWeight, Qsqrt2.nonnegLowerExpr] using hq

/-- Exact vertex of the weighted coordinate cross-polytope.  The Boolean sign is `true` for the
positive vertex and `false` for the negative vertex. -/
def vertexExact : Fin 5 → Bool → ExactFlag5
  | 0, true => ![⟨0, 1 / 4⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 0, false => ![⟨0, -1 / 4⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 1, true => ![⟨0, 0⟩, ⟨1 / 4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 1, false => ![⟨0, 0⟩, ⟨-1 / 4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 2, true => ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1 / 4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 2, false => ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1 / 4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 3, true => ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1 / 4⟩, ⟨0, 0⟩]
  | 3, false => ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1 / 4⟩, ⟨0, 0⟩]
  | 4, true => ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1 / 4, 0⟩]
  | 4, false => ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1 / 4, 0⟩]

def axisRadius : Fin 5 → ℝ
  | 0 => Real.sqrt 2 / 4
  | 1 => 1 / 4
  | 2 => 1 / 4
  | 3 => Real.sqrt 2 / 4
  | 4 => 1 / 4

theorem axisRadius_pos (i : Fin 5) : 0 < axisRadius i := by
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  fin_cases i <;> simp [axisRadius, hsqrt_pos]

theorem vertex_apply (i j : Fin 5) (positive : Bool) :
    ExactVec.toReal (vertexExact i positive) j =
      if j = i then (if positive then axisRadius i else -axisRadius i) else 0 := by
  fin_cases i <;> fin_cases j <;> cases positive <;>
    simp [vertexExact, axisRadius, ExactVec.toReal, Qsqrt2.toReal] <;> ring_nf

theorem vertex_apply_self (i : Fin 5) (positive : Bool) :
    ExactVec.toReal (vertexExact i positive) i =
      if positive then axisRadius i else -axisRadius i := by
  simpa using vertex_apply i i positive

theorem vertex_apply_ne {i j : Fin 5} (hji : j ≠ i) (positive : Bool) :
    ExactVec.toReal (vertexExact i positive) j = 0 := by
  simpa [hji] using vertex_apply i j positive

theorem axisRadius_inv_sq_sum :
    (∑ i : Fin 5, (axisRadius i)⁻¹ ^ 2) = 64 := by
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt_ne : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
  rw [Fin.sum_univ_five]
  simp [axisRadius]
  field_simp [hsqrt_ne]
  nlinarith [hsqrt_sq]

theorem one_fourth_le_axisRadius (i : Fin 5) : (1 / 4 : ℝ) ≤ axisRadius i := by
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  fin_cases i <;> simp [axisRadius] <;> nlinarith

theorem inner_vertex (i : Fin 5) (positive : Bool) (x : UStarFlag5) :
    ⟪ExactVec.toReal (vertexExact i positive), x⟫ =
      (if positive then axisRadius i else -axisRadius i) * x i := by
  rw [PiLp.inner_apply, Fin.sum_univ_five]
  fin_cases i <;> cases positive <;>
    simp [vertex_apply, axisRadius] <;> ring

/-- Exact convex-combination witness for `vertexExact`. -/
def witness : Fin 5 → Bool → ConvexComboWitness
  | 0, true =>
      { terms :=
          [term 1 (5 / 42), term 3 (5 / 18), term 6 (5 / 18), term 8 (5 / 42),
            term 10 (13 / 126), term 11 (13 / 126)] }
  | 0, false =>
      { terms :=
          [term 3 (35 / 612), term 4 (205 / 612), term 5 (205 / 612),
            term 6 (35 / 612), term 10 (11 / 102), term 11 (11 / 102)] }
  | 1, true =>
      { terms :=
          [term 2 (625 / 2244), term 3 (5 / 44), term 5 (5 / 44),
            term 7 (625 / 2244), term 10 (11 / 102), term 11 (11 / 102)] }
  | 1, false =>
      { terms :=
          [term 1 (625 / 2156), term 4 (5 / 44), term 6 (5 / 44),
            term 8 (625 / 2156), term 10 (52 / 539), term 11 (52 / 539)] }
  | 2, true =>
      { terms :=
          [term 0 (20 / 49), term 9 (20 / 49), term 10 (95 / 1568),
            term 11 (193 / 1568)] }
  | 2, false =>
      { terms :=
          [term 1 (20 / 49), term 8 (20 / 49), term 10 (193 / 1568),
            term 11 (95 / 1568)] }
  | 3, true =>
      { terms :=
          [term 1 (45 / 98), term 8 (45 / 98), term 10 (2 / 49),
            term 11 (2 / 49)] }
  | 3, false =>
      { terms :=
          [term 1 (5 / 14), term 9 (5 / 14), term 10 (2403 / 8960),
            term 11 (157 / 8960)] }
  | 4, true =>
      { terms :=
          [term 3 (35 / 612), term 4 (35 / 612), term 5 (205 / 612),
            term 6 (205 / 612), term 10 (125 / 1632), term 11 (227 / 1632)] }
  | 4, false =>
      { terms :=
          [term 3 (205 / 612), term 4 (205 / 612), term 5 (35 / 612),
            term 6 (35 / 612), term 10 (227 / 1632), term 11 (125 / 1632)] }

theorem witness_weightSum (i : Fin 5) (positive : Bool) :
    (witness i positive).weightSum = 1 := by
  fin_cases i <;> cases positive <;> native_decide

theorem witness_evalExact (i : Fin 5) (positive : Bool) :
    (witness i positive).evalExact uStarExactFlagTableExact = vertexExact i positive := by
  fin_cases i <;> cases positive <;> native_decide

def witness_valid : (i : Fin 5) → (positive : Bool) →
    (witness i positive).ValidAgainstExactFlags uStarExactFlagList
  | 0, true => by
      constructor
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          exact ratWeight_nonnegCert _ (by norm_num)
      · native_decide
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          simp [witness, term, uStarExactFlagList, uStarActiveIncidenceList,
            ConvexComboWitness.termAt]
  | 0, false => by
      constructor
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          exact ratWeight_nonnegCert _ (by norm_num)
      · native_decide
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          simp [witness, term, uStarExactFlagList, uStarActiveIncidenceList,
            ConvexComboWitness.termAt]
  | 1, true => by
      constructor
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          exact ratWeight_nonnegCert _ (by norm_num)
      · native_decide
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          simp [witness, term, uStarExactFlagList, uStarActiveIncidenceList,
            ConvexComboWitness.termAt]
  | 1, false => by
      constructor
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          exact ratWeight_nonnegCert _ (by norm_num)
      · native_decide
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          simp [witness, term, uStarExactFlagList, uStarActiveIncidenceList,
            ConvexComboWitness.termAt]
  | 2, true => by
      constructor
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          exact ratWeight_nonnegCert _ (by norm_num)
      · native_decide
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          simp [witness, term, uStarExactFlagList, uStarActiveIncidenceList,
            ConvexComboWitness.termAt]
  | 2, false => by
      constructor
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          exact ratWeight_nonnegCert _ (by norm_num)
      · native_decide
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          simp [witness, term, uStarExactFlagList, uStarActiveIncidenceList,
            ConvexComboWitness.termAt]
  | 3, true => by
      constructor
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          exact ratWeight_nonnegCert _ (by norm_num)
      · native_decide
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          simp [witness, term, uStarExactFlagList, uStarActiveIncidenceList,
            ConvexComboWitness.termAt]
  | 3, false => by
      constructor
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          exact ratWeight_nonnegCert _ (by norm_num)
      · native_decide
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          simp [witness, term, uStarExactFlagList, uStarActiveIncidenceList,
            ConvexComboWitness.termAt]
  | 4, true => by
      constructor
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          exact ratWeight_nonnegCert _ (by norm_num)
      · native_decide
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          simp [witness, term, uStarExactFlagList, uStarActiveIncidenceList,
            ConvexComboWitness.termAt]
  | 4, false => by
      constructor
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          exact ratWeight_nonnegCert _ (by norm_num)
      · native_decide
      · rintro ⟨j, hj⟩; norm_num [witness] at hj; interval_cases j <;>
          simp [witness, term, uStarExactFlagList, uStarActiveIncidenceList,
            ConvexComboWitness.termAt]

theorem vertex_mem_convexHull (i : Fin 5) (positive : Bool) :
    ExactVec.toReal (vertexExact i positive) ∈
      convexHull ℝ (uStarActiveFlagsExactReal : Set UStarFlag5) := by
  have hmem :=
    ConvexComboWitness.evalExact_toReal_mem_convexHull_exactFlags
      (w := witness i positive) (flags := uStarExactFlagList) (witness_valid i positive)
  have heval : (witness i positive).evalExact uStarExactFlagTableExact = vertexExact i positive :=
    witness_evalExact i positive
  rw [← heval]
  simpa [uStarExactFlagTableExact, uStarExactFlagList_realFinset_eq] using hmem

def vertices : Set UStarFlag5 :=
  {x | ∃ i : Fin 5, ∃ positive : Bool, x = ExactVec.toReal (vertexExact i positive)}

def vertexFinset : Finset UStarFlag5 :=
  Finset.univ.image fun p : Fin 5 × Bool => ExactVec.toReal (vertexExact p.1 p.2)

theorem vertexFinset_coe_eq_vertices :
    (vertexFinset : Set UStarFlag5) = vertices := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨p, _hp, rfl⟩
    exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨i, positive, rfl⟩
    exact Finset.mem_image.mpr ⟨(i, positive), by simp, rfl⟩

theorem vertex_mem_vertices (i : Fin 5) (positive : Bool) :
    ExactVec.toReal (vertexExact i positive) ∈ vertices := by
  exact ⟨i, positive, rfl⟩

theorem vertices_subset_activeHull :
    vertices ⊆ convexHull ℝ (uStarActiveFlagsExactReal : Set UStarFlag5) := by
  intro x hx
  rcases hx with ⟨i, positive, rfl⟩
  exact vertex_mem_convexHull i positive

theorem convexHull_vertices_subset_activeHull :
    convexHull ℝ vertices ⊆ convexHull ℝ (uStarActiveFlagsExactReal : Set UStarFlag5) := by
  exact convexHull_min vertices_subset_activeHull (convex_convexHull ℝ _)

theorem exists_abs_coord_ge_four_thirteenths (x : UStarFlag5) (hx : ‖x‖ = 1) :
    ∃ i : Fin 5, (4 / 13 : ℝ) ≤ |x i| := by
  by_contra h
  push Not at h
  have hsum_sq : (∑ i : Fin 5, x i ^ 2) = 1 := by
    have hnorm := EuclideanSpace.real_norm_sq_eq x
    rw [hx] at hnorm
    norm_num at hnorm
    simpa [Real.norm_eq_abs, sq_abs] using hnorm.symm
  have hlt_each :
      ∀ i ∈ (Finset.univ : Finset (Fin 5)), x i ^ 2 < (4 / 13 : ℝ) ^ 2 := by
    intro i _hi
    have hiabs : |x i| < (4 / 13 : ℝ) := h i
    have habs_nonneg : 0 ≤ |x i| := abs_nonneg _
    have hsq_abs : |x i| ^ 2 = x i ^ 2 := sq_abs (x i)
    nlinarith
  have hsum_lt :
      (∑ i : Fin 5, x i ^ 2) < ∑ _i : Fin 5, (4 / 13 : ℝ) ^ 2 := by
    exact Finset.sum_lt_sum (fun i hi => (hlt_each i hi).le) ⟨0, by simp, hlt_each 0 (by simp)⟩
  have hsum_const : (∑ _i : Fin 5, (4 / 13 : ℝ) ^ 2) = 5 * (4 / 13 : ℝ) ^ 2 := by
    norm_num [Fin.sum_univ_five]
  nlinarith

theorem axis_mul_abs_coord_ge_radius {x : UStarFlag5} {i : Fin 5}
    (hi : (4 / 13 : ℝ) ≤ |x i|) :
    (1 / 13 : ℝ) ≤ axisRadius i * |x i| := by
  have haxis := one_fourth_le_axisRadius i
  have haxis_nonneg : 0 ≤ axisRadius i := le_trans (by norm_num : (0 : ℝ) ≤ 1 / 4) haxis
  have hmul := mul_le_mul haxis hi (by norm_num : (0 : ℝ) ≤ 4 / 13) haxis_nonneg
  nlinarith

theorem vertexFinset_supportKill :
    ∀ x : UStarFlag5, ‖x‖ = 1 →
      ∃ r ∈ vertexFinset, ⟪r, x⟫ ≤ -standardUStarDepthPayload.radius.toReal := by
  intro x hx
  obtain ⟨i, hiabs⟩ := exists_abs_coord_ge_four_thirteenths x hx
  have hprod := axis_mul_abs_coord_ge_radius (x := x) (i := i) hiabs
  by_cases hxi_nonneg : 0 ≤ x i
  · refine ⟨ExactVec.toReal (vertexExact i false), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(i, false), by simp, rfl⟩
    · have hinner := inner_vertex i false x
      have habs : |x i| = x i := abs_of_nonneg hxi_nonneg
      have hprod' := hprod
      rw [habs] at hprod'
      rw [hinner]
      simp [standardUStarDepthPayload, uStarDepthRadiusQ_toReal, uStarDepthRadius]
      nlinarith
  · refine ⟨ExactVec.toReal (vertexExact i true), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(i, true), by simp, rfl⟩
    · have hinner := inner_vertex i true x
      have hxi_neg : x i < 0 := lt_of_not_ge hxi_nonneg
      have habs : |x i| = -x i := abs_of_neg hxi_neg
      have hprod' := hprod
      rw [habs] at hprod'
      rw [hinner]
      simp [standardUStarDepthPayload, uStarDepthRadiusQ_toReal, uStarDepthRadius]
      nlinarith

/-- The finite hull-containment certificate shape for the cross-polytope route to the standard
`u*` hull soundness theorem. -/
structure BallInCrossPolytopeHull where
  ball_subset :
    Metric.closedBall (0 : UStarFlag5) standardUStarDepthPayload.radius.toReal ⊆
      convexHull ℝ vertices

def BallInCrossPolytopeHull.toStandardHullSoundness
    (soundness : BallInCrossPolytopeHull) :
    UStarCertifiedInput.StandardHullSoundness where
  exactHullContainsRadiusBall := by
    intro x hx
    exact convexHull_vertices_subset_activeHull (soundness.ball_subset hx)

def ballInCrossPolytopeHull : BallInCrossPolytopeHull where
  ball_subset := by
    have hradius_pos : 0 < standardUStarDepthPayload.radius.toReal := by
      simpa [standardUStarDepthPayload, uStarDepthRadiusQ_toReal] using uStarDepthRadius_pos
    have hball :=
      (DepthCylinderTheorem.depth_duality vertexFinset
        standardUStarDepthPayload.radius.toReal hradius_pos).mpr vertexFinset_supportKill
    intro x hx
    have hx_finset := hball hx
    simpa [vertexFinset_coe_eq_vertices] using hx_finset

def standardHullSoundness : UStarCertifiedInput.StandardHullSoundness :=
  ballInCrossPolytopeHull.toStandardHullSoundness

def facetRecord (i : Fin 5) (positive : Bool) : UStarDepthFacetRecord where
  normal := vertexExact i positive
  offsetLower := uStarDepthRadiusQ
  witness := witness i positive

def facetRecord_verified (i : Fin 5) (positive : Bool) :
    (facetRecord i positive).Verified where
  witness_valid := witness_valid i positive
  normal_eq_eval_exact := by
    exact (witness_evalExact i positive).symm

end UStarCrossPolytope

end RupertStellatedTetrahedron
