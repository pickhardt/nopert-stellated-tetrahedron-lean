import RupertStellatedTetrahedron.CriticalDisk.ExactCertificates
import RupertStellatedTetrahedron.DepthCylinderTheorem.Duality
import RupertStellatedTetrahedron.Stellated.UStarGeometry

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

open DepthCylinderTheorem

/-!
## Depth certificate at `u*`

The proof draft has a finite active-flag depth computation at the critical direction `u*`.
This file records the Lean target for that computation, indexed by the twelve named active
incidences from `UStarGeometry`.
-/

def uStarDepthRadius : ℝ := 1 / 13

abbrev UStarFlag5 := EuclideanSpace ℝ (Fin 5)

/-- Coordinates of a vertex in the `u*` frame, adapted to the project's projection convention. -/
def uStarFrameCoord (v : V3) : V3 :=
  WithLp.toLp 2 ![-uStarB v, uStarA v, uStarHeight v]

lemma proj_uStarFrameCoord (v : V3) :
    proj (uStarFrameCoord v) = uStarProj v := by
  ext i
  fin_cases i <;> simp [uStarFrameCoord, uStarProj]

/-- Left normal to an oriented planar edge.  The `u*` pentagon is listed counterclockwise. -/
def planarLeftNormal (a b : V2) : V2 :=
  WithLp.toLp 2 ![-(b 1 - a 1), b 0 - a 0]

/-- The concrete first-order flag attached to one of the twelve active `u*` incidences. -/
def uStarActiveFlag (i : UStarActiveFlagIndex) : UStarFlag5 :=
  firstOrderFlag (planarLeftNormal i.edgeStart i.edgeEnd) (uStarFrameCoord i.vertex)

lemma uStarDepthRadius_pos : 0 < uStarDepthRadius := by
  norm_num [uStarDepthRadius]

/-- The fixed twelve-flag set at `u*`. -/
def uStarActiveFlags : Finset UStarFlag5 := by
  classical
  exact Finset.univ.image uStarActiveFlag

private def q2 (re sqrtCoeff : ℚ) : Qsqrt2 :=
  ⟨re, sqrtCoeff⟩

def uStarDepthRadiusQ : Qsqrt2 :=
  q2 (1 / 13) 0

lemma uStarDepthRadiusQ_toReal :
    uStarDepthRadiusQ.toReal = uStarDepthRadius := by
  norm_num [uStarDepthRadiusQ, uStarDepthRadius, q2, Qsqrt2.toReal]

/-- Exact `ℚ[√2]` coordinates of the twelve first-order active flags at `u*`. -/
def uStarActiveFlagExact : UStarActiveFlagIndex → ExactFlag5
  | .edgeV4P1_v4 =>
      ![q2 0 0, q2 0 0, q2 (-49 / 20) 0, q2 0 (9 / 20), q2 (-31 / 20) 0]
  | .edgeV4P1_p1 =>
      ![q2 0 0, q2 0 0, q2 (143 / 400) 0, q2 0 (9 / 20), q2 (-31 / 20) 0]
  | .edgeP1D_p1 =>
      ![q2 0 0, q2 0 0, q2 (-143 / 400) 0, q2 0 (11 / 20), q2 (-9 / 20) 0]
  | .edgeP1D_v2 =>
      ![q2 0 (9 / 20), q2 (11 / 10) 0, q2 (9 / 20) 0, q2 0 (11 / 20),
        q2 (-9 / 20) 0]
  | .edgeP1D_v3 =>
      ![q2 0 (-9 / 20), q2 (-11 / 10) 0, q2 (9 / 20) 0, q2 0 (11 / 20),
        q2 (-9 / 20) 0]
  | .edgeDP4_v2 =>
      ![q2 0 (-9 / 20), q2 (11 / 10) 0, q2 (-9 / 20) 0, q2 0 (11 / 20),
        q2 (9 / 20) 0]
  | .edgeDP4_v3 =>
      ![q2 0 (9 / 20), q2 (-11 / 10) 0, q2 (-9 / 20) 0, q2 0 (11 / 20),
        q2 (9 / 20) 0]
  | .edgeDP4_p4 =>
      ![q2 0 0, q2 0 0, q2 (143 / 400) 0, q2 0 (11 / 20), q2 (9 / 20) 0]
  | .edgeP4V1_p4 =>
      ![q2 0 0, q2 0 0, q2 (-143 / 400) 0, q2 0 (9 / 20), q2 (31 / 20) 0]
  | .edgeP4V1_v1 =>
      ![q2 0 0, q2 0 0, q2 (49 / 20) 0, q2 0 (9 / 20), q2 (31 / 20) 0]
  | .edgeV1V4_v1 =>
      ![q2 0 0, q2 0 0, q2 (-4) 0, q2 0 (-2), q2 0 0]
  | .edgeV1V4_v4 =>
      ![q2 0 0, q2 0 0, q2 4 0, q2 0 (-2), q2 0 0]

lemma q2_toReal (re sqrtCoeff : ℚ) :
    (q2 re sqrtCoeff).toReal = (re : ℝ) + (sqrtCoeff : ℝ) * Real.sqrt 2 := by
  rfl

lemma uStarActiveFlagExact_toReal (i : UStarActiveFlagIndex) :
    ExactVec.toReal (uStarActiveFlagExact i) = uStarActiveFlag i := by
  have hinv_sqrt_two : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
    exact inv_sqrt_two_mul_two
  have hsqrt_two_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  ext k
  fin_cases i <;> fin_cases k <;>
    simp [ExactVec.toReal, Qsqrt2.toReal, uStarActiveFlagExact, uStarActiveFlag, q2,
      planarLeftNormal,
      uStarFrameCoord, UStarActiveFlagIndex.vertex, UStarActiveFlagIndex.edgeStart,
      UStarActiveFlagIndex.edgeEnd, uStarCoincidentTetraCorner, uStarProj, uStarA, uStarB,
      uStarHeight, tetraVertex, stellatedApex, div_eq_mul_inv, hinv_sqrt_two] <;>
    nlinarith [hsqrt_two_sq]

def uStarActiveFlagsExactReal : Finset UStarFlag5 := by
  classical
  exact Finset.univ.image fun i : UStarActiveFlagIndex =>
    ExactVec.toReal (uStarActiveFlagExact i)

lemma uStarActiveFlagsExactReal_eq :
    uStarActiveFlagsExactReal = uStarActiveFlags := by
  classical
  ext r
  constructor
  · intro hr
    rw [uStarActiveFlagsExactReal] at hr
    obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp hr
    rw [← hir, uStarActiveFlagExact_toReal i]
    exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
  · intro hr
    rw [uStarActiveFlags] at hr
    obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp hr
    rw [← hir, ← uStarActiveFlagExact_toReal i]
    exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩

def uStarActiveIncidenceList : List UStarActiveFlagIndex :=
  [.edgeV4P1_v4, .edgeV4P1_p1, .edgeP1D_p1, .edgeP1D_v2, .edgeP1D_v3,
    .edgeDP4_v2, .edgeDP4_v3, .edgeDP4_p4, .edgeP4V1_p4, .edgeP4V1_v1,
    .edgeV1V4_v1, .edgeV1V4_v4]

lemma mem_uStarActiveIncidenceList (i : UStarActiveFlagIndex) :
    i ∈ uStarActiveIncidenceList := by
  fin_cases i <;> simp [uStarActiveIncidenceList]

def uStarExactFlagList : List ExactFlag5 :=
  uStarActiveIncidenceList.map uStarActiveFlagExact

def uStarExactFlagTable : Nat → UStarFlag5 :=
  ExactFlagList.table uStarExactFlagList

def uStarExactFlagTableExact : Nat → ExactFlag5 :=
  ExactFlagList.exactTable uStarExactFlagList

lemma uStarExactFlagList_realFinset_eq :
    ExactFlagList.realFinset uStarExactFlagList = uStarActiveFlagsExactReal := by
  classical
  ext r
  constructor
  · intro hr
    rw [ExactFlagList.realFinset] at hr
    obtain ⟨flag, hflag, hr⟩ := Finset.mem_image.mp hr
    have hflagList : flag ∈ uStarExactFlagList := by
      simpa using hflag
    rw [uStarExactFlagList, List.mem_map] at hflagList
    obtain ⟨i, hi, hiflag⟩ := hflagList
    rw [← hr, ← hiflag, uStarActiveFlagsExactReal]
    exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
  · intro hr
    rw [uStarActiveFlagsExactReal] at hr
    obtain ⟨i, _hi, hir⟩ := Finset.mem_image.mp hr
    rw [ExactFlagList.realFinset, ← hir]
    exact Finset.mem_image.mpr
      ⟨uStarActiveFlagExact i, by
        have hmem : uStarActiveFlagExact i ∈ uStarExactFlagList := by
          rw [uStarExactFlagList, List.mem_map]
          exact ⟨i, mem_uStarActiveIncidenceList i, rfl⟩
        simpa using hmem, rfl⟩

structure UStarDepthFacetRecord.Verified (facet : UStarDepthFacetRecord) : Type where
  witness_valid :
    facet.witness.ValidAgainstExactFlags uStarExactFlagList
  normal_eq_eval_exact :
    facet.normal = facet.witness.evalExact uStarExactFlagTableExact

theorem UStarDepthFacetRecord.Verified.normal_mem_convexHull
    {facet : UStarDepthFacetRecord} (verified : facet.Verified) :
    ExactVec.toReal facet.normal ∈
      convexHull ℝ (uStarActiveFlagsExactReal : Set UStarFlag5) := by
  have hmem :=
    ConvexComboWitness.eval_mem_convexHull_exactFlags
      (w := facet.witness) (flags := uStarExactFlagList) verified.witness_valid
  have hnormal :
      ExactVec.toReal facet.normal = facet.witness.eval uStarExactFlagTable := by
    rw [verified.normal_eq_eval_exact]
    simpa [uStarExactFlagTable, uStarExactFlagTableExact] using
      ConvexComboWitness.evalExact_toReal_eq_eval facet.witness uStarExactFlagList
  simpa [uStarExactFlagTable, uStarExactFlagList_realFinset_eq, hnormal] using hmem

/-- A finite support-cover certificate for the exact `u*` depth payload.

Each unit direction is killed by one verified facet normal.  Since every verified facet normal is
itself a convex combination of the exact active flags, this is enough to recover the usual
closed-ball containment by depth duality. -/
structure UStarDepthFacetSupportVerified (payload : UStarDepthPayload) where
  radius_eq : uStarDepthRadius = payload.radius.toReal
  radius_pos : 0 < payload.radius.toReal
  activeIncidences_complete :
    ∀ i : UStarActiveFlagIndex, i ∈ payload.activeIncidences
  facets_verified :
    ∀ facet ∈ payload.facets, facet.Verified
  supportCover :
    ∀ x : UStarFlag5, ‖x‖ = 1 →
      ∃ facet ∈ payload.facets,
        ⟪ExactVec.toReal facet.normal, x⟫ ≤ -payload.radius.toReal

theorem UStarDepthFacetSupportVerified.supportKill_activeFlags
    {payload : UStarDepthPayload}
    (verified : UStarDepthFacetSupportVerified payload) :
    ∀ x : UStarFlag5, ‖x‖ = 1 →
      ∃ r ∈ uStarActiveFlagsExactReal, ⟪r, x⟫ ≤ -payload.radius.toReal := by
  intro x hx
  obtain ⟨facet, hfacet, hkillFacet⟩ := verified.supportCover x hx
  have hnormal :
      ExactVec.toReal facet.normal ∈
        convexHull ℝ (uStarActiveFlagsExactReal : Set UStarFlag5) :=
    (verified.facets_verified facet hfacet).normal_mem_convexHull
  have hlinear :
      ConcaveOn ℝ Set.univ (fun r : UStarFlag5 => ⟪x, r⟫) := by
    simpa using ((innerSL ℝ x).toLinearMap.concaveOn
      (convex_univ : Convex ℝ (Set.univ : Set UStarFlag5)))
  obtain ⟨r, hr, hrle⟩ :=
    hlinear.exists_le_of_mem_convexHull (by intro z hz; simp) hnormal
  refine ⟨r, hr, ?_⟩
  calc
    ⟪r, x⟫ = ⟪x, r⟫ := (real_inner_comm r x).symm
    _ ≤ ⟪x, ExactVec.toReal facet.normal⟫ := hrle
    _ = ⟪ExactVec.toReal facet.normal, x⟫ :=
      (real_inner_comm x (ExactVec.toReal facet.normal)).symm
    _ ≤ -payload.radius.toReal := hkillFacet

def standardUStarDepthPayload : UStarDepthPayload where
  radius := uStarDepthRadiusQ
  activeIncidences := uStarActiveIncidenceList
  facets := []
  inputHash := ""
  outputHash := ""

lemma standardUStarDepthPayload_radius_eq :
    uStarDepthRadius = standardUStarDepthPayload.radius.toReal := by
  simp [standardUStarDepthPayload, uStarDepthRadiusQ_toReal]

lemma standardUStarDepthPayload_activeIncidences_complete (i : UStarActiveFlagIndex) :
    i ∈ standardUStarDepthPayload.activeIncidences := by
  exact mem_uStarActiveIncidenceList i

def standardUStarDepthPayload_facets_verified :
    ∀ facet ∈ standardUStarDepthPayload.facets, facet.Verified := by
  intro facet hfacet
  simp [standardUStarDepthPayload] at hfacet

/-- Semantic verifier output for the exact `u*` depth payload.

The finite checker proves exact hull containment from facet/stress witness rows in the payload.
Lean then converts that exact hull containment into the support-kill form used downstream.
-/
structure UStarDepthPayloadVerified (payload : UStarDepthPayload) where
  radius_eq : uStarDepthRadius = payload.radius.toReal
  activeIncidences_complete :
    ∀ i : UStarActiveFlagIndex, i ∈ payload.activeIncidences
  facets_verified :
    ∀ facet ∈ payload.facets, facet.Verified
  exactHullContainsRadiusBall :
    Metric.closedBall (0 : UStarFlag5) payload.radius.toReal ⊆
      convexHull ℝ (uStarActiveFlagsExactReal : Set UStarFlag5)

def UStarDepthFacetSupportVerified.toPayloadVerified
    {payload : UStarDepthPayload}
    (verified : UStarDepthFacetSupportVerified payload) :
    UStarDepthPayloadVerified payload where
  radius_eq := verified.radius_eq
  activeIncidences_complete := verified.activeIncidences_complete
  facets_verified := verified.facets_verified
  exactHullContainsRadiusBall := by
    exact
      (depth_duality uStarActiveFlagsExactReal payload.radius.toReal
        verified.radius_pos).mpr verified.supportKill_activeFlags

theorem UStarDepthPayloadVerified.facet_normal_mem_convexHull
    {payload : UStarDepthPayload} (verified : UStarDepthPayloadVerified payload)
    {facet : UStarDepthFacetRecord} (hfacet : facet ∈ payload.facets) :
    ExactVec.toReal facet.normal ∈
      convexHull ℝ (uStarActiveFlagsExactReal : Set UStarFlag5) :=
  (verified.facets_verified facet hfacet).normal_mem_convexHull

def standardUStarDepthPayloadVerified
    (hball :
      Metric.closedBall (0 : UStarFlag5) standardUStarDepthPayload.radius.toReal ⊆
        convexHull ℝ (uStarActiveFlagsExactReal : Set UStarFlag5)) :
    UStarDepthPayloadVerified standardUStarDepthPayload where
  radius_eq := standardUStarDepthPayload_radius_eq
  activeIncidences_complete := standardUStarDepthPayload_activeIncidences_complete
  facets_verified := standardUStarDepthPayload_facets_verified
  exactHullContainsRadiusBall := hball

/-- External support certificate for the convex-hull ball at `u*`.

By `depth_duality`, this is equivalent to placing the closed ball of radius `1/13` inside the
convex hull of the twelve concrete active flags, but it is closer to the finite stress certificate:
every unit direction has a certified killing flag.
-/
structure UStarDepthCertificate where
  payload : UStarDepthPayload
  radius_eq : uStarDepthRadius = payload.radius.toReal
  activeIncidences_complete :
    ∀ i : UStarActiveFlagIndex, i ∈ payload.activeIncidences
  supportKill :
    ∀ x : UStarFlag5, ‖x‖ = 1 →
      ∃ r ∈ uStarActiveFlags, ⟪r, x⟫ ≤ -uStarDepthRadius

def UStarDepthPayloadVerified.toCertificate {payload : UStarDepthPayload}
    (verified : UStarDepthPayloadVerified payload) :
    UStarDepthCertificate where
  payload := payload
  radius_eq := verified.radius_eq
  activeIncidences_complete := verified.activeIncidences_complete
  supportKill := by
    intro x hx
    have hball :
        Metric.closedBall (0 : UStarFlag5) uStarDepthRadius ⊆
          convexHull ℝ (uStarActiveFlags : Set UStarFlag5) := by
      intro y hy
      have hyPayload :
          y ∈ Metric.closedBall (0 : UStarFlag5) payload.radius.toReal := by
        simpa [verified.radius_eq] using hy
      have hyExact := verified.exactHullContainsRadiusBall hyPayload
      simpa [uStarActiveFlagsExactReal_eq] using hyExact
    exact (depth_duality uStarActiveFlags uStarDepthRadius uStarDepthRadius_pos).mp hball x hx

def UStarDepthCertificate.flags (_cert : UStarDepthCertificate) : Finset UStarFlag5 :=
  uStarActiveFlags

theorem uStar_depth_from_certificate (cert : UStarDepthCertificate) :
    Metric.closedBall (0 : UStarFlag5) uStarDepthRadius ⊆
      convexHull ℝ (cert.flags : Set UStarFlag5) := by
  exact (depth_duality cert.flags uStarDepthRadius uStarDepthRadius_pos).mpr cert.supportKill

theorem uStar_support_from_certificate (cert : UStarDepthCertificate) :
    ∀ x : UStarFlag5, ‖x‖ = 1 → ∃ r ∈ cert.flags, ⟪r, x⟫ ≤ -uStarDepthRadius := by
  exact cert.supportKill

/-- Operational depth form: every nonzero direction is killed by radius `1/13` times its norm. -/
theorem uStar_support_nonzero_from_certificate (cert : UStarDepthCertificate)
    (x : UStarFlag5) (hx : x ≠ 0) :
    ∃ r ∈ cert.flags, ⟪r, x⟫ ≤ -uStarDepthRadius * ‖x‖ := by
  let u : UStarFlag5 := (‖x‖⁻¹ : ℝ) • x
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖u‖ = 1 := by
    rw [show u = (‖x‖⁻¹ : ℝ) • x from rfl, norm_smul]
    rw [norm_inv, Real.norm_of_nonneg (le_of_lt hxpos)]
    exact inv_mul_cancel₀ (ne_of_gt hxpos)
  obtain ⟨r, hr, hkill⟩ := cert.supportKill u hu
  refine ⟨r, hr, ?_⟩
  have hmul := mul_le_mul_of_nonneg_right hkill (le_of_lt hxpos)
  have hinner :
      ⟪r, u⟫ * ‖x‖ = ⟪r, x⟫ := by
    rw [show u = (‖x‖⁻¹ : ℝ) • x from rfl, inner_smul_right]
    have hcancel : ‖x‖⁻¹ * ‖x‖ = 1 := inv_mul_cancel₀ (ne_of_gt hxpos)
    calc
      (‖x‖⁻¹ * ⟪r, x⟫) * ‖x‖ =
          (‖x‖⁻¹ * ‖x‖) * ⟪r, x⟫ := by ring
      _ = ⟪r, x⟫ := by rw [hcancel]; ring
  have hrhs : (-uStarDepthRadius) * ‖x‖ = -uStarDepthRadius * ‖x‖ := by ring
  rwa [hinner, hrhs] at hmul

end RupertStellatedTetrahedron
