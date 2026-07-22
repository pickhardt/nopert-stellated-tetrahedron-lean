import RupertStellatedTetrahedron.DepthCylinderTheorem.Assembly

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace DepthCylinderTheorem

/-!
## Box-anchored cylinder theorem

This is the Lean-facing form of draft Theorem 8.2.  The computational checker may prove the
geometric inclusion `δ K_box ⊆ conv F`; the local theorem only needs its support-function
consequence: every direction is killed by an active flag by at least the box support.
-/

abbrev BoxFlag5 := EuclideanSpace ℝ (Fin 5)

/-- Norm of the two tilt coordinates `(x₀,x₁)`. -/
def tiltNorm (x : BoxFlag5) : ℝ :=
  Real.sqrt (x 0 ^ 2 + x 1 ^ 2)

/-- Norm of the two translation coordinates `(x₃,x₄)`. -/
def translationNorm (x : BoxFlag5) : ℝ :=
  Real.sqrt (x 3 ^ 2 + x 4 ^ 2)

/-- Support function of the coordinate box used in Theorem 8.2. -/
def boxSupport (bPi bGamma bT : ℝ) (x : BoxFlag5) : ℝ :=
  bPi * tiltNorm x + bGamma * |x 2| + bT * translationNorm x

/-- Membership in the scaled coordinate box `δ K_box`. -/
def scaledBoxMember (delta bPi bGamma bT : ℝ) (y : BoxFlag5) : Prop :=
  tiltNorm y ≤ delta * bPi ∧ |y 2| ≤ delta * bGamma ∧
    translationNorm y ≤ delta * bT

/-- The candidate point attaining the negative support of the scaled coordinate box. -/
def boxSupportPoint (delta bPi bGamma bT : ℝ) (x : BoxFlag5) : BoxFlag5 :=
  WithLp.toLp 2 fun i : Fin 5 =>
    match i with
    | 0 =>
        if _h : tiltNorm x = 0 then 0 else -(delta * bPi) * x 0 / tiltNorm x
    | 1 =>
        if _h : tiltNorm x = 0 then 0 else -(delta * bPi) * x 1 / tiltNorm x
    | 2 => if 0 ≤ x 2 then -(delta * bGamma) else delta * bGamma
    | 3 =>
        if _h : translationNorm x = 0 then 0 else -(delta * bT) * x 3 / translationNorm x
    | 4 =>
        if _h : translationNorm x = 0 then 0 else -(delta * bT) * x 4 / translationNorm x

@[simp] lemma boxSupportPoint_apply_zero (delta bPi bGamma bT : ℝ) (x : BoxFlag5) :
    boxSupportPoint delta bPi bGamma bT x 0 =
      if _h : tiltNorm x = 0 then 0 else -(delta * bPi) * x 0 / tiltNorm x := by
  simp [boxSupportPoint]

@[simp] lemma boxSupportPoint_apply_one (delta bPi bGamma bT : ℝ) (x : BoxFlag5) :
    boxSupportPoint delta bPi bGamma bT x 1 =
      if _h : tiltNorm x = 0 then 0 else -(delta * bPi) * x 1 / tiltNorm x := by
  simp [boxSupportPoint]

@[simp] lemma boxSupportPoint_apply_two (delta bPi bGamma bT : ℝ) (x : BoxFlag5) :
    boxSupportPoint delta bPi bGamma bT x 2 =
      if 0 ≤ x 2 then -(delta * bGamma) else delta * bGamma := by
  simp [boxSupportPoint]

@[simp] lemma boxSupportPoint_apply_three (delta bPi bGamma bT : ℝ) (x : BoxFlag5) :
    boxSupportPoint delta bPi bGamma bT x 3 =
      if _h : translationNorm x = 0 then 0 else
        -(delta * bT) * x 3 / translationNorm x := by
  simp [boxSupportPoint]

@[simp] lemma boxSupportPoint_apply_four (delta bPi bGamma bT : ℝ) (x : BoxFlag5) :
    boxSupportPoint delta bPi bGamma bT x 4 =
      if _h : translationNorm x = 0 then 0 else
        -(delta * bT) * x 4 / translationNorm x := by
  simp [boxSupportPoint]

lemma tiltNorm_nonneg (x : BoxFlag5) : 0 ≤ tiltNorm x := by
  unfold tiltNorm
  positivity

lemma translationNorm_nonneg (x : BoxFlag5) : 0 ≤ translationNorm x := by
  unfold translationNorm
  positivity

lemma boxSupport_nonneg {bPi bGamma bT : ℝ}
    (hbPi : 0 ≤ bPi) (hbGamma : 0 ≤ bGamma) (hbT : 0 ≤ bT) (x : BoxFlag5) :
    0 ≤ boxSupport bPi bGamma bT x := by
  unfold boxSupport
  have ht := tiltNorm_nonneg x
  have hg : 0 ≤ |x 2| := abs_nonneg _
  have hτ := translationNorm_nonneg x
  nlinarith [mul_nonneg hbPi ht, mul_nonneg hbGamma hg, mul_nonneg hbT hτ]

lemma boxSupportPoint_tiltNorm_le {delta bPi bGamma bT : ℝ} (x : BoxFlag5)
    (hdelta : 0 ≤ delta) (hbPi : 0 ≤ bPi) :
    tiltNorm (boxSupportPoint delta bPi bGamma bT x) ≤ delta * bPi := by
  by_cases hzero : tiltNorm x = 0
  · unfold tiltNorm
    simp [boxSupportPoint, hzero, pow_two]
    exact mul_nonneg hdelta hbPi
  · have hpos : 0 < tiltNorm x := lt_of_le_of_ne' (tiltNorm_nonneg x) hzero
    have hsumsq : x 0 ^ 2 + x 1 ^ 2 = tiltNorm x ^ 2 := by
      unfold tiltNorm
      rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    unfold tiltNorm
    have hinside :
        (boxSupportPoint delta bPi bGamma bT x 0) ^ 2 +
            (boxSupportPoint delta bPi bGamma bT x 1) ^ 2 =
          (delta * bPi) ^ 2 := by
      simp [boxSupportPoint, hzero]
      calc
        (-(delta * bPi * x 0) / tiltNorm x) ^ 2 +
            (-(delta * bPi * x 1) / tiltNorm x) ^ 2 =
            (delta * bPi) ^ 2 * (x 0 ^ 2 + x 1 ^ 2) / tiltNorm x ^ 2 := by
          field_simp [ne_of_gt hpos]
        _ = (delta * bPi) ^ 2 * tiltNorm x ^ 2 / tiltNorm x ^ 2 := by
          rw [hsumsq]
        _ = (delta * bPi) ^ 2 := by
          field_simp [pow_ne_zero 2 (ne_of_gt hpos)]
    rw [hinside, Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hdelta hbPi)]

lemma boxSupportPoint_translationNorm_le {delta bPi bGamma bT : ℝ} (x : BoxFlag5)
    (hdelta : 0 ≤ delta) (hbT : 0 ≤ bT) :
    translationNorm (boxSupportPoint delta bPi bGamma bT x) ≤ delta * bT := by
  by_cases hzero : translationNorm x = 0
  · unfold translationNorm
    simp [boxSupportPoint, hzero, pow_two]
    exact mul_nonneg hdelta hbT
  · have hpos : 0 < translationNorm x := lt_of_le_of_ne' (translationNorm_nonneg x) hzero
    have hsumsq : x 3 ^ 2 + x 4 ^ 2 = translationNorm x ^ 2 := by
      unfold translationNorm
      rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    unfold translationNorm
    have hinside :
        (boxSupportPoint delta bPi bGamma bT x 3) ^ 2 +
            (boxSupportPoint delta bPi bGamma bT x 4) ^ 2 =
          (delta * bT) ^ 2 := by
      simp [boxSupportPoint, hzero]
      calc
        (-(delta * bT * x 3) / translationNorm x) ^ 2 +
            (-(delta * bT * x 4) / translationNorm x) ^ 2 =
            (delta * bT) ^ 2 * (x 3 ^ 2 + x 4 ^ 2) / translationNorm x ^ 2 := by
          field_simp [ne_of_gt hpos]
        _ = (delta * bT) ^ 2 * translationNorm x ^ 2 / translationNorm x ^ 2 := by
          rw [hsumsq]
        _ = (delta * bT) ^ 2 := by
          field_simp [pow_ne_zero 2 (ne_of_gt hpos)]
    rw [hinside, Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hdelta hbT)]

lemma boxSupportPoint_gamma_abs_le {delta bPi bGamma bT : ℝ} (x : BoxFlag5)
    (hdelta : 0 ≤ delta) (hbGamma : 0 ≤ bGamma) :
    |boxSupportPoint delta bPi bGamma bT x 2| ≤ delta * bGamma := by
  have hnonneg : 0 ≤ delta * bGamma := mul_nonneg hdelta hbGamma
  have habs : |delta * bGamma| = delta * bGamma := abs_of_nonneg hnonneg
  by_cases hx : 0 ≤ x 2
  · simp [boxSupportPoint, hx, abs_neg, habs]
  · simp [boxSupportPoint, hx, habs]

lemma boxSupportPoint_mem_scaledBox {delta bPi bGamma bT : ℝ} (x : BoxFlag5)
    (hdelta : 0 ≤ delta) (hbPi : 0 ≤ bPi) (hbGamma : 0 ≤ bGamma) (hbT : 0 ≤ bT) :
    scaledBoxMember delta bPi bGamma bT (boxSupportPoint delta bPi bGamma bT x) := by
  exact ⟨boxSupportPoint_tiltNorm_le x hdelta hbPi,
    boxSupportPoint_gamma_abs_le x hdelta hbGamma,
    boxSupportPoint_translationNorm_le x hdelta hbT⟩

lemma boxSupportPoint_tilt_inner {delta bPi bGamma bT : ℝ} (x : BoxFlag5) :
    x 0 * boxSupportPoint delta bPi bGamma bT x 0 +
        x 1 * boxSupportPoint delta bPi bGamma bT x 1 =
      -(delta * bPi * tiltNorm x) := by
  by_cases hzero : tiltNorm x = 0
  · have hsumsq : x 0 ^ 2 + x 1 ^ 2 = 0 := by
      have hsq := congrArg (fun r : ℝ => r ^ 2) hzero
      unfold tiltNorm at hsq
      rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))] at hsq
      simpa using hsq
    have hx0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have hx1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    simp [boxSupportPoint, hzero, hx0, hx1]
  · have hpos : 0 < tiltNorm x := lt_of_le_of_ne' (tiltNorm_nonneg x) hzero
    have hsumsq : x 0 ^ 2 + x 1 ^ 2 = tiltNorm x ^ 2 := by
      unfold tiltNorm
      rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    simp [boxSupportPoint, hzero]
    calc
      x 0 * (-(delta * bPi * x 0) / tiltNorm x) +
          x 1 * (-(delta * bPi * x 1) / tiltNorm x) =
          -(delta * bPi) * (x 0 ^ 2 + x 1 ^ 2) / tiltNorm x := by
        field_simp [ne_of_gt hpos]
        ring
      _ = -(delta * bPi * tiltNorm x) := by
        rw [hsumsq]
        field_simp [ne_of_gt hpos]

lemma boxSupportPoint_gamma_inner {delta bPi bGamma bT : ℝ} (x : BoxFlag5) :
    x 2 * boxSupportPoint delta bPi bGamma bT x 2 =
      -(delta * bGamma * |x 2|) := by
  by_cases hx : 0 ≤ x 2
  · rw [boxSupportPoint_apply_two, if_pos hx, abs_of_nonneg hx]
    ring
  · have hxle : x 2 ≤ 0 := le_of_lt (lt_of_not_ge hx)
    rw [boxSupportPoint_apply_two, if_neg hx, abs_of_nonpos hxle]
    ring

lemma boxSupportPoint_translation_inner {delta bPi bGamma bT : ℝ} (x : BoxFlag5) :
    x 3 * boxSupportPoint delta bPi bGamma bT x 3 +
        x 4 * boxSupportPoint delta bPi bGamma bT x 4 =
      -(delta * bT * translationNorm x) := by
  by_cases hzero : translationNorm x = 0
  · have hsumsq : x 3 ^ 2 + x 4 ^ 2 = 0 := by
      have hsq := congrArg (fun r : ℝ => r ^ 2) hzero
      unfold translationNorm at hsq
      rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))] at hsq
      simpa using hsq
    have hx3 : x 3 = 0 := by nlinarith [sq_nonneg (x 3), sq_nonneg (x 4)]
    have hx4 : x 4 = 0 := by nlinarith [sq_nonneg (x 3), sq_nonneg (x 4)]
    simp [boxSupportPoint, hzero, hx3, hx4]
  · have hpos : 0 < translationNorm x := lt_of_le_of_ne' (translationNorm_nonneg x) hzero
    have hsumsq : x 3 ^ 2 + x 4 ^ 2 = translationNorm x ^ 2 := by
      unfold translationNorm
      rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    simp [boxSupportPoint, hzero]
    calc
      x 3 * (-(delta * bT * x 3) / translationNorm x) +
          x 4 * (-(delta * bT * x 4) / translationNorm x) =
          -(delta * bT) * (x 3 ^ 2 + x 4 ^ 2) / translationNorm x := by
        field_simp [ne_of_gt hpos]
        ring
      _ = -(delta * bT * translationNorm x) := by
        rw [hsumsq]
        field_simp [ne_of_gt hpos]

lemma boxSupportPoint_inner_eq {delta bPi bGamma bT : ℝ} (x : BoxFlag5) :
    ⟪boxSupportPoint delta bPi bGamma bT x, x⟫ =
      -delta * boxSupport bPi bGamma bT x := by
  have htilt := boxSupportPoint_tilt_inner (delta := delta) (bPi := bPi)
    (bGamma := bGamma) (bT := bT) x
  have hgamma := boxSupportPoint_gamma_inner (delta := delta) (bPi := bPi)
    (bGamma := bGamma) (bT := bT) x
  have htrans := boxSupportPoint_translation_inner (delta := delta) (bPi := bPi)
    (bGamma := bGamma) (bT := bT) x
  rw [PiLp.inner_apply, Fin.sum_univ_five]
  simp only [RCLike.inner_apply]
  simp only [show ∀ r : ℝ, (starRingEnd ℝ) r = r by intro r; simp]
  unfold boxSupport
  nlinarith [htilt, hgamma, htrans]

lemma boxSupportPoint_support {delta bPi bGamma bT : ℝ} (x : BoxFlag5) :
    ⟪boxSupportPoint delta bPi bGamma bT x, x⟫ ≤
      -delta * boxSupport bPi bGamma bT x := by
  rw [boxSupportPoint_inner_eq]

/-- A proof-carrying support certificate for a scaled coordinate box. -/
structure BoxSupportCertificate {V : Finset V3}
    {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ}
    (cert : Finset (ActivePair V R₂)) where
  delta : ℝ
  bPi : ℝ
  bGamma : ℝ
  bT : ℝ
  delta_pos : 0 < delta
  bPi_pos : 0 < bPi
  bGamma_pos : 0 < bGamma
  bT_pos : 0 < bT
  supportKill :
    ∀ x : BoxFlag5, ∃ y ∈ convexHull ℝ (flagFinset cert : Set BoxFlag5),
      ⟪y, x⟫ ≤ -delta * boxSupport bPi bGamma bT x

/-- Proof-carrying form closer to the paper statement `δ K_box ⊆ conv F`.

The coordinate-box support function is proved once in `boxSupportPoint_support`; the certificate
only needs to supply the geometric inclusion `δ K_box ⊆ conv F`.
-/
structure BoxInclusionCertificate {V : Finset V3}
    {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ}
    (cert : Finset (ActivePair V R₂)) where
  delta : ℝ
  bPi : ℝ
  bGamma : ℝ
  bT : ℝ
  delta_pos : 0 < delta
  bPi_pos : 0 < bPi
  bGamma_pos : 0 < bGamma
  bT_pos : 0 < bT
  scaledBoxSubset :
    ∀ y : BoxFlag5, scaledBoxMember delta bPi bGamma bT y →
      y ∈ convexHull ℝ (flagFinset cert : Set BoxFlag5)

/-- A scaled-box inclusion certificate produces the support-kill certificate used by the theorem. -/
def BoxInclusionCertificate.toSupportCertificate {V : Finset V3}
    {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ}
    {cert : Finset (ActivePair V R₂)}
    (box : BoxInclusionCertificate cert) : BoxSupportCertificate cert where
  delta := box.delta
  bPi := box.bPi
  bGamma := box.bGamma
  bT := box.bT
  delta_pos := box.delta_pos
  bPi_pos := box.bPi_pos
  bGamma_pos := box.bGamma_pos
  bT_pos := box.bT_pos
  supportKill := by
    intro x
    let y := boxSupportPoint box.delta box.bPi box.bGamma box.bT x
    have hybox : scaledBoxMember box.delta box.bPi box.bGamma box.bT y :=
      boxSupportPoint_mem_scaledBox x (le_of_lt box.delta_pos) (le_of_lt box.bPi_pos)
        (le_of_lt box.bGamma_pos) (le_of_lt box.bT_pos)
    exact ⟨y, box.scaledBoxSubset y hybox, boxSupportPoint_support x⟩

lemma exists_box_cert_flag_kill {V : Finset V3}
    {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ}
    {cert : Finset (ActivePair V R₂)}
    (box : BoxSupportCertificate cert) (x : BoxFlag5) :
    ∃ p ∈ cert,
      ⟪flagOf p, x⟫ ≤ -box.delta * boxSupport box.bPi box.bGamma box.bT x := by
  classical
  obtain ⟨y, hyconv, hyle⟩ := box.supportKill x
  have hf : ConcaveOn ℝ Set.univ (fun r : BoxFlag5 => ⟪x, r⟫) := by
    simpa using ((innerSL ℝ x).toLinearMap.concaveOn
      (convex_univ : Convex ℝ (Set.univ : Set BoxFlag5)))
  obtain ⟨r, hrSet, hrle⟩ := hf.exists_le_of_mem_convexHull (by intro z hz; simp) hyconv
  obtain ⟨p, hp, hpr⟩ := by
    simpa [flagFinset] using (Finset.mem_image.mp hrSet)
  refine ⟨p, hp, ?_⟩
  subst hpr
  rw [real_inner_comm (flagOf p) x] at hrle
  have hyle' : ⟪x, y⟫ ≤ -box.delta * boxSupport box.bPi box.bGamma box.bT x := by
    calc
      ⟪x, y⟫ = ⟪y, x⟫ := (real_inner_comm x y).symm
      _ ≤ -box.delta * boxSupport box.bPi box.bGamma box.bT x := hyle
  exact le_trans hrle hyle'

/-- Box-cylinder theorem, explicit exponential-coordinate form.

The hypothesis `hrotationBudget` is exactly the decoupled rotation budget after the componentwise
box inequalities have been checked.  No hypothesis is imposed on the translation coordinates.
-/
theorem box_cylinder_theorem_cert_of_exp
    (V : Finset V3) (c : Config V)
    (cert : Finset (ActivePair V c.R₂))
    (box : BoxSupportCertificate cert)
    (s₀ M : ℝ) (hM : M = circumradius V * (1/2 + s₀/6))
    (ξ : V3)
    (hξexp : NormedSpace.exp (skewMatrix ξ) =
      ((c.R₁ * c.R₂⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ))
    (hs_le : ‖ξ‖ ≤ s₀)
    (hmotion : relCoord ξ c.t ≠ 0)
    (hrotationBudget :
      M * ‖ξ‖ ^ 2 <
        box.delta * (box.bPi * tiltNorm (relCoord ξ c.t) +
          box.bGamma * |(relCoord ξ c.t) 2|) ∨ ξ = 0) :
    ¬ RupertContainment V c := by
  rintro hcont
  set x := relCoord ξ c.t with hx_def
  have hx0 : x ≠ 0 := by
    intro hx
    exact hmotion (by simpa [hx_def] using hx)
  obtain ⟨p, _hp, hkill⟩ := exists_box_cert_flag_kill box x
  obtain ⟨Q, hdecomp, hQbnd⟩ := slack_decomp p ξ c.t
  have hQ : |Q| ≤ M * ‖ξ‖ ^ 2 := by
    rw [hM]
    have hρ : 0 ≤ circumradius V := circumradius_nonneg V
    have hs2 : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg ‖ξ‖
    have hfac : 1 / 2 + ‖ξ‖ / 6 ≤ 1 / 2 + s₀ / 6 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hfac hρ, hs2, hQbnd]
  have hQle : Q ≤ M * ‖ξ‖ ^ 2 := le_trans (le_abs_self Q) hQ
  have hneg : slack p ξ c.t < 0 := by
    have hstep :
        slack p ξ c.t ≤
          -box.delta * boxSupport box.bPi box.bGamma box.bT x + M * ‖ξ‖ ^ 2 := by
      rw [hdecomp]
      nlinarith [hkill, hQle]
    rcases hrotationBudget with hrot | hξ0
    · have hsupport_split :
          box.delta * (box.bPi * tiltNorm x + box.bGamma * |x 2|) ≤
            box.delta * boxSupport box.bPi box.bGamma box.bT x := by
        have hτ : 0 ≤ box.bT * translationNorm x :=
          mul_nonneg (le_of_lt box.bT_pos) (translationNorm_nonneg x)
        have hδ : 0 ≤ box.delta := le_of_lt box.delta_pos
        unfold boxSupport
        nlinarith [mul_le_mul_of_nonneg_left (by nlinarith : box.bPi * tiltNorm x +
          box.bGamma * |x 2| ≤ box.bPi * tiltNorm x + box.bGamma * |x 2| +
          box.bT * translationNorm x) hδ]
      have hrot' : M * ‖ξ‖ ^ 2 < box.delta * boxSupport box.bPi box.bGamma box.bT x := by
        exact lt_of_lt_of_le hrot hsupport_split
      nlinarith
    · have hξnorm0 : ‖ξ‖ = 0 := by rw [hξ0, norm_zero]
      have hquad : M * ‖ξ‖ ^ 2 = 0 := by rw [hξnorm0]; ring
      have ht_ne : c.t ≠ 0 := by
        intro ht
        apply hx0
        rw [hx_def, hξ0, ht]
        ext i
        fin_cases i <;> simp [relCoord]
      have ht_pos : 0 < translationNorm x := by
        unfold translationNorm
        rw [hx_def, hξ0]
        simp [relCoord]
        have ht0 : c.t 0 ^ 2 + c.t 1 ^ 2 ≠ 0 := by
          intro hsum
          have h0 : c.t 0 = 0 := by nlinarith [sq_nonneg (c.t 0), sq_nonneg (c.t 1)]
          have h1 : c.t 1 = 0 := by nlinarith [sq_nonneg (c.t 0), sq_nonneg (c.t 1)]
          exact ht_ne (by ext i; fin_cases i <;> simp [h0, h1])
        exact lt_of_le_of_ne' (add_nonneg (sq_nonneg _) (sq_nonneg _)) ht0
      have hbox_pos : 0 < boxSupport box.bPi box.bGamma box.bT x := by
        unfold boxSupport
        have hτpos : 0 < box.bT * translationNorm x :=
          mul_pos box.bT_pos ht_pos
        nlinarith [mul_nonneg (le_of_lt box.bPi_pos) (tiltNorm_nonneg x),
          mul_nonneg (le_of_lt box.bGamma_pos) (abs_nonneg (x 2))]
      nlinarith [hstep, hquad, box.delta_pos, hbox_pos]
  have hpos : 0 < slack p ξ c.t := containment_imp_slack_pos hcont ξ hξexp p
  exact absurd hpos (not_lt.mpr (le_of_lt hneg))

/-- Box-cylinder theorem in the paper-facing scaled-box inclusion form. -/
theorem box_cylinder_theorem_of_box_inclusion_cert_of_exp
    (V : Finset V3) (c : Config V)
    (cert : Finset (ActivePair V c.R₂))
    (box : BoxInclusionCertificate cert)
    (s₀ M : ℝ) (hM : M = circumradius V * (1/2 + s₀/6))
    (ξ : V3)
    (hξexp : NormedSpace.exp (skewMatrix ξ) =
      ((c.R₁ * c.R₂⁻¹ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ))
    (hs_le : ‖ξ‖ ≤ s₀)
    (hmotion : relCoord ξ c.t ≠ 0)
    (hrotationBudget :
      M * ‖ξ‖ ^ 2 <
        box.delta * (box.bPi * tiltNorm (relCoord ξ c.t) +
          box.bGamma * |(relCoord ξ c.t) 2|) ∨ ξ = 0) :
    ¬ RupertContainment V c := by
  exact box_cylinder_theorem_cert_of_exp V c cert box.toSupportCertificate s₀ M hM ξ
    hξexp hs_le hmotion hrotationBudget

end DepthCylinderTheorem
