import RupertStellatedTetrahedron.DepthCylinderTheorem.Duality

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace DepthCylinderTheorem

/-!
## Depth perturbation

The fully quantitative perturbation lemma will use a nearest-point matching between two finite flag
sets. The support-side form below is already checked and is the right assembly target after the
external matching certificate has been expanded.
-/

abbrev Flag5 := EuclideanSpace ℝ (Fin 5)

/-- If the depth-duality support inequalities hold for radius `d - ε`, then the perturbed
flag set contains that ball. -/
theorem depth_perturbation_from_support (F' : Finset Flag5) (d ε : ℝ)
    (hpos : 0 < d - ε)
    (hsupport : ∀ x : Flag5, ‖x‖ = 1 → ∃ r ∈ F', ⟪r, x⟫ ≤ -(d - ε)) :
    Metric.closedBall (0 : Flag5) (d - ε) ⊆ convexHull ℝ (F' : Set Flag5) := by
  exact (depth_duality F' (d - ε) hpos).mpr hsupport

/-- A nearest-flag matching transfers support inequalities from `F` to `F'`, losing at most `ε`.

This is the quantitative core used by the perturbation certificate: the checker only has to provide
the old support certificate and, for every old flag used by it, a nearby new flag.
-/
theorem depth_support_perturbation_from_matching (F F' : Finset Flag5) (d ε : ℝ)
    (hsupport : ∀ x : Flag5, ‖x‖ = 1 → ∃ r ∈ F, ⟪r, x⟫ ≤ -d)
    (hmatch : ∀ r ∈ F, ∃ r' ∈ F', ‖r' - r‖ ≤ ε) :
    ∀ x : Flag5, ‖x‖ = 1 → ∃ r' ∈ F', ⟪r', x⟫ ≤ -(d - ε) := by
  intro x hx
  obtain ⟨r, hrF, hrkill⟩ := hsupport x hx
  obtain ⟨r', hr'F, hclose⟩ := hmatch r hrF
  refine ⟨r', hr'F, ?_⟩
  have hdiff :
      ⟪r' - r, x⟫ ≤ ε := by
    have hinner :
        ⟪r' - r, x⟫ ≤ ‖r' - r‖ * ‖x‖ :=
      le_trans (le_abs_self _)
        (by simpa [Real.norm_eq_abs] using
          (norm_inner_le_norm (𝕜 := ℝ) (r' - r) x))
    rw [hx] at hinner
    nlinarith
  have hdecomp : ⟪r', x⟫ = ⟪r, x⟫ + ⟪r' - r, x⟫ := by
    calc
      ⟪r', x⟫ = ⟪r + (r' - r), x⟫ := by
        rw [show r + (r' - r) = r' by abel]
      _ = ⟪r, x⟫ + ⟪r' - r, x⟫ := by
        rw [inner_add_left]
  rw [hdecomp]
  nlinarith

/-- Certificate boundary for the metric perturbation of a finite flag set.

The checker output is a finite matching from every old flag used by the support certificate to a
new flag, plus the verified `≤ ε` error bound.
-/
structure DepthPerturbationCertificate (F F' : Finset Flag5) (d ε : ℝ) where
  radiusPositive : 0 < d - ε
  supportBeforePerturbation :
    ∀ x : Flag5, ‖x‖ = 1 → ∃ r ∈ F, ⟪r, x⟫ ≤ -d
  matching :
    ∀ r ∈ F, ∃ r' ∈ F', ‖r' - r‖ ≤ ε

theorem DepthPerturbationCertificate.supportAfterPerturbation
    {F F' : Finset Flag5} {d ε : ℝ}
    (cert : DepthPerturbationCertificate F F' d ε) :
    ∀ x : Flag5, ‖x‖ = 1 → ∃ r ∈ F', ⟪r, x⟫ ≤ -(d - ε) :=
  depth_support_perturbation_from_matching F F' d ε cert.supportBeforePerturbation
    cert.matching

theorem depth_perturbation_from_certificate {F F' : Finset Flag5} {d ε : ℝ}
    (cert : DepthPerturbationCertificate F F' d ε) :
    Metric.closedBall (0 : Flag5) (d - ε) ⊆ convexHull ℝ (F' : Set Flag5) := by
  exact depth_perturbation_from_support F' d ε cert.radiusPositive
    cert.supportAfterPerturbation

end DepthCylinderTheorem
