import RupertStellatedTetrahedron.Stellated.UStarDepth

/-!
Lean boundary for the standard `u*` depth certificate.

The geometric part of `UStarDepth.lean` already reduces the downstream support-kill theorem to
one finite exact-hull containment statement for the standard payload.  This file names that
remaining statement as the certified input boundary.
-/

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

namespace UStarCertifiedInput

/-- The remaining verifier output for the standard `u*` depth payload. -/
structure StandardHullSoundness where
  exactHullContainsRadiusBall :
    Metric.closedBall (0 : UStarFlag5) standardUStarDepthPayload.radius.toReal ⊆
      convexHull ℝ (uStarActiveFlagsExactReal : Set UStarFlag5)

/-- A verifier can alternatively provide a finite facet-support cover.  Lean then derives the
closed-ball containment by using the facet convex-combination witnesses and depth duality. -/
structure StandardFacetSupportSoundness where
  support_verified : UStarDepthFacetSupportVerified standardUStarDepthPayload

def StandardFacetSupportSoundness.toPayloadVerified
    (soundness : StandardFacetSupportSoundness) :
    UStarDepthPayloadVerified standardUStarDepthPayload :=
  soundness.support_verified.toPayloadVerified

def StandardFacetSupportSoundness.toHullSoundness
    (soundness : StandardFacetSupportSoundness) :
    StandardHullSoundness where
  exactHullContainsRadiusBall :=
    soundness.toPayloadVerified.exactHullContainsRadiusBall

def StandardFacetSupportSoundness.toCertificate
    (soundness : StandardFacetSupportSoundness) : UStarDepthCertificate :=
  soundness.toPayloadVerified.toCertificate

theorem StandardFacetSupportSoundness.supportKill
    (soundness : StandardFacetSupportSoundness) :
    ∀ x : UStarFlag5, ‖x‖ = 1 →
      ∃ r ∈ soundness.toCertificate.flags, ⟪r, x⟫ ≤ -uStarDepthRadius :=
  soundness.toCertificate.supportKill

theorem StandardFacetSupportSoundness.supportKill_nonzero
    (soundness : StandardFacetSupportSoundness) (x : UStarFlag5) (hx : x ≠ 0) :
    ∃ r ∈ soundness.toCertificate.flags, ⟪r, x⟫ ≤ -uStarDepthRadius * ‖x‖ :=
  uStar_support_nonzero_from_certificate soundness.toCertificate x hx

def StandardHullSoundness.toPayloadVerified
    (soundness : StandardHullSoundness) :
    UStarDepthPayloadVerified standardUStarDepthPayload :=
  standardUStarDepthPayloadVerified soundness.exactHullContainsRadiusBall

def StandardHullSoundness.toCertificate
    (soundness : StandardHullSoundness) : UStarDepthCertificate :=
  soundness.toPayloadVerified.toCertificate

theorem StandardHullSoundness.supportKill
    (soundness : StandardHullSoundness) :
    ∀ x : UStarFlag5, ‖x‖ = 1 →
      ∃ r ∈ soundness.toCertificate.flags, ⟪r, x⟫ ≤ -uStarDepthRadius :=
  soundness.toCertificate.supportKill

theorem StandardHullSoundness.supportKill_nonzero
    (soundness : StandardHullSoundness) (x : UStarFlag5) (hx : x ≠ 0) :
    ∃ r ∈ soundness.toCertificate.flags, ⟪r, x⟫ ≤ -uStarDepthRadius * ‖x‖ :=
  uStar_support_nonzero_from_certificate soundness.toCertificate x hx

end UStarCertifiedInput

end RupertStellatedTetrahedron
