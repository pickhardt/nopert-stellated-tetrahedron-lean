import RupertStellatedTetrahedron.CriticalDisk.Statement

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

/-!
## Zone consequences for the critical-disk assembly

The computational inputs are still abstract.  This file fixes the logical interface: each zone
proves the same concrete critical-disk exclusion statement, and the pentachotomy turns those five
zone-local consequences into Lemma 6' for the candidate.
-/

/-- Zone-local exclusion hypotheses for one candidate. -/
structure CriticalDiskZoneConsequences (cand : CriticalDiskCandidate) where
  zone0Excludes :
    CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand
  zoneAExcludes :
    CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand
  zoneBExcludes :
    CriticalDiskHypotheses cand → CriticalDiskZoneB cand.point → CriticalDiskExclusion cand
  zoneCExcludes :
    CriticalDiskHypotheses cand → CriticalDiskZoneC cand.point → CriticalDiskExclusion cand
  zoneDExcludes :
    CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand

theorem CriticalDiskZoneConsequences.excludes
    {cand : CriticalDiskCandidate}
    (zones : CriticalDiskZoneConsequences cand)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand := by
  rcases criticalDisk_zone_pentachotomy cand.point with h0 | hA | hB | hC | hD
  · exact zones.zone0Excludes hcand h0
  · exact zones.zoneAExcludes hcand hA
  · exact zones.zoneBExcludes hcand hB
  · exact zones.zoneCExcludes hcand hC
  · exact zones.zoneDExcludes hcand hD

theorem CriticalDiskZoneConsequences.lemma6prime
    {cand : CriticalDiskCandidate}
    (zones : CriticalDiskZoneConsequences cand) :
    CriticalDiskLemma6PrimeStatement cand := by
  intro hcand
  exact zones.excludes hcand

theorem criticalDisk_exclusion_of_zone_consequences
    {cand : CriticalDiskCandidate}
    (zones : CriticalDiskZoneConsequences cand)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  zones.excludes hcand

theorem criticalDisk_lemma6prime_of_zone_consequences
    {cand : CriticalDiskCandidate}
    (zones : CriticalDiskZoneConsequences cand) :
    CriticalDiskLemma6PrimeStatement cand :=
  zones.lemma6prime

/-- A Zone B consequence often needs only an angle-bound hypothesis plus the SB cylinder theorem. -/
structure ZoneBAngleConsequence (cand : CriticalDiskCandidate)
    (E : Type*) [SeminormedAddCommGroup E] where
  xiHat : E
  normSqBound : ‖xiHat‖ ^ 2 ≤ criticalDiskAnchorRadiusSq
  sbCylinderExcludes :
    CriticalDiskHypotheses cand →
      cand.delta * ‖xiHat‖ < criticalDiskG1 * cand.delta / criticalDiskM →
      CriticalDiskExclusion cand

theorem ZoneBAngleConsequence.angleBound
    {cand : CriticalDiskCandidate} {E : Type*} [SeminormedAddCommGroup E]
    (z : ZoneBAngleConsequence cand E)
    (hcand : CriticalDiskHypotheses cand) :
    cand.delta * ‖z.xiHat‖ < criticalDiskG1 * cand.delta / criticalDiskM :=
  zoneB_angle_bound_of_norm_sq_le_anchor cand.delta hcand.delta_pos z.xiHat z.normSqBound

theorem ZoneBAngleConsequence.excludes
    {cand : CriticalDiskCandidate} {E : Type*} [SeminormedAddCommGroup E]
    (z : ZoneBAngleConsequence cand E)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand := by
  exact z.sbCylinderExcludes hcand (z.angleBound hcand)

theorem ZoneBAngleConsequence.zoneExcludes
    {cand : CriticalDiskCandidate} {E : Type*} [SeminormedAddCommGroup E]
    (z : ZoneBAngleConsequence cand E)
    (hcand : CriticalDiskHypotheses cand)
    (_hzone : CriticalDiskZoneB cand.point) :
    CriticalDiskExclusion cand :=
  z.excludes hcand

/-- A Zone C consequence has the analogous sheet-anchor angle bound. -/
structure ZoneCAngleConsequence (cand : CriticalDiskCandidate)
    (E : Type*) [SeminormedAddCommGroup E] where
  xiHatDiff : E
  normSqBound : ‖xiHatDiff‖ ^ 2 ≤ criticalDiskAnchorRadiusSq
  scCylinderExcludes :
    CriticalDiskHypotheses cand →
      cand.delta * ‖xiHatDiff‖ < criticalDiskCMin * cand.delta / criticalDiskM →
      CriticalDiskExclusion cand

theorem ZoneCAngleConsequence.angleBound
    {cand : CriticalDiskCandidate} {E : Type*} [SeminormedAddCommGroup E]
    (z : ZoneCAngleConsequence cand E)
    (hcand : CriticalDiskHypotheses cand) :
    cand.delta * ‖z.xiHatDiff‖ < criticalDiskCMin * cand.delta / criticalDiskM :=
  zoneC_angle_bound_of_norm_sq_le_anchor cand.delta hcand.delta_pos z.xiHatDiff z.normSqBound

theorem ZoneCAngleConsequence.excludes
    {cand : CriticalDiskCandidate} {E : Type*} [SeminormedAddCommGroup E]
    (z : ZoneCAngleConsequence cand E)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand := by
  exact z.scCylinderExcludes hcand (z.angleBound hcand)

theorem ZoneCAngleConsequence.zoneExcludes
    {cand : CriticalDiskCandidate} {E : Type*} [SeminormedAddCommGroup E]
    (z : ZoneCAngleConsequence cand E)
    (hcand : CriticalDiskHypotheses cand)
    (_hzone : CriticalDiskZoneC cand.point) :
    CriticalDiskExclusion cand :=
  z.excludes hcand

/-- Assemble the five zone consequences when Zones B and C are supplied in their common
angle-consequence form. -/
def CriticalDiskZoneConsequences.ofAngleConsequences
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand) :
    CriticalDiskZoneConsequences cand where
  zone0Excludes := zone0
  zoneAExcludes := zoneA
  zoneBExcludes := zoneB.zoneExcludes
  zoneCExcludes := zoneC.zoneExcludes
  zoneDExcludes := zoneD

end RupertStellatedTetrahedron
