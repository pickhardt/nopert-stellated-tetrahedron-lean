import RupertStellatedTetrahedron.CriticalDisk.Assembly
import RupertStellatedTetrahedron.CriticalDisk.SymmetryTransport

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

/-!
## Transport of critical-disk assembly data along marginal sheets

The lower transport module identifies the containment problem after applying the marginal
reflection map to the inner rotation.  This file lifts that fact through the zone-consequence and
Lemma 6' certificate interfaces.
-/

def CriticalDiskZoneConsequences.iotaInner
    {cand : CriticalDiskCandidate}
    (zones : CriticalDiskZoneConsequences cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskZoneConsequences (cand.iotaInner S) where
  zone0Excludes := by
    intro hiota hzone
    exact (criticalDiskExclusion_iotaInner_iff cand S).mpr
      (zones.zone0Excludes
        ((criticalDiskHypotheses_iotaInner_iff cand S).mp hiota)
        (by simpa [CriticalDiskCandidate.iotaInner] using hzone))
  zoneAExcludes := by
    intro hiota hzone
    exact (criticalDiskExclusion_iotaInner_iff cand S).mpr
      (zones.zoneAExcludes
        ((criticalDiskHypotheses_iotaInner_iff cand S).mp hiota)
        (by simpa [CriticalDiskCandidate.iotaInner] using hzone))
  zoneBExcludes := by
    intro hiota hzone
    exact (criticalDiskExclusion_iotaInner_iff cand S).mpr
      (zones.zoneBExcludes
        ((criticalDiskHypotheses_iotaInner_iff cand S).mp hiota)
        (by simpa [CriticalDiskCandidate.iotaInner] using hzone))
  zoneCExcludes := by
    intro hiota hzone
    exact (criticalDiskExclusion_iotaInner_iff cand S).mpr
      (zones.zoneCExcludes
        ((criticalDiskHypotheses_iotaInner_iff cand S).mp hiota)
        (by simpa [CriticalDiskCandidate.iotaInner] using hzone))
  zoneDExcludes := by
    intro hiota hzone
    exact (criticalDiskExclusion_iotaInner_iff cand S).mpr
      (zones.zoneDExcludes
        ((criticalDiskHypotheses_iotaInner_iff cand S).mp hiota)
        (by simpa [CriticalDiskCandidate.iotaInner] using hzone))

def CriticalDiskLemma6PrimeCertificate.iotaInner
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (cert : CriticalDiskLemma6PrimeCertificate inputs cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLemma6PrimeCertificate inputs (cand.iotaInner S) where
  zoneConsequences hinputs := (cert.zoneConsequences hinputs).iotaInner S

def CriticalDiskZoneConsequences.faceDiagonalReflection
    {cand : CriticalDiskCandidate}
    (zones : CriticalDiskZoneConsequences cand) (i : Fin 6) :
    CriticalDiskZoneConsequences (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  zones.iotaInner (faceDiagonalReflectionSymmetry i)

def CriticalDiskLemma6PrimeCertificate.faceDiagonalReflection
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (cert : CriticalDiskLemma6PrimeCertificate inputs cand) (i : Fin 6) :
    CriticalDiskLemma6PrimeCertificate inputs
      (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  cert.iotaInner (faceDiagonalReflectionSymmetry i)

/-- A packaged statement of Lemma 6' on all six face-diagonal reflected marginal sheets. -/
def FaceDiagonalLemma6PrimeFamily (cand : CriticalDiskCandidate) : Prop :=
  ∀ i : Fin 6,
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner (faceDiagonalReflectionSymmetry i))

/-- A packaged localized exclusion statement on all six face-diagonal reflected marginal sheets. -/
def FaceDiagonalLocalizedExclusionFamily (cand : CriticalDiskCandidate) : Prop :=
  ∀ i : Fin 6,
    CriticalDiskLocalizedExclusionStatement
      (cand.iotaInner (faceDiagonalReflectionSymmetry i))

/-- Apply an all-six face-diagonal Lemma 6' family at one reflected sheet. -/
theorem critical_disk_exclusion_of_faceDiagonalFamily
    {cand : CriticalDiskCandidate}
    (family : FaceDiagonalLemma6PrimeFamily cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  family i hiota

/-- Apply an all-six localized family at one reflected sheet, returning localization plus
exclusion. -/
theorem critical_disk_localized_exclusion_of_faceDiagonalFamily
    {cand : CriticalDiskCandidate}
    (family : FaceDiagonalLocalizedExclusionFamily cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskLocalizationConclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) ∧
      CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  family i hiota

/-- Apply a localized exclusion statement after an arbitrary iota-inner transport. -/
theorem critical_disk_localized_exclusion_of_iotaInnerLocalizedStatement
    {cand : CriticalDiskCandidate}
    {S : ImproperVertexSymmetry stellatedVertices}
    (h : CriticalDiskLocalizedExclusionStatement (cand.iotaInner S))
    (hiota : CriticalDiskHypotheses (cand.iotaInner S)) :
    CriticalDiskLocalizationConclusion (cand.iotaInner S) ∧
      CriticalDiskExclusion (cand.iotaInner S) :=
  h hiota

theorem critical_disk_localization_of_iotaInnerLocalizedStatement
    {cand : CriticalDiskCandidate}
    {S : ImproperVertexSymmetry stellatedVertices}
    (h : CriticalDiskLocalizedExclusionStatement (cand.iotaInner S))
    (hiota : CriticalDiskHypotheses (cand.iotaInner S)) :
    CriticalDiskLocalizationConclusion (cand.iotaInner S) :=
  h.localization hiota

theorem critical_disk_planar_tube_of_iotaInnerLocalizedStatement
    {cand : CriticalDiskCandidate}
    {S : ImproperVertexSymmetry stellatedVertices}
    (h : CriticalDiskLocalizedExclusionStatement (cand.iotaInner S))
    (hiota : CriticalDiskHypotheses (cand.iotaInner S)) :
    (cand.iotaInner S).point.distToD < criticalDiskLocalizationPlanarTube :=
  h.planarTube hiota

theorem critical_disk_transverse_tube_of_iotaInnerLocalizedStatement
    {cand : CriticalDiskCandidate}
    {S : ImproperVertexSymmetry stellatedVertices}
    (h : CriticalDiskLocalizedExclusionStatement (cand.iotaInner S))
    (hiota : CriticalDiskHypotheses (cand.iotaInner S)) :
    (cand.iotaInner S).point.transverseNorm < criticalDiskLocalizationTransverseTube :=
  h.transverseTube hiota

theorem critical_disk_exclusion_of_iotaInnerLocalizedStatement
    {cand : CriticalDiskCandidate}
    {S : ImproperVertexSymmetry stellatedVertices}
    (h : CriticalDiskLocalizedExclusionStatement (cand.iotaInner S))
    (hiota : CriticalDiskHypotheses (cand.iotaInner S)) :
    CriticalDiskExclusion (cand.iotaInner S) :=
  h.exclusion hiota

theorem critical_disk_localization_of_faceDiagonalLocalizedFamily
    {cand : CriticalDiskCandidate}
    (family : FaceDiagonalLocalizedExclusionFamily cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskLocalizationConclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_localization_of_iotaInnerLocalizedStatement (family i) hiota

theorem critical_disk_planar_tube_of_faceDiagonalLocalizedFamily
    {cand : CriticalDiskCandidate}
    (family : FaceDiagonalLocalizedExclusionFamily cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    (cand.iotaInner (faceDiagonalReflectionSymmetry i)).point.distToD <
      criticalDiskLocalizationPlanarTube :=
  critical_disk_planar_tube_of_iotaInnerLocalizedStatement (family i) hiota

theorem critical_disk_transverse_tube_of_faceDiagonalLocalizedFamily
    {cand : CriticalDiskCandidate}
    (family : FaceDiagonalLocalizedExclusionFamily cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    (cand.iotaInner (faceDiagonalReflectionSymmetry i)).point.transverseNorm <
      criticalDiskLocalizationTransverseTube :=
  critical_disk_transverse_tube_of_iotaInnerLocalizedStatement (family i) hiota

theorem critical_disk_exclusion_of_faceDiagonalLocalizedFamily
    {cand : CriticalDiskCandidate}
    (family : FaceDiagonalLocalizedExclusionFamily cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_of_iotaInnerLocalizedStatement (family i) hiota

theorem critical_disk_assembly_conditional_iotaInner
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (cert : CriticalDiskLemma6PrimeCertificate inputs cand)
    (hinputs : inputs.allCertified)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLemma6PrimeStatement (cand.iotaInner S) :=
  critical_disk_assembly_conditional (cert.iotaInner S) hinputs

/-- Localized transported assembly along an arbitrary marginal-sheet symmetry. -/
theorem critical_disk_localized_exclusion_conditional_iotaInner
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (cert : CriticalDiskLemma6PrimeCertificate inputs cand)
    (hinputs : inputs.allCertified)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLocalizedExclusionStatement (cand.iotaInner S) :=
  criticalDisk_localized_exclusion_from_analytic_inputs analytics
    (critical_disk_assembly_conditional_iotaInner cert hinputs S)

/-- Transported assembly from an already-certified zone consequence bundle. -/
theorem critical_disk_assembly_conditional_iotaInner_of_zone_consequences
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (hinputs : inputs.allCertified)
    (zones : CriticalDiskZoneConsequences cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLemma6PrimeStatement (cand.iotaInner S) :=
  critical_disk_assembly_conditional_iotaInner
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones) hinputs S

/-- Direct transported exclusion from an already-certified zone consequence bundle. -/
theorem critical_disk_exclusion_conditional_iotaInner_of_zone_consequences
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (hinputs : inputs.allCertified)
    (zones : CriticalDiskZoneConsequences cand)
    (S : ImproperVertexSymmetry stellatedVertices)
    (hiota : CriticalDiskHypotheses (cand.iotaInner S)) :
    CriticalDiskExclusion (cand.iotaInner S) :=
  critical_disk_assembly_conditional_iotaInner_of_zone_consequences
    hinputs zones S hiota

/-- Transported assembly when Zones B/C are supplied in their common angle-bound form. -/
theorem critical_disk_assembly_conditional_iotaInner_of_angle_consequences
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (hinputs : inputs.allCertified)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLemma6PrimeStatement (cand.iotaInner S) :=
  critical_disk_assembly_conditional_iotaInner
    (CriticalDiskLemma6PrimeCertificate.ofAngleConsequences
      zone0 zoneA zoneB zoneC zoneD)
    hinputs S

/-- Direct transported exclusion when Zones B/C are supplied in their common angle-bound form. -/
theorem critical_disk_exclusion_conditional_iotaInner_of_angle_consequences
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (hinputs : inputs.allCertified)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand)
    (S : ImproperVertexSymmetry stellatedVertices)
    (hiota : CriticalDiskHypotheses (cand.iotaInner S)) :
    CriticalDiskExclusion (cand.iotaInner S) :=
  critical_disk_assembly_conditional_iotaInner_of_angle_consequences
    hinputs zone0 zoneA zoneB zoneC zoneD S hiota

theorem critical_disk_assembly_conditional_swapXY
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (cert : CriticalDiskLemma6PrimeCertificate inputs cand)
    (hinputs : inputs.allCertified) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner swapXYImproperVertexSymmetry) :=
  critical_disk_assembly_conditional_iotaInner cert hinputs swapXYImproperVertexSymmetry

theorem critical_disk_assembly_conditional_swapXZ
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (cert : CriticalDiskLemma6PrimeCertificate inputs cand)
    (hinputs : inputs.allCertified) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner swapXZImproperVertexSymmetry) :=
  critical_disk_assembly_conditional_iotaInner cert hinputs swapXZImproperVertexSymmetry

theorem critical_disk_assembly_conditional_swapYZ
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (cert : CriticalDiskLemma6PrimeCertificate inputs cand)
    (hinputs : inputs.allCertified) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner swapYZImproperVertexSymmetry) :=
  critical_disk_assembly_conditional_iotaInner cert hinputs swapYZImproperVertexSymmetry

theorem critical_disk_assembly_conditional_negSwapXY
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (cert : CriticalDiskLemma6PrimeCertificate inputs cand)
    (hinputs : inputs.allCertified) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner negSwapXYImproperVertexSymmetry) :=
  critical_disk_assembly_conditional_iotaInner cert hinputs negSwapXYImproperVertexSymmetry

theorem critical_disk_assembly_conditional_negSwapXZ
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (cert : CriticalDiskLemma6PrimeCertificate inputs cand)
    (hinputs : inputs.allCertified) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner negSwapXZImproperVertexSymmetry) :=
  critical_disk_assembly_conditional_iotaInner cert hinputs negSwapXZImproperVertexSymmetry

theorem critical_disk_assembly_conditional_negSwapYZ
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (cert : CriticalDiskLemma6PrimeCertificate inputs cand)
    (hinputs : inputs.allCertified) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner negSwapYZImproperVertexSymmetry) :=
  critical_disk_assembly_conditional_iotaInner cert hinputs negSwapYZImproperVertexSymmetry

theorem critical_disk_assembly_conditional_faceDiagonalReflection
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (cert : CriticalDiskLemma6PrimeCertificate inputs cand)
    (hinputs : inputs.allCertified) (i : Fin 6) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_assembly_conditional (cert.faceDiagonalReflection i) hinputs

/-- One face-diagonal reflected assembly from an already-certified zone consequence bundle. -/
theorem critical_disk_assembly_conditional_faceDiagonalReflection_of_zone_consequences
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (hinputs : inputs.allCertified)
    (zones : CriticalDiskZoneConsequences cand) (i : Fin 6) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_assembly_conditional_faceDiagonalReflection
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones) hinputs i

/-- Direct one-face-diagonal exclusion from an already-certified zone consequence bundle. -/
theorem critical_disk_exclusion_conditional_faceDiagonalReflection_of_zone_consequences
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (hinputs : inputs.allCertified)
    (zones : CriticalDiskZoneConsequences cand) (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_assembly_conditional_faceDiagonalReflection_of_zone_consequences
    hinputs zones i hiota

/-- One face-diagonal reflected assembly when Zones B/C are supplied in their common angle-bound
form. -/
theorem critical_disk_assembly_conditional_faceDiagonalReflection_of_angle_consequences
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (hinputs : inputs.allCertified)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand)
    (i : Fin 6) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_assembly_conditional_faceDiagonalReflection
    (CriticalDiskLemma6PrimeCertificate.ofAngleConsequences
      zone0 zoneA zoneB zoneC zoneD)
    hinputs i

/-- Direct one-face-diagonal exclusion when Zones B/C are supplied in their common angle-bound
form. -/
theorem critical_disk_exclusion_conditional_faceDiagonalReflection_of_angle_consequences
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (hinputs : inputs.allCertified)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_assembly_conditional_faceDiagonalReflection_of_angle_consequences
    hinputs zone0 zoneA zoneB zoneC zoneD i hiota

theorem critical_disk_assembly_conditional_faceDiagonalFamily
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (cert : CriticalDiskLemma6PrimeCertificate inputs cand)
    (hinputs : inputs.allCertified) :
    FaceDiagonalLemma6PrimeFamily cand := by
  intro i
  exact critical_disk_assembly_conditional_faceDiagonalReflection cert hinputs i

/-- All-six localized face-diagonal conclusion from analytic localization and conditional
Lemma 6'. -/
theorem critical_disk_localized_exclusion_conditional_faceDiagonalFamily
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (cert : CriticalDiskLemma6PrimeCertificate inputs cand)
    (hinputs : inputs.allCertified) :
    FaceDiagonalLocalizedExclusionFamily cand := by
  intro i
  exact criticalDisk_localized_exclusion_from_analytic_inputs analytics
    (critical_disk_assembly_conditional_faceDiagonalReflection cert hinputs i)

/-- All-six face-diagonal assembly from an already-certified zone consequence bundle. -/
theorem critical_disk_assembly_conditional_faceDiagonalFamily_of_zone_consequences
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (hinputs : inputs.allCertified)
    (zones : CriticalDiskZoneConsequences cand) :
    FaceDiagonalLemma6PrimeFamily cand :=
  critical_disk_assembly_conditional_faceDiagonalFamily
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones)
    hinputs

/-- All-six face-diagonal assembly when Zones B/C are supplied in their common angle-bound form. -/
theorem critical_disk_assembly_conditional_faceDiagonalFamily_of_angle_consequences
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (hinputs : inputs.allCertified)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand) :
    FaceDiagonalLemma6PrimeFamily cand :=
  critical_disk_assembly_conditional_faceDiagonalFamily
    (CriticalDiskLemma6PrimeCertificate.ofAngleConsequences
      zone0 zoneA zoneB zoneC zoneD)
    hinputs

/-! ### Standard certificate symmetry entry points -/

/-- Transported Lemma 6' from standard `(SF)` and `(SB-box)` certificates plus a zone bundle. -/
theorem critical_disk_assembly_iotaInner_from_standard_certificates_and_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLemma6PrimeStatement (cand.iotaInner S) :=
  critical_disk_assembly_conditional_iotaInner_of_zone_consequences
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert) zones S

/-- Direct transported exclusion from standard certificates plus a zone bundle. -/
theorem critical_disk_exclusion_iotaInner_from_standard_certificates_and_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand)
    (S : ImproperVertexSymmetry stellatedVertices)
    (hiota : CriticalDiskHypotheses (cand.iotaInner S)) :
    CriticalDiskExclusion (cand.iotaInner S) :=
  critical_disk_exclusion_conditional_iotaInner_of_zone_consequences
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert) zones S hiota

/-- Localized transported exclusion from standard certificates plus a zone bundle. -/
theorem critical_disk_localized_exclusion_iotaInner_from_standard_certificates_and_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLocalizedExclusionStatement (cand.iotaInner S) :=
  critical_disk_localized_exclusion_conditional_iotaInner analytics
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones)
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert) S

/-- Transported Lemma 6' from standard certificates when Zones B/C are supplied in their
angle-consequence form. -/
theorem critical_disk_assembly_iotaInner_from_standard_certificates_and_angle_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLemma6PrimeStatement (cand.iotaInner S) :=
  critical_disk_assembly_conditional_iotaInner_of_angle_consequences
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert)
    zone0 zoneA zoneB zoneC zoneD S

/-- Direct transported exclusion from standard certificates and B/C angle consequences. -/
theorem critical_disk_exclusion_iotaInner_from_standard_certificates_and_angle_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand)
    (S : ImproperVertexSymmetry stellatedVertices)
    (hiota : CriticalDiskHypotheses (cand.iotaInner S)) :
    CriticalDiskExclusion (cand.iotaInner S) :=
  critical_disk_exclusion_conditional_iotaInner_of_angle_consequences
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert)
    zone0 zoneA zoneB zoneC zoneD S hiota

/-- Localized transported exclusion from standard certificates and B/C angle consequences. -/
theorem critical_disk_localized_exclusion_iotaInner_from_standard_certificates_and_angle_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (analytics : CriticalDiskAnalyticInputs)
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLocalizedExclusionStatement (cand.iotaInner S) :=
  critical_disk_localized_exclusion_conditional_iotaInner analytics
    (CriticalDiskLemma6PrimeCertificate.ofAngleConsequences
      zone0 zoneA zoneB zoneC zoneD)
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert) S

/-- One face-diagonal Lemma 6' from standard certificates plus a zone bundle. -/
theorem critical_disk_assembly_faceDiagonal_from_standard_certificates_and_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand)
    (i : Fin 6) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_assembly_conditional_faceDiagonalReflection_of_zone_consequences
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert) zones i

/-- Direct one-face-diagonal exclusion from standard certificates plus a zone bundle. -/
theorem critical_disk_exclusion_faceDiagonal_from_standard_certificates_and_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_conditional_faceDiagonalReflection_of_zone_consequences
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert) zones i hiota

/-- One face-diagonal Lemma 6' from standard certificates when Zones B/C are supplied in their
angle-consequence form. -/
theorem critical_disk_assembly_faceDiagonal_from_standard_certificates_and_angle_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand)
    (i : Fin 6) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_assembly_conditional_faceDiagonalReflection_of_angle_consequences
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert)
    zone0 zoneA zoneB zoneC zoneD i

/-- Direct one-face-diagonal exclusion from standard certificates and B/C angle consequences. -/
theorem critical_disk_exclusion_faceDiagonal_from_standard_certificates_and_angle_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_conditional_faceDiagonalReflection_of_angle_consequences
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert)
    zone0 zoneA zoneB zoneC zoneD i hiota

/-- All-six face-diagonal Lemma 6' from standard `(SF)` and `(SB-box)` certificates plus a zone
bundle. -/
theorem critical_disk_assembly_faceDiagonalFamily_from_standard_certificates_and_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand) :
    FaceDiagonalLemma6PrimeFamily cand :=
  critical_disk_assembly_conditional_faceDiagonalFamily_of_zone_consequences
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert) zones

/-- All-six localized face-diagonal conclusion from analytic inputs, standard certificates, and a
zone bundle. -/
theorem critical_disk_localized_exclusion_faceDiagonalFamily_from_standard_certificates_and_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand) :
    FaceDiagonalLocalizedExclusionFamily cand :=
  critical_disk_localized_exclusion_conditional_faceDiagonalFamily analytics
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones)
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert)

/-- Direct indexed localized exclusion from standard certificates, a zone bundle, and analytic
inputs. -/
theorem critical_disk_localized_exclusion_faceDiagonal_from_standard_certificates_and_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskLocalizationConclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) ∧
      CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_localized_exclusion_of_faceDiagonalFamily
    (critical_disk_localized_exclusion_faceDiagonalFamily_from_standard_certificates_and_zones
      analytics SFcert SBBoxCert zones)
    i hiota

/-- Direct indexed exclusion from standard certificates, a zone bundle, and the packaged all-six
face-diagonal family. -/
theorem critical_disk_exclusion_faceDiagonalFamily_from_standard_certificates_and_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_of_faceDiagonalFamily
    (critical_disk_assembly_faceDiagonalFamily_from_standard_certificates_and_zones
      SFcert SBBoxCert zones)
    i hiota

/-- All-six face-diagonal Lemma 6' from standard certificates when Zones B/C are supplied in
their angle-consequence form. -/
theorem critical_disk_assembly_faceDiagonalFamily_from_standard_certificates_and_angle_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand) :
    FaceDiagonalLemma6PrimeFamily cand :=
  critical_disk_assembly_conditional_faceDiagonalFamily_of_angle_consequences
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert)
    zone0 zoneA zoneB zoneC zoneD

/-- All-six localized face-diagonal conclusion from analytic inputs and standard certificates when
Zones B/C are supplied in angle-consequence form. -/
theorem
    critical_disk_localized_exclusion_faceDiagonalFamily_from_standard_certificates_and_angle_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (analytics : CriticalDiskAnalyticInputs)
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand) :
    FaceDiagonalLocalizedExclusionFamily cand :=
  critical_disk_localized_exclusion_conditional_faceDiagonalFamily analytics
    (CriticalDiskLemma6PrimeCertificate.ofAngleConsequences
      zone0 zoneA zoneB zoneC zoneD)
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert)

/-- Direct indexed localized exclusion from standard certificates and B/C angle consequences. -/
theorem critical_disk_localized_exclusion_faceDiagonal_from_standard_certificates_and_angle_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (analytics : CriticalDiskAnalyticInputs)
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskLocalizationConclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) ∧
      CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_localized_exclusion_of_faceDiagonalFamily
    (critical_disk_localized_exclusion_faceDiagonalFamily_from_standard_certificates_and_angle_zones
      analytics SFcert SBBoxCert zone0 zoneA zoneB zoneC zoneD)
    i hiota

/-- Direct indexed exclusion from standard certificates, B/C angle consequences, and the packaged
all-six face-diagonal family. -/
theorem critical_disk_exclusion_faceDiagonalFamily_from_standard_certificates_and_angle_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_of_faceDiagonalFamily
    (critical_disk_assembly_faceDiagonalFamily_from_standard_certificates_and_angle_zones
      SFcert SBBoxCert zone0 zoneA zoneB zoneC zoneD)
    i hiota

/-- Transported Lemma 6' from payload-verified standard certificates plus a zone bundle. -/
theorem critical_disk_assembly_iotaInner_from_payloadVerified_and_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLemma6PrimeStatement (cand.iotaInner S) :=
  critical_disk_assembly_conditional_iotaInner_of_zone_consequences
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified) zones S

/-- Direct transported exclusion from payload-verified standard certificates plus a zone bundle. -/
theorem critical_disk_exclusion_iotaInner_from_payloadVerified_and_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand)
    (S : ImproperVertexSymmetry stellatedVertices)
    (hiota : CriticalDiskHypotheses (cand.iotaInner S)) :
    CriticalDiskExclusion (cand.iotaInner S) :=
  critical_disk_exclusion_conditional_iotaInner_of_zone_consequences
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified)
    zones S hiota

/-- Localized transported exclusion from payload-verified certificates plus a zone bundle. -/
theorem critical_disk_localized_exclusion_iotaInner_from_payloadVerified_and_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLocalizedExclusionStatement (cand.iotaInner S) :=
  critical_disk_localized_exclusion_conditional_iotaInner analytics
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones)
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified) S

/-- Transported Lemma 6' from payload-verified standard certificates and B/C angle
consequences. -/
theorem critical_disk_assembly_iotaInner_from_payloadVerified_and_angle_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLemma6PrimeStatement (cand.iotaInner S) :=
  critical_disk_assembly_conditional_iotaInner_of_angle_consequences
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified)
    zone0 zoneA zoneB zoneC zoneD S

/-- Direct transported exclusion from payload-verified standard certificates and B/C angle
consequences. -/
theorem critical_disk_exclusion_iotaInner_from_payloadVerified_and_angle_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand)
    (S : ImproperVertexSymmetry stellatedVertices)
    (hiota : CriticalDiskHypotheses (cand.iotaInner S)) :
    CriticalDiskExclusion (cand.iotaInner S) :=
  critical_disk_exclusion_conditional_iotaInner_of_angle_consequences
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified)
    zone0 zoneA zoneB zoneC zoneD S hiota

/-- Localized transported exclusion from payload-verified certificates and B/C angle
consequences. -/
theorem critical_disk_localized_exclusion_iotaInner_from_payloadVerified_and_angle_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (analytics : CriticalDiskAnalyticInputs)
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLocalizedExclusionStatement (cand.iotaInner S) :=
  critical_disk_localized_exclusion_conditional_iotaInner analytics
    (CriticalDiskLemma6PrimeCertificate.ofAngleConsequences
      zone0 zoneA zoneB zoneC zoneD)
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified) S

/-- One face-diagonal Lemma 6' from payload-verified standard certificates plus a zone bundle. -/
theorem critical_disk_assembly_faceDiagonal_from_payloadVerified_and_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand)
    (i : Fin 6) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_assembly_conditional_faceDiagonalReflection_of_zone_consequences
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified) zones i

/-- Direct one-face-diagonal exclusion from payload-verified standard certificates plus a zone
bundle. -/
theorem critical_disk_exclusion_faceDiagonal_from_payloadVerified_and_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_conditional_faceDiagonalReflection_of_zone_consequences
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified)
    zones i hiota

/-- One face-diagonal Lemma 6' from payload-verified standard certificates and B/C angle
consequences. -/
theorem critical_disk_assembly_faceDiagonal_from_payloadVerified_and_angle_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand)
    (i : Fin 6) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_assembly_conditional_faceDiagonalReflection_of_angle_consequences
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified)
    zone0 zoneA zoneB zoneC zoneD i

/-- Direct one-face-diagonal exclusion from payload-verified standard certificates and B/C angle
consequences. -/
theorem critical_disk_exclusion_faceDiagonal_from_payloadVerified_and_angle_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_conditional_faceDiagonalReflection_of_angle_consequences
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified)
    zone0 zoneA zoneB zoneC zoneD i hiota

/-- All-six face-diagonal Lemma 6' from payload-verified standard certificates plus a zone
bundle. -/
theorem critical_disk_assembly_faceDiagonalFamily_from_payloadVerified_and_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand) :
    FaceDiagonalLemma6PrimeFamily cand :=
  critical_disk_assembly_conditional_faceDiagonalFamily_of_zone_consequences
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified) zones

/-- All-six localized face-diagonal conclusion from analytic inputs, payload-verified
certificates, and a zone bundle. -/
theorem critical_disk_localized_exclusion_faceDiagonalFamily_from_payloadVerified_and_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand) :
    FaceDiagonalLocalizedExclusionFamily cand :=
  critical_disk_localized_exclusion_conditional_faceDiagonalFamily analytics
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones)
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified)

/-- Direct indexed localized exclusion from payload-verified certificates, a zone bundle, and
analytic inputs. -/
theorem critical_disk_localized_exclusion_faceDiagonal_from_payloadVerified_and_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskLocalizationConclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) ∧
      CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_localized_exclusion_of_faceDiagonalFamily
    (critical_disk_localized_exclusion_faceDiagonalFamily_from_payloadVerified_and_zones
      analytics SFverified SBverified zones)
    i hiota

/-- Direct indexed exclusion from payload-verified standard certificates, a zone bundle, and the
packaged all-six face-diagonal family. -/
theorem critical_disk_exclusion_faceDiagonalFamily_from_payloadVerified_and_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_of_faceDiagonalFamily
    (critical_disk_assembly_faceDiagonalFamily_from_payloadVerified_and_zones
      SFverified SBverified zones)
    i hiota

/-- All-six face-diagonal Lemma 6' from payload-verified standard certificates and B/C angle
consequences. -/
theorem critical_disk_assembly_faceDiagonalFamily_from_payloadVerified_and_angle_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand) :
    FaceDiagonalLemma6PrimeFamily cand :=
  critical_disk_assembly_conditional_faceDiagonalFamily_of_angle_consequences
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified)
    zone0 zoneA zoneB zoneC zoneD

/-- All-six localized face-diagonal conclusion from analytic inputs and payload-verified
certificates when Zones B/C are supplied in angle-consequence form. -/
theorem
    critical_disk_localized_exclusion_faceDiagonalFamily_from_payloadVerified_and_angle_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (analytics : CriticalDiskAnalyticInputs)
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand) :
    FaceDiagonalLocalizedExclusionFamily cand :=
  critical_disk_localized_exclusion_conditional_faceDiagonalFamily analytics
    (CriticalDiskLemma6PrimeCertificate.ofAngleConsequences
      zone0 zoneA zoneB zoneC zoneD)
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified)

/-- Direct indexed localized exclusion from payload-verified certificates and B/C angle
consequences. -/
theorem critical_disk_localized_exclusion_faceDiagonal_from_payloadVerified_and_angle_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (analytics : CriticalDiskAnalyticInputs)
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskLocalizationConclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) ∧
      CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_localized_exclusion_of_faceDiagonalFamily
    (critical_disk_localized_exclusion_faceDiagonalFamily_from_payloadVerified_and_angle_zones
      analytics SFverified SBverified zone0 zoneA zoneB zoneC zoneD)
    i hiota

/-- Direct indexed exclusion from payload-verified standard certificates, B/C angle consequences,
and the packaged all-six face-diagonal family. -/
theorem critical_disk_exclusion_faceDiagonalFamily_from_payloadVerified_and_angle_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_of_faceDiagonalFamily
    (critical_disk_assembly_faceDiagonalFamily_from_payloadVerified_and_angle_zones
      SFverified SBverified zone0 zoneA zoneB zoneC zoneD)
    i hiota

end RupertStellatedTetrahedron
