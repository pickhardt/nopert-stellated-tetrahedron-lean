import RupertStellatedTetrahedron.CriticalDisk.AnalyticInterfaces
import RupertStellatedTetrahedron.CriticalDisk.CertifiedInputs
import RupertStellatedTetrahedron.CriticalDisk.DepthPerturbation
import RupertStellatedTetrahedron.CriticalDisk.ZoneConsequences
import RupertStellatedTetrahedron.Local.SupportOffset
import RupertStellatedTetrahedron.Stellated.UStarDepth

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

open DepthCylinderTheorem

/-!
## Critical-disk assembly

This is the top-level Lean boundary for the current two-certificate critical-disk proof.  The
external inputs are `(SF)` and `(SB-box)`; once they are certified, the remaining Lean-facing
payload is a concrete set of zone-local consequences for the target candidate.
-/

/-- Concrete Lean-facing certificate for conditional Lemma 6' for one candidate. -/
structure CriticalDiskLemma6PrimeCertificate
    (inputs : CriticalDiskCertifiedInputs) (cand : CriticalDiskCandidate) where
  zoneConsequences :
    inputs.allCertified → CriticalDiskZoneConsequences cand

def CriticalDiskLemma6PrimeCertificate.zoneBundle
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (cert : CriticalDiskLemma6PrimeCertificate inputs cand)
    (hinputs : inputs.allCertified) :
    CriticalDiskZoneConsequences cand :=
  cert.zoneConsequences hinputs

theorem CriticalDiskLemma6PrimeCertificate.lemma6prime
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (cert : CriticalDiskLemma6PrimeCertificate inputs cand)
    (hinputs : inputs.allCertified) :
    CriticalDiskLemma6PrimeStatement cand :=
  (cert.zoneBundle hinputs).lemma6prime

theorem CriticalDiskLemma6PrimeCertificate.exclusion
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (cert : CriticalDiskLemma6PrimeCertificate inputs cand)
    (hinputs : inputs.allCertified)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  (cert.zoneBundle hinputs).excludes hcand

/-- Promote an already-certified zone consequence bundle into the Lean-facing Lemma 6'
certificate interface. -/
def CriticalDiskLemma6PrimeCertificate.ofZoneConsequences
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    (zones : CriticalDiskZoneConsequences cand) :
    CriticalDiskLemma6PrimeCertificate inputs cand where
  zoneConsequences _hinputs := zones

/-- Build the Lemma 6' certificate directly from the common zone interface in which Zones B and C
are supplied by their angle-bound consequences. -/
def CriticalDiskLemma6PrimeCertificate.ofAngleConsequences
    {inputs : CriticalDiskCertifiedInputs} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand) :
    CriticalDiskLemma6PrimeCertificate inputs cand :=
  .ofZoneConsequences
    (CriticalDiskZoneConsequences.ofAngleConsequences zone0 zoneA zoneB zoneC zoneD)

/-- Conditional assembly of Lemma 6' from `(SF)`, `(SB-box)`, and zone-local consequences. -/
theorem critical_disk_assembly_conditional {inputs : CriticalDiskCertifiedInputs}
    {cand : CriticalDiskCandidate}
    (cert : CriticalDiskLemma6PrimeCertificate inputs cand)
    (hinputs : inputs.allCertified) :
    CriticalDiskLemma6PrimeStatement cand := by
  exact cert.lemma6prime hinputs

/-- Direct exclusion form for callers that already have the analytic side conditions. -/
theorem critical_disk_exclusion_conditional {inputs : CriticalDiskCertifiedInputs}
    {cand : CriticalDiskCandidate}
    (cert : CriticalDiskLemma6PrimeCertificate inputs cand)
    (hinputs : inputs.allCertified)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand := by
  exact cert.exclusion hinputs hcand

/-- Combined local theorem: analytic localization plus the conditional critical-disk exclusion. -/
theorem critical_disk_localized_exclusion_conditional {inputs : CriticalDiskCertifiedInputs}
    {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (cert : CriticalDiskLemma6PrimeCertificate inputs cand)
    (hinputs : inputs.allCertified) :
    CriticalDiskLocalizedExclusionStatement cand :=
  criticalDisk_localized_exclusion_from_analytic_inputs analytics
    (critical_disk_assembly_conditional cert hinputs)

/-- Conditional Lemma 6' directly from zone consequences when Zones B/C are supplied in their
angle-bound form. -/
theorem critical_disk_assembly_conditional_of_angle_consequences
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
    CriticalDiskLemma6PrimeStatement cand :=
  critical_disk_assembly_conditional
    (CriticalDiskLemma6PrimeCertificate.ofAngleConsequences
      zone0 zoneA zoneB zoneC zoneD)
    hinputs

/-- Direct exclusion form of the angle-consequence assembly. -/
theorem critical_disk_exclusion_conditional_of_angle_consequences
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
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  critical_disk_exclusion_conditional
    (CriticalDiskLemma6PrimeCertificate.ofAngleConsequences
      zone0 zoneA zoneB zoneC zoneD)
    hinputs hcand

/-! ### Standard certificate entry points -/

/-- Conditional Lemma 6' from standard `(SF)` and `(SB-box)` certificates plus a zone bundle. -/
theorem critical_disk_assembly_from_standard_certificates_and_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand) :
    CriticalDiskLemma6PrimeStatement cand :=
  critical_disk_assembly_conditional
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones)
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert)

/-- Direct exclusion from standard `(SF)` and `(SB-box)` certificates plus a zone bundle. -/
theorem critical_disk_exclusion_from_standard_certificates_and_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  critical_disk_exclusion_conditional
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones)
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert)
    hcand

/-- Localized exclusion from analytic inputs, standard `(SF)`/`(SB-box)` certificates, and zones. -/
theorem critical_disk_localized_exclusion_from_standard_certificates_and_zones
    {rhoF rhoB : ℝ} {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand) :
    CriticalDiskLocalizedExclusionStatement cand :=
  critical_disk_localized_exclusion_conditional analytics
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones)
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert)

/-- Conditional Lemma 6' from standard certificates when Zones B/C are supplied in their
angle-consequence form. -/
theorem critical_disk_assembly_from_standard_certificates_and_angle_zones
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
    CriticalDiskLemma6PrimeStatement cand :=
  critical_disk_assembly_conditional_of_angle_consequences
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert)
    zone0 zoneA zoneB zoneC zoneD

/-- Direct exclusion from standard certificates when Zones B/C are supplied in their
angle-consequence form. -/
theorem critical_disk_exclusion_from_standard_certificates_and_angle_zones
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
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  critical_disk_exclusion_conditional_of_angle_consequences
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert)
    zone0 zoneA zoneB zoneC zoneD hcand

/-- Localized exclusion from analytic inputs and standard certificates when Zones B/C are supplied
in angle-consequence form. -/
theorem critical_disk_localized_exclusion_from_standard_certificates_and_angle_zones
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
    CriticalDiskLocalizedExclusionStatement cand :=
  critical_disk_localized_exclusion_conditional analytics
    (CriticalDiskLemma6PrimeCertificate.ofAngleConsequences
      zone0 zoneA zoneB zoneC zoneD)
    (standardCriticalDiskInputs_allCertified rhoF rhoB SFcert SBBoxCert)

/-- Conditional Lemma 6' from payload-verified standard certificates plus a zone bundle. -/
theorem critical_disk_assembly_from_payloadVerified_and_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand) :
    CriticalDiskLemma6PrimeStatement cand :=
  critical_disk_assembly_conditional
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones)
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified)

/-- Direct exclusion from payload-verified standard certificates plus a zone bundle. -/
theorem critical_disk_exclusion_from_payloadVerified_and_zones
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    {cand : CriticalDiskCandidate}
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT)
    (zones : CriticalDiskZoneConsequences cand)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  critical_disk_exclusion_conditional
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones)
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified)
    hcand

/-- Localized exclusion from analytic inputs, payload-verified certificates, and zones. -/
theorem critical_disk_localized_exclusion_from_payloadVerified_and_zones
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
    CriticalDiskLocalizedExclusionStatement cand :=
  critical_disk_localized_exclusion_conditional analytics
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones)
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified)

/-- Conditional Lemma 6' from payload-verified standard certificates and B/C angle
consequences. -/
theorem critical_disk_assembly_from_payloadVerified_and_angle_zones
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
    CriticalDiskLemma6PrimeStatement cand :=
  critical_disk_assembly_conditional_of_angle_consequences
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified)
    zone0 zoneA zoneB zoneC zoneD

/-- Direct exclusion from payload-verified standard certificates and B/C angle consequences. -/
theorem critical_disk_exclusion_from_payloadVerified_and_angle_zones
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
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  critical_disk_exclusion_conditional_of_angle_consequences
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified)
    zone0 zoneA zoneB zoneC zoneD hcand

/-- Localized exclusion from analytic inputs and payload-verified certificates when Zones B/C are
supplied in angle-consequence form. -/
theorem critical_disk_localized_exclusion_from_payloadVerified_and_angle_zones
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
    CriticalDiskLocalizedExclusionStatement cand :=
  critical_disk_localized_exclusion_conditional analytics
    (CriticalDiskLemma6PrimeCertificate.ofAngleConsequences
      zone0 zoneA zoneB zoneC zoneD)
    (standardCriticalDiskInputs_of_payloadVerified_allCertified SFverified SBverified)

end RupertStellatedTetrahedron
