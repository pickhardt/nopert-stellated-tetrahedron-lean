import RupertStellatedTetrahedron.CriticalDisk.Assembly
import RupertStellatedTetrahedron.CriticalDisk.Generated.SBBoxCertifiedInput
import RupertStellatedTetrahedron.CriticalDisk.Generated.SFCertifiedInput
import RupertStellatedTetrahedron.CriticalDisk.SymmetryAssembly

/-!
Lean boundary from the generated `(SF)` and `(SB-box)` artifacts to the two certified inputs used
by the critical-disk assembly.

This module deliberately keeps the remaining soundness assumptions explicit.  The current generated
files replay exact rows and tilings, but `(SF)` still needs a standard semantic sweep certificate
and `(SB-box)` still needs pointwise box-inclusion soundness.
-/

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

namespace GeneratedCriticalDiskInputs

open GeneratedSFCertifiedInput GeneratedSBBoxCertifiedInput

/-- The remaining generated-input soundness needed to instantiate the standard critical-disk
input bundle. -/
structure StandardGeneratedSoundness (rhoF : ℝ) where
  sf : GeneratedSFCertifiedInput.StandardSweepSoundness rhoF
  sbBox : GeneratedSBBoxCertifiedInput.StandardReplaySoundness

/-- Constructor exposing the two semantic obligations that remain after generated replay:
standard `(SF)` and pointwise `(SB-box)`. -/
def standardGeneratedSoundness_of_certificates {rhoF : ℝ}
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness) :
    StandardGeneratedSoundness rhoF where
  sf := GeneratedSFCertifiedInput.standardSweepSoundness_of_certificate sfCert
  sbBox := GeneratedSBBoxCertifiedInput.standardReplaySoundness_of_pointwise sbPointwise

def StandardGeneratedSoundness.toCriticalDiskInputs {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    CriticalDiskCertifiedInputs where
  sf := soundness.sf.toSFInput
  sbBox := standardSBBoxInput_of_replaySoundness soundness.sbBox

theorem StandardGeneratedSoundness.toCriticalDiskInputs_sf {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    soundness.toCriticalDiskInputs.sf = soundness.sf.toSFInput :=
  rfl

theorem StandardGeneratedSoundness.toCriticalDiskInputs_sbBox {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    soundness.toCriticalDiskInputs.sbBox =
      standardSBBoxInput_of_replaySoundness soundness.sbBox :=
  rfl

theorem StandardGeneratedSoundness.toCriticalDiskInputs_sf_rhoF {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    soundness.toCriticalDiskInputs.sf.rhoF = rhoF :=
  rfl

theorem StandardGeneratedSoundness.toCriticalDiskInputs_sf_rb {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    soundness.toCriticalDiskInputs.sf.rb = criticalDiskRb :=
  rfl

theorem StandardGeneratedSoundness.toCriticalDiskInputs_sf_nu {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    soundness.toCriticalDiskInputs.sf.nu = criticalDiskNu :=
  rfl

theorem StandardGeneratedSoundness.toCriticalDiskInputs_sf_psiMin {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    soundness.toCriticalDiskInputs.sf.psiMin = criticalDiskPsiMin :=
  rfl

theorem StandardGeneratedSoundness.toCriticalDiskInputs_sf_shellSlope {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    soundness.toCriticalDiskInputs.sf.shellSlope = criticalDiskShellSlope :=
  rfl

theorem StandardGeneratedSoundness.toCriticalDiskInputs_sbBox_rhoB {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    soundness.toCriticalDiskInputs.sbBox.rhoB = criticalDiskRhoCap :=
  rfl

theorem StandardGeneratedSoundness.toCriticalDiskInputs_sbBox_bPi {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    soundness.toCriticalDiskInputs.sbBox.bPi = criticalDiskBoxBPi :=
  rfl

theorem StandardGeneratedSoundness.toCriticalDiskInputs_sbBox_bGamma {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    soundness.toCriticalDiskInputs.sbBox.bGamma = criticalDiskBoxBGamma :=
  rfl

theorem StandardGeneratedSoundness.toCriticalDiskInputs_sbBox_bT {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    soundness.toCriticalDiskInputs.sbBox.bT = criticalDiskBoxBT :=
  rfl

theorem StandardGeneratedSoundness.toCriticalDiskInputs_allCertified {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    soundness.toCriticalDiskInputs.allCertified := by
  exact
    ⟨soundness.sf.toSFInput_certified,
      standardSBBoxInput_of_replaySoundness_certified soundness.sbBox⟩

theorem StandardGeneratedSoundness.toCriticalDiskInputs_sf_certified {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    soundness.toCriticalDiskInputs.sf.certified :=
  soundness.sf.toSFInput_certified

theorem StandardGeneratedSoundness.toCriticalDiskInputs_sbBox_certified {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    soundness.toCriticalDiskInputs.sbBox.certified :=
  standardSBBoxInput_of_replaySoundness_certified soundness.sbBox

theorem StandardGeneratedSoundness.sbBoxReplayAssemblyValid {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    SBBoxReplayAssembly
      GeneratedSBBoxTailWitness.manifest GeneratedSBBoxBulkWitness.manifest
      GeneratedSBBoxAssemblyReport.report
      GeneratedSBBoxAssemblyReport.tailDomain
      GeneratedSBBoxAssemblyReport.bulkDeltaDomain
      GeneratedSBBoxAssemblyReport.bulkPhiDomain
      GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.sbBox.replayAssembly_valid

theorem StandardGeneratedSoundness.sfCertifiedRowsValid {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    GeneratedSFWitness.manifest.CertifiedRowsValid
      GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  soundness.sf.certifiedRowsValid

theorem StandardGeneratedSoundness.sfCertifiedRowValid {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF)
    {row : SFCertifiedSweepRow}
    (hrow : row ∈ GeneratedSFWitness.manifest.certified) :
    row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  soundness.sf.certifiedRowValid hrow

theorem StandardGeneratedSoundness.sbBoxTailRowsValid {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    GeneratedSBBoxTailWitness.manifest.RowsValid :=
  soundness.sbBox.tailRowsValid

theorem StandardGeneratedSoundness.sbBoxBulkRowsValid {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    GeneratedSBBoxBulkWitness.manifest.RowsValid
      GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.sbBox.bulkRowsValid

theorem StandardGeneratedSoundness.sbBoxTailRowValid {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF)
    {row : SBBoxTailRow}
    (hrow : row ∈ GeneratedSBBoxTailWitness.manifest.rows) :
    row.Valid :=
  soundness.sbBox.tailRowValid hrow

theorem StandardGeneratedSoundness.sbBoxBulkRowValid {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF)
    {row : SBBoxBulkRow}
    (hrow : row ∈ GeneratedSBBoxBulkWitness.manifest.rows) :
    row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.sbBox.bulkRowValid hrow

theorem StandardGeneratedSoundness.sbBoxTailExistsValidRow {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF)
    (chart : SBBoxTailChart) {r : ℝ}
    (hr : GeneratedSBBoxAssemblyReport.tailDomain.contains r) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains r ∧ row.Valid :=
  soundness.sbBox.tailExistsValidRow chart hr

theorem StandardGeneratedSoundness.sbBoxBulkExistsValidRow {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF)
    {delta phi : ℝ}
    (hdelta : GeneratedSBBoxAssemblyReport.bulkDeltaDomain.contains delta)
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains delta ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.sbBox.bulkExistsValidRow hdelta hphi

theorem StandardGeneratedSoundness.sbBoxTailExistsValidRowAtZero {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF)
    (chart : SBBoxTailChart) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains (0 : ℝ) ∧ row.Valid :=
  soundness.sbBox.tailExistsValidRowAtZero chart

theorem StandardGeneratedSoundness.sbBoxTailExistsValidRowAtOne {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF)
    (chart : SBBoxTailChart) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains (1 : ℝ) ∧ row.Valid :=
  soundness.sbBox.tailExistsValidRowAtOne chart

theorem StandardGeneratedSoundness.sbBoxBulkExistsValidRowAtTailCut {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF)
    {phi : ℝ}
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskTailCut ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.sbBox.bulkExistsValidRowAtTailCut hphi

theorem StandardGeneratedSoundness.sbBoxBulkExistsValidRowAtRhoCap {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF)
    {phi : ℝ}
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskRhoCap ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.sbBox.bulkExistsValidRowAtRhoCap hphi

theorem StandardGeneratedSoundness.sbBoxBulkExistsValidRowAtTailCutZeroPhi {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskTailCut ∧ row.phi.contains (0 : ℝ) ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.sbBox.bulkExistsValidRowAtTailCutZeroPhi

theorem StandardGeneratedSoundness.sbBoxBulkExistsValidRowAtRhoCapZeroPhi {rhoF : ℝ}
    (soundness : StandardGeneratedSoundness rhoF) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskRhoCap ∧ row.phi.contains (0 : ℝ) ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.sbBox.bulkExistsValidRowAtRhoCapZeroPhi

theorem StandardGeneratedSoundness.delta_le_rhoCap
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (soundness : StandardGeneratedSoundness rhoF)
    (hcand : CriticalDiskHypotheses cand) :
    cand.delta ≤ criticalDiskRhoCap :=
  soundness.toCriticalDiskInputs.delta_le_rhoCap hcand

theorem StandardGeneratedSoundness.delta_le_sf_rhoF
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (soundness : StandardGeneratedSoundness rhoF)
    (hcand : CriticalDiskHypotheses cand) :
    cand.delta ≤ soundness.toCriticalDiskInputs.sf.rhoF :=
  soundness.toCriticalDiskInputs.delta_le_sf_rhoF hcand

theorem StandardGeneratedSoundness.delta_le_sbBox_rhoB
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (soundness : StandardGeneratedSoundness rhoF)
    (hcand : CriticalDiskHypotheses cand) :
    cand.delta ≤ soundness.toCriticalDiskInputs.sbBox.rhoB :=
  soundness.toCriticalDiskInputs.delta_le_sbBox_rhoB hcand

def StandardGeneratedSoundness.sbBoxPointCertificate
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (soundness : StandardGeneratedSoundness rhoF)
    (hcand : CriticalDiskHypotheses cand) :
    SBBoxPointCertificate cand.R₂ cand.delta
      soundness.toCriticalDiskInputs.sbBox.bPi
      soundness.toCriticalDiskInputs.sbBox.bGamma
      soundness.toCriticalDiskInputs.sbBox.bT :=
  soundness.toCriticalDiskInputs.sbBoxPointCertificate hcand

def StandardGeneratedSoundness.sbBoxInclusion
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (soundness : StandardGeneratedSoundness rhoF)
    (hcand : CriticalDiskHypotheses cand) :
    DepthCylinderTheorem.BoxInclusionCertificate
      (soundness.sbBoxPointCertificate hcand).cert :=
  soundness.toCriticalDiskInputs.sbBoxInclusion hcand

theorem StandardGeneratedSoundness.sfCovers
    {rhoF : ℝ} (soundness : StandardGeneratedSoundness rhoF)
    {φ s : ℝ}
    (hφlo : -Real.pi ≤ φ) (hφhi : φ ≤ Real.pi)
    (hslo : 0 ≤ s) (hshi : s ≤ 1) :
    ∃ c : soundness.toCriticalDiskInputs.sf.certificate.chart,
      soundness.toCriticalDiskInputs.sf.certificate.inChart c φ s :=
  soundness.sf.covers hφlo hφhi hslo hshi

theorem StandardGeneratedSoundness.sfChartClassified
    {rhoF : ℝ} (soundness : StandardGeneratedSoundness rhoF)
    (c : soundness.toCriticalDiskInputs.sf.certificate.chart) :
    soundness.toCriticalDiskInputs.sf.certificate.isShell c ∨
      soundness.toCriticalDiskInputs.sf.certificate.isBulk c :=
  soundness.sf.chartClassified c

theorem StandardGeneratedSoundness.sfCornerDistLower_nonneg
    {rhoF : ℝ} (soundness : StandardGeneratedSoundness rhoF)
    (c : soundness.toCriticalDiskInputs.sf.certificate.chart) :
    0 ≤ soundness.toCriticalDiskInputs.sf.certificate.cornerDistLower c :=
  soundness.sf.cornerDistLower_nonneg c

theorem StandardGeneratedSoundness.sfShellBound
    {rhoF : ℝ} (soundness : StandardGeneratedSoundness rhoF)
    (c : soundness.toCriticalDiskInputs.sf.certificate.chart)
    (hc : soundness.toCriticalDiskInputs.sf.certificate.isShell c) :
    soundness.toCriticalDiskInputs.sf.shellSlope *
        soundness.toCriticalDiskInputs.sf.certificate.cornerDistLower c ≤
      soundness.toCriticalDiskInputs.sf.certificate.psiLower c :=
  soundness.sf.shellBound c hc

theorem StandardGeneratedSoundness.sfBulkBound
    {rhoF : ℝ} (soundness : StandardGeneratedSoundness rhoF)
    (c : soundness.toCriticalDiskInputs.sf.certificate.chart)
    (hc : soundness.toCriticalDiskInputs.sf.certificate.isBulk c) :
    soundness.toCriticalDiskInputs.sf.psiMin ≤
      soundness.toCriticalDiskInputs.sf.certificate.psiLower c :=
  soundness.sf.bulkBound c hc

/-- Conditional Lemma 6' instantiated with the generated-input boundary. -/
theorem critical_disk_assembly_from_generated_soundness
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (soundness : StandardGeneratedSoundness rhoF)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand) :
    CriticalDiskLemma6PrimeStatement cand :=
  critical_disk_assembly_conditional cert soundness.toCriticalDiskInputs_allCertified

/-- Direct exclusion instantiated with the generated-input boundary. -/
theorem critical_disk_exclusion_from_generated_soundness
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (soundness : StandardGeneratedSoundness rhoF)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  critical_disk_exclusion_conditional cert soundness.toCriticalDiskInputs_allCertified hcand

/-- Localized exclusion instantiated with the generated-input boundary. -/
theorem critical_disk_localized_exclusion_from_generated_soundness
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (soundness : StandardGeneratedSoundness rhoF)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand) :
    CriticalDiskLocalizedExclusionStatement cand :=
  critical_disk_localized_exclusion_conditional analytics cert
    soundness.toCriticalDiskInputs_allCertified

/-- Conditional Lemma 6' after transporting the inner marginal sheet by any vertex symmetry. -/
theorem critical_disk_assembly_iotaInner_from_generated_soundness
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (soundness : StandardGeneratedSoundness rhoF)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLemma6PrimeStatement (cand.iotaInner S) :=
  critical_disk_assembly_conditional_iotaInner cert
    soundness.toCriticalDiskInputs_allCertified S

/-- Direct transported exclusion instantiated with the generated-input boundary. -/
theorem critical_disk_exclusion_iotaInner_from_generated_soundness
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (soundness : StandardGeneratedSoundness rhoF)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand)
    (S : ImproperVertexSymmetry stellatedVertices)
    (hiota : CriticalDiskHypotheses (cand.iotaInner S)) :
    CriticalDiskExclusion (cand.iotaInner S) :=
  critical_disk_assembly_conditional_iotaInner cert
    soundness.toCriticalDiskInputs_allCertified S hiota

/-- Localized transported exclusion instantiated with the generated-input boundary. -/
theorem critical_disk_localized_exclusion_iotaInner_from_generated_soundness
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (soundness : StandardGeneratedSoundness rhoF)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLocalizedExclusionStatement (cand.iotaInner S) :=
  critical_disk_localized_exclusion_conditional_iotaInner analytics cert
    soundness.toCriticalDiskInputs_allCertified S

/-- Conditional Lemma 6' for all six face-diagonal reflected marginal sheets. -/
theorem critical_disk_assembly_faceDiagonal_from_generated_soundness
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (soundness : StandardGeneratedSoundness rhoF)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand)
    (i : Fin 6) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_assembly_conditional_faceDiagonalReflection cert
    soundness.toCriticalDiskInputs_allCertified i

/-- Direct one-face-diagonal exclusion instantiated with the generated-input boundary. -/
theorem critical_disk_exclusion_faceDiagonal_from_generated_soundness
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (soundness : StandardGeneratedSoundness rhoF)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_assembly_conditional_faceDiagonalReflection cert
    soundness.toCriticalDiskInputs_allCertified i hiota

/-- Packaged all-six version of the generated-input conditional Lemma 6' boundary. -/
theorem critical_disk_assembly_faceDiagonalFamily_from_generated_soundness
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (soundness : StandardGeneratedSoundness rhoF)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand) :
    FaceDiagonalLemma6PrimeFamily cand :=
  critical_disk_assembly_conditional_faceDiagonalFamily cert
    soundness.toCriticalDiskInputs_allCertified

/-- All-six localized face-diagonal conclusion instantiated with the generated-input boundary. -/
theorem critical_disk_localized_exclusion_faceDiagonalFamily_from_generated_soundness
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (soundness : StandardGeneratedSoundness rhoF)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand) :
    FaceDiagonalLocalizedExclusionFamily cand :=
  critical_disk_localized_exclusion_conditional_faceDiagonalFamily analytics cert
    soundness.toCriticalDiskInputs_allCertified

/-- Apply the generated-input localized all-six family at one face-diagonal reflected sheet. -/
theorem critical_disk_localized_exclusion_faceDiagonal_from_generated_soundness
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (soundness : StandardGeneratedSoundness rhoF)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskLocalizationConclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) ∧
      CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_localized_exclusion_of_faceDiagonalFamily
    (critical_disk_localized_exclusion_faceDiagonalFamily_from_generated_soundness
      analytics soundness cert)
    i hiota

/-- Apply the generated-input all-six family at one face-diagonal reflected sheet. -/
theorem critical_disk_exclusion_faceDiagonalFamily_from_generated_soundness
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (soundness : StandardGeneratedSoundness rhoF)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_of_faceDiagonalFamily
    (critical_disk_assembly_faceDiagonalFamily_from_generated_soundness soundness cert)
    i hiota

/-! ### Packaged local certificate boundary

The following bundle is the Lean artifact that remains once the generated `(SF)` and `(SB-box)`
semantic obligations and the zone consequences have all been supplied.  It keeps the inputs
explicit while avoiding repeated theorem arguments in downstream local/global assembly code.
-/

structure StandardGeneratedLocalCertificate
    (rhoF : ℝ) (cand : CriticalDiskCandidate) where
  soundness : StandardGeneratedSoundness rhoF
  zones : CriticalDiskZoneConsequences cand

def standardGeneratedLocalCertificate_of_certificates_and_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand) :
    StandardGeneratedLocalCertificate rhoF cand where
  soundness := standardGeneratedSoundness_of_certificates sfCert sbPointwise
  zones := zones

def standardGeneratedLocalCertificate_of_certificates_and_angle_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand) :
    StandardGeneratedLocalCertificate rhoF cand :=
  standardGeneratedLocalCertificate_of_certificates_and_zones sfCert sbPointwise
    (CriticalDiskZoneConsequences.ofAngleConsequences zone0 zoneA zoneB zoneC zoneD)

def StandardGeneratedLocalCertificate.lemma6PrimeCertificate
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand) :
    CriticalDiskLemma6PrimeCertificate cert.soundness.toCriticalDiskInputs cand :=
  CriticalDiskLemma6PrimeCertificate.ofZoneConsequences cert.zones

def StandardGeneratedLocalCertificate.toCriticalDiskInputs
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand) :
    CriticalDiskCertifiedInputs :=
  cert.soundness.toCriticalDiskInputs

theorem StandardGeneratedLocalCertificate.inputs_allCertified
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand) :
    cert.toCriticalDiskInputs.allCertified :=
  cert.soundness.toCriticalDiskInputs_allCertified

theorem StandardGeneratedLocalCertificate.sfCertifiedRowsValid
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand) :
    GeneratedSFWitness.manifest.CertifiedRowsValid
      GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  cert.soundness.sfCertifiedRowsValid

theorem StandardGeneratedLocalCertificate.sfCertifiedRowValid
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand)
    {row : SFCertifiedSweepRow}
    (hrow : row ∈ GeneratedSFWitness.manifest.certified) :
    row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  cert.soundness.sfCertifiedRowValid hrow

theorem StandardGeneratedLocalCertificate.sbBoxReplayAssemblyValid
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand) :
    SBBoxReplayAssembly
      GeneratedSBBoxTailWitness.manifest GeneratedSBBoxBulkWitness.manifest
      GeneratedSBBoxAssemblyReport.report
      GeneratedSBBoxAssemblyReport.tailDomain
      GeneratedSBBoxAssemblyReport.bulkDeltaDomain
      GeneratedSBBoxAssemblyReport.bulkPhiDomain
      GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxReplayAssemblyValid

theorem StandardGeneratedLocalCertificate.sbBoxTailRowValid
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand)
    {row : SBBoxTailRow}
    (hrow : row ∈ GeneratedSBBoxTailWitness.manifest.rows) :
    row.Valid :=
  cert.soundness.sbBoxTailRowValid hrow

theorem StandardGeneratedLocalCertificate.sbBoxBulkRowValid
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand)
    {row : SBBoxBulkRow}
    (hrow : row ∈ GeneratedSBBoxBulkWitness.manifest.rows) :
    row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxBulkRowValid hrow

theorem StandardGeneratedLocalCertificate.sbBoxTailExistsValidRow
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand)
    (chart : SBBoxTailChart) {r : ℝ}
    (hr : GeneratedSBBoxAssemblyReport.tailDomain.contains r) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains r ∧ row.Valid :=
  cert.soundness.sbBoxTailExistsValidRow chart hr

theorem StandardGeneratedLocalCertificate.sbBoxBulkExistsValidRow
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand)
    {delta phi : ℝ}
    (hdelta : GeneratedSBBoxAssemblyReport.bulkDeltaDomain.contains delta)
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains delta ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxBulkExistsValidRow hdelta hphi

def StandardGeneratedLocalCertificate.sbBoxPointCertificate
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand)
    (hcand : CriticalDiskHypotheses cand) :
    SBBoxPointCertificate cand.R₂ cand.delta
      cert.toCriticalDiskInputs.sbBox.bPi
      cert.toCriticalDiskInputs.sbBox.bGamma
      cert.toCriticalDiskInputs.sbBox.bT :=
  cert.soundness.sbBoxPointCertificate hcand

def StandardGeneratedLocalCertificate.sbBoxInclusion
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand)
    (hcand : CriticalDiskHypotheses cand) :
    DepthCylinderTheorem.BoxInclusionCertificate
      (cert.sbBoxPointCertificate hcand).cert :=
  cert.soundness.sbBoxInclusion hcand

theorem StandardGeneratedLocalCertificate.sfCovers
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand)
    {φ s : ℝ}
    (hφlo : -Real.pi ≤ φ) (hφhi : φ ≤ Real.pi)
    (hslo : 0 ≤ s) (hshi : s ≤ 1) :
    ∃ c : cert.toCriticalDiskInputs.sf.certificate.chart,
      cert.toCriticalDiskInputs.sf.certificate.inChart c φ s :=
  cert.soundness.sfCovers hφlo hφhi hslo hshi

theorem StandardGeneratedLocalCertificate.lemma6prime
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand) :
    CriticalDiskLemma6PrimeStatement cand :=
  critical_disk_assembly_from_generated_soundness
    cert.soundness cert.lemma6PrimeCertificate

theorem StandardGeneratedLocalCertificate.exclusion
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  cert.lemma6prime hcand

theorem StandardGeneratedLocalCertificate.localizedExclusion
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand)
    (analytics : CriticalDiskAnalyticInputs) :
    CriticalDiskLocalizedExclusionStatement cand :=
  critical_disk_localized_exclusion_from_generated_soundness analytics
    cert.soundness cert.lemma6PrimeCertificate

theorem StandardGeneratedLocalCertificate.iotaInnerLemma6Prime
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLemma6PrimeStatement (cand.iotaInner S) :=
  critical_disk_assembly_iotaInner_from_generated_soundness
    cert.soundness cert.lemma6PrimeCertificate S

theorem StandardGeneratedLocalCertificate.iotaInnerExclusion
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand)
    (S : ImproperVertexSymmetry stellatedVertices)
    (hiota : CriticalDiskHypotheses (cand.iotaInner S)) :
    CriticalDiskExclusion (cand.iotaInner S) :=
  cert.iotaInnerLemma6Prime S hiota

theorem StandardGeneratedLocalCertificate.iotaInnerLocalizedExclusion
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand)
    (analytics : CriticalDiskAnalyticInputs)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLocalizedExclusionStatement (cand.iotaInner S) :=
  critical_disk_localized_exclusion_iotaInner_from_generated_soundness analytics
    cert.soundness cert.lemma6PrimeCertificate S

theorem StandardGeneratedLocalCertificate.faceDiagonalLemma6Prime
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand)
    (i : Fin 6) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_assembly_faceDiagonal_from_generated_soundness
    cert.soundness cert.lemma6PrimeCertificate i

theorem StandardGeneratedLocalCertificate.faceDiagonalExclusion
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  cert.faceDiagonalLemma6Prime i hiota

theorem StandardGeneratedLocalCertificate.faceDiagonalFamily
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand) :
    FaceDiagonalLemma6PrimeFamily cand :=
  critical_disk_assembly_faceDiagonalFamily_from_generated_soundness
    cert.soundness cert.lemma6PrimeCertificate

theorem StandardGeneratedLocalCertificate.faceDiagonalLocalizedFamily
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand)
    (analytics : CriticalDiskAnalyticInputs) :
    FaceDiagonalLocalizedExclusionFamily cand :=
  critical_disk_localized_exclusion_faceDiagonalFamily_from_generated_soundness
    analytics cert.soundness cert.lemma6PrimeCertificate

theorem StandardGeneratedLocalCertificate.faceDiagonalLocalizedExclusion
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand)
    (analytics : CriticalDiskAnalyticInputs)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskLocalizationConclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) ∧
      CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_localized_exclusion_of_faceDiagonalFamily
    (cert.faceDiagonalLocalizedFamily analytics) i hiota

theorem StandardGeneratedLocalCertificate.faceDiagonalFamilyExclusion
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedLocalCertificate rhoF cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_of_faceDiagonalFamily cert.faceDiagonalFamily i hiota

/-- Conditional Lemma 6' from exactly the two semantic generated-certificate obligations. -/
theorem critical_disk_assembly_from_generated_certificates
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (cert :
      CriticalDiskLemma6PrimeCertificate
        (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs
        cand) :
    CriticalDiskLemma6PrimeStatement cand :=
  critical_disk_assembly_from_generated_soundness
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise) cert

/-- Direct exclusion from exactly the two semantic generated-certificate obligations. -/
theorem critical_disk_exclusion_from_generated_certificates
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (cert :
      CriticalDiskLemma6PrimeCertificate
        (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs
        cand)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  critical_disk_exclusion_from_generated_soundness
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise) cert hcand

/-- Transported conditional Lemma 6' from exactly the two semantic generated-certificate
obligations. -/
theorem critical_disk_assembly_iotaInner_from_generated_certificates
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (cert :
      CriticalDiskLemma6PrimeCertificate
        (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs
        cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLemma6PrimeStatement (cand.iotaInner S) :=
  critical_disk_assembly_iotaInner_from_generated_soundness
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise) cert S

/-- Direct transported exclusion from exactly the two semantic generated-certificate obligations. -/
theorem critical_disk_exclusion_iotaInner_from_generated_certificates
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (cert :
      CriticalDiskLemma6PrimeCertificate
        (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs
        cand)
    (S : ImproperVertexSymmetry stellatedVertices)
    (hiota : CriticalDiskHypotheses (cand.iotaInner S)) :
    CriticalDiskExclusion (cand.iotaInner S) :=
  critical_disk_exclusion_iotaInner_from_generated_soundness
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise) cert S hiota

/-- Localized transported exclusion from exactly the two semantic generated-certificate
obligations. -/
theorem critical_disk_localized_exclusion_iotaInner_from_generated_certificates
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (cert :
      CriticalDiskLemma6PrimeCertificate
        (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs
        cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLocalizedExclusionStatement (cand.iotaInner S) :=
  critical_disk_localized_exclusion_iotaInner_from_generated_soundness analytics
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise) cert S

/-- Face-diagonal conditional Lemma 6' from exactly the two semantic generated-certificate
obligations. -/
theorem critical_disk_assembly_faceDiagonal_from_generated_certificates
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (cert :
      CriticalDiskLemma6PrimeCertificate
        (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs
        cand)
    (i : Fin 6) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_assembly_faceDiagonal_from_generated_soundness
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise) cert i

/-- Direct one-face-diagonal exclusion from exactly the two semantic generated-certificate
obligations. -/
theorem critical_disk_exclusion_faceDiagonal_from_generated_certificates
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (cert :
      CriticalDiskLemma6PrimeCertificate
        (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs
        cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_faceDiagonal_from_generated_soundness
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise) cert i hiota

/-- Packaged all-six conditional Lemma 6' from exactly the two semantic generated-certificate
obligations. -/
theorem critical_disk_assembly_faceDiagonalFamily_from_generated_certificates
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (cert :
      CriticalDiskLemma6PrimeCertificate
        (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs
        cand) :
    FaceDiagonalLemma6PrimeFamily cand :=
  critical_disk_assembly_faceDiagonalFamily_from_generated_soundness
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise) cert

/-- Apply the generated-certificate all-six family at one face-diagonal reflected sheet. -/
theorem critical_disk_exclusion_faceDiagonalFamily_from_generated_certificates
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (cert :
      CriticalDiskLemma6PrimeCertificate
        (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs
        cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_of_faceDiagonalFamily
    (critical_disk_assembly_faceDiagonalFamily_from_generated_certificates
      sfCert sbPointwise cert)
    i hiota

/-- Conditional Lemma 6' directly from the two generated semantic obligations and a zone bundle. -/
theorem critical_disk_assembly_from_generated_certificates_and_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand) :
    CriticalDiskLemma6PrimeStatement cand :=
  critical_disk_assembly_from_generated_certificates sfCert sbPointwise
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones)

/-- Direct exclusion from the two generated semantic obligations and a zone bundle. -/
theorem critical_disk_exclusion_from_generated_certificates_and_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  critical_disk_exclusion_conditional
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones)
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs_allCertified
    hcand

/-- Localized exclusion from the two generated semantic obligations and a zone bundle. -/
theorem critical_disk_localized_exclusion_from_generated_certificates_and_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand) :
    CriticalDiskLocalizedExclusionStatement cand :=
  critical_disk_localized_exclusion_from_generated_soundness analytics
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise)
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones)

/-- Transported conditional Lemma 6' directly from generated obligations and a zone bundle. -/
theorem critical_disk_assembly_iotaInner_from_generated_certificates_and_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLemma6PrimeStatement (cand.iotaInner S) :=
  critical_disk_assembly_conditional_iotaInner_of_zone_consequences
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zones S

/-- Direct transported exclusion from generated obligations and a zone bundle. -/
theorem critical_disk_exclusion_iotaInner_from_generated_certificates_and_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand)
    (S : ImproperVertexSymmetry stellatedVertices)
    (hiota : CriticalDiskHypotheses (cand.iotaInner S)) :
    CriticalDiskExclusion (cand.iotaInner S) :=
  critical_disk_exclusion_conditional_iotaInner_of_zone_consequences
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zones S hiota

/-- Localized transported exclusion directly from generated obligations and a zone bundle. -/
theorem critical_disk_localized_exclusion_iotaInner_from_generated_certificates_and_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLocalizedExclusionStatement (cand.iotaInner S) :=
  critical_disk_localized_exclusion_iotaInner_from_generated_soundness analytics
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise)
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones) S

/-- One face-diagonal conditional Lemma 6' directly from generated obligations and a zone bundle. -/
theorem critical_disk_assembly_faceDiagonal_from_generated_certificates_and_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand)
    (i : Fin 6) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_assembly_conditional_faceDiagonalReflection_of_zone_consequences
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zones i

/-- Direct one-face-diagonal exclusion from generated obligations and a zone bundle. -/
theorem critical_disk_exclusion_faceDiagonal_from_generated_certificates_and_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_conditional_faceDiagonalReflection_of_zone_consequences
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zones i hiota

/-- Packaged all-six Lemma 6' directly from the generated semantic obligations and a zone bundle. -/
theorem critical_disk_assembly_faceDiagonalFamily_from_generated_certificates_and_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand) :
    FaceDiagonalLemma6PrimeFamily cand :=
  critical_disk_assembly_conditional_faceDiagonalFamily_of_zone_consequences
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zones

/-- All-six localized face-diagonal conclusion from generated certificates and a zone bundle. -/
theorem critical_disk_localized_exclusion_faceDiagonalFamily_from_generated_certificates_and_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand) :
    FaceDiagonalLocalizedExclusionFamily cand :=
  critical_disk_localized_exclusion_conditional_faceDiagonalFamily analytics
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones)
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs_allCertified

/-- Direct indexed localized exclusion from generated certificates and a zone bundle. -/
theorem critical_disk_localized_exclusion_faceDiagonal_from_generated_certificates_and_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskLocalizationConclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) ∧
      CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_localized_exclusion_of_faceDiagonalFamily
    (critical_disk_localized_exclusion_faceDiagonalFamily_from_generated_certificates_and_zones
      analytics sfCert sbPointwise zones)
    i hiota

/-- Apply the generated-obligations-and-zones all-six family at one face-diagonal reflected
sheet. -/
theorem critical_disk_exclusion_faceDiagonalFamily_from_generated_certificates_and_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_of_faceDiagonalFamily
    (critical_disk_assembly_faceDiagonalFamily_from_generated_certificates_and_zones
      sfCert sbPointwise zones)
    i hiota

/-- Conditional Lemma 6' directly from generated obligations when Zones B/C are supplied in
their angle-consequence form. -/
theorem critical_disk_assembly_from_generated_certificates_and_angle_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand) :
    CriticalDiskLemma6PrimeStatement cand :=
  critical_disk_assembly_from_generated_certificates sfCert sbPointwise
    (CriticalDiskLemma6PrimeCertificate.ofAngleConsequences
      zone0 zoneA zoneB zoneC zoneD)

/-- Direct exclusion from generated obligations when Zones B/C are supplied in their
angle-consequence form. -/
theorem critical_disk_exclusion_from_generated_certificates_and_angle_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zone0 zoneA zoneB zoneC zoneD hcand

/-- Localized exclusion from generated obligations when Zones B/C are supplied in their
angle-consequence form. -/
theorem critical_disk_localized_exclusion_from_generated_certificates_and_angle_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (analytics : CriticalDiskAnalyticInputs)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand) :
    CriticalDiskLocalizedExclusionStatement cand :=
  critical_disk_localized_exclusion_from_generated_soundness analytics
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise)
    (CriticalDiskLemma6PrimeCertificate.ofAngleConsequences
      zone0 zoneA zoneB zoneC zoneD)

/-- Transported conditional Lemma 6' directly from generated obligations and B/C angle
consequences. -/
theorem critical_disk_assembly_iotaInner_from_generated_certificates_and_angle_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zone0 zoneA zoneB zoneC zoneD S

/-- Direct transported exclusion from generated obligations and B/C angle consequences. -/
theorem critical_disk_exclusion_iotaInner_from_generated_certificates_and_angle_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zone0 zoneA zoneB zoneC zoneD S hiota

/-- Localized transported exclusion directly from generated obligations and B/C angle
consequences. -/
theorem critical_disk_localized_exclusion_iotaInner_from_generated_certificates_and_angle_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (analytics : CriticalDiskAnalyticInputs)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
  critical_disk_localized_exclusion_iotaInner_from_generated_soundness analytics
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise)
    (CriticalDiskLemma6PrimeCertificate.ofAngleConsequences
      zone0 zoneA zoneB zoneC zoneD) S

/-- One face-diagonal conditional Lemma 6' directly from generated obligations and B/C angle
consequences. -/
theorem critical_disk_assembly_faceDiagonal_from_generated_certificates_and_angle_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zone0 zoneA zoneB zoneC zoneD i

/-- Direct one-face-diagonal exclusion from generated obligations and B/C angle consequences. -/
theorem critical_disk_exclusion_faceDiagonal_from_generated_certificates_and_angle_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zone0 zoneA zoneB zoneC zoneD i hiota

/-- Packaged all-six Lemma 6' directly from generated obligations and B/C angle consequences. -/
theorem critical_disk_assembly_faceDiagonalFamily_from_generated_certificates_and_angle_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zone0 zoneA zoneB zoneC zoneD

/-- All-six localized face-diagonal conclusion from generated certificates when Zones B/C are
supplied in angle-consequence form. -/
theorem
    critical_disk_localized_exclusion_faceDiagonalFamily_from_generated_certificates_and_angle_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (analytics : CriticalDiskAnalyticInputs)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
    (standardGeneratedSoundness_of_certificates sfCert sbPointwise).toCriticalDiskInputs_allCertified

/-- Direct indexed localized exclusion from generated certificates and B/C angle consequences. -/
theorem critical_disk_localized_exclusion_faceDiagonal_from_generated_certificates_and_angle_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (analytics : CriticalDiskAnalyticInputs)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
    (critical_disk_localized_exclusion_faceDiagonalFamily_from_generated_certificates_and_angle_zones
      analytics sfCert sbPointwise zone0 zoneA zoneB zoneC zoneD)
    i hiota

/-- Apply the generated-obligations-and-angle-zones all-six family at one face-diagonal reflected
sheet. -/
theorem critical_disk_exclusion_faceDiagonalFamily_from_generated_certificates_and_angle_zones
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
    (critical_disk_assembly_faceDiagonalFamily_from_generated_certificates_and_angle_zones
      sfCert sbPointwise zone0 zoneA zoneB zoneC zoneD)
    i hiota

/-- Stronger generated-input boundary that also retains the audited `(SF)` sweep facts. -/
structure AuditedGeneratedSoundness
    (rhoF : ℝ) (phiDomain xDomain yDomain : RatInterval) where
  sf :
    GeneratedSFCertifiedInput.StandardAuditedSweepSoundness rhoF
      phiDomain xDomain yDomain
  sbBox : GeneratedSBBoxCertifiedInput.StandardReplaySoundness

/-- Constructor for the stronger generated boundary once the `(SF)` audit, semantic `(SF)`
certificate, and pointwise `(SB-box)` bridge have been supplied. -/
def auditedGeneratedSoundness_of_audit_and_certificates
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness) :
    AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain where
  sf :=
    GeneratedSFCertifiedInput.standardAuditedSweepSoundness_of_audit_and_certificate
      audit sfCert
  sbBox := GeneratedSBBoxCertifiedInput.standardReplaySoundness_of_pointwise sbPointwise

def AuditedGeneratedSoundness.toStandardGeneratedSoundness
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain) :
    StandardGeneratedSoundness rhoF where
  sf := soundness.sf.toStandardSweepSoundness
  sbBox := soundness.sbBox

def AuditedGeneratedSoundness.toCriticalDiskInputs
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain) :
    CriticalDiskCertifiedInputs :=
  soundness.toStandardGeneratedSoundness.toCriticalDiskInputs

theorem AuditedGeneratedSoundness.toCriticalDiskInputs_allCertified
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain) :
    soundness.toCriticalDiskInputs.allCertified :=
  soundness.toStandardGeneratedSoundness.toCriticalDiskInputs_allCertified

theorem AuditedGeneratedSoundness.toCriticalDiskInputs_sf_certified
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain) :
    soundness.toCriticalDiskInputs.sf.certified :=
  soundness.toStandardGeneratedSoundness.toCriticalDiskInputs_sf_certified

theorem AuditedGeneratedSoundness.toCriticalDiskInputs_sbBox_certified
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain) :
    soundness.toCriticalDiskInputs.sbBox.certified :=
  soundness.toStandardGeneratedSoundness.toCriticalDiskInputs_sbBox_certified

theorem AuditedGeneratedSoundness.coverWithDeferred
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain) :
    GeneratedSFWitness.manifest.DomainCoverWithDeferred
      phiDomain xDomain yDomain :=
  soundness.sf.coverWithDeferred

theorem AuditedGeneratedSoundness.sfCertifiedRowsValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain) :
    GeneratedSFWitness.manifest.CertifiedRowsValid
      GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  soundness.sf.certifiedRowsValid

theorem AuditedGeneratedSoundness.sfCertifiedRowValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    {row : SFCertifiedSweepRow}
    (hrow : row ∈ GeneratedSFWitness.manifest.certified) :
    row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  soundness.sf.certifiedRowValid hrow

theorem AuditedGeneratedSoundness.deferredDischarged
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (φ x y : ℝ)
    (hφ : phiDomain.contains φ) (hx : xDomain.contains x) (hy : yDomain.contains y)
    (hdeferred :
      ∃ row ∈ GeneratedSFWitness.manifest.deferred, row.box.contains φ x y) :
    ∃ row ∈ GeneratedSFWitness.manifest.certified, row.box.contains φ x y :=
  soundness.sf.deferredDischarged φ x y hφ hx hy hdeferred

def AuditedGeneratedSoundness.certifiedDomainCover
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain) :
    GeneratedSFWitness.manifest.CertifiedDomainCover
      phiDomain xDomain yDomain :=
  soundness.sf.certifiedDomainCover

theorem AuditedGeneratedSoundness.existsValidCertifiedRow
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    {φ x y : ℝ}
    (hφ : phiDomain.contains φ) (hx : xDomain.contains x) (hy : yDomain.contains y) :
    ∃ row ∈ GeneratedSFWitness.manifest.certified,
      row.box.contains φ x y ∧
        row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  soundness.sf.existsValidCertifiedRow hφ hx hy

theorem AuditedGeneratedSoundness.sbBoxReplayAssemblyValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain) :
    SBBoxReplayAssembly
      GeneratedSBBoxTailWitness.manifest GeneratedSBBoxBulkWitness.manifest
      GeneratedSBBoxAssemblyReport.report
      GeneratedSBBoxAssemblyReport.tailDomain
      GeneratedSBBoxAssemblyReport.bulkDeltaDomain
      GeneratedSBBoxAssemblyReport.bulkPhiDomain
      GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.toStandardGeneratedSoundness.sbBoxReplayAssemblyValid

theorem AuditedGeneratedSoundness.sbBoxTailRowsValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain) :
    GeneratedSBBoxTailWitness.manifest.RowsValid :=
  soundness.toStandardGeneratedSoundness.sbBoxTailRowsValid

theorem AuditedGeneratedSoundness.sbBoxBulkRowsValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain) :
    GeneratedSBBoxBulkWitness.manifest.RowsValid
      GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.toStandardGeneratedSoundness.sbBoxBulkRowsValid

theorem AuditedGeneratedSoundness.sbBoxTailRowValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    {row : SBBoxTailRow}
    (hrow : row ∈ GeneratedSBBoxTailWitness.manifest.rows) :
    row.Valid :=
  soundness.toStandardGeneratedSoundness.sbBoxTailRowValid hrow

theorem AuditedGeneratedSoundness.sbBoxBulkRowValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    {row : SBBoxBulkRow}
    (hrow : row ∈ GeneratedSBBoxBulkWitness.manifest.rows) :
    row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.toStandardGeneratedSoundness.sbBoxBulkRowValid hrow

theorem AuditedGeneratedSoundness.sbBoxTailExistsValidRow
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (chart : SBBoxTailChart) {r : ℝ}
    (hr : GeneratedSBBoxAssemblyReport.tailDomain.contains r) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains r ∧ row.Valid :=
  soundness.toStandardGeneratedSoundness.sbBoxTailExistsValidRow chart hr

theorem AuditedGeneratedSoundness.sbBoxBulkExistsValidRow
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    {delta phi : ℝ}
    (hdelta : GeneratedSBBoxAssemblyReport.bulkDeltaDomain.contains delta)
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains delta ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.toStandardGeneratedSoundness.sbBoxBulkExistsValidRow hdelta hphi

theorem AuditedGeneratedSoundness.sbBoxTailExistsValidRowAtZero
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (chart : SBBoxTailChart) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains (0 : ℝ) ∧ row.Valid :=
  soundness.toStandardGeneratedSoundness.sbBoxTailExistsValidRowAtZero chart

theorem AuditedGeneratedSoundness.sbBoxTailExistsValidRowAtOne
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (chart : SBBoxTailChart) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains (1 : ℝ) ∧ row.Valid :=
  soundness.toStandardGeneratedSoundness.sbBoxTailExistsValidRowAtOne chart

theorem AuditedGeneratedSoundness.sbBoxBulkExistsValidRowAtTailCut
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    {phi : ℝ}
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskTailCut ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.toStandardGeneratedSoundness.sbBoxBulkExistsValidRowAtTailCut hphi

theorem AuditedGeneratedSoundness.sbBoxBulkExistsValidRowAtRhoCap
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    {phi : ℝ}
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskRhoCap ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.toStandardGeneratedSoundness.sbBoxBulkExistsValidRowAtRhoCap hphi

theorem AuditedGeneratedSoundness.sbBoxBulkExistsValidRowAtTailCutZeroPhi
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskTailCut ∧ row.phi.contains (0 : ℝ) ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.toStandardGeneratedSoundness.sbBoxBulkExistsValidRowAtTailCutZeroPhi

theorem AuditedGeneratedSoundness.sbBoxBulkExistsValidRowAtRhoCapZeroPhi
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskRhoCap ∧ row.phi.contains (0 : ℝ) ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.toStandardGeneratedSoundness.sbBoxBulkExistsValidRowAtRhoCapZeroPhi

theorem AuditedGeneratedSoundness.delta_le_rhoCap
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (hcand : CriticalDiskHypotheses cand) :
    cand.delta ≤ criticalDiskRhoCap :=
  soundness.toStandardGeneratedSoundness.delta_le_rhoCap hcand

theorem AuditedGeneratedSoundness.delta_le_sf_rhoF
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (hcand : CriticalDiskHypotheses cand) :
    cand.delta ≤ soundness.toCriticalDiskInputs.sf.rhoF :=
  soundness.toStandardGeneratedSoundness.delta_le_sf_rhoF hcand

theorem AuditedGeneratedSoundness.delta_le_sbBox_rhoB
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (hcand : CriticalDiskHypotheses cand) :
    cand.delta ≤ soundness.toCriticalDiskInputs.sbBox.rhoB :=
  soundness.toStandardGeneratedSoundness.delta_le_sbBox_rhoB hcand

def AuditedGeneratedSoundness.sbBoxPointCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (hcand : CriticalDiskHypotheses cand) :
    SBBoxPointCertificate cand.R₂ cand.delta
      soundness.toCriticalDiskInputs.sbBox.bPi
      soundness.toCriticalDiskInputs.sbBox.bGamma
      soundness.toCriticalDiskInputs.sbBox.bT :=
  soundness.toStandardGeneratedSoundness.sbBoxPointCertificate hcand

def AuditedGeneratedSoundness.sbBoxInclusion
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (hcand : CriticalDiskHypotheses cand) :
    DepthCylinderTheorem.BoxInclusionCertificate
      (soundness.sbBoxPointCertificate hcand).cert :=
  soundness.toStandardGeneratedSoundness.sbBoxInclusion hcand

theorem AuditedGeneratedSoundness.sfCovers
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    {φ s : ℝ}
    (hφlo : -Real.pi ≤ φ) (hφhi : φ ≤ Real.pi)
    (hslo : 0 ≤ s) (hshi : s ≤ 1) :
    ∃ c : soundness.toCriticalDiskInputs.sf.certificate.chart,
      soundness.toCriticalDiskInputs.sf.certificate.inChart c φ s :=
  soundness.toStandardGeneratedSoundness.sfCovers hφlo hφhi hslo hshi

theorem AuditedGeneratedSoundness.sfChartClassified
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (c : soundness.toCriticalDiskInputs.sf.certificate.chart) :
    soundness.toCriticalDiskInputs.sf.certificate.isShell c ∨
      soundness.toCriticalDiskInputs.sf.certificate.isBulk c :=
  soundness.toStandardGeneratedSoundness.sfChartClassified c

theorem AuditedGeneratedSoundness.sfCornerDistLower_nonneg
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (c : soundness.toCriticalDiskInputs.sf.certificate.chart) :
    0 ≤ soundness.toCriticalDiskInputs.sf.certificate.cornerDistLower c :=
  soundness.toStandardGeneratedSoundness.sfCornerDistLower_nonneg c

theorem AuditedGeneratedSoundness.sfShellBound
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (c : soundness.toCriticalDiskInputs.sf.certificate.chart)
    (hc : soundness.toCriticalDiskInputs.sf.certificate.isShell c) :
    soundness.toCriticalDiskInputs.sf.shellSlope *
        soundness.toCriticalDiskInputs.sf.certificate.cornerDistLower c ≤
      soundness.toCriticalDiskInputs.sf.certificate.psiLower c :=
  soundness.toStandardGeneratedSoundness.sfShellBound c hc

theorem AuditedGeneratedSoundness.sfBulkBound
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (c : soundness.toCriticalDiskInputs.sf.certificate.chart)
    (hc : soundness.toCriticalDiskInputs.sf.certificate.isBulk c) :
    soundness.toCriticalDiskInputs.sf.psiMin ≤
      soundness.toCriticalDiskInputs.sf.certificate.psiLower c :=
  soundness.toStandardGeneratedSoundness.sfBulkBound c hc

/-- Conditional Lemma 6' instantiated with the stronger audited generated-input boundary. -/
theorem critical_disk_assembly_from_audited_generated_soundness
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand) :
    CriticalDiskLemma6PrimeStatement cand :=
  critical_disk_assembly_conditional cert soundness.toCriticalDiskInputs_allCertified

/-- Direct exclusion instantiated with the stronger audited generated-input boundary. -/
theorem critical_disk_exclusion_from_audited_generated_soundness
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  critical_disk_exclusion_conditional cert soundness.toCriticalDiskInputs_allCertified hcand

/-- Localized exclusion instantiated with the stronger audited generated-input boundary. -/
theorem critical_disk_localized_exclusion_from_audited_generated_soundness
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand) :
    CriticalDiskLocalizedExclusionStatement cand :=
  critical_disk_localized_exclusion_conditional analytics cert
    soundness.toCriticalDiskInputs_allCertified

/-- Conditional Lemma 6' after transporting the audited generated boundary by any vertex symmetry. -/
theorem critical_disk_assembly_iotaInner_from_audited_generated_soundness
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLemma6PrimeStatement (cand.iotaInner S) :=
  critical_disk_assembly_conditional_iotaInner cert
    soundness.toCriticalDiskInputs_allCertified S

/-- Direct transported exclusion instantiated with the stronger audited generated-input boundary. -/
theorem critical_disk_exclusion_iotaInner_from_audited_generated_soundness
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand)
    (S : ImproperVertexSymmetry stellatedVertices)
    (hiota : CriticalDiskHypotheses (cand.iotaInner S)) :
    CriticalDiskExclusion (cand.iotaInner S) :=
  critical_disk_assembly_conditional_iotaInner cert
    soundness.toCriticalDiskInputs_allCertified S hiota

/-- Localized transported exclusion instantiated with the stronger audited generated-input
boundary. -/
theorem critical_disk_localized_exclusion_iotaInner_from_audited_generated_soundness
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLocalizedExclusionStatement (cand.iotaInner S) :=
  critical_disk_localized_exclusion_conditional_iotaInner analytics cert
    soundness.toCriticalDiskInputs_allCertified S

/-- Conditional Lemma 6' for each face-diagonal reflected marginal sheet from audited inputs. -/
theorem critical_disk_assembly_faceDiagonal_from_audited_generated_soundness
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand)
    (i : Fin 6) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_assembly_conditional_faceDiagonalReflection cert
    soundness.toCriticalDiskInputs_allCertified i

/-- Direct one-face-diagonal exclusion instantiated with the stronger audited generated-input
boundary. -/
theorem critical_disk_exclusion_faceDiagonal_from_audited_generated_soundness
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_assembly_conditional_faceDiagonalReflection cert
    soundness.toCriticalDiskInputs_allCertified i hiota

/-- Packaged all-six version of the audited generated-input conditional Lemma 6' boundary. -/
theorem critical_disk_assembly_faceDiagonalFamily_from_audited_generated_soundness
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand) :
    FaceDiagonalLemma6PrimeFamily cand :=
  critical_disk_assembly_conditional_faceDiagonalFamily cert
    soundness.toCriticalDiskInputs_allCertified

/-- All-six localized face-diagonal conclusion instantiated with the audited generated boundary. -/
theorem critical_disk_localized_exclusion_faceDiagonalFamily_from_audited_generated_soundness
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand) :
    FaceDiagonalLocalizedExclusionFamily cand :=
  critical_disk_localized_exclusion_conditional_faceDiagonalFamily analytics cert
    soundness.toCriticalDiskInputs_allCertified

/-- Apply the audited generated-input localized all-six family at one face-diagonal reflected
sheet. -/
theorem critical_disk_localized_exclusion_faceDiagonal_from_audited_generated_soundness
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskLocalizationConclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) ∧
      CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_localized_exclusion_of_faceDiagonalFamily
    (critical_disk_localized_exclusion_faceDiagonalFamily_from_audited_generated_soundness
      analytics soundness cert)
    i hiota

/-- Apply the audited generated-input all-six family at one face-diagonal reflected sheet. -/
theorem critical_disk_exclusion_faceDiagonalFamily_from_audited_generated_soundness
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain)
    (cert : CriticalDiskLemma6PrimeCertificate soundness.toCriticalDiskInputs cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_of_faceDiagonalFamily
    (critical_disk_assembly_faceDiagonalFamily_from_audited_generated_soundness soundness cert)
    i hiota

/-! ### Packaged audited local certificate boundary -/

structure AuditedGeneratedLocalCertificate
    (rhoF : ℝ) (phiDomain xDomain yDomain : RatInterval)
    (cand : CriticalDiskCandidate) where
  soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain
  zones : CriticalDiskZoneConsequences cand

def auditedGeneratedLocalCertificate_of_audit_and_certificates_and_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand) :
    AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand where
  soundness := auditedGeneratedSoundness_of_audit_and_certificates audit sfCert sbPointwise
  zones := zones

def auditedGeneratedLocalCertificate_of_audit_and_certificates_and_angle_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand) :
    AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand :=
  auditedGeneratedLocalCertificate_of_audit_and_certificates_and_zones
    audit sfCert sbPointwise
    (CriticalDiskZoneConsequences.ofAngleConsequences zone0 zoneA zoneB zoneC zoneD)

def AuditedGeneratedLocalCertificate.toStandardGeneratedLocalCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand) :
    StandardGeneratedLocalCertificate rhoF cand where
  soundness := cert.soundness.toStandardGeneratedSoundness
  zones := cert.zones

def AuditedGeneratedLocalCertificate.lemma6PrimeCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand) :
    CriticalDiskLemma6PrimeCertificate cert.soundness.toCriticalDiskInputs cand :=
  CriticalDiskLemma6PrimeCertificate.ofZoneConsequences cert.zones

def AuditedGeneratedLocalCertificate.toCriticalDiskInputs
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand) :
    CriticalDiskCertifiedInputs :=
  cert.soundness.toCriticalDiskInputs

theorem AuditedGeneratedLocalCertificate.inputs_allCertified
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand) :
    cert.toCriticalDiskInputs.allCertified :=
  cert.soundness.toCriticalDiskInputs_allCertified

theorem AuditedGeneratedLocalCertificate.coverWithDeferred
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand) :
    GeneratedSFWitness.manifest.DomainCoverWithDeferred
      phiDomain xDomain yDomain :=
  cert.soundness.coverWithDeferred

theorem AuditedGeneratedLocalCertificate.deferredDischarged
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    (φ x y : ℝ)
    (hφ : phiDomain.contains φ) (hx : xDomain.contains x) (hy : yDomain.contains y)
    (hdeferred :
      ∃ row ∈ GeneratedSFWitness.manifest.deferred, row.box.contains φ x y) :
    ∃ row ∈ GeneratedSFWitness.manifest.certified, row.box.contains φ x y :=
  cert.soundness.deferredDischarged φ x y hφ hx hy hdeferred

def AuditedGeneratedLocalCertificate.certifiedDomainCover
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand) :
    GeneratedSFWitness.manifest.CertifiedDomainCover
      phiDomain xDomain yDomain :=
  cert.soundness.certifiedDomainCover

theorem AuditedGeneratedLocalCertificate.existsValidCertifiedRow
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    {φ x y : ℝ}
    (hφ : phiDomain.contains φ) (hx : xDomain.contains x) (hy : yDomain.contains y) :
    ∃ row ∈ GeneratedSFWitness.manifest.certified,
      row.box.contains φ x y ∧
        row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  cert.soundness.existsValidCertifiedRow hφ hx hy

theorem AuditedGeneratedLocalCertificate.sfCertifiedRowsValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand) :
    GeneratedSFWitness.manifest.CertifiedRowsValid
      GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  cert.soundness.sfCertifiedRowsValid

theorem AuditedGeneratedLocalCertificate.sfCertifiedRowValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    {row : SFCertifiedSweepRow}
    (hrow : row ∈ GeneratedSFWitness.manifest.certified) :
    row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  cert.soundness.sfCertifiedRowValid hrow

theorem AuditedGeneratedLocalCertificate.sbBoxReplayAssemblyValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand) :
    SBBoxReplayAssembly
      GeneratedSBBoxTailWitness.manifest GeneratedSBBoxBulkWitness.manifest
      GeneratedSBBoxAssemblyReport.report
      GeneratedSBBoxAssemblyReport.tailDomain
      GeneratedSBBoxAssemblyReport.bulkDeltaDomain
      GeneratedSBBoxAssemblyReport.bulkPhiDomain
      GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxReplayAssemblyValid

theorem AuditedGeneratedLocalCertificate.sbBoxTailRowValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    {row : SBBoxTailRow}
    (hrow : row ∈ GeneratedSBBoxTailWitness.manifest.rows) :
    row.Valid :=
  cert.soundness.sbBoxTailRowValid hrow

theorem AuditedGeneratedLocalCertificate.sbBoxBulkRowValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    {row : SBBoxBulkRow}
    (hrow : row ∈ GeneratedSBBoxBulkWitness.manifest.rows) :
    row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxBulkRowValid hrow

theorem AuditedGeneratedLocalCertificate.sbBoxTailExistsValidRow
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    (chart : SBBoxTailChart) {r : ℝ}
    (hr : GeneratedSBBoxAssemblyReport.tailDomain.contains r) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains r ∧ row.Valid :=
  cert.soundness.sbBoxTailExistsValidRow chart hr

theorem AuditedGeneratedLocalCertificate.sbBoxBulkExistsValidRow
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    {delta phi : ℝ}
    (hdelta : GeneratedSBBoxAssemblyReport.bulkDeltaDomain.contains delta)
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains delta ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxBulkExistsValidRow hdelta hphi

def AuditedGeneratedLocalCertificate.sbBoxPointCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    (hcand : CriticalDiskHypotheses cand) :
    SBBoxPointCertificate cand.R₂ cand.delta
      cert.toCriticalDiskInputs.sbBox.bPi
      cert.toCriticalDiskInputs.sbBox.bGamma
      cert.toCriticalDiskInputs.sbBox.bT :=
  cert.soundness.sbBoxPointCertificate hcand

def AuditedGeneratedLocalCertificate.sbBoxInclusion
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    (hcand : CriticalDiskHypotheses cand) :
    DepthCylinderTheorem.BoxInclusionCertificate
      (cert.sbBoxPointCertificate hcand).cert :=
  cert.soundness.sbBoxInclusion hcand

theorem AuditedGeneratedLocalCertificate.sfCovers
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    {φ s : ℝ}
    (hφlo : -Real.pi ≤ φ) (hφhi : φ ≤ Real.pi)
    (hslo : 0 ≤ s) (hshi : s ≤ 1) :
    ∃ c : cert.toCriticalDiskInputs.sf.certificate.chart,
      cert.toCriticalDiskInputs.sf.certificate.inChart c φ s :=
  cert.soundness.sfCovers hφlo hφhi hslo hshi

theorem AuditedGeneratedLocalCertificate.lemma6prime
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand) :
    CriticalDiskLemma6PrimeStatement cand :=
  critical_disk_assembly_from_audited_generated_soundness
    cert.soundness cert.lemma6PrimeCertificate

theorem AuditedGeneratedLocalCertificate.exclusion
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  cert.lemma6prime hcand

theorem AuditedGeneratedLocalCertificate.localizedExclusion
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    (analytics : CriticalDiskAnalyticInputs) :
    CriticalDiskLocalizedExclusionStatement cand :=
  critical_disk_localized_exclusion_from_audited_generated_soundness analytics
    cert.soundness cert.lemma6PrimeCertificate

theorem AuditedGeneratedLocalCertificate.iotaInnerLemma6Prime
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLemma6PrimeStatement (cand.iotaInner S) :=
  critical_disk_assembly_iotaInner_from_audited_generated_soundness
    cert.soundness cert.lemma6PrimeCertificate S

theorem AuditedGeneratedLocalCertificate.iotaInnerExclusion
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    (S : ImproperVertexSymmetry stellatedVertices)
    (hiota : CriticalDiskHypotheses (cand.iotaInner S)) :
    CriticalDiskExclusion (cand.iotaInner S) :=
  cert.iotaInnerLemma6Prime S hiota

theorem AuditedGeneratedLocalCertificate.iotaInnerLocalizedExclusion
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    (analytics : CriticalDiskAnalyticInputs)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLocalizedExclusionStatement (cand.iotaInner S) :=
  critical_disk_localized_exclusion_iotaInner_from_audited_generated_soundness analytics
    cert.soundness cert.lemma6PrimeCertificate S

theorem AuditedGeneratedLocalCertificate.faceDiagonalLemma6Prime
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    (i : Fin 6) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_assembly_faceDiagonal_from_audited_generated_soundness
    cert.soundness cert.lemma6PrimeCertificate i

theorem AuditedGeneratedLocalCertificate.faceDiagonalExclusion
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  cert.faceDiagonalLemma6Prime i hiota

theorem AuditedGeneratedLocalCertificate.faceDiagonalFamily
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand) :
    FaceDiagonalLemma6PrimeFamily cand :=
  critical_disk_assembly_faceDiagonalFamily_from_audited_generated_soundness
    cert.soundness cert.lemma6PrimeCertificate

theorem AuditedGeneratedLocalCertificate.faceDiagonalLocalizedFamily
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    (analytics : CriticalDiskAnalyticInputs) :
    FaceDiagonalLocalizedExclusionFamily cand :=
  critical_disk_localized_exclusion_faceDiagonalFamily_from_audited_generated_soundness
    analytics cert.soundness cert.lemma6PrimeCertificate

theorem AuditedGeneratedLocalCertificate.faceDiagonalLocalizedExclusion
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    (analytics : CriticalDiskAnalyticInputs)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskLocalizationConclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) ∧
      CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_localized_exclusion_of_faceDiagonalFamily
    (cert.faceDiagonalLocalizedFamily analytics) i hiota

theorem AuditedGeneratedLocalCertificate.faceDiagonalFamilyExclusion
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_of_faceDiagonalFamily cert.faceDiagonalFamily i hiota

/-- Conditional Lemma 6' from the audited generated boundary's raw obligations. -/
theorem critical_disk_assembly_from_audited_generated_certificates
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (cert :
      CriticalDiskLemma6PrimeCertificate
        (auditedGeneratedSoundness_of_audit_and_certificates
          audit sfCert sbPointwise).toCriticalDiskInputs cand) :
    CriticalDiskLemma6PrimeStatement cand :=
  critical_disk_assembly_from_audited_generated_soundness
    (auditedGeneratedSoundness_of_audit_and_certificates audit sfCert sbPointwise) cert

/-- Direct exclusion from the audited generated boundary's raw obligations. -/
theorem critical_disk_exclusion_from_audited_generated_certificates
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (cert :
      CriticalDiskLemma6PrimeCertificate
        (auditedGeneratedSoundness_of_audit_and_certificates
          audit sfCert sbPointwise).toCriticalDiskInputs cand)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  critical_disk_exclusion_from_audited_generated_soundness
    (auditedGeneratedSoundness_of_audit_and_certificates audit sfCert sbPointwise) cert hcand

/-- Transported conditional Lemma 6' from the audited generated boundary's raw obligations. -/
theorem critical_disk_assembly_iotaInner_from_audited_generated_certificates
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (cert :
      CriticalDiskLemma6PrimeCertificate
        (auditedGeneratedSoundness_of_audit_and_certificates
          audit sfCert sbPointwise).toCriticalDiskInputs cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLemma6PrimeStatement (cand.iotaInner S) :=
  critical_disk_assembly_iotaInner_from_audited_generated_soundness
    (auditedGeneratedSoundness_of_audit_and_certificates audit sfCert sbPointwise) cert S

/-- Direct transported exclusion from the audited generated boundary's raw obligations. -/
theorem critical_disk_exclusion_iotaInner_from_audited_generated_certificates
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (cert :
      CriticalDiskLemma6PrimeCertificate
        (auditedGeneratedSoundness_of_audit_and_certificates
          audit sfCert sbPointwise).toCriticalDiskInputs cand)
    (S : ImproperVertexSymmetry stellatedVertices)
    (hiota : CriticalDiskHypotheses (cand.iotaInner S)) :
    CriticalDiskExclusion (cand.iotaInner S) :=
  critical_disk_exclusion_iotaInner_from_audited_generated_soundness
    (auditedGeneratedSoundness_of_audit_and_certificates audit sfCert sbPointwise) cert S hiota

/-- Localized transported exclusion from the audited generated boundary's raw obligations. -/
theorem critical_disk_localized_exclusion_iotaInner_from_audited_generated_certificates
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (cert :
      CriticalDiskLemma6PrimeCertificate
        (auditedGeneratedSoundness_of_audit_and_certificates
          audit sfCert sbPointwise).toCriticalDiskInputs cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLocalizedExclusionStatement (cand.iotaInner S) :=
  critical_disk_localized_exclusion_iotaInner_from_audited_generated_soundness analytics
    (auditedGeneratedSoundness_of_audit_and_certificates audit sfCert sbPointwise) cert S

/-- Face-diagonal conditional Lemma 6' from the audited generated boundary's raw obligations. -/
theorem critical_disk_assembly_faceDiagonal_from_audited_generated_certificates
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (cert :
      CriticalDiskLemma6PrimeCertificate
        (auditedGeneratedSoundness_of_audit_and_certificates
          audit sfCert sbPointwise).toCriticalDiskInputs cand)
    (i : Fin 6) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_assembly_faceDiagonal_from_audited_generated_soundness
    (auditedGeneratedSoundness_of_audit_and_certificates audit sfCert sbPointwise) cert i

/-- Direct one-face-diagonal exclusion from the audited generated boundary's raw obligations. -/
theorem critical_disk_exclusion_faceDiagonal_from_audited_generated_certificates
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (cert :
      CriticalDiskLemma6PrimeCertificate
        (auditedGeneratedSoundness_of_audit_and_certificates
          audit sfCert sbPointwise).toCriticalDiskInputs cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_faceDiagonal_from_audited_generated_soundness
    (auditedGeneratedSoundness_of_audit_and_certificates audit sfCert sbPointwise) cert i hiota

/-- Packaged all-six conditional Lemma 6' from the audited generated boundary's raw obligations. -/
theorem critical_disk_assembly_faceDiagonalFamily_from_audited_generated_certificates
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (cert :
      CriticalDiskLemma6PrimeCertificate
        (auditedGeneratedSoundness_of_audit_and_certificates
          audit sfCert sbPointwise).toCriticalDiskInputs cand) :
    FaceDiagonalLemma6PrimeFamily cand :=
  critical_disk_assembly_faceDiagonalFamily_from_audited_generated_soundness
    (auditedGeneratedSoundness_of_audit_and_certificates audit sfCert sbPointwise) cert

/-- Apply the audited generated-certificate all-six family at one face-diagonal reflected sheet. -/
theorem critical_disk_exclusion_faceDiagonalFamily_from_audited_generated_certificates
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (cert :
      CriticalDiskLemma6PrimeCertificate
        (auditedGeneratedSoundness_of_audit_and_certificates
          audit sfCert sbPointwise).toCriticalDiskInputs cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_of_faceDiagonalFamily
    (critical_disk_assembly_faceDiagonalFamily_from_audited_generated_certificates
      audit sfCert sbPointwise cert)
    i hiota

/-- Conditional Lemma 6' directly from the audited generated obligations and a zone bundle. -/
theorem critical_disk_assembly_from_audited_generated_certificates_and_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand) :
    CriticalDiskLemma6PrimeStatement cand :=
  critical_disk_assembly_from_audited_generated_certificates audit sfCert sbPointwise
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones)

/-- Direct exclusion from audited generated obligations and a zone bundle. -/
theorem critical_disk_exclusion_from_audited_generated_certificates_and_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  critical_disk_exclusion_conditional
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones)
    (auditedGeneratedSoundness_of_audit_and_certificates
      audit sfCert sbPointwise).toCriticalDiskInputs_allCertified
    hcand

/-- Localized exclusion from audited generated obligations and a zone bundle. -/
theorem critical_disk_localized_exclusion_from_audited_generated_certificates_and_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand) :
    CriticalDiskLocalizedExclusionStatement cand :=
  critical_disk_localized_exclusion_from_audited_generated_soundness analytics
    (auditedGeneratedSoundness_of_audit_and_certificates audit sfCert sbPointwise)
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones)

/-- Transported conditional Lemma 6' directly from audited generated obligations and a zone
bundle. -/
theorem critical_disk_assembly_iotaInner_from_audited_generated_certificates_and_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLemma6PrimeStatement (cand.iotaInner S) :=
  critical_disk_assembly_conditional_iotaInner_of_zone_consequences
    (auditedGeneratedSoundness_of_audit_and_certificates
      audit sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zones S

/-- Direct transported exclusion from audited generated obligations and a zone bundle. -/
theorem critical_disk_exclusion_iotaInner_from_audited_generated_certificates_and_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand)
    (S : ImproperVertexSymmetry stellatedVertices)
    (hiota : CriticalDiskHypotheses (cand.iotaInner S)) :
    CriticalDiskExclusion (cand.iotaInner S) :=
  critical_disk_exclusion_conditional_iotaInner_of_zone_consequences
    (auditedGeneratedSoundness_of_audit_and_certificates
      audit sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zones S hiota

/-- Localized transported exclusion directly from audited generated obligations and a zone
bundle. -/
theorem critical_disk_localized_exclusion_iotaInner_from_audited_generated_certificates_and_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand)
    (S : ImproperVertexSymmetry stellatedVertices) :
    CriticalDiskLocalizedExclusionStatement (cand.iotaInner S) :=
  critical_disk_localized_exclusion_iotaInner_from_audited_generated_soundness analytics
    (auditedGeneratedSoundness_of_audit_and_certificates audit sfCert sbPointwise)
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones) S

/-- One face-diagonal conditional Lemma 6' directly from audited generated obligations and a zone
bundle. -/
theorem critical_disk_assembly_faceDiagonal_from_audited_generated_certificates_and_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand)
    (i : Fin 6) :
    CriticalDiskLemma6PrimeStatement
      (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_assembly_conditional_faceDiagonalReflection_of_zone_consequences
    (auditedGeneratedSoundness_of_audit_and_certificates
      audit sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zones i

/-- Direct one-face-diagonal exclusion from audited generated obligations and a zone bundle. -/
theorem critical_disk_exclusion_faceDiagonal_from_audited_generated_certificates_and_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_conditional_faceDiagonalReflection_of_zone_consequences
    (auditedGeneratedSoundness_of_audit_and_certificates
      audit sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zones i hiota

/-- Packaged all-six Lemma 6' directly from the audited generated obligations and a zone bundle. -/
theorem critical_disk_assembly_faceDiagonalFamily_from_audited_generated_certificates_and_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand) :
    FaceDiagonalLemma6PrimeFamily cand :=
  critical_disk_assembly_conditional_faceDiagonalFamily_of_zone_consequences
    (auditedGeneratedSoundness_of_audit_and_certificates
      audit sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zones

/-- All-six localized face-diagonal conclusion from audited generated certificates and a zone
bundle. -/
theorem
    critical_disk_localized_exclusion_faceDiagonalFamily_from_audited_generated_certificates_and_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand) :
    FaceDiagonalLocalizedExclusionFamily cand :=
  critical_disk_localized_exclusion_conditional_faceDiagonalFamily analytics
    (CriticalDiskLemma6PrimeCertificate.ofZoneConsequences zones)
    (auditedGeneratedSoundness_of_audit_and_certificates
      audit sfCert sbPointwise).toCriticalDiskInputs_allCertified

/-- Direct indexed localized exclusion from audited generated certificates and a zone bundle. -/
theorem critical_disk_localized_exclusion_faceDiagonal_from_audited_generated_certificates_and_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (analytics : CriticalDiskAnalyticInputs)
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskLocalizationConclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) ∧
      CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_localized_exclusion_of_faceDiagonalFamily
    (critical_disk_localized_exclusion_faceDiagonalFamily_from_audited_generated_certificates_and_zones
      analytics audit sfCert sbPointwise zones)
    i hiota

/-- Apply the audited generated-obligations-and-zones all-six family at one face-diagonal reflected
sheet. -/
theorem critical_disk_exclusion_faceDiagonalFamily_from_audited_generated_certificates_and_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : CriticalDiskZoneConsequences cand)
    (i : Fin 6)
    (hiota :
      CriticalDiskHypotheses (cand.iotaInner (faceDiagonalReflectionSymmetry i))) :
    CriticalDiskExclusion (cand.iotaInner (faceDiagonalReflectionSymmetry i)) :=
  critical_disk_exclusion_of_faceDiagonalFamily
    (critical_disk_assembly_faceDiagonalFamily_from_audited_generated_certificates_and_zones
      audit sfCert sbPointwise zones)
    i hiota

/-- Conditional Lemma 6' directly from audited generated obligations when Zones B/C are supplied
in their angle-consequence form. -/
theorem critical_disk_assembly_from_audited_generated_certificates_and_angle_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand) :
    CriticalDiskLemma6PrimeStatement cand :=
  critical_disk_assembly_from_audited_generated_certificates audit sfCert sbPointwise
    (CriticalDiskLemma6PrimeCertificate.ofAngleConsequences
      zone0 zoneA zoneB zoneC zoneD)

/-- Direct exclusion from audited generated obligations when Zones B/C are supplied in their
angle-consequence form. -/
theorem critical_disk_exclusion_from_audited_generated_certificates_and_angle_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
    (auditedGeneratedSoundness_of_audit_and_certificates
      audit sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zone0 zoneA zoneB zoneC zoneD hcand

/-- Localized exclusion from audited generated obligations when Zones B/C are supplied in their
angle-consequence form. -/
theorem critical_disk_localized_exclusion_from_audited_generated_certificates_and_angle_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (analytics : CriticalDiskAnalyticInputs)
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zone0 :
      CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point → CriticalDiskExclusion cand)
    (zoneA :
      CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point → CriticalDiskExclusion cand)
    (zoneB : ZoneBAngleConsequence cand EB)
    (zoneC : ZoneCAngleConsequence cand EC)
    (zoneD :
      CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point → CriticalDiskExclusion cand) :
    CriticalDiskLocalizedExclusionStatement cand :=
  critical_disk_localized_exclusion_from_audited_generated_soundness analytics
    (auditedGeneratedSoundness_of_audit_and_certificates audit sfCert sbPointwise)
    (CriticalDiskLemma6PrimeCertificate.ofAngleConsequences
      zone0 zoneA zoneB zoneC zoneD)

/-- Transported conditional Lemma 6' directly from audited generated obligations and B/C angle
consequences. -/
theorem critical_disk_assembly_iotaInner_from_audited_generated_certificates_and_angle_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
    (auditedGeneratedSoundness_of_audit_and_certificates
      audit sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zone0 zoneA zoneB zoneC zoneD S

/-- Direct transported exclusion from audited generated obligations and B/C angle consequences. -/
theorem critical_disk_exclusion_iotaInner_from_audited_generated_certificates_and_angle_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
    (auditedGeneratedSoundness_of_audit_and_certificates
      audit sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zone0 zoneA zoneB zoneC zoneD S hiota

/-- Localized transported exclusion directly from audited generated obligations and B/C angle
consequences. -/
theorem critical_disk_localized_exclusion_iotaInner_from_audited_generated_certificates_and_angle_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (analytics : CriticalDiskAnalyticInputs)
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
  critical_disk_localized_exclusion_iotaInner_from_audited_generated_soundness analytics
    (auditedGeneratedSoundness_of_audit_and_certificates audit sfCert sbPointwise)
    (CriticalDiskLemma6PrimeCertificate.ofAngleConsequences
      zone0 zoneA zoneB zoneC zoneD) S

/-- One face-diagonal conditional Lemma 6' directly from audited generated obligations and B/C
angle consequences. -/
theorem critical_disk_assembly_faceDiagonal_from_audited_generated_certificates_and_angle_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
    (auditedGeneratedSoundness_of_audit_and_certificates
      audit sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zone0 zoneA zoneB zoneC zoneD i

/-- Direct one-face-diagonal exclusion from audited generated obligations and B/C angle
consequences. -/
theorem critical_disk_exclusion_faceDiagonal_from_audited_generated_certificates_and_angle_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
    (auditedGeneratedSoundness_of_audit_and_certificates
      audit sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zone0 zoneA zoneB zoneC zoneD i hiota

/-- Packaged all-six Lemma 6' directly from audited generated obligations and B/C angle
consequences. -/
theorem critical_disk_assembly_faceDiagonalFamily_from_audited_generated_certificates_and_angle_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
    (auditedGeneratedSoundness_of_audit_and_certificates
      audit sfCert sbPointwise).toCriticalDiskInputs_allCertified
    zone0 zoneA zoneB zoneC zoneD

/-- All-six localized face-diagonal conclusion from audited generated certificates when Zones B/C
are supplied in angle-consequence form. -/
theorem
    critical_disk_localized_exclusion_faceDiagonalFamily_from_audited_generated_certificates_and_angle_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (analytics : CriticalDiskAnalyticInputs)
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
    (auditedGeneratedSoundness_of_audit_and_certificates
      audit sfCert sbPointwise).toCriticalDiskInputs_allCertified

/-- Direct indexed localized exclusion from audited generated certificates and B/C angle
consequences. -/
theorem
    critical_disk_localized_exclusion_faceDiagonal_from_audited_generated_certificates_and_angle_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (analytics : CriticalDiskAnalyticInputs)
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
    (critical_disk_localized_exclusion_faceDiagonalFamily_from_audited_generated_certificates_and_angle_zones
      analytics audit sfCert sbPointwise zone0 zoneA zoneB zoneC zoneD)
    i hiota

/-- Apply the audited generated-obligations-and-angle-zones all-six family at one face-diagonal
reflected sheet. -/
theorem critical_disk_exclusion_faceDiagonalFamily_from_audited_generated_certificates_and_angle_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
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
    (critical_disk_assembly_faceDiagonalFamily_from_audited_generated_certificates_and_angle_zones
      audit sfCert sbPointwise zone0 zoneA zoneB zoneC zoneD)
    i hiota

@[reducible] def noGeneratedRootAuditedSoundness (rhoF : ℝ) :
    IsEmpty
      (AuditedGeneratedSoundness rhoF
        generatedPhiRootDomain generatedUnitDomain generatedUnitDomain) where
  false := by
    intro soundness
    exact generated_rootDomain_no_standardAuditedSweepSoundness rhoF |>.false soundness.sf

/-- The current generated root-domain artifact cannot supply an audited local certificate.
The SF root cover misses the origin, so the audited sweep layer is impossible before the
certificate payload is regenerated or the root domain is split. -/
@[reducible] def noGeneratedRootAuditedLocalCertificate
    (rhoF : ℝ) (cand : CriticalDiskCandidate) :
    IsEmpty
      (AuditedGeneratedLocalCertificate rhoF
        generatedPhiRootDomain generatedUnitDomain generatedUnitDomain cand) where
  false := by
    intro cert
    exact noGeneratedRootAuditedSoundness rhoF |>.false cert.soundness

end GeneratedCriticalDiskInputs

end RupertStellatedTetrahedron
