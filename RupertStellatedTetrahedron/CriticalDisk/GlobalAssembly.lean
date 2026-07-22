import RupertStellatedTetrahedron.CriticalDisk.Generated.CriticalDiskInputs

/-!
## Global assembly boundary

The draft's remaining global obligations are not hidden inside the critical-disk certificate.  They
are a separate finite cover: far region, near-critical disks, and the off-diagonal/Zeng bridge.
This module records that interface and proves the final logical assembly once those external
regions are certified.
-/

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

open DepthCylinderTheorem
open GeneratedCriticalDiskInputs

/-- A concrete configuration of the stellated tetrahedron. -/
abbrev StellatedConfig :=
  Config stellatedVertices

/-- Global non-Rupertness statement for the fixed stellated tetrahedron. -/
def StellatedNonRupertStatement : Prop :=
  ∀ c : StellatedConfig, ¬ RupertContainment stellatedVertices c

/-- The remaining global cover obligations from draft §17.

`FarRegion` is the certified cover away from the six critical disks.  `OffDiagonalRegion` is the
intermediate collar/Zeng-interface branch.  The near-critical branch must produce a
`CriticalDiskCandidate` whose concrete configuration is the configuration being classified. -/
structure StellatedGlobalCover where
  FarRegion : StellatedConfig → Prop
  OffDiagonalRegion : StellatedConfig → Prop
  trichotomy :
    ∀ c : StellatedConfig,
      FarRegion c ∨
        (∃ cand : CriticalDiskCandidate, c = cand.config ∧ CriticalDiskHypotheses cand) ∨
          OffDiagonalRegion c

theorem StellatedGlobalCover.nearCritical_of_not_far_not_offDiagonal
    (cover : StellatedGlobalCover)
    {c : StellatedConfig}
    (hfar : ¬ cover.FarRegion c)
    (hoff : ¬ cover.OffDiagonalRegion c) :
    ∃ cand : CriticalDiskCandidate, c = cand.config ∧ CriticalDiskHypotheses cand := by
  rcases cover.trichotomy c with hfar' | hnearOrOff
  · exact False.elim (hfar hfar')
  · rcases hnearOrOff with hnear | hoff'
    · exact hnear
    · exact False.elim (hoff hoff')

/-- Exclusion payloads for the far and off-diagonal branches of the global cover. -/
structure StellatedFarOffDiagonalCertificate (cover : StellatedGlobalCover) where
  farExcludes :
    ∀ {c : StellatedConfig}, cover.FarRegion c → ¬ RupertContainment stellatedVertices c
  offDiagonalExcludes :
    ∀ {c : StellatedConfig}, cover.OffDiagonalRegion c →
      ¬ RupertContainment stellatedVertices c

def StellatedFarOffDiagonalCertificate.ofExclusions
    {cover : StellatedGlobalCover}
    (farExcludes :
      ∀ {c : StellatedConfig}, cover.FarRegion c → ¬ RupertContainment stellatedVertices c)
    (offDiagonalExcludes :
      ∀ {c : StellatedConfig}, cover.OffDiagonalRegion c →
        ¬ RupertContainment stellatedVertices c) :
    StellatedFarOffDiagonalCertificate cover where
  farExcludes := farExcludes
  offDiagonalExcludes := offDiagonalExcludes

/-- A local critical-disk family strong enough for the global trichotomy. -/
def CriticalDiskLemma6PrimeGlobalFamily : Prop :=
  ∀ cand : CriticalDiskCandidate, CriticalDiskLemma6PrimeStatement cand

/-- One object containing all data needed for the final global non-Rupert statement. -/
structure StellatedGlobalCertificate where
  cover : StellatedGlobalCover
  farOff : StellatedFarOffDiagonalCertificate cover
  localFamily : CriticalDiskLemma6PrimeGlobalFamily

def StellatedGlobalCertificate.ofLocalFamily
    (cover : StellatedGlobalCover)
    (farOff : StellatedFarOffDiagonalCertificate cover)
    (localFamily : CriticalDiskLemma6PrimeGlobalFamily) :
    StellatedGlobalCertificate where
  cover := cover
  farOff := farOff
  localFamily := localFamily

/-- Global assembly from an explicit trichotomy, far/off-diagonal exclusions, and Lemma 6' on
every near-critical candidate emitted by the trichotomy. -/
theorem stellated_nonRupert_of_global_cover
    (cover : StellatedGlobalCover)
    (farOff : StellatedFarOffDiagonalCertificate cover)
    (localFamily : CriticalDiskLemma6PrimeGlobalFamily) :
    StellatedNonRupertStatement := by
  intro c
  rcases cover.trichotomy c with hfar | hnearOrOff
  · exact farOff.farExcludes hfar
  · rcases hnearOrOff with hnear | hoff
    · rcases hnear with ⟨cand, hc, hcand⟩
      subst c
      exact localFamily cand hcand
    · exact farOff.offDiagonalExcludes hoff

theorem stellated_nonRupert_of_branch_exclusions
    (cover : StellatedGlobalCover)
    (farExcludes :
      ∀ {c : StellatedConfig}, cover.FarRegion c → ¬ RupertContainment stellatedVertices c)
    (nearExcludes :
      ∀ cand : CriticalDiskCandidate, CriticalDiskHypotheses cand →
        ¬ RupertContainment stellatedVertices cand.config)
    (offDiagonalExcludes :
      ∀ {c : StellatedConfig}, cover.OffDiagonalRegion c →
        ¬ RupertContainment stellatedVertices c) :
    StellatedNonRupertStatement := by
  intro c
  rcases cover.trichotomy c with hfar | hnearOrOff
  · exact farExcludes hfar
  · rcases hnearOrOff with hnear | hoff
    · rcases hnear with ⟨cand, hc, hcand⟩
      subst c
      exact nearExcludes cand hcand
    · exact offDiagonalExcludes hoff

/-- Final theorem from the packaged global certificate. -/
theorem StellatedGlobalCertificate.nonRupert
    (cert : StellatedGlobalCertificate) :
    StellatedNonRupertStatement :=
  stellated_nonRupert_of_global_cover cert.cover cert.farOff cert.localFamily

theorem StellatedGlobalCertificate.excludes
    (cert : StellatedGlobalCertificate)
    (c : StellatedConfig) :
    ¬ RupertContainment stellatedVertices c :=
  cert.nonRupert c

theorem StellatedGlobalCertificate.false_of_containment
    (cert : StellatedGlobalCertificate)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    False :=
  cert.excludes c hcont

theorem StellatedGlobalCertificate.excludesFar
    (cert : StellatedGlobalCertificate)
    {c : StellatedConfig}
    (hfar : cert.cover.FarRegion c) :
    ¬ RupertContainment stellatedVertices c :=
  cert.farOff.farExcludes hfar

theorem StellatedGlobalCertificate.excludesOffDiagonal
    (cert : StellatedGlobalCertificate)
    {c : StellatedConfig}
    (hoff : cert.cover.OffDiagonalRegion c) :
    ¬ RupertContainment stellatedVertices c :=
  cert.farOff.offDiagonalExcludes hoff

theorem StellatedGlobalCertificate.trichotomy
    (cert : StellatedGlobalCertificate)
    (c : StellatedConfig) :
    cert.cover.FarRegion c ∨
      (∃ cand : CriticalDiskCandidate, c = cand.config ∧ CriticalDiskHypotheses cand) ∨
        cert.cover.OffDiagonalRegion c :=
  cert.cover.trichotomy c

theorem StellatedGlobalCertificate.excludesNearCritical
    (cert : StellatedGlobalCertificate)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  cert.localFamily cand hcand

theorem StellatedGlobalCertificate.notFar_of_containment
    (cert : StellatedGlobalCertificate)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    ¬ cert.cover.FarRegion c := by
  intro hfar
  exact cert.excludesFar hfar hcont

theorem StellatedGlobalCertificate.notOffDiagonal_of_containment
    (cert : StellatedGlobalCertificate)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    ¬ cert.cover.OffDiagonalRegion c := by
  intro hoff
  exact cert.excludesOffDiagonal hoff hcont

theorem StellatedGlobalCertificate.nearCritical_of_containment
    (cert : StellatedGlobalCertificate)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    ∃ cand : CriticalDiskCandidate, c = cand.config ∧ CriticalDiskHypotheses cand :=
  cert.cover.nearCritical_of_not_far_not_offDiagonal
    (cert.notFar_of_containment hcont)
    (cert.notOffDiagonal_of_containment hcont)

theorem StellatedGlobalCertificate.excludesNearCriticalConfig
    (cert : StellatedGlobalCertificate)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand) :
    ¬ RupertContainment stellatedVertices cand.config :=
  cert.excludesNearCritical cand hcand

theorem StellatedGlobalCertificate.excludes_of_not_far_not_offDiagonal
    (cert : StellatedGlobalCertificate)
    {c : StellatedConfig}
    (hfar : ¬ cert.cover.FarRegion c)
    (hoff : ¬ cert.cover.OffDiagonalRegion c) :
    ¬ RupertContainment stellatedVertices c := by
  obtain ⟨cand, hc, hcand⟩ :=
    cert.cover.nearCritical_of_not_far_not_offDiagonal hfar hoff
  subst c
  exact cert.excludesNearCriticalConfig cand hcand

/-- A generated local certificate family, separating the common generated `(SF)`/`(SB-box)`
soundness from the candidate-dependent zone consequences. -/
structure StandardGeneratedGlobalLocalCertificate (rhoF : ℝ) where
  soundness : StandardGeneratedSoundness rhoF
  zones : ∀ cand : CriticalDiskCandidate, CriticalDiskZoneConsequences cand

def StandardGeneratedGlobalLocalCertificate.localCertificate
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF)
    (cand : CriticalDiskCandidate) :
    StandardGeneratedLocalCertificate rhoF cand where
  soundness := cert.soundness
  zones := cert.zones cand

theorem StandardGeneratedGlobalLocalCertificate.localFamily
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF) :
    CriticalDiskLemma6PrimeGlobalFamily := by
  intro cand
  exact (cert.localCertificate cand).lemma6prime

theorem StandardGeneratedGlobalLocalCertificate.sfCertifiedRowsValid
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF) :
    GeneratedSFWitness.manifest.CertifiedRowsValid
      GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  cert.soundness.sfCertifiedRowsValid

theorem StandardGeneratedGlobalLocalCertificate.sfCertifiedRowValid
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF)
    {row : SFCertifiedSweepRow}
    (hrow : row ∈ GeneratedSFWitness.manifest.certified) :
    row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  cert.soundness.sfCertifiedRowValid hrow

theorem StandardGeneratedGlobalLocalCertificate.sbBoxReplayAssemblyValid
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF) :
    SBBoxReplayAssembly
      GeneratedSBBoxTailWitness.manifest GeneratedSBBoxBulkWitness.manifest
      GeneratedSBBoxAssemblyReport.report
      GeneratedSBBoxAssemblyReport.tailDomain
      GeneratedSBBoxAssemblyReport.bulkDeltaDomain
      GeneratedSBBoxAssemblyReport.bulkPhiDomain
      GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxReplayAssemblyValid

theorem StandardGeneratedGlobalLocalCertificate.sbBoxTailRowsValid
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF) :
    GeneratedSBBoxTailWitness.manifest.RowsValid :=
  cert.soundness.sbBoxTailRowsValid

theorem StandardGeneratedGlobalLocalCertificate.sbBoxBulkRowsValid
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF) :
    GeneratedSBBoxBulkWitness.manifest.RowsValid
      GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxBulkRowsValid

theorem StandardGeneratedGlobalLocalCertificate.sbBoxTailRowValid
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF)
    {row : SBBoxTailRow}
    (hrow : row ∈ GeneratedSBBoxTailWitness.manifest.rows) :
    row.Valid :=
  cert.soundness.sbBoxTailRowValid hrow

theorem StandardGeneratedGlobalLocalCertificate.sbBoxBulkRowValid
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF)
    {row : SBBoxBulkRow}
    (hrow : row ∈ GeneratedSBBoxBulkWitness.manifest.rows) :
    row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxBulkRowValid hrow

theorem StandardGeneratedGlobalLocalCertificate.sbBoxTailExistsValidRow
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF)
    (chart : SBBoxTailChart) {r : ℝ}
    (hr : GeneratedSBBoxAssemblyReport.tailDomain.contains r) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains r ∧ row.Valid :=
  cert.soundness.sbBoxTailExistsValidRow chart hr

theorem StandardGeneratedGlobalLocalCertificate.sbBoxBulkExistsValidRow
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF)
    {delta phi : ℝ}
    (hdelta : GeneratedSBBoxAssemblyReport.bulkDeltaDomain.contains delta)
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains delta ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxBulkExistsValidRow hdelta hphi

theorem StandardGeneratedGlobalLocalCertificate.sbBoxTailExistsValidRowAtZero
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF)
    (chart : SBBoxTailChart) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains (0 : ℝ) ∧ row.Valid :=
  cert.soundness.sbBoxTailExistsValidRowAtZero chart

theorem StandardGeneratedGlobalLocalCertificate.sbBoxTailExistsValidRowAtOne
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF)
    (chart : SBBoxTailChart) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains (1 : ℝ) ∧ row.Valid :=
  cert.soundness.sbBoxTailExistsValidRowAtOne chart

theorem StandardGeneratedGlobalLocalCertificate.sbBoxBulkExistsValidRowAtTailCut
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF)
    {phi : ℝ}
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskTailCut ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxBulkExistsValidRowAtTailCut hphi

theorem StandardGeneratedGlobalLocalCertificate.sbBoxBulkExistsValidRowAtRhoCap
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF)
    {phi : ℝ}
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskRhoCap ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxBulkExistsValidRowAtRhoCap hphi

theorem StandardGeneratedGlobalLocalCertificate.sbBoxBulkExistsValidRowAtTailCutZeroPhi
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskTailCut ∧ row.phi.contains (0 : ℝ) ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxBulkExistsValidRowAtTailCutZeroPhi

theorem StandardGeneratedGlobalLocalCertificate.sbBoxBulkExistsValidRowAtRhoCapZeroPhi
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskRhoCap ∧ row.phi.contains (0 : ℝ) ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxBulkExistsValidRowAtRhoCapZeroPhi

def StandardGeneratedGlobalLocalCertificate.sbBoxPointCertificate
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF)
    (hcand : CriticalDiskHypotheses cand) :
    SBBoxPointCertificate cand.R₂ cand.delta
      cert.soundness.toCriticalDiskInputs.sbBox.bPi
      cert.soundness.toCriticalDiskInputs.sbBox.bGamma
      cert.soundness.toCriticalDiskInputs.sbBox.bT :=
  cert.soundness.sbBoxPointCertificate hcand

def StandardGeneratedGlobalLocalCertificate.sbBoxInclusion
    {rhoF : ℝ} {cand : CriticalDiskCandidate}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF)
    (hcand : CriticalDiskHypotheses cand) :
    DepthCylinderTheorem.BoxInclusionCertificate
      (cert.sbBoxPointCertificate hcand).cert :=
  cert.soundness.sbBoxInclusion hcand

theorem StandardGeneratedGlobalLocalCertificate.sfCovers
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF)
    {φ s : ℝ}
    (hφlo : -Real.pi ≤ φ) (hφhi : φ ≤ Real.pi)
    (hslo : 0 ≤ s) (hshi : s ≤ 1) :
    ∃ c : cert.soundness.toCriticalDiskInputs.sf.certificate.chart,
      cert.soundness.toCriticalDiskInputs.sf.certificate.inChart c φ s :=
  cert.soundness.sfCovers hφlo hφhi hslo hshi

theorem StandardGeneratedGlobalLocalCertificate.sfChartClassified
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF)
    (c : cert.soundness.toCriticalDiskInputs.sf.certificate.chart) :
    cert.soundness.toCriticalDiskInputs.sf.certificate.isShell c ∨
      cert.soundness.toCriticalDiskInputs.sf.certificate.isBulk c :=
  cert.soundness.sfChartClassified c

theorem StandardGeneratedGlobalLocalCertificate.sfCornerDistLower_nonneg
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF)
    (c : cert.soundness.toCriticalDiskInputs.sf.certificate.chart) :
    0 ≤ cert.soundness.toCriticalDiskInputs.sf.certificate.cornerDistLower c :=
  cert.soundness.sfCornerDistLower_nonneg c

theorem StandardGeneratedGlobalLocalCertificate.sfShellBound
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF)
    (c : cert.soundness.toCriticalDiskInputs.sf.certificate.chart)
    (hc : cert.soundness.toCriticalDiskInputs.sf.certificate.isShell c) :
    cert.soundness.toCriticalDiskInputs.sf.shellSlope *
        cert.soundness.toCriticalDiskInputs.sf.certificate.cornerDistLower c ≤
      cert.soundness.toCriticalDiskInputs.sf.certificate.psiLower c :=
  cert.soundness.sfShellBound c hc

theorem StandardGeneratedGlobalLocalCertificate.sfBulkBound
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF)
    (c : cert.soundness.toCriticalDiskInputs.sf.certificate.chart)
    (hc : cert.soundness.toCriticalDiskInputs.sf.certificate.isBulk c) :
    cert.soundness.toCriticalDiskInputs.sf.psiMin ≤
      cert.soundness.toCriticalDiskInputs.sf.certificate.psiLower c :=
  cert.soundness.sfBulkBound c hc

def StandardGeneratedGlobalLocalCertificate.toGlobalCertificate
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalLocalCertificate rhoF)
    (cover : StellatedGlobalCover)
    (farOff : StellatedFarOffDiagonalCertificate cover) :
    StellatedGlobalCertificate :=
  StellatedGlobalCertificate.ofLocalFamily cover farOff cert.localFamily

/-- Final global assembly from standard generated local certificates plus the remaining
far/off-diagonal cover certificate. -/
theorem stellated_nonRupert_of_standard_generated_global_certificate
    {rhoF : ℝ}
    (cover : StellatedGlobalCover)
    (farOff : StellatedFarOffDiagonalCertificate cover)
    (localCert : StandardGeneratedGlobalLocalCertificate rhoF) :
    StellatedNonRupertStatement :=
  stellated_nonRupert_of_global_cover cover farOff localCert.localFamily

/-- The raw-obligation constructor for the standard generated global-local certificate. -/
def standardGeneratedGlobalLocalCertificate_of_certificates_and_zones
    {rhoF : ℝ}
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : ∀ cand : CriticalDiskCandidate, CriticalDiskZoneConsequences cand) :
    StandardGeneratedGlobalLocalCertificate rhoF where
  soundness := standardGeneratedSoundness_of_certificates sfCert sbPointwise
  zones := zones

/-- Final global assembly directly from the two standard generated semantic obligations, all
candidate zone consequences, and the far/off-diagonal cover certificate. -/
theorem stellated_nonRupert_of_generated_certificates_and_global_cover
    {rhoF : ℝ}
    (cover : StellatedGlobalCover)
    (farOff : StellatedFarOffDiagonalCertificate cover)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : ∀ cand : CriticalDiskCandidate, CriticalDiskZoneConsequences cand) :
    StellatedNonRupertStatement :=
  stellated_nonRupert_of_standard_generated_global_certificate cover farOff
    (standardGeneratedGlobalLocalCertificate_of_certificates_and_zones
      sfCert sbPointwise zones)

/-- Pack the final standard-generated global certificate once the far/off-diagonal cover and all
candidate zone consequences are supplied. -/
def stellatedGlobalCertificate_of_generated_certificates_and_global_cover
    {rhoF : ℝ}
    (cover : StellatedGlobalCover)
    (farOff : StellatedFarOffDiagonalCertificate cover)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : ∀ cand : CriticalDiskCandidate, CriticalDiskZoneConsequences cand) :
    StellatedGlobalCertificate :=
  (standardGeneratedGlobalLocalCertificate_of_certificates_and_zones
      sfCert sbPointwise zones).toGlobalCertificate cover farOff

theorem stellatedGlobalCertificate_of_generated_certificates_nonRupert
    {rhoF : ℝ}
    (cover : StellatedGlobalCover)
    (farOff : StellatedFarOffDiagonalCertificate cover)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : ∀ cand : CriticalDiskCandidate, CriticalDiskZoneConsequences cand) :
    (stellatedGlobalCertificate_of_generated_certificates_and_global_cover
      cover farOff sfCert sbPointwise zones).nonRupert =
      stellated_nonRupert_of_generated_certificates_and_global_cover
        cover farOff sfCert sbPointwise zones :=
  rfl

/-- Fully packaged standard generated route to the final global theorem.  This is the Lean object
left after supplying the standard semantic `(SF)` certificate, pointwise `(SB-box)`, all critical
zone consequences, and the far/off-diagonal global cover. -/
structure StandardGeneratedGlobalCertificate (rhoF : ℝ) where
  localCert : StandardGeneratedGlobalLocalCertificate rhoF
  cover : StellatedGlobalCover
  farOff : StellatedFarOffDiagonalCertificate cover

def StandardGeneratedGlobalCertificate.toGlobalCertificate
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalCertificate rhoF) :
    StellatedGlobalCertificate :=
  cert.localCert.toGlobalCertificate cert.cover cert.farOff

theorem StandardGeneratedGlobalCertificate.nonRupert
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalCertificate rhoF) :
    StellatedNonRupertStatement :=
  cert.toGlobalCertificate.nonRupert

theorem StandardGeneratedGlobalCertificate.excludes
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalCertificate rhoF)
    (c : StellatedConfig) :
    ¬ RupertContainment stellatedVertices c :=
  cert.nonRupert c

theorem StandardGeneratedGlobalCertificate.excludesNearCritical
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalCertificate rhoF)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  cert.toGlobalCertificate.excludesNearCritical cand hcand

theorem StandardGeneratedGlobalCertificate.sfCertifiedRowsValid
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalCertificate rhoF) :
    GeneratedSFWitness.manifest.CertifiedRowsValid
      GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  cert.localCert.sfCertifiedRowsValid

theorem StandardGeneratedGlobalCertificate.sbBoxReplayAssemblyValid
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalCertificate rhoF) :
    SBBoxReplayAssembly
      GeneratedSBBoxTailWitness.manifest GeneratedSBBoxBulkWitness.manifest
      GeneratedSBBoxAssemblyReport.report
      GeneratedSBBoxAssemblyReport.tailDomain
      GeneratedSBBoxAssemblyReport.bulkDeltaDomain
      GeneratedSBBoxAssemblyReport.bulkPhiDomain
      GeneratedSBBoxBulkWitness.etaBudget :=
  cert.localCert.sbBoxReplayAssemblyValid

def standardGeneratedGlobalCertificate_of_certificates_and_zones
    {rhoF : ℝ}
    (cover : StellatedGlobalCover)
    (farOff : StellatedFarOffDiagonalCertificate cover)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : ∀ cand : CriticalDiskCandidate, CriticalDiskZoneConsequences cand) :
    StandardGeneratedGlobalCertificate rhoF where
  localCert := standardGeneratedGlobalLocalCertificate_of_certificates_and_zones
    sfCert sbPointwise zones
  cover := cover
  farOff := farOff

/-- The standard generated route expressed as the actual remaining proof obligations:
semantic `(SF)`, pointwise `(SB-box)`, all near-critical zone consequences, and the final
far/off-diagonal global cover. -/
structure StandardGeneratedRemainingObligations (rhoF : ℝ) where
  sfSemantic : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF
  sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness
  zoneConsequences : ∀ cand : CriticalDiskCandidate, CriticalDiskZoneConsequences cand
  globalCover : StellatedGlobalCover
  farOffDiagonal : StellatedFarOffDiagonalCertificate globalCover

abbrev StellatedSBBoxPointwiseBridge :=
  GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness

abbrev StellatedSBBoxReplayObligation :=
  SBBoxReplayAssembly
    GeneratedSBBoxTailWitness.manifest GeneratedSBBoxBulkWitness.manifest
    GeneratedSBBoxAssemblyReport.report
    GeneratedSBBoxAssemblyReport.tailDomain
    GeneratedSBBoxAssemblyReport.bulkDeltaDomain
    GeneratedSBBoxAssemblyReport.bulkPhiDomain
    GeneratedSBBoxBulkWitness.etaBudget

abbrev StellatedSBBoxTailReplayObligation :=
  GeneratedSBBoxTailWitness.manifest.RowsValid

abbrev StellatedSBBoxBulkReplayObligation :=
  GeneratedSBBoxBulkWitness.manifest.RowsValid
    GeneratedSBBoxBulkWitness.etaBudget

abbrev StellatedSBBoxObligation :=
  StellatedSBBoxPointwiseBridge

abbrev StellatedSFSemanticBridge (rhoF : ℝ) :=
  GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF

abbrev StellatedSFReplayObligation :=
  GeneratedSFWitness.manifest.CertifiedRowsValid
    GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap

abbrev StellatedSFObligation (rhoF : ℝ) :=
  StellatedSFSemanticBridge rhoF

abbrev StellatedNearCriticalObligation :=
  ∀ cand : CriticalDiskCandidate, CriticalDiskZoneConsequences cand

def stellatedNearCriticalObligation_ofUniformAngleConsequences
    {EB EC : Type*} [SeminormedAddCommGroup EB] [SeminormedAddCommGroup EC]
    (zone0 :
      ∀ cand : CriticalDiskCandidate,
        CriticalDiskHypotheses cand → CriticalDiskZone0 cand.point →
          CriticalDiskExclusion cand)
    (zoneA :
      ∀ cand : CriticalDiskCandidate,
        CriticalDiskHypotheses cand → CriticalDiskZoneA cand.point →
          CriticalDiskExclusion cand)
    (zoneB : ∀ cand : CriticalDiskCandidate, ZoneBAngleConsequence cand EB)
    (zoneC : ∀ cand : CriticalDiskCandidate, ZoneCAngleConsequence cand EC)
    (zoneD :
      ∀ cand : CriticalDiskCandidate,
        CriticalDiskHypotheses cand → CriticalDiskZoneD cand.point →
          CriticalDiskExclusion cand) :
    StellatedNearCriticalObligation :=
  fun cand =>
    CriticalDiskZoneConsequences.ofAngleConsequences
      (zone0 cand) (zoneA cand) (zoneB cand) (zoneC cand) (zoneD cand)

abbrev StellatedGlobalCoverObligation :=
  StellatedGlobalCover

abbrev StellatedFarOffDiagonalObligation (cover : StellatedGlobalCoverObligation) :=
  StellatedFarOffDiagonalCertificate cover

abbrev StellatedFarExclusionObligation (cover : StellatedGlobalCoverObligation) :=
  ∀ {c : StellatedConfig}, cover.FarRegion c → ¬ RupertContainment stellatedVertices c

abbrev StellatedOffDiagonalExclusionObligation
    (cover : StellatedGlobalCoverObligation) :=
  ∀ {c : StellatedConfig}, cover.OffDiagonalRegion c →
    ¬ RupertContainment stellatedVertices c

/-- Draft §17 §17 items 4 and 5 as branch-level global payloads.  The `cover` field is the
far/near/off-diagonal trichotomy; the two exclusion fields are the certified far-region exclusion
and the Zeng/off-diagonal interface exclusion. -/
structure StellatedGlobalBranchObligations where
  cover : StellatedGlobalCoverObligation
  farExcludes : StellatedFarExclusionObligation cover
  offDiagonalExcludes : StellatedOffDiagonalExclusionObligation cover

def StellatedGlobalBranchObligations.toFarOffDiagonal
    (global : StellatedGlobalBranchObligations) :
    StellatedFarOffDiagonalObligation global.cover :=
  StellatedFarOffDiagonalCertificate.ofExclusions
    global.farExcludes global.offDiagonalExcludes

def StellatedGlobalBranchObligations.toGlobalCertificate
    (global : StellatedGlobalBranchObligations)
    (localFamily : CriticalDiskLemma6PrimeGlobalFamily) :
    StellatedGlobalCertificate :=
  StellatedGlobalCertificate.ofLocalFamily
    global.cover global.toFarOffDiagonal localFamily

theorem StellatedGlobalBranchObligations.nonRupert_of_localFamily
    (global : StellatedGlobalBranchObligations)
    (localFamily : CriticalDiskLemma6PrimeGlobalFamily) :
    StellatedNonRupertStatement :=
  (global.toGlobalCertificate localFamily).nonRupert

theorem StellatedGlobalBranchObligations.trichotomy
    (global : StellatedGlobalBranchObligations)
    (c : StellatedConfig) :
    global.cover.FarRegion c ∨
      (∃ cand : CriticalDiskCandidate, c = cand.config ∧ CriticalDiskHypotheses cand) ∨
        global.cover.OffDiagonalRegion c :=
  global.cover.trichotomy c

/-- The generated `(SB-box)` replay facts that are already checked before the remaining
pointwise bridge is supplied.  This separates §17's replay/tile obligations from the final
semantic pointwise inclusion obligation. -/
structure StellatedSBBoxReplayEvidence where
  replay : StellatedSBBoxReplayObligation
  tailRows : StellatedSBBoxTailReplayObligation
  bulkRows : StellatedSBBoxBulkReplayObligation
  tailCover :
    ∀ (chart : SBBoxTailChart) {r : ℝ},
      GeneratedSBBoxAssemblyReport.tailDomain.contains r →
        ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
          row.chart = chart ∧ row.r.contains r ∧ row.Valid
  bulkCover :
    ∀ {delta phi : ℝ},
      GeneratedSBBoxAssemblyReport.bulkDeltaDomain.contains delta →
        GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi →
          ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
            row.delta.contains delta ∧ row.phi.contains phi ∧
              row.Valid GeneratedSBBoxBulkWitness.etaBudget
  interfaceValid : GeneratedSBBoxAssemblyReport.report.InterfaceValid
  omittedTailFailRows_eq : GeneratedSBBoxTailWitness.omittedFailRows = 40

def stellatedGeneratedSBBoxReplayEvidence : StellatedSBBoxReplayEvidence where
  replay := GeneratedSBBoxCertifiedInput.replayAssembly
  tailRows := GeneratedSBBoxCertifiedInput.tailRowsValid
  bulkRows := GeneratedSBBoxCertifiedInput.bulkRowsValid
  tailCover := GeneratedSBBoxCertifiedInput.tail_exists_valid_row
  bulkCover := GeneratedSBBoxCertifiedInput.bulk_exists_valid_row
  interfaceValid := GeneratedSBBoxCertifiedInput.interfaceValid
  omittedTailFailRows_eq := GeneratedSBBoxCertifiedInput.omittedTailFailRows_eq

/-- The generated `(SF)` row replay facts that are already checked.  The standard semantic
certificate is deliberately separate because the generated replay floor is lower than the
critical-disk `(SF)` bulk floor. -/
structure StellatedSFReplayEvidence where
  certifiedRows_length : GeneratedSFWitness.certifiedRows.length = 566
  deferredRows_length : GeneratedSFWitness.deferredRows.length = 48
  certifiedRows : StellatedSFReplayObligation
  certifiedRow :
    ∀ {row : SFCertifiedSweepRow},
      row ∈ GeneratedSFWitness.manifest.certified →
        row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap
  generatedStressFloor_lt_standardBulkFloor :
    (GeneratedSFWitness.psiMin : ℝ) < criticalDiskPsiMin

def stellatedGeneratedSFReplayEvidence : StellatedSFReplayEvidence where
  certifiedRows_length := GeneratedSFCertifiedInput.certifiedRows_length
  deferredRows_length := GeneratedSFCertifiedInput.deferredRows_length
  certifiedRows := GeneratedSFCertifiedInput.certifiedRowsValid
  certifiedRow := GeneratedSFCertifiedInput.certified_row_valid
  generatedStressFloor_lt_standardBulkFloor :=
    GeneratedSFCertifiedInput.generatedStressFloor_lt_standardBulkFloor

/-- Draft §17 §17, items 1-5, as a named standard-route Lean target.

Items 1 and 2 have generated replay evidence available separately; the `sbBox` field is the
remaining pointwise `(SB-box)` bridge from replay rows to semantic box-inclusion certificates.
Item 3 has generated row replay evidence available separately; the `sf` field is the semantic
`(SF)` bridge with the standard critical-disk constants.  The near-critical zone consequences
connect those two local certificates to Lemma 6'.  The last two fields are the far/off-diagonal
trichotomy and exclusion payloads. -/
structure StellatedStandardPlanObligations (rhoF : ℝ) where
  sbBox : StellatedSBBoxObligation
  sf : StellatedSFObligation rhoF
  zones : StellatedNearCriticalObligation
  cover : StellatedGlobalCoverObligation
  farOff : StellatedFarOffDiagonalObligation cover

def StellatedStandardPlanObligations.toRemainingObligations
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    StandardGeneratedRemainingObligations rhoF where
  sfSemantic := plan.sf
  sbPointwise := plan.sbBox
  zoneConsequences := plan.zones
  globalCover := plan.cover
  farOffDiagonal := plan.farOff

def StandardGeneratedRemainingObligations.toStellatedPlanObligations
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF) :
    StellatedStandardPlanObligations rhoF where
  sbBox := obligations.sbPointwise
  sf := obligations.sfSemantic
  zones := obligations.zoneConsequences
  cover := obligations.globalCover
  farOff := obligations.farOffDiagonal

def StandardGeneratedRemainingObligations.toGlobalBranchObligations
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF) :
    StellatedGlobalBranchObligations where
  cover := obligations.globalCover
  farExcludes := obligations.farOffDiagonal.farExcludes
  offDiagonalExcludes := obligations.farOffDiagonal.offDiagonalExcludes

def StellatedStandardPlanObligations.toGlobalBranchObligations
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    StellatedGlobalBranchObligations where
  cover := plan.cover
  farExcludes := plan.farOff.farExcludes
  offDiagonalExcludes := plan.farOff.offDiagonalExcludes

def stellatedStandardPlanObligations_of_globalBranches
    {rhoF : ℝ}
    (sbBox : StellatedSBBoxObligation)
    (sf : StellatedSFObligation rhoF)
    (zones : StellatedNearCriticalObligation)
    (global : StellatedGlobalBranchObligations) :
    StellatedStandardPlanObligations rhoF where
  sbBox := sbBox
  sf := sf
  zones := zones
  cover := global.cover
  farOff := global.toFarOffDiagonal

/-- Fully split standard §17 packet: generated replay evidence plus the remaining semantic
bridges and global branch payloads.  This is the most explicit standard-route target; converting it
to `StellatedStandardPlanObligations` forgets only the replay evidence that is already checked
by the generated files. -/
structure StellatedStandardFullPacket (rhoF : ℝ) where
  sbReplay : StellatedSBBoxReplayEvidence
  sfReplay : StellatedSFReplayEvidence
  sbBox : StellatedSBBoxObligation
  sf : StellatedSFObligation rhoF
  zones : StellatedNearCriticalObligation
  global : StellatedGlobalBranchObligations

def StellatedStandardFullPacket.toPlan
    {rhoF : ℝ}
    (packet : StellatedStandardFullPacket rhoF) :
    StellatedStandardPlanObligations rhoF :=
  stellatedStandardPlanObligations_of_globalBranches
    packet.sbBox packet.sf packet.zones packet.global

def stellatedStandardFullPacket_of_payloads
    {rhoF : ℝ}
    (sbBox : StellatedSBBoxObligation)
    (sf : StellatedSFObligation rhoF)
    (zones : StellatedNearCriticalObligation)
    (global : StellatedGlobalBranchObligations) :
    StellatedStandardFullPacket rhoF where
  sbReplay := stellatedGeneratedSBBoxReplayEvidence
  sfReplay := stellatedGeneratedSFReplayEvidence
  sbBox := sbBox
  sf := sf
  zones := zones
  global := global

def StellatedStandardPlanObligations.toFullPacket
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    StellatedStandardFullPacket rhoF where
  sbReplay := stellatedGeneratedSBBoxReplayEvidence
  sfReplay := stellatedGeneratedSFReplayEvidence
  sbBox := plan.sbBox
  sf := plan.sf
  zones := plan.zones
  global := plan.toGlobalBranchObligations

def StandardGeneratedRemainingObligations.toStellatedFullPacket
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF) :
    StellatedStandardFullPacket rhoF :=
  obligations.toStellatedPlanObligations.toFullPacket

theorem StellatedStandardPlanObligations.toFullPacket_toPlan
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    plan.toFullPacket.toPlan = plan :=
  rfl

def StellatedStandardFullPacket.toRemainingObligations
    {rhoF : ℝ}
    (packet : StellatedStandardFullPacket rhoF) :
    StandardGeneratedRemainingObligations rhoF :=
  packet.toPlan.toRemainingObligations

def StellatedStandardFullPacket.sbBoxPointwiseBridge
    {rhoF : ℝ}
    (packet : StellatedStandardFullPacket rhoF) :
    StellatedSBBoxPointwiseBridge :=
  packet.sbBox

def StellatedStandardFullPacket.sfSemanticBridge
    {rhoF : ℝ}
    (packet : StellatedStandardFullPacket rhoF) :
    StellatedSFSemanticBridge rhoF :=
  packet.sf

def StellatedStandardFullPacket.zoneConsequences
    {rhoF : ℝ}
    (packet : StellatedStandardFullPacket rhoF)
    (cand : CriticalDiskCandidate) :
    CriticalDiskZoneConsequences cand :=
  packet.zones cand

def StellatedStandardFullPacket.globalBranchObligations
    {rhoF : ℝ}
    (packet : StellatedStandardFullPacket rhoF) :
    StellatedGlobalBranchObligations :=
  packet.global

def StellatedStandardFullPacket.farOffDiagonal
    {rhoF : ℝ}
    (packet : StellatedStandardFullPacket rhoF) :
    StellatedFarOffDiagonalObligation packet.global.cover :=
  packet.global.toFarOffDiagonal

theorem StellatedStandardFullPacket.trichotomy
    {rhoF : ℝ}
    (packet : StellatedStandardFullPacket rhoF)
    (c : StellatedConfig) :
    packet.global.cover.FarRegion c ∨
      (∃ cand : CriticalDiskCandidate, c = cand.config ∧ CriticalDiskHypotheses cand) ∨
        packet.global.cover.OffDiagonalRegion c :=
  packet.global.trichotomy c

theorem StellatedStandardPlanObligations.toRemaining_toPlan
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    plan.toRemainingObligations.toStellatedPlanObligations = plan :=
  rfl

theorem StandardGeneratedRemainingObligations.toPlan_toRemaining
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF) :
    obligations.toStellatedPlanObligations.toRemainingObligations = obligations :=
  rfl

theorem StellatedStandardPlanObligations.toGlobalBranchObligations_toFarOffDiagonal
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    plan.toGlobalBranchObligations.toFarOffDiagonal = plan.farOff :=
  rfl

def StandardGeneratedGlobalCertificate.toRemainingObligations
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalCertificate rhoF) :
    StandardGeneratedRemainingObligations rhoF where
  sfSemantic := cert.localCert.soundness.sf.to_certificate
  sbPointwise := cert.localCert.soundness.sbBox.pointwise
  zoneConsequences := cert.localCert.zones
  globalCover := cert.cover
  farOffDiagonal := cert.farOff

def StandardGeneratedRemainingObligations.toGlobalLocalCertificate
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF) :
    StandardGeneratedGlobalLocalCertificate rhoF :=
  standardGeneratedGlobalLocalCertificate_of_certificates_and_zones
    obligations.sfSemantic obligations.sbPointwise obligations.zoneConsequences

def StandardGeneratedRemainingObligations.toGlobalCertificate
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF) :
    StandardGeneratedGlobalCertificate rhoF where
  localCert := obligations.toGlobalLocalCertificate
  cover := obligations.globalCover
  farOff := obligations.farOffDiagonal

def StandardGeneratedRemainingObligations.toStellatedGlobalCertificate
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF) :
    StellatedGlobalCertificate :=
  obligations.toGlobalCertificate.toGlobalCertificate

theorem StandardGeneratedRemainingObligations.existsGlobalCertificate
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF) :
    ∃ _cert : StellatedGlobalCertificate, StellatedNonRupertStatement :=
  ⟨obligations.toStellatedGlobalCertificate,
    obligations.toStellatedGlobalCertificate.nonRupert⟩

theorem StellatedStandardPlanObligations.nonRupert
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    StellatedNonRupertStatement :=
  plan.toRemainingObligations.toGlobalCertificate.nonRupert

theorem StellatedStandardPlanObligations.existsGlobalCertificate
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    ∃ _cert : StellatedGlobalCertificate, StellatedNonRupertStatement :=
  plan.toRemainingObligations.existsGlobalCertificate

theorem StellatedStandardFullPacket.nonRupert
    {rhoF : ℝ}
    (packet : StellatedStandardFullPacket rhoF) :
    StellatedNonRupertStatement :=
  packet.toPlan.nonRupert

theorem StellatedStandardFullPacket.existsGlobalCertificate
    {rhoF : ℝ}
    (packet : StellatedStandardFullPacket rhoF) :
    ∃ _cert : StellatedGlobalCertificate, StellatedNonRupertStatement :=
  packet.toPlan.existsGlobalCertificate

theorem StandardGeneratedRemainingObligations.nonRupert
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF) :
    StellatedNonRupertStatement :=
  obligations.toGlobalCertificate.nonRupert

theorem StandardGeneratedRemainingObligations.excludes
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF)
    (c : StellatedConfig) :
    ¬ RupertContainment stellatedVertices c :=
  obligations.nonRupert c

theorem StandardGeneratedRemainingObligations.false_of_containment
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    False :=
  obligations.excludes c hcont

theorem StandardGeneratedRemainingObligations.trichotomy
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF)
    (c : StellatedConfig) :
    obligations.globalCover.FarRegion c ∨
      (∃ cand : CriticalDiskCandidate, c = cand.config ∧ CriticalDiskHypotheses cand) ∨
        obligations.globalCover.OffDiagonalRegion c :=
  obligations.globalCover.trichotomy c

theorem StandardGeneratedRemainingObligations.nearCritical_of_not_far_not_offDiagonal
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF)
    {c : StellatedConfig}
    (hfar : ¬ obligations.globalCover.FarRegion c)
    (hoff : ¬ obligations.globalCover.OffDiagonalRegion c) :
    ∃ cand : CriticalDiskCandidate, c = cand.config ∧ CriticalDiskHypotheses cand :=
  obligations.globalCover.nearCritical_of_not_far_not_offDiagonal hfar hoff

theorem StandardGeneratedRemainingObligations.notFar_of_containment
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    ¬ obligations.globalCover.FarRegion c := by
  intro hfar
  exact obligations.farOffDiagonal.farExcludes hfar hcont

theorem StandardGeneratedRemainingObligations.notOffDiagonal_of_containment
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    ¬ obligations.globalCover.OffDiagonalRegion c := by
  intro hoff
  exact obligations.farOffDiagonal.offDiagonalExcludes hoff hcont

theorem StandardGeneratedRemainingObligations.nearCritical_of_containment
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    ∃ cand : CriticalDiskCandidate, c = cand.config ∧ CriticalDiskHypotheses cand :=
  obligations.globalCover.nearCritical_of_not_far_not_offDiagonal
    (obligations.notFar_of_containment hcont)
    (obligations.notOffDiagonal_of_containment hcont)

theorem StandardGeneratedRemainingObligations.excludes_of_not_far_not_offDiagonal
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF)
    {c : StellatedConfig}
    (hfar : ¬ obligations.globalCover.FarRegion c)
    (hoff : ¬ obligations.globalCover.OffDiagonalRegion c) :
    ¬ RupertContainment stellatedVertices c :=
  obligations.toGlobalCertificate.toGlobalCertificate.excludes_of_not_far_not_offDiagonal
    hfar hoff

theorem StandardGeneratedRemainingObligations.excludesFar
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF)
    {c : StellatedConfig}
    (hfar : obligations.globalCover.FarRegion c) :
    ¬ RupertContainment stellatedVertices c :=
  obligations.farOffDiagonal.farExcludes hfar

theorem StandardGeneratedRemainingObligations.excludesOffDiagonal
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF)
    {c : StellatedConfig}
    (hoff : obligations.globalCover.OffDiagonalRegion c) :
    ¬ RupertContainment stellatedVertices c :=
  obligations.farOffDiagonal.offDiagonalExcludes hoff

theorem StandardGeneratedRemainingObligations.excludesNearCritical
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  (obligations.zoneConsequences cand).excludes hcand

theorem StandardGeneratedRemainingObligations.sfCertifiedRowsValid
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF) :
    GeneratedSFWitness.manifest.CertifiedRowsValid
      GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  obligations.toGlobalLocalCertificate.sfCertifiedRowsValid

theorem StandardGeneratedRemainingObligations.sbBoxReplayAssemblyValid
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF) :
    SBBoxReplayAssembly
      GeneratedSBBoxTailWitness.manifest GeneratedSBBoxBulkWitness.manifest
      GeneratedSBBoxAssemblyReport.report
      GeneratedSBBoxAssemblyReport.tailDomain
      GeneratedSBBoxAssemblyReport.bulkDeltaDomain
      GeneratedSBBoxAssemblyReport.bulkPhiDomain
      GeneratedSBBoxBulkWitness.etaBudget :=
  obligations.toGlobalLocalCertificate.sbBoxReplayAssemblyValid

def StellatedStandardPlanObligations.toGlobalLocalCertificate
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    StandardGeneratedGlobalLocalCertificate rhoF :=
  plan.toRemainingObligations.toGlobalLocalCertificate

def StellatedStandardPlanObligations.toGlobalCertificate
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    StandardGeneratedGlobalCertificate rhoF :=
  plan.toRemainingObligations.toGlobalCertificate

def StellatedStandardPlanObligations.toStellatedGlobalCertificate
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    StellatedGlobalCertificate :=
  plan.toRemainingObligations.toStellatedGlobalCertificate

theorem StellatedStandardPlanObligations.localFamily
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    CriticalDiskLemma6PrimeGlobalFamily :=
  plan.toGlobalLocalCertificate.localFamily

def StellatedStandardPlanObligations.localCertificate
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (cand : CriticalDiskCandidate) :
    StandardGeneratedLocalCertificate rhoF cand :=
  plan.toGlobalLocalCertificate.localCertificate cand

def StellatedStandardPlanObligations.lemma6PrimeCertificate
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (cand : CriticalDiskCandidate) :
    CriticalDiskLemma6PrimeCertificate
      (plan.localCertificate cand).soundness.toCriticalDiskInputs cand :=
  (plan.localCertificate cand).lemma6PrimeCertificate

def StellatedStandardPlanObligations.toCriticalDiskInputs
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (cand : CriticalDiskCandidate) :
    CriticalDiskCertifiedInputs :=
  (plan.localCertificate cand).toCriticalDiskInputs

theorem StellatedStandardPlanObligations.inputs_allCertified
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (cand : CriticalDiskCandidate) :
    (plan.toCriticalDiskInputs cand).allCertified :=
  (plan.localCertificate cand).inputs_allCertified

theorem StellatedStandardPlanObligations.lemma6prime
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (cand : CriticalDiskCandidate) :
    CriticalDiskLemma6PrimeStatement cand :=
  (plan.localCertificate cand).lemma6prime

theorem StellatedStandardPlanObligations.exclusion
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  (plan.localCertificate cand).exclusion hcand

theorem StellatedStandardPlanObligations.localizedExclusion
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (cand : CriticalDiskCandidate)
    (analytics : CriticalDiskAnalyticInputs) :
    CriticalDiskLocalizedExclusionStatement cand :=
  (plan.localCertificate cand).localizedExclusion analytics

theorem StellatedStandardPlanObligations.excludes
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (c : StellatedConfig) :
    ¬ RupertContainment stellatedVertices c :=
  plan.toRemainingObligations.excludes c

theorem StellatedStandardPlanObligations.false_of_containment
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    False :=
  plan.toRemainingObligations.false_of_containment hcont

theorem StellatedStandardPlanObligations.trichotomy
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (c : StellatedConfig) :
    plan.cover.FarRegion c ∨
      (∃ cand : CriticalDiskCandidate, c = cand.config ∧ CriticalDiskHypotheses cand) ∨
        plan.cover.OffDiagonalRegion c :=
  plan.cover.trichotomy c

theorem StellatedStandardPlanObligations.nearCritical_of_not_far_not_offDiagonal
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    {c : StellatedConfig}
    (hfar : ¬ plan.cover.FarRegion c)
    (hoff : ¬ plan.cover.OffDiagonalRegion c) :
    ∃ cand : CriticalDiskCandidate, c = cand.config ∧ CriticalDiskHypotheses cand :=
  plan.toRemainingObligations.nearCritical_of_not_far_not_offDiagonal hfar hoff

theorem StellatedStandardPlanObligations.notFar_of_containment
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    ¬ plan.cover.FarRegion c :=
  plan.toRemainingObligations.notFar_of_containment hcont

theorem StellatedStandardPlanObligations.notOffDiagonal_of_containment
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    ¬ plan.cover.OffDiagonalRegion c :=
  plan.toRemainingObligations.notOffDiagonal_of_containment hcont

theorem StellatedStandardPlanObligations.nearCritical_of_containment
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    ∃ cand : CriticalDiskCandidate, c = cand.config ∧ CriticalDiskHypotheses cand :=
  plan.toRemainingObligations.nearCritical_of_containment hcont

theorem StellatedStandardPlanObligations.excludesNearCritical
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  plan.toRemainingObligations.excludesNearCritical cand hcand

def StellatedStandardPlanObligations.zoneConsequences
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (cand : CriticalDiskCandidate) :
    CriticalDiskZoneConsequences cand :=
  plan.zones cand

theorem StellatedStandardPlanObligations.zoneLemma6prime
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (cand : CriticalDiskCandidate) :
    CriticalDiskLemma6PrimeStatement cand :=
  (plan.zoneConsequences cand).lemma6prime

theorem StellatedStandardPlanObligations.zoneExcludes
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  (plan.zoneConsequences cand).excludes hcand

theorem StellatedStandardPlanObligations.zone0Excludes
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand)
    (hzone : CriticalDiskZone0 cand.point) :
    CriticalDiskExclusion cand :=
  (plan.zones cand).zone0Excludes hcand hzone

theorem StellatedStandardPlanObligations.zoneAExcludes
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand)
    (hzone : CriticalDiskZoneA cand.point) :
    CriticalDiskExclusion cand :=
  (plan.zones cand).zoneAExcludes hcand hzone

theorem StellatedStandardPlanObligations.zoneBExcludes
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand)
    (hzone : CriticalDiskZoneB cand.point) :
    CriticalDiskExclusion cand :=
  (plan.zones cand).zoneBExcludes hcand hzone

theorem StellatedStandardPlanObligations.zoneCExcludes
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand)
    (hzone : CriticalDiskZoneC cand.point) :
    CriticalDiskExclusion cand :=
  (plan.zones cand).zoneCExcludes hcand hzone

theorem StellatedStandardPlanObligations.zoneDExcludes
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand)
    (hzone : CriticalDiskZoneD cand.point) :
    CriticalDiskExclusion cand :=
  (plan.zones cand).zoneDExcludes hcand hzone

theorem StellatedStandardPlanObligations.excludesFar
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    {c : StellatedConfig}
    (hfar : plan.cover.FarRegion c) :
    ¬ RupertContainment stellatedVertices c :=
  plan.toRemainingObligations.excludesFar hfar

theorem StellatedStandardPlanObligations.excludesOffDiagonal
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    {c : StellatedConfig}
    (hoff : plan.cover.OffDiagonalRegion c) :
    ¬ RupertContainment stellatedVertices c :=
  plan.toRemainingObligations.excludesOffDiagonal hoff

theorem StellatedStandardPlanObligations.excludes_of_not_far_not_offDiagonal
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    {c : StellatedConfig}
    (hfar : ¬ plan.cover.FarRegion c)
    (hoff : ¬ plan.cover.OffDiagonalRegion c) :
    ¬ RupertContainment stellatedVertices c :=
  plan.toRemainingObligations.excludes_of_not_far_not_offDiagonal hfar hoff

def StellatedStandardPlanObligations.sfReplayEvidence
    {rhoF : ℝ}
    (_plan : StellatedStandardPlanObligations rhoF) :
    StellatedSFReplayEvidence :=
  stellatedGeneratedSFReplayEvidence

def StellatedStandardPlanObligations.sfSemanticBridge
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    StellatedSFSemanticBridge rhoF :=
  plan.sf

theorem StellatedStandardPlanObligations.sfCertifiedRowsValid
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    GeneratedSFWitness.manifest.CertifiedRowsValid
      GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  plan.toRemainingObligations.sfCertifiedRowsValid

theorem StellatedStandardPlanObligations.sfCertifiedRowValid
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    {row : SFCertifiedSweepRow}
    (hrow : row ∈ GeneratedSFWitness.manifest.certified) :
    row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  plan.toGlobalLocalCertificate.sfCertifiedRowValid hrow

theorem StellatedStandardPlanObligations.sfCovers
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    {φ s : ℝ}
    (hφlo : -Real.pi ≤ φ) (hφhi : φ ≤ Real.pi)
    (hslo : 0 ≤ s) (hshi : s ≤ 1) :
    ∃ c :
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.chart,
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.inChart
        c φ s :=
  plan.toGlobalLocalCertificate.sfCovers hφlo hφhi hslo hshi

theorem StellatedStandardPlanObligations.sfChartClassified
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (c :
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.chart) :
    plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.isShell c ∨
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.isBulk c :=
  plan.toGlobalLocalCertificate.sfChartClassified c

theorem StellatedStandardPlanObligations.sfCornerDistLower_nonneg
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (c :
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.chart) :
    0 ≤
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.cornerDistLower
        c :=
  plan.toGlobalLocalCertificate.sfCornerDistLower_nonneg c

theorem StellatedStandardPlanObligations.sfShellBound
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (c :
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.chart)
    (hc :
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.isShell c) :
    plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.shellSlope *
        plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.cornerDistLower
          c ≤
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.psiLower c :=
  plan.toGlobalLocalCertificate.sfShellBound c hc

theorem StellatedStandardPlanObligations.sfBulkBound
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (c :
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.chart)
    (hc :
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.isBulk c) :
    plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.psiMin ≤
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.psiLower c :=
  plan.toGlobalLocalCertificate.sfBulkBound c hc

def StellatedStandardPlanObligations.sbBoxReplayEvidence
    {rhoF : ℝ}
    (_plan : StellatedStandardPlanObligations rhoF) :
    StellatedSBBoxReplayEvidence :=
  stellatedGeneratedSBBoxReplayEvidence

def StellatedStandardPlanObligations.sbBoxPointwiseBridge
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    StellatedSBBoxPointwiseBridge :=
  plan.sbBox

theorem StellatedStandardPlanObligations.sbBoxReplayAssemblyValid
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    SBBoxReplayAssembly
      GeneratedSBBoxTailWitness.manifest GeneratedSBBoxBulkWitness.manifest
      GeneratedSBBoxAssemblyReport.report
      GeneratedSBBoxAssemblyReport.tailDomain
      GeneratedSBBoxAssemblyReport.bulkDeltaDomain
      GeneratedSBBoxAssemblyReport.bulkPhiDomain
      GeneratedSBBoxBulkWitness.etaBudget :=
  plan.toRemainingObligations.sbBoxReplayAssemblyValid

theorem StellatedStandardPlanObligations.sbBoxTailRowsValid
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    GeneratedSBBoxTailWitness.manifest.RowsValid :=
  plan.toGlobalLocalCertificate.sbBoxTailRowsValid

theorem StellatedStandardPlanObligations.sbBoxBulkRowsValid
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    GeneratedSBBoxBulkWitness.manifest.RowsValid
      GeneratedSBBoxBulkWitness.etaBudget :=
  plan.toGlobalLocalCertificate.sbBoxBulkRowsValid

theorem StellatedStandardPlanObligations.sbBoxTailRowValid
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    {row : SBBoxTailRow}
    (hrow : row ∈ GeneratedSBBoxTailWitness.manifest.rows) :
    row.Valid :=
  plan.toGlobalLocalCertificate.sbBoxTailRowValid hrow

theorem StellatedStandardPlanObligations.sbBoxBulkRowValid
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    {row : SBBoxBulkRow}
    (hrow : row ∈ GeneratedSBBoxBulkWitness.manifest.rows) :
    row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  plan.toGlobalLocalCertificate.sbBoxBulkRowValid hrow

theorem StellatedStandardPlanObligations.sbBoxTailExistsValidRow
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (chart : SBBoxTailChart) {r : ℝ}
    (hr : GeneratedSBBoxAssemblyReport.tailDomain.contains r) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains r ∧ row.Valid :=
  plan.toGlobalLocalCertificate.sbBoxTailExistsValidRow chart hr

theorem StellatedStandardPlanObligations.sbBoxBulkExistsValidRow
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    {delta phi : ℝ}
    (hdelta : GeneratedSBBoxAssemblyReport.bulkDeltaDomain.contains delta)
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains delta ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  plan.toGlobalLocalCertificate.sbBoxBulkExistsValidRow hdelta hphi

theorem StellatedStandardPlanObligations.sbBoxTailExistsValidRowAtZero
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (chart : SBBoxTailChart) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains (0 : ℝ) ∧ row.Valid :=
  plan.toGlobalLocalCertificate.sbBoxTailExistsValidRowAtZero chart

theorem StellatedStandardPlanObligations.sbBoxTailExistsValidRowAtOne
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (chart : SBBoxTailChart) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains (1 : ℝ) ∧ row.Valid :=
  plan.toGlobalLocalCertificate.sbBoxTailExistsValidRowAtOne chart

theorem StellatedStandardPlanObligations.sbBoxBulkExistsValidRowAtTailCut
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    {phi : ℝ}
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskTailCut ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  plan.toGlobalLocalCertificate.sbBoxBulkExistsValidRowAtTailCut hphi

theorem StellatedStandardPlanObligations.sbBoxBulkExistsValidRowAtRhoCap
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    {phi : ℝ}
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskRhoCap ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  plan.toGlobalLocalCertificate.sbBoxBulkExistsValidRowAtRhoCap hphi

theorem StellatedStandardPlanObligations.sbBoxBulkExistsValidRowAtTailCutZeroPhi
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskTailCut ∧ row.phi.contains (0 : ℝ) ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  plan.toGlobalLocalCertificate.sbBoxBulkExistsValidRowAtTailCutZeroPhi

theorem StellatedStandardPlanObligations.sbBoxBulkExistsValidRowAtRhoCapZeroPhi
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskRhoCap ∧ row.phi.contains (0 : ℝ) ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  plan.toGlobalLocalCertificate.sbBoxBulkExistsValidRowAtRhoCapZeroPhi

def StellatedStandardPlanObligations.sbBoxPointCertificate
    {rhoF : ℝ}
    (plan : StellatedStandardPlanObligations rhoF)
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) {delta : ℝ}
    (hdelta_pos : 0 < delta) (hdelta_cap : delta ≤ criticalDiskRhoCap) :
    SBBoxPointCertificate R₂ delta
      criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT :=
  plan.sbBox R₂ hdelta_pos hdelta_cap

theorem StandardGeneratedRemainingObligations.toRemainingObligations_toGlobalCertificate
    {rhoF : ℝ}
    (obligations : StandardGeneratedRemainingObligations rhoF) :
    obligations.toGlobalCertificate.toRemainingObligations = obligations :=
  rfl

theorem StandardGeneratedGlobalCertificate.nonRupert_via_remainingObligations
    {rhoF : ℝ}
    (cert : StandardGeneratedGlobalCertificate rhoF) :
    cert.toRemainingObligations.nonRupert = cert.nonRupert :=
  rfl

/-- Audited generated analogue of the global-local certificate. -/
structure AuditedGeneratedGlobalLocalCertificate
    (rhoF : ℝ) (phiDomain xDomain yDomain : RatInterval) where
  soundness : AuditedGeneratedSoundness rhoF phiDomain xDomain yDomain
  zones : ∀ cand : CriticalDiskCandidate, CriticalDiskZoneConsequences cand

def AuditedGeneratedGlobalLocalCertificate.localCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate) :
    AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand where
  soundness := cert.soundness
  zones := cert.zones cand

theorem AuditedGeneratedGlobalLocalCertificate.localFamily
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain) :
    CriticalDiskLemma6PrimeGlobalFamily := by
  intro cand
  exact (cert.localCertificate cand).lemma6prime

theorem AuditedGeneratedGlobalLocalCertificate.coverWithDeferred
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain) :
    GeneratedSFWitness.manifest.DomainCoverWithDeferred
      phiDomain xDomain yDomain :=
  cert.soundness.coverWithDeferred

def AuditedGeneratedGlobalLocalCertificate.certifiedDomainCover
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain) :
    GeneratedSFWitness.manifest.CertifiedDomainCover
      phiDomain xDomain yDomain :=
  cert.soundness.certifiedDomainCover

theorem AuditedGeneratedGlobalLocalCertificate.existsValidCertifiedRow
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain)
    {φ x y : ℝ}
    (hφ : phiDomain.contains φ) (hx : xDomain.contains x) (hy : yDomain.contains y) :
    ∃ row ∈ GeneratedSFWitness.manifest.certified,
      row.box.contains φ x y ∧
        row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  cert.soundness.existsValidCertifiedRow hφ hx hy

theorem AuditedGeneratedGlobalLocalCertificate.sfCertifiedRowValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain)
    {row : SFCertifiedSweepRow}
    (hrow : row ∈ GeneratedSFWitness.manifest.certified) :
    row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  cert.soundness.sfCertifiedRowValid hrow

theorem AuditedGeneratedGlobalLocalCertificate.sbBoxReplayAssemblyValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain) :
    SBBoxReplayAssembly
      GeneratedSBBoxTailWitness.manifest GeneratedSBBoxBulkWitness.manifest
      GeneratedSBBoxAssemblyReport.report
      GeneratedSBBoxAssemblyReport.tailDomain
      GeneratedSBBoxAssemblyReport.bulkDeltaDomain
      GeneratedSBBoxAssemblyReport.bulkPhiDomain
      GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxReplayAssemblyValid

theorem AuditedGeneratedGlobalLocalCertificate.sbBoxTailRowsValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain) :
    GeneratedSBBoxTailWitness.manifest.RowsValid :=
  cert.soundness.sbBoxTailRowsValid

theorem AuditedGeneratedGlobalLocalCertificate.sbBoxBulkRowsValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain) :
    GeneratedSBBoxBulkWitness.manifest.RowsValid
      GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxBulkRowsValid

theorem AuditedGeneratedGlobalLocalCertificate.sbBoxTailRowValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain)
    {row : SBBoxTailRow}
    (hrow : row ∈ GeneratedSBBoxTailWitness.manifest.rows) :
    row.Valid :=
  cert.soundness.sbBoxTailRowValid hrow

theorem AuditedGeneratedGlobalLocalCertificate.sbBoxBulkRowValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain)
    {row : SBBoxBulkRow}
    (hrow : row ∈ GeneratedSBBoxBulkWitness.manifest.rows) :
    row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxBulkRowValid hrow

theorem AuditedGeneratedGlobalLocalCertificate.sbBoxTailExistsValidRow
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain)
    (chart : SBBoxTailChart) {r : ℝ}
    (hr : GeneratedSBBoxAssemblyReport.tailDomain.contains r) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains r ∧ row.Valid :=
  cert.soundness.sbBoxTailExistsValidRow chart hr

theorem AuditedGeneratedGlobalLocalCertificate.sbBoxBulkExistsValidRow
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain)
    {delta phi : ℝ}
    (hdelta : GeneratedSBBoxAssemblyReport.bulkDeltaDomain.contains delta)
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains delta ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxBulkExistsValidRow hdelta hphi

theorem AuditedGeneratedGlobalLocalCertificate.sbBoxTailExistsValidRowAtZero
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain)
    (chart : SBBoxTailChart) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains (0 : ℝ) ∧ row.Valid :=
  cert.soundness.sbBoxTailExistsValidRowAtZero chart

theorem AuditedGeneratedGlobalLocalCertificate.sbBoxTailExistsValidRowAtOne
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain)
    (chart : SBBoxTailChart) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains (1 : ℝ) ∧ row.Valid :=
  cert.soundness.sbBoxTailExistsValidRowAtOne chart

theorem AuditedGeneratedGlobalLocalCertificate.sbBoxBulkExistsValidRowAtTailCut
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain)
    {phi : ℝ}
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskTailCut ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxBulkExistsValidRowAtTailCut hphi

theorem AuditedGeneratedGlobalLocalCertificate.sbBoxBulkExistsValidRowAtRhoCap
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain)
    {phi : ℝ}
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskRhoCap ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxBulkExistsValidRowAtRhoCap hphi

theorem AuditedGeneratedGlobalLocalCertificate.sbBoxBulkExistsValidRowAtTailCutZeroPhi
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskTailCut ∧ row.phi.contains (0 : ℝ) ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxBulkExistsValidRowAtTailCutZeroPhi

theorem AuditedGeneratedGlobalLocalCertificate.sbBoxBulkExistsValidRowAtRhoCapZeroPhi
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskRhoCap ∧ row.phi.contains (0 : ℝ) ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  cert.soundness.sbBoxBulkExistsValidRowAtRhoCapZeroPhi

def AuditedGeneratedGlobalLocalCertificate.sbBoxPointCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain)
    (hcand : CriticalDiskHypotheses cand) :
    SBBoxPointCertificate cand.R₂ cand.delta
      cert.soundness.toCriticalDiskInputs.sbBox.bPi
      cert.soundness.toCriticalDiskInputs.sbBox.bGamma
      cert.soundness.toCriticalDiskInputs.sbBox.bT :=
  cert.soundness.sbBoxPointCertificate hcand

def AuditedGeneratedGlobalLocalCertificate.sbBoxInclusion
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    {cand : CriticalDiskCandidate}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain)
    (hcand : CriticalDiskHypotheses cand) :
    DepthCylinderTheorem.BoxInclusionCertificate
      (cert.sbBoxPointCertificate hcand).cert :=
  cert.soundness.sbBoxInclusion hcand

theorem AuditedGeneratedGlobalLocalCertificate.sfCovers
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain)
    {φ s : ℝ}
    (hφlo : -Real.pi ≤ φ) (hφhi : φ ≤ Real.pi)
    (hslo : 0 ≤ s) (hshi : s ≤ 1) :
    ∃ c : cert.soundness.toCriticalDiskInputs.sf.certificate.chart,
      cert.soundness.toCriticalDiskInputs.sf.certificate.inChart c φ s :=
  cert.soundness.sfCovers hφlo hφhi hslo hshi

theorem AuditedGeneratedGlobalLocalCertificate.sfChartClassified
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain)
    (c : cert.soundness.toCriticalDiskInputs.sf.certificate.chart) :
    cert.soundness.toCriticalDiskInputs.sf.certificate.isShell c ∨
      cert.soundness.toCriticalDiskInputs.sf.certificate.isBulk c :=
  cert.soundness.sfChartClassified c

theorem AuditedGeneratedGlobalLocalCertificate.sfCornerDistLower_nonneg
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain)
    (c : cert.soundness.toCriticalDiskInputs.sf.certificate.chart) :
    0 ≤ cert.soundness.toCriticalDiskInputs.sf.certificate.cornerDistLower c :=
  cert.soundness.sfCornerDistLower_nonneg c

theorem AuditedGeneratedGlobalLocalCertificate.sfShellBound
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain)
    (c : cert.soundness.toCriticalDiskInputs.sf.certificate.chart)
    (hc : cert.soundness.toCriticalDiskInputs.sf.certificate.isShell c) :
    cert.soundness.toCriticalDiskInputs.sf.shellSlope *
        cert.soundness.toCriticalDiskInputs.sf.certificate.cornerDistLower c ≤
      cert.soundness.toCriticalDiskInputs.sf.certificate.psiLower c :=
  cert.soundness.sfShellBound c hc

theorem AuditedGeneratedGlobalLocalCertificate.sfBulkBound
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain)
    (c : cert.soundness.toCriticalDiskInputs.sf.certificate.chart)
    (hc : cert.soundness.toCriticalDiskInputs.sf.certificate.isBulk c) :
    cert.soundness.toCriticalDiskInputs.sf.psiMin ≤
      cert.soundness.toCriticalDiskInputs.sf.certificate.psiLower c :=
  cert.soundness.sfBulkBound c hc

def AuditedGeneratedGlobalLocalCertificate.toGlobalCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain)
    (cover : StellatedGlobalCover)
    (farOff : StellatedFarOffDiagonalCertificate cover) :
    StellatedGlobalCertificate :=
  StellatedGlobalCertificate.ofLocalFamily cover farOff cert.localFamily

/-- Final global assembly from audited generated local certificates plus the remaining
far/off-diagonal cover certificate. -/
theorem stellated_nonRupert_of_audited_generated_global_certificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cover : StellatedGlobalCover)
    (farOff : StellatedFarOffDiagonalCertificate cover)
    (localCert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain) :
    StellatedNonRupertStatement :=
  stellated_nonRupert_of_global_cover cover farOff localCert.localFamily

/-- Constructor for the audited generated global-local certificate once the generated sweep audit,
the two semantic certificate obligations, and all zone consequences have been supplied. -/
def auditedGeneratedGlobalLocalCertificate_of_audit_and_certificates_and_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : ∀ cand : CriticalDiskCandidate, CriticalDiskZoneConsequences cand) :
    AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain where
  soundness := auditedGeneratedSoundness_of_audit_and_certificates audit sfCert sbPointwise
  zones := zones

/-- Final global assembly directly from the audited generated raw obligations and the
far/off-diagonal cover certificate. -/
theorem stellated_nonRupert_of_audited_generated_certificates_and_global_cover
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cover : StellatedGlobalCover)
    (farOff : StellatedFarOffDiagonalCertificate cover)
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : ∀ cand : CriticalDiskCandidate, CriticalDiskZoneConsequences cand) :
    StellatedNonRupertStatement :=
  stellated_nonRupert_of_audited_generated_global_certificate cover farOff
    (auditedGeneratedGlobalLocalCertificate_of_audit_and_certificates_and_zones
      audit sfCert sbPointwise zones)

/-- Pack the final audited-generated global certificate once the sweep audit, far/off-diagonal
cover, and all candidate zone consequences are supplied. -/
def stellatedGlobalCertificate_of_audited_generated_certificates_and_global_cover
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cover : StellatedGlobalCover)
    (farOff : StellatedFarOffDiagonalCertificate cover)
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : ∀ cand : CriticalDiskCandidate, CriticalDiskZoneConsequences cand) :
    StellatedGlobalCertificate :=
  (auditedGeneratedGlobalLocalCertificate_of_audit_and_certificates_and_zones
      audit sfCert sbPointwise zones).toGlobalCertificate cover farOff

theorem stellatedGlobalCertificate_of_audited_generated_certificates_nonRupert
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cover : StellatedGlobalCover)
    (farOff : StellatedFarOffDiagonalCertificate cover)
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : ∀ cand : CriticalDiskCandidate, CriticalDiskZoneConsequences cand) :
    (stellatedGlobalCertificate_of_audited_generated_certificates_and_global_cover
      cover farOff audit sfCert sbPointwise zones).nonRupert =
      stellated_nonRupert_of_audited_generated_certificates_and_global_cover
        cover farOff audit sfCert sbPointwise zones :=
  rfl

/-- Fully packaged audited generated route to the final global theorem.  In addition to the
standard final obligations, this keeps the generated `(SF)` sweep audit with the certificate. -/
structure AuditedGeneratedGlobalCertificate
    (rhoF : ℝ) (phiDomain xDomain yDomain : RatInterval) where
  localCert : AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain
  cover : StellatedGlobalCover
  farOff : StellatedFarOffDiagonalCertificate cover

def AuditedGeneratedGlobalCertificate.toGlobalCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalCertificate rhoF phiDomain xDomain yDomain) :
    StellatedGlobalCertificate :=
  cert.localCert.toGlobalCertificate cert.cover cert.farOff

theorem AuditedGeneratedGlobalCertificate.nonRupert
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalCertificate rhoF phiDomain xDomain yDomain) :
    StellatedNonRupertStatement :=
  cert.toGlobalCertificate.nonRupert

theorem AuditedGeneratedGlobalCertificate.excludes
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalCertificate rhoF phiDomain xDomain yDomain)
    (c : StellatedConfig) :
    ¬ RupertContainment stellatedVertices c :=
  cert.nonRupert c

theorem AuditedGeneratedGlobalCertificate.excludesNearCritical
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalCertificate rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  cert.toGlobalCertificate.excludesNearCritical cand hcand

theorem AuditedGeneratedGlobalCertificate.coverWithDeferred
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalCertificate rhoF phiDomain xDomain yDomain) :
    GeneratedSFWitness.manifest.DomainCoverWithDeferred
      phiDomain xDomain yDomain :=
  cert.localCert.coverWithDeferred

def AuditedGeneratedGlobalCertificate.certifiedDomainCover
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalCertificate rhoF phiDomain xDomain yDomain) :
    GeneratedSFWitness.manifest.CertifiedDomainCover
      phiDomain xDomain yDomain :=
  cert.localCert.certifiedDomainCover

theorem AuditedGeneratedGlobalCertificate.sbBoxReplayAssemblyValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalCertificate rhoF phiDomain xDomain yDomain) :
    SBBoxReplayAssembly
      GeneratedSBBoxTailWitness.manifest GeneratedSBBoxBulkWitness.manifest
      GeneratedSBBoxAssemblyReport.report
      GeneratedSBBoxAssemblyReport.tailDomain
      GeneratedSBBoxAssemblyReport.bulkDeltaDomain
      GeneratedSBBoxAssemblyReport.bulkPhiDomain
      GeneratedSBBoxBulkWitness.etaBudget :=
  cert.localCert.sbBoxReplayAssemblyValid

def auditedGeneratedGlobalCertificate_of_audit_and_certificates_and_zones
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cover : StellatedGlobalCover)
    (farOff : StellatedFarOffDiagonalCertificate cover)
    (audit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain)
    (sfCert : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF)
    (sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness)
    (zones : ∀ cand : CriticalDiskCandidate, CriticalDiskZoneConsequences cand) :
    AuditedGeneratedGlobalCertificate rhoF phiDomain xDomain yDomain where
  localCert := auditedGeneratedGlobalLocalCertificate_of_audit_and_certificates_and_zones
    audit sfCert sbPointwise zones
  cover := cover
  farOff := farOff

/-- The audited generated route expressed as the actual remaining proof obligations.  This keeps
the generated `(SF)` sweep audit next to the semantic `(SF)`, pointwise `(SB-box)`, zone, and
global-cover payloads. -/
structure AuditedGeneratedRemainingObligations
    (rhoF : ℝ) (phiDomain xDomain yDomain : RatInterval) where
  sfAudit : GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain
  sfSemantic : GeneratedSFCertifiedInput.StandardSemanticCertificate rhoF
  sbPointwise : GeneratedSBBoxCertifiedInput.StandardPointwiseSoundness
  zoneConsequences : ∀ cand : CriticalDiskCandidate, CriticalDiskZoneConsequences cand
  globalCover : StellatedGlobalCover
  farOffDiagonal : StellatedFarOffDiagonalCertificate globalCover

abbrev StellatedSFAuditObligation (phiDomain xDomain yDomain : RatInterval) :=
  GeneratedSFCertifiedInput.GeneratedSweepAudit phiDomain xDomain yDomain

/-- Draft §17 §17 as an audited-route Lean target.

This is the same payload split as `StellatedStandardPlanObligations`, plus the generated
domain audit required before trusting the `(SF)` rows as a cover of the intended sweep domain. -/
structure StellatedAuditedPlanObligations
    (rhoF : ℝ) (phiDomain xDomain yDomain : RatInterval) where
  sfAudit : StellatedSFAuditObligation phiDomain xDomain yDomain
  sbBox : StellatedSBBoxObligation
  sf : StellatedSFObligation rhoF
  zones : StellatedNearCriticalObligation
  cover : StellatedGlobalCoverObligation
  farOff : StellatedFarOffDiagonalObligation cover

def StellatedAuditedPlanObligations.toRemainingObligations
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain where
  sfAudit := plan.sfAudit
  sfSemantic := plan.sf
  sbPointwise := plan.sbBox
  zoneConsequences := plan.zones
  globalCover := plan.cover
  farOffDiagonal := plan.farOff

def AuditedGeneratedRemainingObligations.toStellatedPlanObligations
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain) :
    StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain where
  sfAudit := obligations.sfAudit
  sbBox := obligations.sbPointwise
  sf := obligations.sfSemantic
  zones := obligations.zoneConsequences
  cover := obligations.globalCover
  farOff := obligations.farOffDiagonal

def AuditedGeneratedRemainingObligations.toGlobalBranchObligations
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain) :
    StellatedGlobalBranchObligations where
  cover := obligations.globalCover
  farExcludes := obligations.farOffDiagonal.farExcludes
  offDiagonalExcludes := obligations.farOffDiagonal.offDiagonalExcludes

def AuditedGeneratedRemainingObligations.toStandardRemainingObligations
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain) :
    StandardGeneratedRemainingObligations rhoF where
  sfSemantic := obligations.sfSemantic
  sbPointwise := obligations.sbPointwise
  zoneConsequences := obligations.zoneConsequences
  globalCover := obligations.globalCover
  farOffDiagonal := obligations.farOffDiagonal

def StellatedAuditedPlanObligations.toStandardPlanObligations
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    StellatedStandardPlanObligations rhoF where
  sbBox := plan.sbBox
  sf := plan.sf
  zones := plan.zones
  cover := plan.cover
  farOff := plan.farOff

def StellatedAuditedPlanObligations.toGlobalBranchObligations
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    StellatedGlobalBranchObligations where
  cover := plan.cover
  farExcludes := plan.farOff.farExcludes
  offDiagonalExcludes := plan.farOff.offDiagonalExcludes

def stellatedAuditedPlanObligations_of_globalBranches
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (sfAudit : StellatedSFAuditObligation phiDomain xDomain yDomain)
    (sbBox : StellatedSBBoxObligation)
    (sf : StellatedSFObligation rhoF)
    (zones : StellatedNearCriticalObligation)
    (global : StellatedGlobalBranchObligations) :
    StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain where
  sfAudit := sfAudit
  sbBox := sbBox
  sf := sf
  zones := zones
  cover := global.cover
  farOff := global.toFarOffDiagonal

/-- Fully split audited §17 packet: generated replay evidence, the audited `(SF)` domain/deferred
row obligation, the semantic bridges, and the global branch payloads. -/
structure StellatedAuditedFullPacket
    (rhoF : ℝ) (phiDomain xDomain yDomain : RatInterval) where
  sbReplay : StellatedSBBoxReplayEvidence
  sfReplay : StellatedSFReplayEvidence
  sfAudit : StellatedSFAuditObligation phiDomain xDomain yDomain
  sbBox : StellatedSBBoxObligation
  sf : StellatedSFObligation rhoF
  zones : StellatedNearCriticalObligation
  global : StellatedGlobalBranchObligations

def StellatedAuditedFullPacket.toPlan
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (packet : StellatedAuditedFullPacket rhoF phiDomain xDomain yDomain) :
    StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain :=
  stellatedAuditedPlanObligations_of_globalBranches
    packet.sfAudit packet.sbBox packet.sf packet.zones packet.global

def stellatedAuditedFullPacket_of_payloads
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (sfAudit : StellatedSFAuditObligation phiDomain xDomain yDomain)
    (sbBox : StellatedSBBoxObligation)
    (sf : StellatedSFObligation rhoF)
    (zones : StellatedNearCriticalObligation)
    (global : StellatedGlobalBranchObligations) :
    StellatedAuditedFullPacket rhoF phiDomain xDomain yDomain where
  sbReplay := stellatedGeneratedSBBoxReplayEvidence
  sfReplay := stellatedGeneratedSFReplayEvidence
  sfAudit := sfAudit
  sbBox := sbBox
  sf := sf
  zones := zones
  global := global

def StellatedAuditedPlanObligations.toFullPacket
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    StellatedAuditedFullPacket rhoF phiDomain xDomain yDomain where
  sbReplay := stellatedGeneratedSBBoxReplayEvidence
  sfReplay := stellatedGeneratedSFReplayEvidence
  sfAudit := plan.sfAudit
  sbBox := plan.sbBox
  sf := plan.sf
  zones := plan.zones
  global := plan.toGlobalBranchObligations

def AuditedGeneratedRemainingObligations.toStellatedFullPacket
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain) :
    StellatedAuditedFullPacket rhoF phiDomain xDomain yDomain :=
  obligations.toStellatedPlanObligations.toFullPacket

theorem StellatedAuditedPlanObligations.toFullPacket_toPlan
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    plan.toFullPacket.toPlan = plan :=
  rfl

def StellatedAuditedFullPacket.toRemainingObligations
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (packet : StellatedAuditedFullPacket rhoF phiDomain xDomain yDomain) :
    AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain :=
  packet.toPlan.toRemainingObligations

def StellatedAuditedFullPacket.sfAuditObligation
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (packet : StellatedAuditedFullPacket rhoF phiDomain xDomain yDomain) :
    StellatedSFAuditObligation phiDomain xDomain yDomain :=
  packet.sfAudit

def StellatedAuditedFullPacket.sbBoxPointwiseBridge
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (packet : StellatedAuditedFullPacket rhoF phiDomain xDomain yDomain) :
    StellatedSBBoxPointwiseBridge :=
  packet.sbBox

def StellatedAuditedFullPacket.sfSemanticBridge
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (packet : StellatedAuditedFullPacket rhoF phiDomain xDomain yDomain) :
    StellatedSFSemanticBridge rhoF :=
  packet.sf

def StellatedAuditedFullPacket.zoneConsequences
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (packet : StellatedAuditedFullPacket rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate) :
    CriticalDiskZoneConsequences cand :=
  packet.zones cand

def StellatedAuditedFullPacket.globalBranchObligations
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (packet : StellatedAuditedFullPacket rhoF phiDomain xDomain yDomain) :
    StellatedGlobalBranchObligations :=
  packet.global

def StellatedAuditedFullPacket.farOffDiagonal
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (packet : StellatedAuditedFullPacket rhoF phiDomain xDomain yDomain) :
    StellatedFarOffDiagonalObligation packet.global.cover :=
  packet.global.toFarOffDiagonal

theorem StellatedAuditedFullPacket.trichotomy
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (packet : StellatedAuditedFullPacket rhoF phiDomain xDomain yDomain)
    (c : StellatedConfig) :
    packet.global.cover.FarRegion c ∨
      (∃ cand : CriticalDiskCandidate, c = cand.config ∧ CriticalDiskHypotheses cand) ∨
        packet.global.cover.OffDiagonalRegion c :=
  packet.global.trichotomy c

theorem StellatedAuditedPlanObligations.toRemaining_toPlan
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    plan.toRemainingObligations.toStellatedPlanObligations = plan :=
  rfl

theorem AuditedGeneratedRemainingObligations.toPlan_toRemaining
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain) :
    obligations.toStellatedPlanObligations.toRemainingObligations = obligations :=
  rfl

theorem StellatedAuditedPlanObligations.toStandard_toRemaining
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    plan.toStandardPlanObligations.toRemainingObligations =
      plan.toRemainingObligations.toStandardRemainingObligations :=
  rfl

theorem AuditedGeneratedRemainingObligations.toStandard_toPlan
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain) :
    obligations.toStandardRemainingObligations.toStellatedPlanObligations =
      obligations.toStellatedPlanObligations.toStandardPlanObligations :=
  rfl

theorem StellatedAuditedPlanObligations.toGlobalBranchObligations_toFarOffDiagonal
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    plan.toGlobalBranchObligations.toFarOffDiagonal = plan.farOff :=
  rfl

def AuditedGeneratedGlobalCertificate.toRemainingObligations
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalCertificate rhoF phiDomain xDomain yDomain) :
    AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain where
  sfAudit := cert.localCert.soundness.sf.sweep_audit
  sfSemantic := cert.localCert.soundness.sf.to_certificate
  sbPointwise := cert.localCert.soundness.sbBox.pointwise
  zoneConsequences := cert.localCert.zones
  globalCover := cert.cover
  farOffDiagonal := cert.farOff

def AuditedGeneratedRemainingObligations.toGlobalLocalCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain) :
    AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain :=
  auditedGeneratedGlobalLocalCertificate_of_audit_and_certificates_and_zones
    obligations.sfAudit obligations.sfSemantic obligations.sbPointwise
    obligations.zoneConsequences

def AuditedGeneratedRemainingObligations.toGlobalCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain) :
    AuditedGeneratedGlobalCertificate rhoF phiDomain xDomain yDomain where
  localCert := obligations.toGlobalLocalCertificate
  cover := obligations.globalCover
  farOff := obligations.farOffDiagonal

def AuditedGeneratedRemainingObligations.toStellatedGlobalCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain) :
    StellatedGlobalCertificate :=
  obligations.toGlobalCertificate.toGlobalCertificate

theorem AuditedGeneratedRemainingObligations.existsGlobalCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain) :
    ∃ _cert : StellatedGlobalCertificate, StellatedNonRupertStatement :=
  ⟨obligations.toStellatedGlobalCertificate,
    obligations.toStellatedGlobalCertificate.nonRupert⟩

theorem StellatedAuditedPlanObligations.nonRupert
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    StellatedNonRupertStatement :=
  plan.toRemainingObligations.toGlobalCertificate.nonRupert

theorem StellatedAuditedPlanObligations.existsGlobalCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    ∃ _cert : StellatedGlobalCertificate, StellatedNonRupertStatement :=
  plan.toRemainingObligations.existsGlobalCertificate

theorem StellatedAuditedFullPacket.nonRupert
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (packet : StellatedAuditedFullPacket rhoF phiDomain xDomain yDomain) :
    StellatedNonRupertStatement :=
  packet.toPlan.nonRupert

theorem StellatedAuditedFullPacket.existsGlobalCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (packet : StellatedAuditedFullPacket rhoF phiDomain xDomain yDomain) :
    ∃ _cert : StellatedGlobalCertificate, StellatedNonRupertStatement :=
  packet.toPlan.existsGlobalCertificate

theorem StellatedAuditedPlanObligations.standardNonRupert
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    StellatedNonRupertStatement :=
  plan.toStandardPlanObligations.nonRupert

theorem StellatedAuditedPlanObligations.standardExistsGlobalCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    ∃ _cert : StellatedGlobalCertificate, StellatedNonRupertStatement :=
  plan.toStandardPlanObligations.existsGlobalCertificate

theorem AuditedGeneratedRemainingObligations.nonRupert
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain) :
    StellatedNonRupertStatement :=
  obligations.toGlobalCertificate.nonRupert

theorem AuditedGeneratedRemainingObligations.excludes
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain)
    (c : StellatedConfig) :
    ¬ RupertContainment stellatedVertices c :=
  obligations.nonRupert c

theorem AuditedGeneratedRemainingObligations.false_of_containment
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    False :=
  obligations.excludes c hcont

theorem AuditedGeneratedRemainingObligations.trichotomy
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain)
    (c : StellatedConfig) :
    obligations.globalCover.FarRegion c ∨
      (∃ cand : CriticalDiskCandidate, c = cand.config ∧ CriticalDiskHypotheses cand) ∨
        obligations.globalCover.OffDiagonalRegion c :=
  obligations.globalCover.trichotomy c

theorem AuditedGeneratedRemainingObligations.nearCritical_of_not_far_not_offDiagonal
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain)
    {c : StellatedConfig}
    (hfar : ¬ obligations.globalCover.FarRegion c)
    (hoff : ¬ obligations.globalCover.OffDiagonalRegion c) :
    ∃ cand : CriticalDiskCandidate, c = cand.config ∧ CriticalDiskHypotheses cand :=
  obligations.globalCover.nearCritical_of_not_far_not_offDiagonal hfar hoff

theorem AuditedGeneratedRemainingObligations.notFar_of_containment
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    ¬ obligations.globalCover.FarRegion c := by
  intro hfar
  exact obligations.farOffDiagonal.farExcludes hfar hcont

theorem AuditedGeneratedRemainingObligations.notOffDiagonal_of_containment
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    ¬ obligations.globalCover.OffDiagonalRegion c := by
  intro hoff
  exact obligations.farOffDiagonal.offDiagonalExcludes hoff hcont

theorem AuditedGeneratedRemainingObligations.nearCritical_of_containment
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    ∃ cand : CriticalDiskCandidate, c = cand.config ∧ CriticalDiskHypotheses cand :=
  obligations.globalCover.nearCritical_of_not_far_not_offDiagonal
    (obligations.notFar_of_containment hcont)
    (obligations.notOffDiagonal_of_containment hcont)

theorem AuditedGeneratedRemainingObligations.excludes_of_not_far_not_offDiagonal
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain)
    {c : StellatedConfig}
    (hfar : ¬ obligations.globalCover.FarRegion c)
    (hoff : ¬ obligations.globalCover.OffDiagonalRegion c) :
    ¬ RupertContainment stellatedVertices c :=
  obligations.toGlobalCertificate.toGlobalCertificate.excludes_of_not_far_not_offDiagonal
    hfar hoff

theorem AuditedGeneratedRemainingObligations.excludesFar
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain)
    {c : StellatedConfig}
    (hfar : obligations.globalCover.FarRegion c) :
    ¬ RupertContainment stellatedVertices c :=
  obligations.farOffDiagonal.farExcludes hfar

theorem AuditedGeneratedRemainingObligations.excludesOffDiagonal
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain)
    {c : StellatedConfig}
    (hoff : obligations.globalCover.OffDiagonalRegion c) :
    ¬ RupertContainment stellatedVertices c :=
  obligations.farOffDiagonal.offDiagonalExcludes hoff

theorem AuditedGeneratedRemainingObligations.excludesNearCritical
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  (obligations.zoneConsequences cand).excludes hcand

theorem AuditedGeneratedRemainingObligations.coverWithDeferred
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain) :
    GeneratedSFWitness.manifest.DomainCoverWithDeferred
      phiDomain xDomain yDomain :=
  obligations.toGlobalLocalCertificate.coverWithDeferred

def AuditedGeneratedRemainingObligations.certifiedDomainCover
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain) :
    GeneratedSFWitness.manifest.CertifiedDomainCover
      phiDomain xDomain yDomain :=
  obligations.toGlobalLocalCertificate.certifiedDomainCover

theorem AuditedGeneratedRemainingObligations.sbBoxReplayAssemblyValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain) :
    SBBoxReplayAssembly
      GeneratedSBBoxTailWitness.manifest GeneratedSBBoxBulkWitness.manifest
      GeneratedSBBoxAssemblyReport.report
      GeneratedSBBoxAssemblyReport.tailDomain
      GeneratedSBBoxAssemblyReport.bulkDeltaDomain
      GeneratedSBBoxAssemblyReport.bulkPhiDomain
      GeneratedSBBoxBulkWitness.etaBudget :=
  obligations.toGlobalLocalCertificate.sbBoxReplayAssemblyValid

def StellatedAuditedPlanObligations.toGlobalLocalCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    AuditedGeneratedGlobalLocalCertificate rhoF phiDomain xDomain yDomain :=
  plan.toRemainingObligations.toGlobalLocalCertificate

def StellatedAuditedPlanObligations.toGlobalCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    AuditedGeneratedGlobalCertificate rhoF phiDomain xDomain yDomain :=
  plan.toRemainingObligations.toGlobalCertificate

def StellatedAuditedPlanObligations.toStellatedGlobalCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    StellatedGlobalCertificate :=
  plan.toRemainingObligations.toStellatedGlobalCertificate

theorem StellatedAuditedPlanObligations.localFamily
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    CriticalDiskLemma6PrimeGlobalFamily :=
  plan.toGlobalLocalCertificate.localFamily

def StellatedAuditedPlanObligations.localCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate) :
    AuditedGeneratedLocalCertificate rhoF phiDomain xDomain yDomain cand :=
  plan.toGlobalLocalCertificate.localCertificate cand

def StellatedAuditedPlanObligations.lemma6PrimeCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate) :
    CriticalDiskLemma6PrimeCertificate
      (plan.localCertificate cand).soundness.toCriticalDiskInputs cand :=
  (plan.localCertificate cand).lemma6PrimeCertificate

def StellatedAuditedPlanObligations.toCriticalDiskInputs
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate) :
    CriticalDiskCertifiedInputs :=
  (plan.localCertificate cand).toCriticalDiskInputs

theorem StellatedAuditedPlanObligations.inputs_allCertified
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate) :
    (plan.toCriticalDiskInputs cand).allCertified :=
  (plan.localCertificate cand).inputs_allCertified

theorem StellatedAuditedPlanObligations.lemma6prime
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate) :
    CriticalDiskLemma6PrimeStatement cand :=
  (plan.localCertificate cand).lemma6prime

theorem StellatedAuditedPlanObligations.exclusion
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  (plan.localCertificate cand).exclusion hcand

theorem StellatedAuditedPlanObligations.localizedExclusion
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate)
    (analytics : CriticalDiskAnalyticInputs) :
    CriticalDiskLocalizedExclusionStatement cand :=
  (plan.localCertificate cand).localizedExclusion analytics

theorem StellatedAuditedPlanObligations.excludes
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (c : StellatedConfig) :
    ¬ RupertContainment stellatedVertices c :=
  plan.toRemainingObligations.excludes c

theorem StellatedAuditedPlanObligations.false_of_containment
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    False :=
  plan.toRemainingObligations.false_of_containment hcont

theorem StellatedAuditedPlanObligations.trichotomy
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (c : StellatedConfig) :
    plan.cover.FarRegion c ∨
      (∃ cand : CriticalDiskCandidate, c = cand.config ∧ CriticalDiskHypotheses cand) ∨
        plan.cover.OffDiagonalRegion c :=
  plan.cover.trichotomy c

theorem StellatedAuditedPlanObligations.nearCritical_of_not_far_not_offDiagonal
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    {c : StellatedConfig}
    (hfar : ¬ plan.cover.FarRegion c)
    (hoff : ¬ plan.cover.OffDiagonalRegion c) :
    ∃ cand : CriticalDiskCandidate, c = cand.config ∧ CriticalDiskHypotheses cand :=
  plan.toRemainingObligations.nearCritical_of_not_far_not_offDiagonal hfar hoff

theorem StellatedAuditedPlanObligations.notFar_of_containment
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    ¬ plan.cover.FarRegion c :=
  plan.toRemainingObligations.notFar_of_containment hcont

theorem StellatedAuditedPlanObligations.notOffDiagonal_of_containment
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    ¬ plan.cover.OffDiagonalRegion c :=
  plan.toRemainingObligations.notOffDiagonal_of_containment hcont

theorem StellatedAuditedPlanObligations.nearCritical_of_containment
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    {c : StellatedConfig}
    (hcont : RupertContainment stellatedVertices c) :
    ∃ cand : CriticalDiskCandidate, c = cand.config ∧ CriticalDiskHypotheses cand :=
  plan.toRemainingObligations.nearCritical_of_containment hcont

theorem StellatedAuditedPlanObligations.excludesNearCritical
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  plan.toRemainingObligations.excludesNearCritical cand hcand

def StellatedAuditedPlanObligations.zoneConsequences
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate) :
    CriticalDiskZoneConsequences cand :=
  plan.zones cand

theorem StellatedAuditedPlanObligations.zoneLemma6prime
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate) :
    CriticalDiskLemma6PrimeStatement cand :=
  (plan.zoneConsequences cand).lemma6prime

theorem StellatedAuditedPlanObligations.zoneExcludes
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand) :
    CriticalDiskExclusion cand :=
  (plan.zoneConsequences cand).excludes hcand

theorem StellatedAuditedPlanObligations.zone0Excludes
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand)
    (hzone : CriticalDiskZone0 cand.point) :
    CriticalDiskExclusion cand :=
  (plan.zones cand).zone0Excludes hcand hzone

theorem StellatedAuditedPlanObligations.zoneAExcludes
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand)
    (hzone : CriticalDiskZoneA cand.point) :
    CriticalDiskExclusion cand :=
  (plan.zones cand).zoneAExcludes hcand hzone

theorem StellatedAuditedPlanObligations.zoneBExcludes
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand)
    (hzone : CriticalDiskZoneB cand.point) :
    CriticalDiskExclusion cand :=
  (plan.zones cand).zoneBExcludes hcand hzone

theorem StellatedAuditedPlanObligations.zoneCExcludes
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand)
    (hzone : CriticalDiskZoneC cand.point) :
    CriticalDiskExclusion cand :=
  (plan.zones cand).zoneCExcludes hcand hzone

theorem StellatedAuditedPlanObligations.zoneDExcludes
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (cand : CriticalDiskCandidate)
    (hcand : CriticalDiskHypotheses cand)
    (hzone : CriticalDiskZoneD cand.point) :
    CriticalDiskExclusion cand :=
  (plan.zones cand).zoneDExcludes hcand hzone

theorem StellatedAuditedPlanObligations.excludesFar
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    {c : StellatedConfig}
    (hfar : plan.cover.FarRegion c) :
    ¬ RupertContainment stellatedVertices c :=
  plan.toRemainingObligations.excludesFar hfar

theorem StellatedAuditedPlanObligations.excludesOffDiagonal
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    {c : StellatedConfig}
    (hoff : plan.cover.OffDiagonalRegion c) :
    ¬ RupertContainment stellatedVertices c :=
  plan.toRemainingObligations.excludesOffDiagonal hoff

theorem StellatedAuditedPlanObligations.excludes_of_not_far_not_offDiagonal
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    {c : StellatedConfig}
    (hfar : ¬ plan.cover.FarRegion c)
    (hoff : ¬ plan.cover.OffDiagonalRegion c) :
    ¬ RupertContainment stellatedVertices c :=
  plan.toRemainingObligations.excludes_of_not_far_not_offDiagonal hfar hoff

def StellatedAuditedPlanObligations.sfReplayEvidence
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (_plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    StellatedSFReplayEvidence :=
  stellatedGeneratedSFReplayEvidence

def StellatedAuditedPlanObligations.sfSemanticBridge
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    StellatedSFSemanticBridge rhoF :=
  plan.sf

def StellatedAuditedPlanObligations.sfAuditObligation
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    StellatedSFAuditObligation phiDomain xDomain yDomain :=
  plan.sfAudit

theorem StellatedAuditedPlanObligations.coverWithDeferred
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    GeneratedSFWitness.manifest.DomainCoverWithDeferred
      phiDomain xDomain yDomain :=
  plan.toRemainingObligations.coverWithDeferred

def StellatedAuditedPlanObligations.certifiedDomainCover
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    GeneratedSFWitness.manifest.CertifiedDomainCover
      phiDomain xDomain yDomain :=
  plan.toRemainingObligations.certifiedDomainCover

theorem StellatedAuditedPlanObligations.deferredDischarged
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (φ x y : ℝ)
    (hφ : phiDomain.contains φ) (hx : xDomain.contains x) (hy : yDomain.contains y)
    (hdeferred :
      ∃ row ∈ GeneratedSFWitness.manifest.deferred, row.box.contains φ x y) :
    ∃ row ∈ GeneratedSFWitness.manifest.certified, row.box.contains φ x y :=
  plan.sfAudit.deferred_discharged φ x y hφ hx hy hdeferred

theorem StellatedAuditedPlanObligations.existsValidCertifiedRow
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    {φ x y : ℝ}
    (hφ : phiDomain.contains φ) (hx : xDomain.contains x) (hy : yDomain.contains y) :
    ∃ row ∈ GeneratedSFWitness.manifest.certified,
      row.box.contains φ x y ∧
        row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  plan.toGlobalLocalCertificate.existsValidCertifiedRow hφ hx hy

theorem StellatedAuditedPlanObligations.sfCertifiedRowsValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    GeneratedSFWitness.manifest.CertifiedRowsValid
      GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  plan.toStandardPlanObligations.sfCertifiedRowsValid

theorem StellatedAuditedPlanObligations.sfCertifiedRowValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    {row : SFCertifiedSweepRow}
    (hrow : row ∈ GeneratedSFWitness.manifest.certified) :
    row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  plan.toGlobalLocalCertificate.sfCertifiedRowValid hrow

theorem StellatedAuditedPlanObligations.sfCovers
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    {φ s : ℝ}
    (hφlo : -Real.pi ≤ φ) (hφhi : φ ≤ Real.pi)
    (hslo : 0 ≤ s) (hshi : s ≤ 1) :
    ∃ c :
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.chart,
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.inChart
        c φ s :=
  plan.toGlobalLocalCertificate.sfCovers hφlo hφhi hslo hshi

theorem StellatedAuditedPlanObligations.sfChartClassified
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (c :
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.chart) :
    plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.isShell c ∨
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.isBulk c :=
  plan.toGlobalLocalCertificate.sfChartClassified c

theorem StellatedAuditedPlanObligations.sfCornerDistLower_nonneg
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (c :
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.chart) :
    0 ≤
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.cornerDistLower
        c :=
  plan.toGlobalLocalCertificate.sfCornerDistLower_nonneg c

theorem StellatedAuditedPlanObligations.sfShellBound
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (c :
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.chart)
    (hc :
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.isShell c) :
    plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.shellSlope *
        plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.cornerDistLower
          c ≤
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.psiLower c :=
  plan.toGlobalLocalCertificate.sfShellBound c hc

theorem StellatedAuditedPlanObligations.sfBulkBound
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (c :
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.chart)
    (hc :
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.isBulk c) :
    plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.psiMin ≤
      plan.toGlobalLocalCertificate.soundness.toCriticalDiskInputs.sf.certificate.psiLower c :=
  plan.toGlobalLocalCertificate.sfBulkBound c hc

def StellatedAuditedPlanObligations.sbBoxReplayEvidence
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (_plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    StellatedSBBoxReplayEvidence :=
  stellatedGeneratedSBBoxReplayEvidence

def StellatedAuditedPlanObligations.sbBoxPointwiseBridge
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    StellatedSBBoxPointwiseBridge :=
  plan.sbBox

theorem StellatedAuditedPlanObligations.sbBoxReplayAssemblyValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    SBBoxReplayAssembly
      GeneratedSBBoxTailWitness.manifest GeneratedSBBoxBulkWitness.manifest
      GeneratedSBBoxAssemblyReport.report
      GeneratedSBBoxAssemblyReport.tailDomain
      GeneratedSBBoxAssemblyReport.bulkDeltaDomain
      GeneratedSBBoxAssemblyReport.bulkPhiDomain
      GeneratedSBBoxBulkWitness.etaBudget :=
  plan.toRemainingObligations.sbBoxReplayAssemblyValid

theorem StellatedAuditedPlanObligations.sbBoxTailRowsValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    GeneratedSBBoxTailWitness.manifest.RowsValid :=
  plan.toGlobalLocalCertificate.sbBoxTailRowsValid

theorem StellatedAuditedPlanObligations.sbBoxBulkRowsValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    GeneratedSBBoxBulkWitness.manifest.RowsValid
      GeneratedSBBoxBulkWitness.etaBudget :=
  plan.toGlobalLocalCertificate.sbBoxBulkRowsValid

theorem StellatedAuditedPlanObligations.sbBoxTailRowValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    {row : SBBoxTailRow}
    (hrow : row ∈ GeneratedSBBoxTailWitness.manifest.rows) :
    row.Valid :=
  plan.toGlobalLocalCertificate.sbBoxTailRowValid hrow

theorem StellatedAuditedPlanObligations.sbBoxBulkRowValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    {row : SBBoxBulkRow}
    (hrow : row ∈ GeneratedSBBoxBulkWitness.manifest.rows) :
    row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  plan.toGlobalLocalCertificate.sbBoxBulkRowValid hrow

theorem StellatedAuditedPlanObligations.sbBoxTailExistsValidRow
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (chart : SBBoxTailChart) {r : ℝ}
    (hr : GeneratedSBBoxAssemblyReport.tailDomain.contains r) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains r ∧ row.Valid :=
  plan.toGlobalLocalCertificate.sbBoxTailExistsValidRow chart hr

theorem StellatedAuditedPlanObligations.sbBoxBulkExistsValidRow
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    {delta phi : ℝ}
    (hdelta : GeneratedSBBoxAssemblyReport.bulkDeltaDomain.contains delta)
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains delta ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  plan.toGlobalLocalCertificate.sbBoxBulkExistsValidRow hdelta hphi

theorem StellatedAuditedPlanObligations.sbBoxTailExistsValidRowAtZero
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (chart : SBBoxTailChart) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains (0 : ℝ) ∧ row.Valid :=
  plan.toGlobalLocalCertificate.sbBoxTailExistsValidRowAtZero chart

theorem StellatedAuditedPlanObligations.sbBoxTailExistsValidRowAtOne
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (chart : SBBoxTailChart) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains (1 : ℝ) ∧ row.Valid :=
  plan.toGlobalLocalCertificate.sbBoxTailExistsValidRowAtOne chart

theorem StellatedAuditedPlanObligations.sbBoxBulkExistsValidRowAtTailCut
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    {phi : ℝ}
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskTailCut ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  plan.toGlobalLocalCertificate.sbBoxBulkExistsValidRowAtTailCut hphi

theorem StellatedAuditedPlanObligations.sbBoxBulkExistsValidRowAtRhoCap
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    {phi : ℝ}
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskRhoCap ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  plan.toGlobalLocalCertificate.sbBoxBulkExistsValidRowAtRhoCap hphi

theorem StellatedAuditedPlanObligations.sbBoxBulkExistsValidRowAtTailCutZeroPhi
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskTailCut ∧ row.phi.contains (0 : ℝ) ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  plan.toGlobalLocalCertificate.sbBoxBulkExistsValidRowAtTailCutZeroPhi

theorem StellatedAuditedPlanObligations.sbBoxBulkExistsValidRowAtRhoCapZeroPhi
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskRhoCap ∧ row.phi.contains (0 : ℝ) ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  plan.toGlobalLocalCertificate.sbBoxBulkExistsValidRowAtRhoCapZeroPhi

def StellatedAuditedPlanObligations.sbBoxPointCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (plan : StellatedAuditedPlanObligations rhoF phiDomain xDomain yDomain)
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) {delta : ℝ}
    (hdelta_pos : 0 < delta) (hdelta_cap : delta ≤ criticalDiskRhoCap) :
    SBBoxPointCertificate R₂ delta
      criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT :=
  plan.sbBox R₂ hdelta_pos hdelta_cap

theorem AuditedGeneratedRemainingObligations.toRemainingObligations_toGlobalCertificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (obligations :
      AuditedGeneratedRemainingObligations rhoF phiDomain xDomain yDomain) :
    obligations.toGlobalCertificate.toRemainingObligations = obligations :=
  rfl

theorem AuditedGeneratedGlobalCertificate.nonRupert_via_remainingObligations
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (cert : AuditedGeneratedGlobalCertificate rhoF phiDomain xDomain yDomain) :
    cert.toRemainingObligations.nonRupert = cert.nonRupert :=
  rfl

/-- The current generated root-domain SF artifact also cannot supply the audited global-local
certificate bundle: the obstruction is already present in its common audited soundness field. -/
@[reducible] def noGeneratedRootAuditedGlobalLocalCertificate (rhoF : ℝ) :
    IsEmpty
      (AuditedGeneratedGlobalLocalCertificate rhoF
        GeneratedSFCertifiedInput.generatedPhiRootDomain
        GeneratedSFCertifiedInput.generatedUnitDomain
        GeneratedSFCertifiedInput.generatedUnitDomain) where
  false := by
    intro cert
    exact noGeneratedRootAuditedSoundness rhoF |>.false cert.soundness

/-- Consequently the current generated root-domain artifact cannot supply the final packaged
audited generated route either. -/
@[reducible] def noGeneratedRootAuditedGlobalCertificate (rhoF : ℝ) :
    IsEmpty
      (AuditedGeneratedGlobalCertificate rhoF
        GeneratedSFCertifiedInput.generatedPhiRootDomain
        GeneratedSFCertifiedInput.generatedUnitDomain
        GeneratedSFCertifiedInput.generatedUnitDomain) where
  false := by
    intro cert
    exact noGeneratedRootAuditedGlobalLocalCertificate rhoF |>.false cert.localCert

/-- The same root-domain obstruction rules out the audited remaining-obligations bundle. -/
@[reducible] def noGeneratedRootAuditedRemainingObligations (rhoF : ℝ) :
    IsEmpty
      (AuditedGeneratedRemainingObligations rhoF
        GeneratedSFCertifiedInput.generatedPhiRootDomain
        GeneratedSFCertifiedInput.generatedUnitDomain
        GeneratedSFCertifiedInput.generatedUnitDomain) where
  false := by
    intro obligations
    exact GeneratedSFCertifiedInput.generated_rootDomain_no_sweepAudit obligations.sfAudit

/-- The root-domain obstruction also rules out the draft §17 audited-plan target.  Any successful
audited plan must therefore replace the current generated root sweep domain or repair its cover. -/
@[reducible] def noGeneratedRootStellatedAuditedPlanObligations (rhoF : ℝ) :
    IsEmpty
      (StellatedAuditedPlanObligations rhoF
        GeneratedSFCertifiedInput.generatedPhiRootDomain
        GeneratedSFCertifiedInput.generatedUnitDomain
        GeneratedSFCertifiedInput.generatedUnitDomain) where
  false := by
    intro plan
    exact noGeneratedRootAuditedRemainingObligations rhoF |>.false
      plan.toRemainingObligations

theorem StellatedAuditedPlanObligations.false_of_generatedRoot
    {rhoF : ℝ}
    (plan :
      StellatedAuditedPlanObligations rhoF
        GeneratedSFCertifiedInput.generatedPhiRootDomain
        GeneratedSFCertifiedInput.generatedUnitDomain
        GeneratedSFCertifiedInput.generatedUnitDomain) :
    False :=
  noGeneratedRootStellatedAuditedPlanObligations rhoF |>.false plan

/-- The same obstruction rules out the fully split audited §17 packet on the current generated
root domain.  The packet carries generated replay evidence explicitly, but its `sfAudit` field
still cannot cover the origin in that root box. -/
@[reducible] def noGeneratedRootStellatedAuditedFullPacket (rhoF : ℝ) :
    IsEmpty
      (StellatedAuditedFullPacket rhoF
        GeneratedSFCertifiedInput.generatedPhiRootDomain
        GeneratedSFCertifiedInput.generatedUnitDomain
        GeneratedSFCertifiedInput.generatedUnitDomain) where
  false := by
    intro packet
    exact noGeneratedRootStellatedAuditedPlanObligations rhoF |>.false
      packet.toPlan

theorem StellatedAuditedFullPacket.false_of_generatedRoot
    {rhoF : ℝ}
    (packet :
      StellatedAuditedFullPacket rhoF
        GeneratedSFCertifiedInput.generatedPhiRootDomain
        GeneratedSFCertifiedInput.generatedUnitDomain
        GeneratedSFCertifiedInput.generatedUnitDomain) :
    False :=
  noGeneratedRootStellatedAuditedFullPacket rhoF |>.false packet

end RupertStellatedTetrahedron
