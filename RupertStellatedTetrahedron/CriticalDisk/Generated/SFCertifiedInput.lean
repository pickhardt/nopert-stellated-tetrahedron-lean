import RupertStellatedTetrahedron.CriticalDisk.CertifiedInputs
import RupertStellatedTetrahedron.CriticalDisk.Generated.SFWitness

/-!
Lean boundary from the generated `(SF)` sweep witness to the standard certified input.

The generated witness currently proves exact rational stress validity for the certified rows of
`slf_witness.jsonl`.  It does not yet prove the audited semantic `(SF)` cover required by
`SFCertificate`, and its replayed stress floor is intentionally kept separate from the standard
critical-disk bulk floor.
-/

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

namespace GeneratedSFCertifiedInput

/-- Number of generated certified `(SF)` stress rows. -/
theorem certifiedRows_length :
    GeneratedSFWitness.certifiedRows.length = 566 :=
  GeneratedSFWitness.certifiedRows_length

/-- Number of generated deferred `(SF)` rows not discharged by the stress replay. -/
theorem deferredRows_length :
    GeneratedSFWitness.deferredRows.length = 48 :=
  GeneratedSFWitness.deferredRows_length

theorem certifiedRows_nonempty :
    0 < GeneratedSFWitness.certifiedRows.length := by
  rw [certifiedRows_length]
  norm_num

theorem deferredRows_nonempty :
    0 < GeneratedSFWitness.deferredRows.length := by
  rw [deferredRows_length]
  norm_num

theorem generatedStressFloor_toReal :
    (GeneratedSFWitness.psiMin : ℝ) = 1 / 400 := by
  norm_num [GeneratedSFWitness.psiMin]

theorem generatedTiltCap_toReal :
    (GeneratedSFWitness.tiltCap : ℝ) = 20 := by
  norm_num [GeneratedSFWitness.tiltCap]

theorem generatedStressFloor_pos :
    0 < (GeneratedSFWitness.psiMin : ℝ) := by
  norm_num [GeneratedSFWitness.psiMin]

theorem generatedTiltCap_pos :
    0 < (GeneratedSFWitness.tiltCap : ℝ) := by
  norm_num [GeneratedSFWitness.tiltCap]

/-- The exact generated stress replay for all certified rows. -/
theorem certifiedRowsValid :
    GeneratedSFWitness.manifest.CertifiedRowsValid
      GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  GeneratedSFWitness.manifest_certifiedRowsValid

theorem certified_row_valid
    {row : SFCertifiedSweepRow}
    (hrow : row ∈ GeneratedSFWitness.manifest.certified) :
    row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  certifiedRowsValid.row_valid hrow

theorem certified_row_valid_from_rowsValid
    (rowsValid :
      GeneratedSFWitness.manifest.CertifiedRowsValid
        GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap)
    {row : SFCertifiedSweepRow}
    (hrow : row ∈ GeneratedSFWitness.manifest.certified) :
    row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  rowsValid.row_valid hrow

/-- The generated stress floor is not the standard `(SF)` bulk floor from the critical-disk
assembly specification. -/
theorem generatedStressFloor_lt_standardBulkFloor :
    (GeneratedSFWitness.psiMin : ℝ) < criticalDiskPsiMin := by
  norm_num [GeneratedSFWitness.psiMin, criticalDiskPsiMin]

/-- A concrete generated stress row is below the standard `(SF)` bulk floor `3/50`.
This records that the current replay cannot be upgraded merely by replacing
`GeneratedSFWitness.psiMin` with the standard bulk constant. -/
theorem certifiedRow206_psiLower_lt_standardBulkFloor :
    (GeneratedSFWitness.certifiedRows.get ⟨206, by native_decide⟩).witness.psiLower <
      (3 / 50 : ℚ) := by
  native_decide

theorem certifiedRow206_not_valid_standardBulkFloor :
    ¬ (GeneratedSFWitness.certifiedRows.get ⟨206, by native_decide⟩).witness.Valid
      (3 / 50) GeneratedSFWitness.tiltCap := by
  intro h
  exact not_lt_of_ge h.psi_bound certifiedRow206_psiLower_lt_standardBulkFloor

/-- Root `φ` interval used by the current generated `slf_witness.jsonl` sweep. -/
def generatedPhiRootDomain : RatInterval where
  lo := 0
  hi := 63 / 20
  valid := by norm_num

/-- Unit interval used for both generated sweep coordinates `x` and `y`. -/
def generatedUnitDomain : RatInterval where
  lo := 0
  hi := 1
  valid := by norm_num

def generatedCertifiedRowsContainRatBool (φ x y : ℚ) : Bool :=
  GeneratedSFWitness.manifest.certified.any fun row => row.box.containsRatBool φ x y

def generatedDeferredRowsContainRatBool (φ x y : ℚ) : Bool :=
  GeneratedSFWitness.manifest.deferred.any fun row => row.box.containsRatBool φ x y

theorem origin_mem_generated_rootDomain :
    generatedPhiRootDomain.contains (0 : ℝ) ∧
      generatedUnitDomain.contains (0 : ℝ) ∧
      generatedUnitDomain.contains (0 : ℝ) := by
  norm_num [generatedPhiRootDomain, generatedUnitDomain, RatInterval.contains]

theorem origin_not_in_generated_certifiedRows_bool :
    generatedCertifiedRowsContainRatBool 0 0 0 = false := by
  native_decide

theorem origin_not_in_generated_deferredRows_bool :
    generatedDeferredRowsContainRatBool 0 0 0 = false := by
  native_decide

theorem origin_not_in_generated_certifiedRows :
    ¬ ∃ row ∈ GeneratedSFWitness.manifest.certified,
      row.box.contains (0 : ℝ) (0 : ℝ) (0 : ℝ) := by
  intro h
  obtain ⟨row, hrow, hcontains⟩ := h
  have hphi : row.box.phi.containsRatBool (0 : ℚ) = true :=
    RatInterval.containsRatBool_eq_true_of_contains
      (I := row.box.phi) (x := (0 : ℚ))
      (by simpa only [Rat.cast_zero] using hcontains.1)
  have hx : row.box.x.containsRatBool (0 : ℚ) = true :=
    RatInterval.containsRatBool_eq_true_of_contains
      (I := row.box.x) (x := (0 : ℚ))
      (by simpa only [Rat.cast_zero] using hcontains.2.1)
  have hy : row.box.y.containsRatBool (0 : ℚ) = true :=
    RatInterval.containsRatBool_eq_true_of_contains
      (I := row.box.y) (x := (0 : ℚ))
      (by simpa only [Rat.cast_zero] using hcontains.2.2)
  have hrowBool : row.box.containsRatBool 0 0 0 = true := by
    simp [SFSweepBox.containsRatBool, hphi, hx, hy]
  have hanyTrue :
      generatedCertifiedRowsContainRatBool 0 0 0 = true := by
    rw [generatedCertifiedRowsContainRatBool]
    exact List.any_eq_true.mpr ⟨row, hrow, hrowBool⟩
  rw [origin_not_in_generated_certifiedRows_bool] at hanyTrue
  contradiction

theorem origin_not_in_generated_deferredRows :
    ¬ ∃ row ∈ GeneratedSFWitness.manifest.deferred,
      row.box.contains (0 : ℝ) (0 : ℝ) (0 : ℝ) := by
  intro h
  obtain ⟨row, hrow, hcontains⟩ := h
  have hphi : row.box.phi.containsRatBool (0 : ℚ) = true :=
    RatInterval.containsRatBool_eq_true_of_contains
      (I := row.box.phi) (x := (0 : ℚ))
      (by simpa only [Rat.cast_zero] using hcontains.1)
  have hx : row.box.x.containsRatBool (0 : ℚ) = true :=
    RatInterval.containsRatBool_eq_true_of_contains
      (I := row.box.x) (x := (0 : ℚ))
      (by simpa only [Rat.cast_zero] using hcontains.2.1)
  have hy : row.box.y.containsRatBool (0 : ℚ) = true :=
    RatInterval.containsRatBool_eq_true_of_contains
      (I := row.box.y) (x := (0 : ℚ))
      (by simpa only [Rat.cast_zero] using hcontains.2.2)
  have hrowBool : row.box.containsRatBool 0 0 0 = true := by
    simp [SFSweepBox.containsRatBool, hphi, hx, hy]
  have hanyTrue :
      generatedDeferredRowsContainRatBool 0 0 0 = true := by
    rw [generatedDeferredRowsContainRatBool]
    exact List.any_eq_true.mpr ⟨row, hrow, hrowBool⟩
  rw [origin_not_in_generated_deferredRows_bool] at hanyTrue
  contradiction

theorem origin_not_in_generated_rows_withDeferred :
    ¬ ((∃ row ∈ GeneratedSFWitness.manifest.certified,
          row.box.contains (0 : ℝ) (0 : ℝ) (0 : ℝ)) ∨
        (∃ row ∈ GeneratedSFWitness.manifest.deferred,
          row.box.contains (0 : ℝ) (0 : ℝ) (0 : ℝ))) := by
  intro h
  cases h with
  | inl hcert => exact origin_not_in_generated_certifiedRows hcert
  | inr hdeferred => exact origin_not_in_generated_deferredRows hdeferred

theorem generated_rootDomain_cover_fails_at_origin
    (cover :
      GeneratedSFWitness.manifest.DomainCoverWithDeferred
        generatedPhiRootDomain generatedUnitDomain generatedUnitDomain) :
    False := by
  obtain hroot := origin_mem_generated_rootDomain
  exact origin_not_in_generated_rows_withDeferred
    (cover.covers 0 0 0 hroot.1 hroot.2.1 hroot.2.2)

theorem generated_rootDomain_not_covered_withDeferred :
    ¬ GeneratedSFWitness.manifest.DomainCoverWithDeferred
      generatedPhiRootDomain generatedUnitDomain generatedUnitDomain := by
  intro cover
  exact generated_rootDomain_cover_fails_at_origin cover

theorem generated_rootDomain_not_certifiedDomainCover :
    ¬ GeneratedSFWitness.manifest.CertifiedDomainCover
      generatedPhiRootDomain generatedUnitDomain generatedUnitDomain := by
  intro cover
  exact generated_rootDomain_not_covered_withDeferred cover.to_withDeferred

/-- The audited finite sweep facts still needed before the generated stress replay can be promoted
to the semantic `(SF)` input used by the critical-disk assembly. -/
structure GeneratedSweepAudit
    (phiDomain xDomain yDomain : RatInterval) : Prop where
  cover_with_deferred :
    GeneratedSFWitness.manifest.DomainCoverWithDeferred phiDomain xDomain yDomain
  deferred_discharged :
    ∀ φ x y : ℝ,
      phiDomain.contains φ → xDomain.contains x → yDomain.contains y →
        (∃ row ∈ GeneratedSFWitness.manifest.deferred, row.box.contains φ x y) →
          ∃ row ∈ GeneratedSFWitness.manifest.certified, row.box.contains φ x y

def GeneratedSweepAudit.certifiedDomainCover
    {phiDomain xDomain yDomain : RatInterval}
    (audit : GeneratedSweepAudit phiDomain xDomain yDomain) :
    GeneratedSFWitness.manifest.CertifiedDomainCover phiDomain xDomain yDomain where
  covers := by
    intro φ x y hφ hx hy
    cases audit.cover_with_deferred.covers φ x y hφ hx hy with
    | inl hcert => exact hcert
    | inr hdeferred => exact audit.deferred_discharged φ x y hφ hx hy hdeferred

theorem GeneratedSweepAudit.origin_exists_valid_certified_row
    {phiDomain xDomain yDomain : RatInterval}
    (audit : GeneratedSweepAudit phiDomain xDomain yDomain)
    (hφ : phiDomain.contains (0 : ℝ))
    (hx : xDomain.contains (0 : ℝ))
    (hy : yDomain.contains (0 : ℝ)) :
    ∃ row ∈ GeneratedSFWitness.manifest.certified,
      row.box.contains (0 : ℝ) (0 : ℝ) (0 : ℝ) ∧
        row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  audit.certifiedDomainCover.exists_valid_row certifiedRowsValid hφ hx hy

theorem GeneratedSweepAudit.exists_valid_certified_row
    {phiDomain xDomain yDomain : RatInterval}
    (audit : GeneratedSweepAudit phiDomain xDomain yDomain)
    {φ x y : ℝ}
    (hφ : phiDomain.contains φ) (hx : xDomain.contains x) (hy : yDomain.contains y) :
    ∃ row ∈ GeneratedSFWitness.manifest.certified,
      row.box.contains φ x y ∧
        row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  audit.certifiedDomainCover.exists_valid_row certifiedRowsValid hφ hx hy

theorem generated_rootDomain_no_sweepAudit :
    ¬ GeneratedSweepAudit generatedPhiRootDomain generatedUnitDomain generatedUnitDomain := by
  intro audit
  exact generated_rootDomain_not_covered_withDeferred audit.cover_with_deferred

/-- The semantic standard `(SF)` certificate obligation left after generated row replay. -/
abbrev StandardSemanticCertificate (rhoF : ℝ) :=
  SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
    criticalDiskShellSlope

/-- The remaining `(SF)` bridge after exact row replay:
the generated stress rows must be connected to an audited semantic `(SF)` certificate with the
standard critical-disk constants. -/
structure StandardSweepSoundness (rhoF : ℝ) where
  certified_rows_valid :
    GeneratedSFWitness.manifest.CertifiedRowsValid
      GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap
  to_certificate : StandardSemanticCertificate rhoF

/-- Constructor exposing the exact remaining standard `(SF)` obligation after generated row
replay: a semantic certificate with the critical-disk constants. -/
def standardSweepSoundness_of_certificate {rhoF : ℝ}
    (cert : StandardSemanticCertificate rhoF) :
    StandardSweepSoundness rhoF where
  certified_rows_valid := certifiedRowsValid
  to_certificate := cert

theorem StandardSweepSoundness.certifiedRowsValid {rhoF : ℝ}
    (soundness : StandardSweepSoundness rhoF) :
    GeneratedSFWitness.manifest.CertifiedRowsValid
      GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  soundness.certified_rows_valid

theorem StandardSweepSoundness.certifiedRowValid {rhoF : ℝ}
    (soundness : StandardSweepSoundness rhoF)
    {row : SFCertifiedSweepRow}
    (hrow : row ∈ GeneratedSFWitness.manifest.certified) :
    row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  soundness.certified_rows_valid.row_valid hrow

/-- Stronger boundary used once the audited sweep domain is fixed: it keeps the generated cover and
deferred-row discharge next to the semantic standard `(SF)` certificate. -/
structure StandardAuditedSweepSoundness
    (rhoF : ℝ) (phiDomain xDomain yDomain : RatInterval) where
  sweep_audit : GeneratedSweepAudit phiDomain xDomain yDomain
  to_certificate : StandardSemanticCertificate rhoF

/-- Constructor for the audited `(SF)` boundary once the domain cover/deferred-row audit and the
semantic standard certificate have both been supplied. -/
def standardAuditedSweepSoundness_of_audit_and_certificate
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (audit : GeneratedSweepAudit phiDomain xDomain yDomain)
    (cert : StandardSemanticCertificate rhoF) :
    StandardAuditedSweepSoundness rhoF phiDomain xDomain yDomain where
  sweep_audit := audit
  to_certificate := cert

def StandardAuditedSweepSoundness.toStandardSweepSoundness
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : StandardAuditedSweepSoundness rhoF phiDomain xDomain yDomain) :
    StandardSweepSoundness rhoF where
  certified_rows_valid := certifiedRowsValid
  to_certificate := soundness.to_certificate

theorem StandardAuditedSweepSoundness.certifiedRowsValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : StandardAuditedSweepSoundness rhoF phiDomain xDomain yDomain) :
    GeneratedSFWitness.manifest.CertifiedRowsValid
      GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  soundness.toStandardSweepSoundness.certifiedRowsValid

theorem StandardAuditedSweepSoundness.certifiedRowValid
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : StandardAuditedSweepSoundness rhoF phiDomain xDomain yDomain)
    {row : SFCertifiedSweepRow}
    (hrow : row ∈ GeneratedSFWitness.manifest.certified) :
    row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  soundness.toStandardSweepSoundness.certifiedRowValid hrow

theorem StandardAuditedSweepSoundness.coverWithDeferred
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : StandardAuditedSweepSoundness rhoF phiDomain xDomain yDomain) :
    GeneratedSFWitness.manifest.DomainCoverWithDeferred
      phiDomain xDomain yDomain :=
  soundness.sweep_audit.cover_with_deferred

theorem StandardAuditedSweepSoundness.deferredDischarged
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : StandardAuditedSweepSoundness rhoF phiDomain xDomain yDomain)
    (φ x y : ℝ)
    (hφ : phiDomain.contains φ) (hx : xDomain.contains x) (hy : yDomain.contains y)
    (hdeferred :
      ∃ row ∈ GeneratedSFWitness.manifest.deferred, row.box.contains φ x y) :
    ∃ row ∈ GeneratedSFWitness.manifest.certified, row.box.contains φ x y :=
  soundness.sweep_audit.deferred_discharged φ x y hφ hx hy hdeferred

def StandardAuditedSweepSoundness.certifiedDomainCover
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : StandardAuditedSweepSoundness rhoF phiDomain xDomain yDomain) :
    GeneratedSFWitness.manifest.CertifiedDomainCover
      phiDomain xDomain yDomain :=
  soundness.sweep_audit.certifiedDomainCover

theorem StandardAuditedSweepSoundness.existsValidCertifiedRow
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : StandardAuditedSweepSoundness rhoF phiDomain xDomain yDomain)
    {φ x y : ℝ}
    (hφ : phiDomain.contains φ) (hx : xDomain.contains x) (hy : yDomain.contains y) :
    ∃ row ∈ GeneratedSFWitness.manifest.certified,
      row.box.contains φ x y ∧
        row.witness.Valid GeneratedSFWitness.psiMin GeneratedSFWitness.tiltCap :=
  soundness.sweep_audit.exists_valid_certified_row hφ hx hy

@[reducible] def generated_rootDomain_no_standardAuditedSweepSoundness
    (rhoF : ℝ) :
    IsEmpty
      (StandardAuditedSweepSoundness rhoF
        generatedPhiRootDomain generatedUnitDomain generatedUnitDomain) where
  false := by
    intro soundness
    exact generated_rootDomain_no_sweepAudit soundness.sweep_audit

def StandardSweepSoundness.toSFInput {rhoF : ℝ}
    (soundness : StandardSweepSoundness rhoF) : SFInput :=
  standardSFInput rhoF soundness.to_certificate

theorem StandardSweepSoundness.toSFInput_rhoF {rhoF : ℝ}
    (soundness : StandardSweepSoundness rhoF) :
    soundness.toSFInput.rhoF = rhoF :=
  rfl

theorem StandardSweepSoundness.toSFInput_rb {rhoF : ℝ}
    (soundness : StandardSweepSoundness rhoF) :
    soundness.toSFInput.rb = criticalDiskRb :=
  rfl

theorem StandardSweepSoundness.toSFInput_nu {rhoF : ℝ}
    (soundness : StandardSweepSoundness rhoF) :
    soundness.toSFInput.nu = criticalDiskNu :=
  rfl

theorem StandardSweepSoundness.toSFInput_psiMin {rhoF : ℝ}
    (soundness : StandardSweepSoundness rhoF) :
    soundness.toSFInput.psiMin = criticalDiskPsiMin :=
  rfl

theorem StandardSweepSoundness.toSFInput_shellSlope {rhoF : ℝ}
    (soundness : StandardSweepSoundness rhoF) :
    soundness.toSFInput.shellSlope = criticalDiskShellSlope :=
  rfl

theorem StandardSweepSoundness.toSFInput_certified {rhoF : ℝ}
    (soundness : StandardSweepSoundness rhoF) :
    soundness.toSFInput.certified := by
  exact soundness.toSFInput.certified_of_certificate

theorem StandardSweepSoundness.covers
    {rhoF : ℝ} (soundness : StandardSweepSoundness rhoF)
    {φ s : ℝ}
    (hφlo : -Real.pi ≤ φ) (hφhi : φ ≤ Real.pi)
    (hslo : 0 ≤ s) (hshi : s ≤ 1) :
    ∃ c : soundness.toSFInput.certificate.chart,
      soundness.toSFInput.certificate.inChart c φ s :=
  soundness.toSFInput.covers hφlo hφhi hslo hshi

theorem StandardSweepSoundness.chartClassified
    {rhoF : ℝ} (soundness : StandardSweepSoundness rhoF)
    (c : soundness.toSFInput.certificate.chart) :
    soundness.toSFInput.certificate.isShell c ∨
      soundness.toSFInput.certificate.isBulk c :=
  soundness.toSFInput.chartClassified c

theorem StandardSweepSoundness.cornerDistLower_nonneg
    {rhoF : ℝ} (soundness : StandardSweepSoundness rhoF)
    (c : soundness.toSFInput.certificate.chart) :
    0 ≤ soundness.toSFInput.certificate.cornerDistLower c :=
  soundness.toSFInput.cornerDistLower_nonneg c

theorem StandardSweepSoundness.shellBound
    {rhoF : ℝ} (soundness : StandardSweepSoundness rhoF)
    (c : soundness.toSFInput.certificate.chart)
    (hc : soundness.toSFInput.certificate.isShell c) :
    soundness.toSFInput.shellSlope *
        soundness.toSFInput.certificate.cornerDistLower c ≤
      soundness.toSFInput.certificate.psiLower c :=
  soundness.toSFInput.shellBound c hc

theorem StandardSweepSoundness.bulkBound
    {rhoF : ℝ} (soundness : StandardSweepSoundness rhoF)
    (c : soundness.toSFInput.certificate.chart)
    (hc : soundness.toSFInput.certificate.isBulk c) :
    soundness.toSFInput.psiMin ≤
      soundness.toSFInput.certificate.psiLower c :=
  soundness.toSFInput.bulkBound c hc

theorem StandardAuditedSweepSoundness.covers
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : StandardAuditedSweepSoundness rhoF phiDomain xDomain yDomain)
    {φ s : ℝ}
    (hφlo : -Real.pi ≤ φ) (hφhi : φ ≤ Real.pi)
    (hslo : 0 ≤ s) (hshi : s ≤ 1) :
    ∃ c : soundness.toStandardSweepSoundness.toSFInput.certificate.chart,
      soundness.toStandardSweepSoundness.toSFInput.certificate.inChart c φ s :=
  soundness.toStandardSweepSoundness.covers hφlo hφhi hslo hshi

theorem StandardAuditedSweepSoundness.chartClassified
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : StandardAuditedSweepSoundness rhoF phiDomain xDomain yDomain)
    (c : soundness.toStandardSweepSoundness.toSFInput.certificate.chart) :
    soundness.toStandardSweepSoundness.toSFInput.certificate.isShell c ∨
      soundness.toStandardSweepSoundness.toSFInput.certificate.isBulk c :=
  soundness.toStandardSweepSoundness.chartClassified c

theorem StandardAuditedSweepSoundness.cornerDistLower_nonneg
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : StandardAuditedSweepSoundness rhoF phiDomain xDomain yDomain)
    (c : soundness.toStandardSweepSoundness.toSFInput.certificate.chart) :
    0 ≤ soundness.toStandardSweepSoundness.toSFInput.certificate.cornerDistLower c :=
  soundness.toStandardSweepSoundness.cornerDistLower_nonneg c

theorem StandardAuditedSweepSoundness.shellBound
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : StandardAuditedSweepSoundness rhoF phiDomain xDomain yDomain)
    (c : soundness.toStandardSweepSoundness.toSFInput.certificate.chart)
    (hc : soundness.toStandardSweepSoundness.toSFInput.certificate.isShell c) :
    soundness.toStandardSweepSoundness.toSFInput.shellSlope *
        soundness.toStandardSweepSoundness.toSFInput.certificate.cornerDistLower c ≤
      soundness.toStandardSweepSoundness.toSFInput.certificate.psiLower c :=
  soundness.toStandardSweepSoundness.shellBound c hc

theorem StandardAuditedSweepSoundness.bulkBound
    {rhoF : ℝ} {phiDomain xDomain yDomain : RatInterval}
    (soundness : StandardAuditedSweepSoundness rhoF phiDomain xDomain yDomain)
    (c : soundness.toStandardSweepSoundness.toSFInput.certificate.chart)
    (hc : soundness.toStandardSweepSoundness.toSFInput.certificate.isBulk c) :
    soundness.toStandardSweepSoundness.toSFInput.psiMin ≤
      soundness.toStandardSweepSoundness.toSFInput.certificate.psiLower c :=
  soundness.toStandardSweepSoundness.bulkBound c hc

end GeneratedSFCertifiedInput

end RupertStellatedTetrahedron
