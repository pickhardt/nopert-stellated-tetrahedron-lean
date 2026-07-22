import RupertStellatedTetrahedron.CriticalDisk.CertifiedInputs
import RupertStellatedTetrahedron.CriticalDisk.Generated.SBBoxAssemblyReport

/-!
Lean boundary from the generated `(SB-box)` replay assembly to the standard certified input.

The replay assembly now proves the exact manifest facts: row validity, tail/bulk tiling, row
counts, and the seam/interface inequalities.  The remaining mathematical bridge is the row
soundness theorem turning those replay rows into the pointwise convex-hull inclusions consumed by
`SBBoxCertificate`.
-/

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

open DepthCylinderTheorem

namespace GeneratedSBBoxCertifiedInput

/-- The exact generated replay assembly, with all manifest tiling and interface facts checked. -/
theorem replayAssembly :
    SBBoxReplayAssembly
      GeneratedSBBoxTailWitness.manifest GeneratedSBBoxBulkWitness.manifest
      GeneratedSBBoxAssemblyReport.report
      GeneratedSBBoxAssemblyReport.tailDomain
      GeneratedSBBoxAssemblyReport.bulkDeltaDomain
      GeneratedSBBoxAssemblyReport.bulkPhiDomain
      GeneratedSBBoxBulkWitness.etaBudget :=
  GeneratedSBBoxAssemblyReport.replayAssembly

theorem tailRowsValid :
    GeneratedSBBoxTailWitness.manifest.RowsValid :=
  replayAssembly.tail_rows_valid

theorem bulkRowsValid :
    GeneratedSBBoxBulkWitness.manifest.RowsValid
      GeneratedSBBoxBulkWitness.etaBudget :=
  replayAssembly.bulk_rows_valid

theorem tail_row_valid
    {row : SBBoxTailRow}
    (hrow : row ∈ GeneratedSBBoxTailWitness.manifest.rows) :
    row.Valid :=
  tailRowsValid.row_valid hrow

theorem bulk_row_valid
    {row : SBBoxBulkRow}
    (hrow : row ∈ GeneratedSBBoxBulkWitness.manifest.rows) :
    row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  bulkRowsValid.row_valid hrow

/-- The generated replay keeps 40 failing tail rows out of the checked tail tiling.  The remaining
rows still tile the declared tail domain, but these failures are not semantic point certificates. -/
theorem omittedTailFailRows_eq :
    GeneratedSBBoxTailWitness.omittedFailRows = 40 :=
  GeneratedSBBoxTailWitness.omittedFailRows_eq

theorem tailRows_match_report :
    GeneratedSBBoxAssemblyReport.report.tailRows =
      GeneratedSBBoxTailWitness.rows.length :=
  GeneratedSBBoxAssemblyReport.tailRows_matches_manifest

theorem bulkRows_match_report :
    GeneratedSBBoxAssemblyReport.report.totalBulkRows =
      GeneratedSBBoxBulkWitness.rows.length :=
  GeneratedSBBoxAssemblyReport.bulkRows_matches_manifest

theorem bulkRows_split :
    GeneratedSBBoxAssemblyReport.report.totalBulkRows = 1544 + 146 :=
  GeneratedSBBoxAssemblyReport.bulkRows_split

theorem interfaceValid :
    GeneratedSBBoxAssemblyReport.report.InterfaceValid :=
  GeneratedSBBoxAssemblyReport.interfaceValid

theorem report_boxReachLower_toReal :
    (GeneratedSBBoxAssemblyReport.report.boxReachLower : ℝ) =
      criticalDiskBoxReachLower :=
  GeneratedSBBoxAssemblyReport.report_boxReachLower_toReal

theorem report_shellRadius_toReal :
    (GeneratedSBBoxAssemblyReport.report.shellRadius : ℝ) =
      criticalDiskShellRadius :=
  GeneratedSBBoxAssemblyReport.report_shellRadius_toReal

theorem report_tailEnd_toReal :
    (GeneratedSBBoxAssemblyReport.report.tailEnd : ℝ) =
      criticalDiskTailCut :=
  GeneratedSBBoxAssemblyReport.report_tailEnd_toReal

theorem report_rho0_toReal :
    (GeneratedSBBoxAssemblyReport.report.rho0 : ℝ) =
      criticalDiskRhoCap :=
  GeneratedSBBoxAssemblyReport.report_rho0_toReal

theorem interface_reaches_canonical_shell :
    criticalDiskShellRadius < criticalDiskBoxReachLower :=
  criticalDiskShellRadius_lt_boxReachLower

theorem tail_cut_before_rhoCap :
    criticalDiskTailCut < criticalDiskRhoCap :=
  criticalDiskTailCut_lt_rhoCap

theorem tailDomain_contains_zero :
    GeneratedSBBoxAssemblyReport.tailDomain.contains (0 : ℝ) :=
  GeneratedSBBoxAssemblyReport.tailDomain_contains_zero

theorem tailDomain_contains_one :
    GeneratedSBBoxAssemblyReport.tailDomain.contains (1 : ℝ) :=
  GeneratedSBBoxAssemblyReport.tailDomain_contains_one

theorem bulkDeltaDomain_contains_tailCut :
    GeneratedSBBoxAssemblyReport.bulkDeltaDomain.contains criticalDiskTailCut :=
  GeneratedSBBoxAssemblyReport.bulkDeltaDomain_contains_tailCut

theorem bulkDeltaDomain_contains_rhoCap :
    GeneratedSBBoxAssemblyReport.bulkDeltaDomain.contains criticalDiskRhoCap :=
  GeneratedSBBoxAssemblyReport.bulkDeltaDomain_contains_rhoCap

theorem bulkPhiDomain_contains_zero :
    GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains (0 : ℝ) :=
  GeneratedSBBoxAssemblyReport.bulkPhiDomain_contains_zero

/-- Every generated tail-chart parameter is covered by a replay row whose exact slack checks
have been reflected into proposition form. -/
theorem tail_exists_valid_row
    (chart : SBBoxTailChart) {r : ℝ}
    (hr : GeneratedSBBoxAssemblyReport.tailDomain.contains r) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains r ∧ row.Valid :=
  replayAssembly.tail_exists_valid_row chart hr

/-- Every generated bulk parameter pair is covered by a replay row whose exact slack and eta checks
have been reflected into proposition form. -/
theorem bulk_exists_valid_row
    {delta phi : ℝ}
    (hdelta : GeneratedSBBoxAssemblyReport.bulkDeltaDomain.contains delta)
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains delta ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  replayAssembly.bulk_exists_valid_row hdelta hphi

theorem tail_exists_valid_row_at_zero
    (chart : SBBoxTailChart) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains (0 : ℝ) ∧ row.Valid :=
  tail_exists_valid_row chart tailDomain_contains_zero

theorem tail_exists_valid_row_at_one
    (chart : SBBoxTailChart) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains (1 : ℝ) ∧ row.Valid :=
  tail_exists_valid_row chart tailDomain_contains_one

theorem bulk_exists_valid_row_at_tailCut
    {phi : ℝ}
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskTailCut ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  bulk_exists_valid_row bulkDeltaDomain_contains_tailCut hphi

theorem bulk_exists_valid_row_at_rhoCap
    {phi : ℝ}
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskRhoCap ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  bulk_exists_valid_row bulkDeltaDomain_contains_rhoCap hphi

theorem bulk_exists_valid_row_at_tailCut_zeroPhi :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskTailCut ∧ row.phi.contains (0 : ℝ) ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  bulk_exists_valid_row_at_tailCut bulkPhiDomain_contains_zero

theorem bulk_exists_valid_row_at_rhoCap_zeroPhi :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskRhoCap ∧ row.phi.contains (0 : ℝ) ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  bulk_exists_valid_row_at_rhoCap bulkPhiDomain_contains_zero

/-- The semantic pointwise `(SB-box)` certificate-producing bridge left after generated replay. -/
abbrev StandardPointwiseSoundness :=
  ∀ (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) {delta : ℝ},
    0 < delta → delta ≤ criticalDiskRhoCap →
      SBBoxPointCertificate R₂ delta
        criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT

/-- The one remaining `(SB-box)` bridge after exact replay:
valid replay rows plus their exact tiling imply the pointwise box-inclusion certificate at every
`δ ≤ ρ_B`. -/
structure StandardReplaySoundness where
  replay_assembly :
    SBBoxReplayAssembly
      GeneratedSBBoxTailWitness.manifest GeneratedSBBoxBulkWitness.manifest
      GeneratedSBBoxAssemblyReport.report
      GeneratedSBBoxAssemblyReport.tailDomain
      GeneratedSBBoxAssemblyReport.bulkDeltaDomain
      GeneratedSBBoxAssemblyReport.bulkPhiDomain
      GeneratedSBBoxBulkWitness.etaBudget
  pointwise : StandardPointwiseSoundness

/-- Constructor exposing the exact remaining `(SB-box)` obligation after replay: pointwise
box-inclusion soundness for every `δ ≤ ρ_B`. -/
def standardReplaySoundness_of_pointwise
    (pointwise : StandardPointwiseSoundness) :
    StandardReplaySoundness where
  replay_assembly := replayAssembly
  pointwise := pointwise

theorem StandardReplaySoundness.replayAssembly_valid
    (soundness : StandardReplaySoundness) :
    SBBoxReplayAssembly
      GeneratedSBBoxTailWitness.manifest GeneratedSBBoxBulkWitness.manifest
      GeneratedSBBoxAssemblyReport.report
      GeneratedSBBoxAssemblyReport.tailDomain
      GeneratedSBBoxAssemblyReport.bulkDeltaDomain
      GeneratedSBBoxAssemblyReport.bulkPhiDomain
      GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.replay_assembly

theorem StandardReplaySoundness.tailRowsValid
    (soundness : StandardReplaySoundness) :
    GeneratedSBBoxTailWitness.manifest.RowsValid :=
  soundness.replay_assembly.tail_rows_valid

theorem StandardReplaySoundness.bulkRowsValid
    (soundness : StandardReplaySoundness) :
    GeneratedSBBoxBulkWitness.manifest.RowsValid
      GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.replay_assembly.bulk_rows_valid

theorem StandardReplaySoundness.tailRowValid
    (soundness : StandardReplaySoundness)
    {row : SBBoxTailRow}
    (hrow : row ∈ GeneratedSBBoxTailWitness.manifest.rows) :
    row.Valid :=
  soundness.tailRowsValid.row_valid hrow

theorem StandardReplaySoundness.bulkRowValid
    (soundness : StandardReplaySoundness)
    {row : SBBoxBulkRow}
    (hrow : row ∈ GeneratedSBBoxBulkWitness.manifest.rows) :
    row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.bulkRowsValid.row_valid hrow

theorem StandardReplaySoundness.tailExistsValidRow
    (soundness : StandardReplaySoundness)
    (chart : SBBoxTailChart) {r : ℝ}
    (hr : GeneratedSBBoxAssemblyReport.tailDomain.contains r) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains r ∧ row.Valid :=
  soundness.replay_assembly.tail_exists_valid_row chart hr

theorem StandardReplaySoundness.bulkExistsValidRow
    (soundness : StandardReplaySoundness)
    {delta phi : ℝ}
    (hdelta : GeneratedSBBoxAssemblyReport.bulkDeltaDomain.contains delta)
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains delta ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.replay_assembly.bulk_exists_valid_row hdelta hphi

theorem StandardReplaySoundness.tailExistsValidRowAtZero
    (soundness : StandardReplaySoundness)
    (chart : SBBoxTailChart) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains (0 : ℝ) ∧ row.Valid :=
  soundness.tailExistsValidRow chart tailDomain_contains_zero

theorem StandardReplaySoundness.tailExistsValidRowAtOne
    (soundness : StandardReplaySoundness)
    (chart : SBBoxTailChart) :
    ∃ row ∈ GeneratedSBBoxTailWitness.manifest.rows,
      row.chart = chart ∧ row.r.contains (1 : ℝ) ∧ row.Valid :=
  soundness.tailExistsValidRow chart tailDomain_contains_one

theorem StandardReplaySoundness.bulkExistsValidRowAtTailCut
    (soundness : StandardReplaySoundness)
    {phi : ℝ}
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskTailCut ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.bulkExistsValidRow bulkDeltaDomain_contains_tailCut hphi

theorem StandardReplaySoundness.bulkExistsValidRowAtRhoCap
    (soundness : StandardReplaySoundness)
    {phi : ℝ}
    (hphi : GeneratedSBBoxAssemblyReport.bulkPhiDomain.contains phi) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskRhoCap ∧ row.phi.contains phi ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.bulkExistsValidRow bulkDeltaDomain_contains_rhoCap hphi

theorem StandardReplaySoundness.bulkExistsValidRowAtTailCutZeroPhi
    (soundness : StandardReplaySoundness) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskTailCut ∧ row.phi.contains (0 : ℝ) ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.bulkExistsValidRowAtTailCut bulkPhiDomain_contains_zero

theorem StandardReplaySoundness.bulkExistsValidRowAtRhoCapZeroPhi
    (soundness : StandardReplaySoundness) :
    ∃ row ∈ GeneratedSBBoxBulkWitness.manifest.rows,
      row.delta.contains criticalDiskRhoCap ∧ row.phi.contains (0 : ℝ) ∧
        row.Valid GeneratedSBBoxBulkWitness.etaBudget :=
  soundness.bulkExistsValidRowAtRhoCap bulkPhiDomain_contains_zero

def StandardReplaySoundness.toSBBoxCertificate
    (soundness : StandardReplaySoundness) :
    SBBoxCertificate criticalDiskRhoCap
      criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT where
  payload := standardSBBoxCheckerPayload criticalDiskRhoCapQ
  rhoB_eq := by
    simp [standardSBBoxCheckerPayload, criticalDiskRhoCapQ_toReal]
  bPi_eq := by
    simp [standardSBBoxCheckerPayload, criticalDiskBoxBPiQ_toReal]
  bGamma_eq := by
    simp [standardSBBoxCheckerPayload, criticalDiskBoxBGammaQ_toReal]
  bT_eq := by
    simp [standardSBBoxCheckerPayload, criticalDiskBoxBTQ_toReal]
  rhoB_pos := criticalDiskRhoCap_pos
  bPi_pos := criticalDiskBoxBPi_pos
  bGamma_pos := criticalDiskBoxBGamma_pos
  bT_pos := criticalDiskBoxBT_pos
  pointwise := soundness.pointwise

def standardSBBoxInput_of_replaySoundness
    (soundness : StandardReplaySoundness) : SBBoxInput :=
  standardSBBoxInput criticalDiskRhoCap soundness.toSBBoxCertificate

theorem standardSBBoxInput_of_replaySoundness_rhoB
    (soundness : StandardReplaySoundness) :
    (standardSBBoxInput_of_replaySoundness soundness).rhoB = criticalDiskRhoCap :=
  rfl

theorem standardSBBoxInput_of_replaySoundness_bPi
    (soundness : StandardReplaySoundness) :
    (standardSBBoxInput_of_replaySoundness soundness).bPi = criticalDiskBoxBPi :=
  rfl

theorem standardSBBoxInput_of_replaySoundness_bGamma
    (soundness : StandardReplaySoundness) :
    (standardSBBoxInput_of_replaySoundness soundness).bGamma = criticalDiskBoxBGamma :=
  rfl

theorem standardSBBoxInput_of_replaySoundness_bT
    (soundness : StandardReplaySoundness) :
    (standardSBBoxInput_of_replaySoundness soundness).bT = criticalDiskBoxBT :=
  rfl

theorem standardSBBoxInput_of_replaySoundness_certified
    (soundness : StandardReplaySoundness) :
    (standardSBBoxInput_of_replaySoundness soundness).certified := by
  exact (standardSBBoxInput_of_replaySoundness soundness).certified_of_certificate

def StandardReplaySoundness.pointCertificate
    (soundness : StandardReplaySoundness)
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) {delta : ℝ}
    (hdelta : 0 < delta) (hle : delta ≤ criticalDiskRhoCap) :
    SBBoxPointCertificate R₂ delta
      criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT :=
  soundness.pointwise R₂ hdelta hle

def StandardReplaySoundness.boxInclusion
    (soundness : StandardReplaySoundness)
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) {delta : ℝ}
    (hdelta : 0 < delta) (hle : delta ≤ criticalDiskRhoCap) :
    BoxInclusionCertificate
      (soundness.pointCertificate R₂ hdelta hle).cert :=
  (soundness.pointCertificate R₂ hdelta hle).toBoxInclusionCertificate

end GeneratedSBBoxCertifiedInput

end RupertStellatedTetrahedron
