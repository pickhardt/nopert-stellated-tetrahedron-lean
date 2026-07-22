import RupertStellatedTetrahedron.CriticalDisk.Constants
import RupertStellatedTetrahedron.CriticalDisk.ExactCertificates
import RupertStellatedTetrahedron.CriticalDisk.ExactConstants
import RupertStellatedTetrahedron.CriticalDisk.Statement
import RupertStellatedTetrahedron.CriticalDisk.TranslationKill
import RupertStellatedTetrahedron.DepthCylinderTheorem.BoxCylinder
import RupertStellatedTetrahedron.Local.ContactBase
import RupertStellatedTetrahedron.Local.EpsilonSlack
import RupertStellatedTetrahedron.Stellated.Vertices

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

open DepthCylinderTheorem

/-!
## Certified inputs for the critical-disk proof

These structures name the two pieces that are checked by external programs in the current proof
draft: the second-order sweep `(SF)` and the box certificate `(SB-box)`.  Both are proof-carrying:
`(SF)` supplies a charted lower-bound cover, and `(SB-box)` supplies the finite active-pair
scaled-box inclusions consumed by the box-cylinder theorem.
-/

/-- The `(SF)` second-order sweep certificate over the rescaled marginal segment.

The external checker must provide a chart cover of `φ ∈ [-π,π]` and segment parameter `s ∈ [0,1]`.
Each chart is classified as shell or bulk and carries a certified lower bound for the second-order
functional `Ψ`.
-/
structure SFCertificate (rhoF rb nu psiMin shellSlope : ℝ) where
  payload : SFCheckerPayload
  rhoF_eq : rhoF = payload.rhoF.toReal
  rb_eq : rb = payload.rb.toReal
  nu_eq : nu = payload.nu.toReal
  psiMin_eq : psiMin = payload.psiMin.toReal
  shellSlope_eq : shellSlope = payload.shellSlope.toReal
  rhoF_pos : 0 < rhoF
  rb_pos : 0 < rb
  nu_pos : 0 < nu
  psiMin_pos : 0 < psiMin
  shellSlope_pos : 0 < shellSlope
  chart : Type
  inChart : chart → ℝ → ℝ → Prop
  isShell : chart → Prop
  isBulk : chart → Prop
  cornerDistLower : chart → ℝ
  psiLower : chart → ℝ
  covers :
    ∀ φ s : ℝ, -Real.pi ≤ φ → φ ≤ Real.pi → 0 ≤ s → s ≤ 1 →
      ∃ c : chart, inChart c φ s
  chartClassified : ∀ c : chart, isShell c ∨ isBulk c
  cornerDistLower_nonneg : ∀ c : chart, 0 ≤ cornerDistLower c
  shellBound :
    ∀ c : chart, isShell c → shellSlope * cornerDistLower c ≤ psiLower c
  bulkBound :
    ∀ c : chart, isBulk c → psiMin ≤ psiLower c

structure SFPayloadVerified
    (payload : SFCheckerPayload) (rhoF rb nu psiMin shellSlope : ℝ) : Prop where
  rhoF_eq : rhoF = payload.rhoF.toReal
  rb_eq : rb = payload.rb.toReal
  nu_eq : nu = payload.nu.toReal
  psiMin_eq : psiMin = payload.psiMin.toReal
  shellSlope_eq : shellSlope = payload.shellSlope.toReal
  rhoF_pos : 0 < rhoF
  rb_pos : 0 < rb
  nu_pos : 0 < nu
  psiMin_pos : 0 < psiMin
  shellSlope_pos : 0 < shellSlope
  covers :
    ∀ φ s : ℝ, -Real.pi ≤ φ → φ ≤ Real.pi → 0 ≤ s → s ≤ 1 →
      ∃ c ∈ payload.charts, c.phi.contains φ ∧ c.segment.contains s
  cornerDistLower_nonneg :
    ∀ c ∈ payload.charts, 0 ≤ c.cornerDistanceLower.toReal
  shellBound :
    ∀ c ∈ payload.charts, c.chartClass = SFChartClass.shell →
      shellSlope * c.cornerDistanceLower.toReal ≤ c.psiLower.toReal
  bulkBound :
    ∀ c ∈ payload.charts, c.chartClass = SFChartClass.bulk →
      psiMin ≤ c.psiLower.toReal

def SFPayloadVerified.toCertificate
    {payload : SFCheckerPayload} {rhoF rb nu psiMin shellSlope : ℝ}
    (verified : SFPayloadVerified payload rhoF rb nu psiMin shellSlope) :
    SFCertificate rhoF rb nu psiMin shellSlope where
  payload := payload
  rhoF_eq := verified.rhoF_eq
  rb_eq := verified.rb_eq
  nu_eq := verified.nu_eq
  psiMin_eq := verified.psiMin_eq
  shellSlope_eq := verified.shellSlope_eq
  rhoF_pos := verified.rhoF_pos
  rb_pos := verified.rb_pos
  nu_pos := verified.nu_pos
  psiMin_pos := verified.psiMin_pos
  shellSlope_pos := verified.shellSlope_pos
  chart := { c : SFChartRecord // c ∈ payload.charts }
  inChart c φ s := c.val.phi.contains φ ∧ c.val.segment.contains s
  isShell c := c.val.chartClass = SFChartClass.shell
  isBulk c := c.val.chartClass = SFChartClass.bulk
  cornerDistLower c := c.val.cornerDistanceLower.toReal
  psiLower c := c.val.psiLower.toReal
  covers := by
    intro φ s hφlo hφhi hslo hshi
    obtain ⟨c, hc, hφs⟩ := verified.covers φ s hφlo hφhi hslo hshi
    exact ⟨⟨c, hc⟩, hφs⟩
  chartClassified := by
    intro c
    cases c.val.chartClass <;> simp
  cornerDistLower_nonneg := by
    intro c
    exact verified.cornerDistLower_nonneg c.val c.property
  shellBound := by
    intro c hc
    exact verified.shellBound c.val c.property hc
  bulkBound := by
    intro c hc
    exact verified.bulkBound c.val c.property hc

structure SFInput where
  rhoF : ℝ
  rb : ℝ
  nu : ℝ
  psiMin : ℝ
  shellSlope : ℝ
  certificate : SFCertificate rhoF rb nu psiMin shellSlope

def SFInput.certified (input : SFInput) : Prop :=
  0 < input.rhoF ∧ 0 < input.rb ∧ 0 < input.nu ∧
    0 < input.psiMin ∧ 0 < input.shellSlope

theorem SFInput.certified_of_certificate (input : SFInput) :
    input.certified := by
  exact ⟨input.certificate.rhoF_pos, input.certificate.rb_pos,
    input.certificate.nu_pos, input.certificate.psiMin_pos,
    input.certificate.shellSlope_pos⟩

theorem SFInput.rhoF_pos (input : SFInput) (h : input.certified) :
    0 < input.rhoF :=
  h.1

theorem SFInput.rb_pos (input : SFInput) (h : input.certified) :
    0 < input.rb :=
  h.2.1

theorem SFInput.nu_pos (input : SFInput) (h : input.certified) :
    0 < input.nu :=
  h.2.2.1

theorem SFInput.psiMin_pos (input : SFInput) (h : input.certified) :
    0 < input.psiMin :=
  h.2.2.2.1

theorem SFInput.shellSlope_pos (input : SFInput) (h : input.certified) :
    0 < input.shellSlope :=
  h.2.2.2.2

theorem SFInput.covers
    (input : SFInput) {φ s : ℝ}
    (hφlo : -Real.pi ≤ φ) (hφhi : φ ≤ Real.pi)
    (hslo : 0 ≤ s) (hshi : s ≤ 1) :
    ∃ c : input.certificate.chart, input.certificate.inChart c φ s :=
  input.certificate.covers φ s hφlo hφhi hslo hshi

theorem SFInput.chartClassified
    (input : SFInput) (c : input.certificate.chart) :
    input.certificate.isShell c ∨ input.certificate.isBulk c :=
  input.certificate.chartClassified c

theorem SFInput.cornerDistLower_nonneg
    (input : SFInput) (c : input.certificate.chart) :
    0 ≤ input.certificate.cornerDistLower c :=
  input.certificate.cornerDistLower_nonneg c

theorem SFInput.shellBound
    (input : SFInput) (c : input.certificate.chart)
    (hc : input.certificate.isShell c) :
    input.shellSlope * input.certificate.cornerDistLower c ≤
      input.certificate.psiLower c :=
  input.certificate.shellBound c hc

theorem SFInput.bulkBound
    (input : SFInput) (c : input.certificate.chart)
    (hc : input.certificate.isBulk c) :
    input.psiMin ≤ input.certificate.psiLower c :=
  input.certificate.bulkBound c hc

/-- One checked scaled-box inclusion at a fixed outer orientation and radius. -/
structure SBBoxPointCertificate
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (delta bPi bGamma bT : ℝ) where
  cert : Finset (ActivePair stellatedVertices R₂)
  delta_pos : 0 < delta
  bPi_pos : 0 < bPi
  bGamma_pos : 0 < bGamma
  bT_pos : 0 < bT
  scaledBoxSubset :
    ∀ y : BoxFlag5, scaledBoxMember delta bPi bGamma bT y →
      y ∈ convexHull ℝ (flagFinset cert : Set BoxFlag5)

def SBBoxPointCertificate.toBoxInclusionCertificate
    {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ}
    {delta bPi bGamma bT : ℝ}
    (cert : SBBoxPointCertificate R₂ delta bPi bGamma bT) :
    BoxInclusionCertificate cert.cert where
  delta := delta
  bPi := bPi
  bGamma := bGamma
  bT := bT
  delta_pos := cert.delta_pos
  bPi_pos := cert.bPi_pos
  bGamma_pos := cert.bGamma_pos
  bT_pos := cert.bT_pos
  scaledBoxSubset := cert.scaledBoxSubset

def SBBoxPointPayload.witnessEvalFinset (payload : SBBoxPointPayload) : Finset BoxFlag5 := by
  classical
  exact Finset.univ.image fun i : Fin payload.boxVertexWitnesses.length =>
    ExactVec.toReal
      ((payload.boxVertexWitnesses.get i).evalExact (ExactFlagList.exactTable payload.activeFlags))

structure SBBoxPointPayloadVerified
    (payload : SBBoxPointPayload)
    {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ}
    (cert : Finset (ActivePair stellatedVertices R₂))
    (delta bPi bGamma bT : ℝ) : Type where
  delta_eq : delta = payload.delta.toReal
  activeFlags_eq :
    ExactFlagList.realFinset payload.activeFlags = flagFinset cert
  boxVertexWitness_valid :
    ∀ i : Fin payload.boxVertexWitnesses.length,
      (payload.boxVertexWitnesses.get i).ValidAgainstExactFlags payload.activeFlags
  scaledBoxSubset_witnessHull :
    ∀ y : BoxFlag5, scaledBoxMember delta bPi bGamma bT y →
      y ∈ convexHull ℝ (payload.witnessEvalFinset : Set BoxFlag5)

def SBBoxPointPayloadVerified.toPointCertificate
    {payload : SBBoxPointPayload}
    {R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ}
    {cert : Finset (ActivePair stellatedVertices R₂)}
    {delta bPi bGamma bT : ℝ}
    (verified : SBBoxPointPayloadVerified payload cert delta bPi bGamma bT)
    (hdelta : 0 < delta) (hbPi : 0 < bPi) (hbGamma : 0 < bGamma) (hbT : 0 < bT) :
    SBBoxPointCertificate R₂ delta bPi bGamma bT where
  cert := cert
  delta_pos := hdelta
  bPi_pos := hbPi
  bGamma_pos := hbGamma
  bT_pos := hbT
  scaledBoxSubset := by
    intro y hy
    have hwitness_subset :
        (payload.witnessEvalFinset : Set BoxFlag5) ⊆
          convexHull ℝ (flagFinset cert : Set BoxFlag5) := by
      intro z hz
      rw [SBBoxPointPayload.witnessEvalFinset] at hz
      obtain ⟨i, _hi, hiz⟩ := Finset.mem_image.mp hz
      rw [← hiz]
      have hmem :=
        ConvexComboWitness.evalExact_toReal_mem_convexHull_exactFlags
          (w := payload.boxVertexWitnesses.get i) (flags := payload.activeFlags)
          (verified.boxVertexWitness_valid i)
      simpa [verified.activeFlags_eq] using hmem
    exact convexHull_min hwitness_subset (convex_convexHull ℝ _) 
      (verified.scaledBoxSubset_witnessHull y hy)

/-- The `(SB-box)` certified input: every radius up to `rhoB` has a finite active-pair
scaled-box inclusion with the advertised box half-widths. -/
structure SBBoxCertificate (rhoB bPi bGamma bT : ℝ) where
  payload : SBBoxCheckerPayload
  rhoB_eq : rhoB = payload.rhoB.toReal
  bPi_eq : bPi = payload.bPi.toReal
  bGamma_eq : bGamma = payload.bGamma.toReal
  bT_eq : bT = payload.bT.toReal
  rhoB_pos : 0 < rhoB
  bPi_pos : 0 < bPi
  bGamma_pos : 0 < bGamma
  bT_pos : 0 < bT
  pointwise :
    ∀ (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) {delta : ℝ},
      0 < delta → delta ≤ rhoB → SBBoxPointCertificate R₂ delta bPi bGamma bT

structure SBBoxPayloadVerified
    (payload : SBBoxCheckerPayload) (rhoB bPi bGamma bT : ℝ) where
  rhoB_eq : rhoB = payload.rhoB.toReal
  bPi_eq : bPi = payload.bPi.toReal
  bGamma_eq : bGamma = payload.bGamma.toReal
  bT_eq : bT = payload.bT.toReal
  rhoB_pos : 0 < rhoB
  bPi_pos : 0 < bPi
  bGamma_pos : 0 < bGamma
  bT_pos : 0 < bT
  pointwise :
    ∀ (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) {delta : ℝ},
      0 < delta → delta ≤ rhoB →
        Σ chart : { chart : SBBoxChartRecord //
            chart ∈ payload.charts ∧ chart.deltaRange.contains delta },
          Σ pointPayload : { pointPayload : SBBoxPointPayload //
              pointPayload ∈ chart.val.points },
            Σ cert : Finset (ActivePair stellatedVertices R₂),
              SBBoxPointPayloadVerified pointPayload.val cert delta bPi bGamma bT

def SBBoxPayloadVerified.toCertificate
    {payload : SBBoxCheckerPayload} {rhoB bPi bGamma bT : ℝ}
    (verified : SBBoxPayloadVerified payload rhoB bPi bGamma bT) :
    SBBoxCertificate rhoB bPi bGamma bT where
  payload := payload
  rhoB_eq := verified.rhoB_eq
  bPi_eq := verified.bPi_eq
  bGamma_eq := verified.bGamma_eq
  bT_eq := verified.bT_eq
  rhoB_pos := verified.rhoB_pos
  bPi_pos := verified.bPi_pos
  bGamma_pos := verified.bGamma_pos
  bT_pos := verified.bT_pos
  pointwise := by
    intro R₂ delta hdelta hle
    obtain ⟨_chart, pointPayload, cert, hverified⟩ :=
      verified.pointwise R₂ hdelta hle
    exact hverified.toPointCertificate hdelta verified.bPi_pos verified.bGamma_pos verified.bT_pos

def SBBoxCertificate.boxInclusion
    {rhoB bPi bGamma bT : ℝ}
    (cert : SBBoxCertificate rhoB bPi bGamma bT)
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    {delta : ℝ} (hdelta : 0 < delta) (hle : delta ≤ rhoB) :
    BoxInclusionCertificate (cert.pointwise R₂ hdelta hle).cert :=
  (cert.pointwise R₂ hdelta hle).toBoxInclusionCertificate

structure SBBoxInput where
  rhoB : ℝ
  bPi : ℝ
  bGamma : ℝ
  bT : ℝ
  certificate : SBBoxCertificate rhoB bPi bGamma bT

def SBBoxInput.certified (input : SBBoxInput) : Prop :=
  0 < input.rhoB ∧ 0 < input.bPi ∧ 0 < input.bGamma ∧ 0 < input.bT

theorem SBBoxInput.certified_of_certificate (input : SBBoxInput) :
    input.certified := by
  exact ⟨input.certificate.rhoB_pos, input.certificate.bPi_pos,
    input.certificate.bGamma_pos, input.certificate.bT_pos⟩

theorem SBBoxInput.rhoB_pos (input : SBBoxInput) (h : input.certified) :
    0 < input.rhoB :=
  h.1

theorem SBBoxInput.bPi_pos (input : SBBoxInput) (h : input.certified) :
    0 < input.bPi :=
  h.2.1

theorem SBBoxInput.bGamma_pos (input : SBBoxInput) (h : input.certified) :
    0 < input.bGamma :=
  h.2.2.1

theorem SBBoxInput.bT_pos (input : SBBoxInput) (h : input.certified) :
    0 < input.bT :=
  h.2.2.2

def SBBoxInput.pointCertificate
    (input : SBBoxInput)
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    {delta : ℝ} (hdelta : 0 < delta) (hle : delta ≤ input.rhoB) :
    SBBoxPointCertificate R₂ delta input.bPi input.bGamma input.bT :=
  input.certificate.pointwise R₂ hdelta hle

def SBBoxInput.boxInclusion
    (input : SBBoxInput)
    (R₂ : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    {delta : ℝ} (hdelta : 0 < delta) (hle : delta ≤ input.rhoB) :
    BoxInclusionCertificate (input.pointCertificate R₂ hdelta hle).cert :=
  (input.pointCertificate R₂ hdelta hle).toBoxInclusionCertificate

structure CriticalDiskCertifiedInputs where
  sf : SFInput
  sbBox : SBBoxInput

def CriticalDiskCertifiedInputs.allCertified (inputs : CriticalDiskCertifiedInputs) : Prop :=
  inputs.sf.certified ∧ inputs.sbBox.certified

theorem allCertified_of_parts (inputs : CriticalDiskCertifiedInputs)
    (hsf : inputs.sf.certified) (hsb : inputs.sbBox.certified) :
    inputs.allCertified := by
  exact ⟨hsf, hsb⟩

theorem CriticalDiskCertifiedInputs.sf_certified
    (inputs : CriticalDiskCertifiedInputs) (h : inputs.allCertified) :
    inputs.sf.certified :=
  h.1

theorem CriticalDiskCertifiedInputs.sbBox_certified
    (inputs : CriticalDiskCertifiedInputs) (h : inputs.allCertified) :
    inputs.sbBox.certified :=
  h.2

theorem CriticalDiskCertifiedInputs.sf_rhoF_pos
    (inputs : CriticalDiskCertifiedInputs) (h : inputs.allCertified) :
    0 < inputs.sf.rhoF :=
  inputs.sf.rhoF_pos (inputs.sf_certified h)

theorem CriticalDiskCertifiedInputs.sf_rb_pos
    (inputs : CriticalDiskCertifiedInputs) (h : inputs.allCertified) :
    0 < inputs.sf.rb :=
  inputs.sf.rb_pos (inputs.sf_certified h)

theorem CriticalDiskCertifiedInputs.sf_nu_pos
    (inputs : CriticalDiskCertifiedInputs) (h : inputs.allCertified) :
    0 < inputs.sf.nu :=
  inputs.sf.nu_pos (inputs.sf_certified h)

theorem CriticalDiskCertifiedInputs.sf_psiMin_pos
    (inputs : CriticalDiskCertifiedInputs) (h : inputs.allCertified) :
    0 < inputs.sf.psiMin :=
  inputs.sf.psiMin_pos (inputs.sf_certified h)

theorem CriticalDiskCertifiedInputs.sf_shellSlope_pos
    (inputs : CriticalDiskCertifiedInputs) (h : inputs.allCertified) :
    0 < inputs.sf.shellSlope :=
  inputs.sf.shellSlope_pos (inputs.sf_certified h)

theorem CriticalDiskCertifiedInputs.sbBox_rhoB_pos
    (inputs : CriticalDiskCertifiedInputs) (h : inputs.allCertified) :
    0 < inputs.sbBox.rhoB :=
  inputs.sbBox.rhoB_pos (inputs.sbBox_certified h)

theorem CriticalDiskCertifiedInputs.sbBox_bPi_pos
    (inputs : CriticalDiskCertifiedInputs) (h : inputs.allCertified) :
    0 < inputs.sbBox.bPi :=
  inputs.sbBox.bPi_pos (inputs.sbBox_certified h)

theorem CriticalDiskCertifiedInputs.sbBox_bGamma_pos
    (inputs : CriticalDiskCertifiedInputs) (h : inputs.allCertified) :
    0 < inputs.sbBox.bGamma :=
  inputs.sbBox.bGamma_pos (inputs.sbBox_certified h)

theorem CriticalDiskCertifiedInputs.sbBox_bT_pos
    (inputs : CriticalDiskCertifiedInputs) (h : inputs.allCertified) :
    0 < inputs.sbBox.bT :=
  inputs.sbBox.bT_pos (inputs.sbBox_certified h)

theorem CriticalDiskCertifiedInputs.delta_le_rhoCap
    (inputs : CriticalDiskCertifiedInputs)
    {cand : CriticalDiskCandidate}
    (hcand : CriticalDiskHypotheses cand) :
    cand.delta ≤ criticalDiskRhoCap :=
  hcand.delta_le_rhoCap inputs.sf.rhoF inputs.sbBox.rhoB

theorem CriticalDiskCertifiedInputs.delta_le_sf_rhoF
    (inputs : CriticalDiskCertifiedInputs)
    {cand : CriticalDiskCandidate}
    (hcand : CriticalDiskHypotheses cand) :
    cand.delta ≤ inputs.sf.rhoF :=
  hcand.delta_le_rhoF inputs.sf.rhoF inputs.sbBox.rhoB

theorem CriticalDiskCertifiedInputs.delta_le_sbBox_rhoB
    (inputs : CriticalDiskCertifiedInputs)
    {cand : CriticalDiskCandidate}
    (hcand : CriticalDiskHypotheses cand) :
    cand.delta ≤ inputs.sbBox.rhoB :=
  hcand.delta_le_rhoB inputs.sf.rhoF inputs.sbBox.rhoB

theorem CriticalDiskCertifiedInputs.delta_le_sigma0
    (inputs : CriticalDiskCertifiedInputs)
    {cand : CriticalDiskCandidate}
    (hcand : CriticalDiskHypotheses cand) :
    cand.delta ≤ criticalDiskSigma0 :=
  hcand.delta_le_sigma0 inputs.sf.rhoF inputs.sbBox.rhoB

def CriticalDiskCertifiedInputs.sbBoxPointCertificate
    (inputs : CriticalDiskCertifiedInputs)
    {cand : CriticalDiskCandidate}
    (hcand : CriticalDiskHypotheses cand) :
    SBBoxPointCertificate cand.R₂ cand.delta
      inputs.sbBox.bPi inputs.sbBox.bGamma inputs.sbBox.bT :=
  inputs.sbBox.pointCertificate cand.R₂ hcand.delta_pos
    (inputs.delta_le_sbBox_rhoB hcand)

def CriticalDiskCertifiedInputs.sbBoxInclusion
    (inputs : CriticalDiskCertifiedInputs)
    {cand : CriticalDiskCandidate}
    (hcand : CriticalDiskHypotheses cand) :
    BoxInclusionCertificate (inputs.sbBoxPointCertificate hcand).cert :=
  inputs.sbBox.boxInclusion cand.R₂ hcand.delta_pos
    (inputs.delta_le_sbBox_rhoB hcand)

/-! ### Standard assembly-input constructors

These constructors pin down the numerical parameters used by the current critical-disk assembly;
the proof-carrying certificate payloads are supplied separately.
-/

def standardSFCheckerPayload (rhoF : Qsqrt2) : SFCheckerPayload where
  rhoF := rhoF
  rb := criticalDiskRbQ
  nu := criticalDiskNuQ
  psiMin := criticalDiskPsiMinQ
  shellSlope := criticalDiskShellSlopeQ
  charts := []
  inputHash := ""
  outputHash := ""

def standardSBBoxCheckerPayload (rhoB : Qsqrt2) : SBBoxCheckerPayload where
  rhoB := rhoB
  bPi := criticalDiskBoxBPiQ
  bGamma := criticalDiskBoxBGammaQ
  bT := criticalDiskBoxBTQ
  charts := []

def standardSFInput (rhoF : ℝ)
    (certificate :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope) :
    SFInput where
  rhoF := rhoF
  rb := criticalDiskRb
  nu := criticalDiskNu
  psiMin := criticalDiskPsiMin
  shellSlope := criticalDiskShellSlope
  certificate := certificate

def standardSBBoxInput (rhoB : ℝ)
    (certificate :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT) :
    SBBoxInput where
  rhoB := rhoB
  bPi := criticalDiskBoxBPi
  bGamma := criticalDiskBoxBGamma
  bT := criticalDiskBoxBT
  certificate := certificate

theorem standardSFInput_rhoF
    (rhoF : ℝ)
    (certificate :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope) :
    (standardSFInput rhoF certificate).rhoF = rhoF :=
  rfl

theorem standardSFInput_rb
    (rhoF : ℝ)
    (certificate :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope) :
    (standardSFInput rhoF certificate).rb = criticalDiskRb :=
  rfl

theorem standardSFInput_nu
    (rhoF : ℝ)
    (certificate :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope) :
    (standardSFInput rhoF certificate).nu = criticalDiskNu :=
  rfl

theorem standardSFInput_psiMin
    (rhoF : ℝ)
    (certificate :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope) :
    (standardSFInput rhoF certificate).psiMin = criticalDiskPsiMin :=
  rfl

theorem standardSFInput_shellSlope
    (rhoF : ℝ)
    (certificate :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope) :
    (standardSFInput rhoF certificate).shellSlope = criticalDiskShellSlope :=
  rfl

theorem standardSBBoxInput_rhoB
    (rhoB : ℝ)
    (certificate :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT) :
    (standardSBBoxInput rhoB certificate).rhoB = rhoB :=
  rfl

theorem standardSBBoxInput_bPi
    (rhoB : ℝ)
    (certificate :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT) :
    (standardSBBoxInput rhoB certificate).bPi = criticalDiskBoxBPi :=
  rfl

theorem standardSBBoxInput_bGamma
    (rhoB : ℝ)
    (certificate :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT) :
    (standardSBBoxInput rhoB certificate).bGamma = criticalDiskBoxBGamma :=
  rfl

theorem standardSBBoxInput_bT
    (rhoB : ℝ)
    (certificate :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT) :
    (standardSBBoxInput rhoB certificate).bT = criticalDiskBoxBT :=
  rfl

def standardSFInput_of_payloadVerified
    {rhoF : ℝ} {payload : SFCheckerPayload}
    (verified :
      SFPayloadVerified payload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope) :
    SFInput :=
  standardSFInput rhoF verified.toCertificate

def standardSBBoxInput_of_payloadVerified
    {rhoB : ℝ} {payload : SBBoxCheckerPayload}
    (verified :
      SBBoxPayloadVerified payload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT) :
    SBBoxInput :=
  standardSBBoxInput rhoB verified.toCertificate

def standardCriticalDiskInputs
    (rhoF rhoB : ℝ)
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT) :
    CriticalDiskCertifiedInputs where
  sf := standardSFInput rhoF SFcert
  sbBox := standardSBBoxInput rhoB SBBoxCert

theorem standardCriticalDiskInputs_sf
    (rhoF rhoB : ℝ)
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT) :
    (standardCriticalDiskInputs rhoF rhoB SFcert SBBoxCert).sf =
      standardSFInput rhoF SFcert :=
  rfl

theorem standardCriticalDiskInputs_sbBox
    (rhoF rhoB : ℝ)
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT) :
    (standardCriticalDiskInputs rhoF rhoB SFcert SBBoxCert).sbBox =
      standardSBBoxInput rhoB SBBoxCert :=
  rfl

theorem standardCriticalDiskInputs_sf_rhoF
    (rhoF rhoB : ℝ)
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT) :
    (standardCriticalDiskInputs rhoF rhoB SFcert SBBoxCert).sf.rhoF = rhoF :=
  rfl

theorem standardCriticalDiskInputs_sbBox_rhoB
    (rhoF rhoB : ℝ)
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT) :
    (standardCriticalDiskInputs rhoF rhoB SFcert SBBoxCert).sbBox.rhoB = rhoB :=
  rfl

def standardCriticalDiskInputs_of_payloadVerified
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT) :
    CriticalDiskCertifiedInputs :=
  standardCriticalDiskInputs rhoF rhoB SFverified.toCertificate SBverified.toCertificate

theorem standardCriticalDiskInputs_allCertified
    (rhoF rhoB : ℝ)
    (SFcert :
      SFCertificate rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBBoxCert :
      SBBoxCertificate rhoB criticalDiskBoxBPi criticalDiskBoxBGamma criticalDiskBoxBT) :
    (standardCriticalDiskInputs rhoF rhoB SFcert SBBoxCert).allCertified := by
  exact ⟨(standardCriticalDiskInputs rhoF rhoB SFcert SBBoxCert).sf.certified_of_certificate,
    (standardCriticalDiskInputs rhoF rhoB SFcert SBBoxCert).sbBox.certified_of_certificate⟩

theorem standardCriticalDiskInputs_of_payloadVerified_allCertified
    {rhoF rhoB : ℝ} {SFpayload : SFCheckerPayload} {SBpayload : SBBoxCheckerPayload}
    (SFverified :
      SFPayloadVerified SFpayload rhoF criticalDiskRb criticalDiskNu criticalDiskPsiMin
        criticalDiskShellSlope)
    (SBverified :
      SBBoxPayloadVerified SBpayload rhoB criticalDiskBoxBPi criticalDiskBoxBGamma
        criticalDiskBoxBT) :
    (standardCriticalDiskInputs_of_payloadVerified SFverified SBverified).allCertified := by
  exact standardCriticalDiskInputs_allCertified rhoF rhoB SFverified.toCertificate
    SBverified.toCertificate

end RupertStellatedTetrahedron
