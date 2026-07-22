import RupertStellatedTetrahedron.CriticalDisk.Constants
import RupertStellatedTetrahedron.CriticalDisk.ExactCertificates

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

/-!
## Exact encodings of critical-disk constants

The external certificate files use rational and `ℚ[√2]` data.  These definitions give canonical
Lean encodings of the constants that lie in `ℚ[√2]`; constants involving `√3` or `√1123` stay in
the real-valued assembly file.
-/

namespace Qsqrt2

def ofRat (q : ℚ) : Qsqrt2 :=
  ⟨q, 0⟩

def sqrt2Mul (q : ℚ) : Qsqrt2 :=
  ⟨0, q⟩

@[simp] lemma toReal_ofRat (q : ℚ) :
    (ofRat q).toReal = (q : ℝ) := by
  simp [ofRat, toReal]

@[simp] lemma toReal_sqrt2Mul (q : ℚ) :
    (sqrt2Mul q).toReal = (q : ℝ) * Real.sqrt 2 := by
  simp [sqrt2Mul, toReal]

end Qsqrt2

def criticalDiskRbQ : Qsqrt2 := Qsqrt2.ofRat (3 / 250)
def criticalDiskNuQ : Qsqrt2 := Qsqrt2.ofRat (7 / 500)
def criticalDiskPsiMinQ : Qsqrt2 := Qsqrt2.ofRat (3 / 50)
def criticalDiskShellSlopeQ : Qsqrt2 := Qsqrt2.ofRat (3 / 10)

def criticalDiskBoxBPiQ : Qsqrt2 := Qsqrt2.ofRat (2 / 125)
def criticalDiskBoxBGammaQ : Qsqrt2 := Qsqrt2.ofRat (1 / 25)
def criticalDiskBoxBTQ : Qsqrt2 := Qsqrt2.ofRat (1 / 500)

def criticalDiskG1Q : Qsqrt2 := Qsqrt2.ofRat (1 / 40)
def criticalDiskCMinQ : Qsqrt2 := Qsqrt2.ofRat (1 / 50)
def criticalDiskKappaTQ : Qsqrt2 := Qsqrt2.ofRat (1 / 1000)
def criticalDiskXDQ : Qsqrt2 := Qsqrt2.sqrt2Mul (323 / 198)
def criticalDiskHoffmanC1Q : Qsqrt2 := Qsqrt2.ofRat (81 / 500)
def criticalDiskLocalizationPlanarTubeQ : Qsqrt2 := Qsqrt2.ofRat (2 / 25)
def criticalDiskLocalizationTransverseTubeQ : Qsqrt2 := Qsqrt2.ofRat (57 / 2000)
def criticalDiskSigma0Q : Qsqrt2 := Qsqrt2.ofRat (427 / 10000)
def criticalDiskRhoCapQ : Qsqrt2 := Qsqrt2.ofRat (1 / 1000)
def criticalDiskTailCutQ : Qsqrt2 := Qsqrt2.ofRat (1 / 100000)
def criticalDiskBoxReachLowerQ : Qsqrt2 := Qsqrt2.ofRat (17879 / 1000000)
def criticalDiskShellRadiusQ : Qsqrt2 := Qsqrt2.ofRat (69 / 5000)

lemma criticalDiskRbQ_toReal :
    criticalDiskRbQ.toReal = criticalDiskRb := by
  norm_num [criticalDiskRbQ, criticalDiskRb, Qsqrt2.ofRat, Qsqrt2.toReal]

lemma criticalDiskNuQ_toReal :
    criticalDiskNuQ.toReal = criticalDiskNu := by
  norm_num [criticalDiskNuQ, criticalDiskNu, Qsqrt2.ofRat, Qsqrt2.toReal]

lemma criticalDiskPsiMinQ_toReal :
    criticalDiskPsiMinQ.toReal = criticalDiskPsiMin := by
  norm_num [criticalDiskPsiMinQ, criticalDiskPsiMin, Qsqrt2.ofRat, Qsqrt2.toReal]

lemma criticalDiskShellSlopeQ_toReal :
    criticalDiskShellSlopeQ.toReal = criticalDiskShellSlope := by
  norm_num [criticalDiskShellSlopeQ, criticalDiskShellSlope, Qsqrt2.ofRat, Qsqrt2.toReal]

lemma criticalDiskBoxBPiQ_toReal :
    criticalDiskBoxBPiQ.toReal = criticalDiskBoxBPi := by
  norm_num [criticalDiskBoxBPiQ, criticalDiskBoxBPi, Qsqrt2.ofRat, Qsqrt2.toReal]

lemma criticalDiskBoxBGammaQ_toReal :
    criticalDiskBoxBGammaQ.toReal = criticalDiskBoxBGamma := by
  norm_num [criticalDiskBoxBGammaQ, criticalDiskBoxBGamma, Qsqrt2.ofRat, Qsqrt2.toReal]

lemma criticalDiskBoxBTQ_toReal :
    criticalDiskBoxBTQ.toReal = criticalDiskBoxBT := by
  norm_num [criticalDiskBoxBTQ, criticalDiskBoxBT, Qsqrt2.ofRat, Qsqrt2.toReal]

lemma criticalDiskG1Q_toReal :
    criticalDiskG1Q.toReal = criticalDiskG1 := by
  norm_num [criticalDiskG1Q, criticalDiskG1, Qsqrt2.ofRat, Qsqrt2.toReal]

lemma criticalDiskCMinQ_toReal :
    criticalDiskCMinQ.toReal = criticalDiskCMin := by
  norm_num [criticalDiskCMinQ, criticalDiskCMin, Qsqrt2.ofRat, Qsqrt2.toReal]

lemma criticalDiskKappaTQ_toReal :
    criticalDiskKappaTQ.toReal = criticalDiskKappaT := by
  norm_num [criticalDiskKappaTQ, criticalDiskKappaT, Qsqrt2.ofRat, Qsqrt2.toReal]

lemma criticalDiskXDQ_toReal :
    criticalDiskXDQ.toReal = criticalDiskXD := by
  unfold criticalDiskXDQ criticalDiskXD Qsqrt2.sqrt2Mul Qsqrt2.toReal
  ring

lemma criticalDiskHoffmanC1Q_toReal :
    criticalDiskHoffmanC1Q.toReal = criticalDiskHoffmanC1 := by
  norm_num [criticalDiskHoffmanC1Q, criticalDiskHoffmanC1, Qsqrt2.ofRat, Qsqrt2.toReal]

lemma criticalDiskLocalizationPlanarTubeQ_toReal :
    criticalDiskLocalizationPlanarTubeQ.toReal = criticalDiskLocalizationPlanarTube := by
  norm_num [criticalDiskLocalizationPlanarTubeQ, criticalDiskLocalizationPlanarTube,
    Qsqrt2.ofRat, Qsqrt2.toReal]

lemma criticalDiskLocalizationTransverseTubeQ_toReal :
    criticalDiskLocalizationTransverseTubeQ.toReal =
      criticalDiskLocalizationTransverseTube := by
  norm_num [criticalDiskLocalizationTransverseTubeQ, criticalDiskLocalizationTransverseTube,
    Qsqrt2.ofRat, Qsqrt2.toReal]

lemma criticalDiskSigma0Q_toReal :
    criticalDiskSigma0Q.toReal = criticalDiskSigma0 := by
  norm_num [criticalDiskSigma0Q, criticalDiskSigma0, Qsqrt2.ofRat, Qsqrt2.toReal]

lemma criticalDiskRhoCapQ_toReal :
    criticalDiskRhoCapQ.toReal = criticalDiskRhoCap := by
  norm_num [criticalDiskRhoCapQ, criticalDiskRhoCap, Qsqrt2.ofRat, Qsqrt2.toReal]

lemma criticalDiskTailCutQ_toReal :
    criticalDiskTailCutQ.toReal = criticalDiskTailCut := by
  norm_num [criticalDiskTailCutQ, criticalDiskTailCut, Qsqrt2.ofRat, Qsqrt2.toReal]

lemma criticalDiskBoxReachLowerQ_toReal :
    criticalDiskBoxReachLowerQ.toReal = criticalDiskBoxReachLower := by
  norm_num [criticalDiskBoxReachLowerQ, criticalDiskBoxReachLower,
    Qsqrt2.ofRat, Qsqrt2.toReal]

lemma criticalDiskShellRadiusQ_toReal :
    criticalDiskShellRadiusQ.toReal = criticalDiskShellRadius := by
  norm_num [criticalDiskShellRadiusQ, criticalDiskShellRadius,
    Qsqrt2.ofRat, Qsqrt2.toReal]

end RupertStellatedTetrahedron
