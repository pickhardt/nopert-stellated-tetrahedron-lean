import RupertStellatedTetrahedron.CriticalDisk.Constants

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

/-!
## Tail obstructions for `(SB-box)`

Draft §13.3 explains why the `δ → 0` tail cannot tolerate a nonzero order-0
stress residual: the box kill is linear in `δ`, so any fixed residual that is
bounded by the tail inequality for all sufficiently small positive `δ` must
vanish exactly.  This file records that analytic core independently of the
generated certificate payloads.
-/

/-- A fixed residual is dominated by a linear-in-`δ` error budget on a punctured tail. -/
def CriticalDiskTailLinearResidualBound (residual bound rho : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ rho → |residual| ≤ bound * δ

/-- If a fixed residual is `O(δ)` for every positive `δ` in a nontrivial tail interval, it must
vanish.  This is the abstract form of the §13.3 `ε₀` obstruction. -/
theorem residual_eq_zero_of_tail_linear_bound
    {residual bound rho : ℝ}
    (hrho : 0 < rho) (hbound : 0 ≤ bound)
    (hres : CriticalDiskTailLinearResidualBound residual bound rho) :
    residual = 0 := by
  have habs_nonpos : |residual| ≤ 0 := by
    refine le_of_forall_pos_le_add ?_
    intro η hη
    let δ := min rho (η / (bound + 1))
    have hden_pos : 0 < bound + 1 := by linarith
    have hδ_pos : 0 < δ := by
      exact lt_min hrho (div_pos hη hden_pos)
    have hδ_le_rho : δ ≤ rho := min_le_left _ _
    have hδ_le_eta : δ ≤ η / (bound + 1) := min_le_right _ _
    have hscale : bound * δ ≤ η := by
      have hmul_le : bound * δ ≤ bound * (η / (bound + 1)) :=
        mul_le_mul_of_nonneg_left hδ_le_eta hbound
      have hratio_le_one : bound / (bound + 1) ≤ 1 := by
        rw [div_le_one hden_pos]
        linarith
      have htarget : bound * (η / (bound + 1)) ≤ η := by
        calc
          bound * (η / (bound + 1)) = η * (bound / (bound + 1)) := by ring
          _ ≤ η * 1 := mul_le_mul_of_nonneg_left hratio_le_one (le_of_lt hη)
          _ = η := by ring
      exact le_trans hmul_le htarget
    exact le_trans (hres δ hδ_pos hδ_le_rho) (by simpa using hscale)
  exact abs_eq_zero.mp (le_antisymm habs_nonpos (abs_nonneg residual))

theorem CriticalDiskTailLinearResidualBound.residual_eq_zero
    {residual bound rho : ℝ}
    (hres : CriticalDiskTailLinearResidualBound residual bound rho)
    (hrho : 0 < rho) (hbound : 0 ≤ bound) :
    residual = 0 :=
  residual_eq_zero_of_tail_linear_bound hrho hbound hres

/-- Named certificate boundary for the exactness condition forced by the `(SB-box)` tail. -/
structure CriticalDiskTailExactResidualCertificate where
  residual : ℝ
  bound : ℝ
  rho : ℝ
  rho_pos : 0 < rho
  bound_nonneg : 0 ≤ bound
  tail_bound : CriticalDiskTailLinearResidualBound residual bound rho

theorem CriticalDiskTailExactResidualCertificate.residual_eq_zero
    (cert : CriticalDiskTailExactResidualCertificate) :
    cert.residual = 0 :=
  residual_eq_zero_of_tail_linear_bound cert.rho_pos cert.bound_nonneg cert.tail_bound

end RupertStellatedTetrahedron
