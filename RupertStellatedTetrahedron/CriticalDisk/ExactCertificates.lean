import Mathlib.Data.Bool.AllAny
import RupertStellatedTetrahedron.DepthCylinderTheorem.BoxCylinder
import RupertStellatedTetrahedron.Stellated.UStarGeometry

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.Operator

namespace RupertStellatedTetrahedron

open DepthCylinderTheorem

/-!
## Exact checker payload grammars

The critical-disk proof has two semantic certified inputs, `(SF)` and `(SB-box)`, plus the
finite depth computation at `u*`.  This file fixes the Lean shape of the exact data emitted by
those checkers: rational/`Qsqrt2` scalars, interval boxes, active-incidence codes, convex
combination witnesses, and audit metadata.  The structures are intentionally separate from the
semantic theorems in `CertifiedInputs`: a checker payload is machine data, while the corresponding
certificate proves that the data has the advertised geometric meaning.
-/

/-- Exact scalar in `ℚ[√2]`, represented as `a + b√2`. -/
structure Qsqrt2 where
  re : ℚ
  sqrtCoeff : ℚ
  deriving DecidableEq, Repr

namespace Qsqrt2

def toReal (x : Qsqrt2) : ℝ :=
  (x.re : ℝ) + (x.sqrtCoeff : ℝ) * Real.sqrt 2

instance : Zero Qsqrt2 where
  zero := ⟨0, 0⟩

instance : One Qsqrt2 where
  one := ⟨1, 0⟩

instance : Add Qsqrt2 where
  add x y := ⟨x.re + y.re, x.sqrtCoeff + y.sqrtCoeff⟩

instance : Neg Qsqrt2 where
  neg x := ⟨-x.re, -x.sqrtCoeff⟩

instance : Sub Qsqrt2 where
  sub x y := x + -y

instance : Mul Qsqrt2 where
  mul x y :=
    ⟨x.re * y.re + 2 * x.sqrtCoeff * y.sqrtCoeff,
      x.re * y.sqrtCoeff + x.sqrtCoeff * y.re⟩

@[simp] lemma toReal_zero : (0 : Qsqrt2).toReal = 0 := by
  change ((0 : ℚ) : ℝ) + ((0 : ℚ) : ℝ) * Real.sqrt 2 = 0
  norm_num

@[simp] lemma toReal_one : (1 : Qsqrt2).toReal = 1 := by
  change ((1 : ℚ) : ℝ) + ((0 : ℚ) : ℝ) * Real.sqrt 2 = 1
  norm_num

@[simp] lemma toReal_add (x y : Qsqrt2) :
    (x + y).toReal = x.toReal + y.toReal := by
  cases x with
  | mk xr xs =>
    cases y with
    | mk yr ys =>
      change ((xr + yr : ℚ) : ℝ) + ((xs + ys : ℚ) : ℝ) * Real.sqrt 2 =
        ((xr : ℝ) + (xs : ℝ) * Real.sqrt 2) + ((yr : ℝ) + (ys : ℝ) * Real.sqrt 2)
      norm_num
      ring

@[simp] lemma toReal_neg (x : Qsqrt2) :
    (-x).toReal = -x.toReal := by
  cases x with
  | mk xr xs =>
    change ((-xr : ℚ) : ℝ) + ((-xs : ℚ) : ℝ) * Real.sqrt 2 =
      -((xr : ℝ) + (xs : ℝ) * Real.sqrt 2)
    norm_num
    ring

@[simp] lemma toReal_sub (x y : Qsqrt2) :
    (x - y).toReal = x.toReal - y.toReal := by
  rw [show x - y = x + -y from rfl]
  simp
  ring

@[simp] lemma toReal_mul (x y : Qsqrt2) :
    (x * y).toReal = x.toReal * y.toReal := by
  have hsqrt_two_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  cases x with
  | mk xr xs =>
    cases y with
    | mk yr ys =>
      change
        (((xr * yr + 2 * xs * ys : ℚ) : ℝ) +
            ((xr * ys + xs * yr : ℚ) : ℝ) * Real.sqrt 2 =
          ((xr : ℝ) + (xs : ℝ) * Real.sqrt 2) *
            ((yr : ℝ) + (ys : ℝ) * Real.sqrt 2))
      norm_num
      ring_nf
      rw [hsqrt_two_sq]

/-- Rational lower/upper bounds for `√2`, checked by squaring. -/
structure Sqrt2Bounds where
  lo : ℚ
  hi : ℚ
  lo_nonneg : 0 ≤ lo
  lo_sq_le_two : lo ^ 2 ≤ 2
  hi_nonneg : 0 ≤ hi
  two_le_hi_sq : 2 ≤ hi ^ 2
  deriving Repr

lemma Sqrt2Bounds.lo_le_sqrt2 (b : Sqrt2Bounds) :
    (b.lo : ℝ) ≤ Real.sqrt 2 := by
  exact Real.le_sqrt_of_sq_le (by
    exact_mod_cast b.lo_sq_le_two)

lemma Sqrt2Bounds.sqrt2_le_hi (b : Sqrt2Bounds) :
    Real.sqrt 2 ≤ (b.hi : ℝ) := by
  rw [Real.sqrt_le_left (by exact_mod_cast b.hi_nonneg)]
  exact_mod_cast b.two_le_hi_sq

def nonnegLowerExpr (x : Qsqrt2) (sqrt2Lower : ℚ) : ℚ :=
  x.re + x.sqrtCoeff * sqrt2Lower

def nonnegUpperExpr (x : Qsqrt2) (sqrt2Upper : ℚ) : ℚ :=
  x.re + x.sqrtCoeff * sqrt2Upper

/-- Exact branch certificate for `0 ≤ a + b√2` using rational bounds on `√2`. -/
structure NonnegCert (x : Qsqrt2) where
  bounds : Sqrt2Bounds
  nonneg :
    if 0 ≤ x.sqrtCoeff then
      0 ≤ nonnegLowerExpr x bounds.lo
    else
      0 ≤ nonnegUpperExpr x bounds.hi
  deriving Repr

lemma toReal_nonneg_of_nonnegCert {x : Qsqrt2} (cert : NonnegCert x) :
    0 ≤ x.toReal := by
  unfold toReal
  by_cases hcoeff : 0 ≤ x.sqrtCoeff
  · have hlower : (0 : ℝ) ≤ (nonnegLowerExpr x cert.bounds.lo : ℝ) := by
      exact_mod_cast (by simpa [NonnegCert.nonneg, hcoeff] using cert.nonneg)
    have hlower_expanded :
        (nonnegLowerExpr x cert.bounds.lo : ℝ) =
          (x.re : ℝ) + (x.sqrtCoeff : ℝ) * (cert.bounds.lo : ℝ) := by
      simp [nonnegLowerExpr]
    have hmono :
        (x.re : ℝ) + (x.sqrtCoeff : ℝ) * (cert.bounds.lo : ℝ) ≤
          (x.re : ℝ) + (x.sqrtCoeff : ℝ) * Real.sqrt 2 := by
      have hcoeff_real : (0 : ℝ) ≤ x.sqrtCoeff := by
        exact_mod_cast hcoeff
      have hmul :
          (x.sqrtCoeff : ℝ) * (cert.bounds.lo : ℝ) ≤
            (x.sqrtCoeff : ℝ) * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_left cert.bounds.lo_le_sqrt2 hcoeff_real
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hmul (x.re : ℝ)
    exact le_trans (by simpa [hlower_expanded] using hlower) hmono
  · have hupper : (0 : ℝ) ≤ (nonnegUpperExpr x cert.bounds.hi : ℝ) := by
      exact_mod_cast (by simpa [NonnegCert.nonneg, hcoeff] using cert.nonneg)
    have hupper_expanded :
        (nonnegUpperExpr x cert.bounds.hi : ℝ) =
          (x.re : ℝ) + (x.sqrtCoeff : ℝ) * (cert.bounds.hi : ℝ) := by
      simp [nonnegUpperExpr]
    have hcoeff_le : (x.sqrtCoeff : ℝ) ≤ 0 := by
      exact_mod_cast le_of_lt (lt_of_not_ge hcoeff)
    have hmono :
        (x.re : ℝ) + (x.sqrtCoeff : ℝ) * (cert.bounds.hi : ℝ) ≤
          (x.re : ℝ) + (x.sqrtCoeff : ℝ) * Real.sqrt 2 := by
      have hmul :
          (x.sqrtCoeff : ℝ) * (cert.bounds.hi : ℝ) ≤
            (x.sqrtCoeff : ℝ) * Real.sqrt 2 :=
        mul_le_mul_of_nonpos_left cert.bounds.sqrt2_le_hi hcoeff_le
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hmul (x.re : ℝ)
    exact le_trans (by simpa [hupper_expanded] using hupper) hmono

end Qsqrt2

/-- A closed rational interval. -/
structure RatInterval where
  lo : ℚ
  hi : ℚ
  valid : lo ≤ hi
  deriving Repr

def RatInterval.contains (I : RatInterval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def RatInterval.containsRatBool (I : RatInterval) (x : ℚ) : Bool :=
  decide (I.lo ≤ x ∧ x ≤ I.hi)

theorem RatInterval.contains_of_containsRatBool_eq_true
    {I : RatInterval} {x : ℚ}
    (h : I.containsRatBool x = true) :
    I.contains (x : ℝ) := by
  unfold RatInterval.containsRatBool at h
  have hrat : I.lo ≤ x ∧ x ≤ I.hi := of_decide_eq_true h
  exact ⟨by exact_mod_cast hrat.1, by exact_mod_cast hrat.2⟩

theorem RatInterval.containsRatBool_eq_true_of_contains
    {I : RatInterval} {x : ℚ}
    (h : I.contains (x : ℝ)) :
    I.containsRatBool x = true := by
  unfold RatInterval.containsRatBool
  exact decide_eq_true
    ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

theorem RatInterval.not_contains_of_containsRatBool_eq_false
    {I : RatInterval} {x : ℚ}
    (h : I.containsRatBool x = false) :
    ¬ I.contains (x : ℝ) := by
  unfold RatInterval.containsRatBool at h
  have hrat : ¬ (I.lo ≤ x ∧ x ≤ I.hi) := of_decide_eq_false h
  intro hcontains
  exact hrat ⟨by exact_mod_cast hcontains.1, by exact_mod_cast hcontains.2⟩

/-- A closed interval with exact `ℚ[√2]` endpoints. -/
structure Qsqrt2Interval where
  lo : Qsqrt2
  hi : Qsqrt2
  valid : lo.toReal ≤ hi.toReal
  deriving Repr

def Qsqrt2Interval.contains (I : Qsqrt2Interval) (x : ℝ) : Prop :=
  I.lo.toReal ≤ x ∧ x ≤ I.hi.toReal

/-- Exact vector in `ℚ[√2]^n`. -/
abbrev ExactVec (n : Nat) := Fin n → Qsqrt2

namespace ExactVec

def zero (n : Nat) : ExactVec n :=
  fun _ => 0

def add {n : Nat} (u v : ExactVec n) : ExactVec n :=
  fun i => u i + v i

def smul {n : Nat} (a : Qsqrt2) (v : ExactVec n) : ExactVec n :=
  fun i => a * v i

def toReal {n : Nat} (v : ExactVec n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => (v i).toReal

@[simp] lemma toReal_zero {n : Nat} :
    toReal (zero n) = (0 : EuclideanSpace ℝ (Fin n)) := by
  ext i
  simp [toReal, zero]

@[simp] lemma toReal_add {n : Nat} (u v : ExactVec n) :
    toReal (add u v) = toReal u + toReal v := by
  ext i
  simp [toReal, add]

@[simp] lemma toReal_smul {n : Nat} (a : Qsqrt2) (v : ExactVec n) :
    toReal (smul a v) = a.toReal • toReal v := by
  ext i
  simp [toReal, smul]

end ExactVec

abbrev ExactFlag5 := ExactVec 5

namespace ExactFlagList

def realFinset (flags : List ExactFlag5) : Finset (EuclideanSpace ℝ (Fin 5)) := by
  classical
  exact flags.toFinset.image ExactVec.toReal

def exactTable (flags : List ExactFlag5) (n : Nat) : ExactFlag5 :=
  match flags[n]? with
  | some flag => flag
  | none => ExactVec.zero 5

def table (flags : List ExactFlag5) (n : Nat) : EuclideanSpace ℝ (Fin 5) :=
  match flags[n]? with
  | some flag => ExactVec.toReal flag
  | none => 0

lemma toReal_exactTable (flags : List ExactFlag5) (n : Nat) :
    ExactVec.toReal (exactTable flags n) = table flags n := by
  unfold exactTable table
  split <;> simp

lemma table_mem_of_get? {flags : List ExactFlag5} {n : Nat} {flag : ExactFlag5}
    (hget : flags[n]? = some flag) :
    table flags n ∈ (realFinset flags : Set (EuclideanSpace ℝ (Fin 5))) := by
  classical
  unfold table realFinset
  rw [hget]
  have hmem : flag ∈ flags := by
    rw [List.mem_iff_getElem?]
    exact ⟨n, hget⟩
  exact Finset.mem_image.mpr ⟨flag, by simpa using hmem, rfl⟩

end ExactFlagList

/-- One term of an exact convex combination over a list-indexed flag table. -/
structure ConvexComboTerm where
  flagIndex : Nat
  weight : Qsqrt2
  deriving DecidableEq, Repr

/-- Exact convex-combination data.  The semantic certificate proves these rows evaluate correctly. -/
structure ConvexComboWitness where
  terms : List ConvexComboTerm
  deriving Repr

private lemma list_foldl_add_eq_add_sum {α M : Type*} [AddCommMonoid M]
    (terms : List α) (f : α → M) (acc : M) :
    terms.foldl (fun acc term => acc + f term) acc =
      acc + (terms.map f).sum := by
  induction terms generalizing acc with
  | nil =>
      simp
  | cons term tail ih =>
      simp [List.foldl, ih, add_assoc]

def ConvexComboWitness.weightSum (w : ConvexComboWitness) : Qsqrt2 :=
  w.terms.foldl (fun acc term => acc + term.weight) 0

def ConvexComboTerm.realWeight (term : ConvexComboTerm) : ℝ :=
  term.weight.toReal

lemma ConvexComboWitness.realWeight_foldl_eq_sum_aux
    (terms : List ConvexComboTerm) (acc : ℝ) :
    terms.foldl (fun acc term => acc + term.realWeight) acc =
      acc + (terms.map ConvexComboTerm.realWeight).sum := by
  exact list_foldl_add_eq_add_sum terms ConvexComboTerm.realWeight acc

lemma ConvexComboWitness.weightSum_toReal_foldl_aux
    (terms : List ConvexComboTerm) (acc : Qsqrt2) :
    (terms.foldl (fun acc term => acc + term.weight) acc).toReal =
      terms.foldl (fun acc term => acc + term.realWeight) acc.toReal := by
  induction terms generalizing acc with
  | nil =>
      simp
  | cons term tail ih =>
      simp [List.foldl, ConvexComboTerm.realWeight, ih]

lemma ConvexComboWitness.weightSum_toReal_foldl (w : ConvexComboWitness) :
    w.weightSum.toReal =
      w.terms.foldl (fun acc term => acc + term.realWeight) 0 := by
  simpa [ConvexComboWitness.weightSum] using
    ConvexComboWitness.weightSum_toReal_foldl_aux w.terms 0

def ConvexComboWitness.termAt (w : ConvexComboWitness) (i : Fin w.terms.length) :
    ConvexComboTerm :=
  w.terms.get i

def ConvexComboWitness.realWeightSum (w : ConvexComboWitness) : ℝ :=
  ∑ i : Fin w.terms.length, (w.termAt i).realWeight

lemma ConvexComboWitness.realWeightSum_eq_foldl (w : ConvexComboWitness) :
    w.realWeightSum =
      w.terms.foldl (fun acc term => acc + term.realWeight) 0 := by
  calc
    w.realWeightSum = (w.terms.map ConvexComboTerm.realWeight).sum := by
      simp [ConvexComboWitness.realWeightSum, ConvexComboWitness.termAt]
    _ = w.terms.foldl (fun acc term => acc + term.realWeight) 0 := by
      have h := ConvexComboWitness.realWeight_foldl_eq_sum_aux w.terms 0
      simpa using h.symm

def ConvexComboWitness.eval
    (w : ConvexComboWitness)
    (table : Nat → EuclideanSpace ℝ (Fin 5)) :
    EuclideanSpace ℝ (Fin 5) :=
  ∑ i : Fin w.terms.length, (w.termAt i).realWeight • table (w.termAt i).flagIndex

lemma ConvexComboWitness.eval_eq_foldl
    (w : ConvexComboWitness)
    (table : Nat → EuclideanSpace ℝ (Fin 5)) :
    w.eval table =
      w.terms.foldl
        (fun acc term => acc + term.realWeight • table term.flagIndex) 0 := by
  calc
    w.eval table =
        (w.terms.map fun term => term.realWeight • table term.flagIndex).sum := by
      simpa [ConvexComboWitness.eval, ConvexComboWitness.termAt] using
        (Fin.sum_univ_fun_getElem w.terms
          (fun term => term.realWeight • table term.flagIndex))
    _ =
        w.terms.foldl
          (fun acc term => acc + term.realWeight • table term.flagIndex) 0 := by
      have h :=
        list_foldl_add_eq_add_sum w.terms
          (fun term => term.realWeight • table term.flagIndex)
          (0 : EuclideanSpace ℝ (Fin 5))
      simpa using h.symm

def ConvexComboWitness.evalExact
    (w : ConvexComboWitness)
    (table : Nat → ExactFlag5) :
    ExactFlag5 :=
  w.terms.foldl
    (fun acc term => ExactVec.add acc (ExactVec.smul term.weight (table term.flagIndex)))
    (ExactVec.zero 5)

lemma ConvexComboWitness.evalExact_toReal_foldl_aux
    (terms : List ConvexComboTerm) (table : Nat → ExactFlag5) (acc : ExactFlag5) :
    ExactVec.toReal
        (terms.foldl
          (fun acc term => ExactVec.add acc (ExactVec.smul term.weight (table term.flagIndex)))
          acc) =
      terms.foldl
        (fun acc term => acc + term.realWeight • ExactVec.toReal (table term.flagIndex))
        (ExactVec.toReal acc) := by
  induction terms generalizing acc with
  | nil =>
      simp
  | cons term tail ih =>
      simp [List.foldl, ConvexComboTerm.realWeight, ih]

lemma ConvexComboWitness.evalExact_toReal_foldl
    (w : ConvexComboWitness) (table : Nat → ExactFlag5) :
    ExactVec.toReal (w.evalExact table) =
      w.terms.foldl
        (fun acc term => acc + term.realWeight • ExactVec.toReal (table term.flagIndex))
        0 := by
  simpa [ConvexComboWitness.evalExact] using
    ConvexComboWitness.evalExact_toReal_foldl_aux w.terms table (ExactVec.zero 5)

lemma ConvexComboWitness.evalExact_toReal_eq_eval
    (w : ConvexComboWitness) (flags : List ExactFlag5) :
    ExactVec.toReal (w.evalExact (ExactFlagList.exactTable flags)) =
      w.eval (ExactFlagList.table flags) := by
  rw [ConvexComboWitness.evalExact_toReal_foldl, ConvexComboWitness.eval_eq_foldl]
  simp [ExactFlagList.toReal_exactTable]

/-- Semantic validity of a finite convex-combination witness against a real flag table. -/
structure ConvexComboWitness.Valid
    (w : ConvexComboWitness)
    (table : Nat → EuclideanSpace ℝ (Fin 5))
    (support : Set (EuclideanSpace ℝ (Fin 5))) : Prop where
  weight_nonneg :
    ∀ i : Fin w.terms.length, 0 ≤ (w.termAt i).realWeight
  weight_sum :
    w.realWeightSum = 1
  table_mem :
    ∀ i : Fin w.terms.length, table (w.termAt i).flagIndex ∈ support

theorem ConvexComboWitness.eval_mem_convexHull
    {w : ConvexComboWitness}
    {table : Nat → EuclideanSpace ℝ (Fin 5)}
    {support : Set (EuclideanSpace ℝ (Fin 5))}
    (valid : w.Valid table support) :
    w.eval table ∈ convexHull ℝ support := by
  simpa [ConvexComboWitness.eval, ConvexComboWitness.realWeightSum] using
    (convex_convexHull ℝ support).sum_mem
      (fun i (_hi : i ∈ (Finset.univ : Finset (Fin w.terms.length))) =>
        valid.weight_nonneg i)
      (by simpa [ConvexComboWitness.realWeightSum] using valid.weight_sum)
      (fun i (_hi : i ∈ (Finset.univ : Finset (Fin w.terms.length))) =>
        subset_convexHull ℝ support (valid.table_mem i))

structure ConvexComboWitness.ValidAgainstExactFlags
    (w : ConvexComboWitness) (flags : List ExactFlag5) : Type where
  weight_nonneg_exact :
    ∀ i : Fin w.terms.length, Qsqrt2.NonnegCert (w.termAt i).weight
  weight_sum_exact :
    w.weightSum = 1
  index_valid :
    ∀ i : Fin w.terms.length, ∃ flag : ExactFlag5, flags[(w.termAt i).flagIndex]? = some flag

lemma ConvexComboWitness.ValidAgainstExactFlags.weight_fold_sum
    {w : ConvexComboWitness} {flags : List ExactFlag5}
    (valid : w.ValidAgainstExactFlags flags) :
    w.terms.foldl (fun acc term => acc + term.realWeight) 0 = 1 := by
  have h := congrArg Qsqrt2.toReal valid.weight_sum_exact
  simpa [ConvexComboWitness.weightSum_toReal_foldl] using h

lemma ConvexComboWitness.ValidAgainstExactFlags.weight_nonneg
    {w : ConvexComboWitness} {flags : List ExactFlag5}
    (valid : w.ValidAgainstExactFlags flags) (i : Fin w.terms.length) :
    0 ≤ (w.termAt i).realWeight :=
  Qsqrt2.toReal_nonneg_of_nonnegCert (valid.weight_nonneg_exact i)

def ConvexComboWitness.ValidAgainstExactFlags.toValid
    {w : ConvexComboWitness} {flags : List ExactFlag5}
    (valid : w.ValidAgainstExactFlags flags) :
    w.Valid (ExactFlagList.table flags)
      (ExactFlagList.realFinset flags : Set (EuclideanSpace ℝ (Fin 5))) where
  weight_nonneg := valid.weight_nonneg
  weight_sum := by
    rw [ConvexComboWitness.realWeightSum_eq_foldl]
    exact valid.weight_fold_sum
  table_mem := by
    intro i
    obtain ⟨flag, hget⟩ := valid.index_valid i
    exact ExactFlagList.table_mem_of_get? hget

theorem ConvexComboWitness.eval_mem_convexHull_exactFlags
    {w : ConvexComboWitness} {flags : List ExactFlag5}
    (valid : w.ValidAgainstExactFlags flags) :
    w.eval (ExactFlagList.table flags) ∈
      convexHull ℝ (ExactFlagList.realFinset flags : Set (EuclideanSpace ℝ (Fin 5))) :=
  w.eval_mem_convexHull valid.toValid

theorem ConvexComboWitness.evalExact_toReal_mem_convexHull_exactFlags
    {w : ConvexComboWitness} {flags : List ExactFlag5}
    (valid : w.ValidAgainstExactFlags flags) :
    ExactVec.toReal (w.evalExact (ExactFlagList.exactTable flags)) ∈
      convexHull ℝ (ExactFlagList.realFinset flags : Set (EuclideanSpace ℝ (Fin 5))) := by
  rw [ConvexComboWitness.evalExact_toReal_eq_eval]
  exact w.eval_mem_convexHull_exactFlags valid

/-- Vertex code for the eight vertices of `P_{11/20}`. -/
inductive StellatedVertexCode
  | tetra (i : Fin 4)
  | apex (i : Fin 4)
  deriving DecidableEq, Repr

def StellatedVertexCode.toVertex : StellatedVertexCode → V3
  | .tetra i => tetraVertex i
  | .apex i => stellatedApex i

/-- A combinatorial active incidence: an oriented shadow edge and the vertex whose flag is used. -/
structure ActiveIncidenceCode where
  edgeStart : StellatedVertexCode
  edgeEnd : StellatedVertexCode
  vertex : StellatedVertexCode
  deriving DecidableEq, Repr

/-- Classification used by the `(SF)` checker. -/
inductive SFChartClass
  | shell
  | bulk
  deriving DecidableEq, Repr

/-- One rectangular chart of the `(SF)` second-order sweep. -/
structure SFChartRecord where
  phi : RatInterval
  segment : RatInterval
  chartClass : SFChartClass
  cornerDistanceLower : Qsqrt2
  psiLower : Qsqrt2
  deriving Repr

/-- A three-dimensional dyadic box in the exact `(SF)` sweep coordinates `(φ,x,y)`. -/
structure SFSweepBox where
  phi : RatInterval
  x : RatInterval
  y : RatInterval
  deriving Repr

def SFSweepBox.contains (box : SFSweepBox) (φ x y : ℝ) : Prop :=
  box.phi.contains φ ∧ box.x.contains x ∧ box.y.contains y

def SFSweepBox.containsRatBool (box : SFSweepBox) (φ x y : ℚ) : Bool :=
  box.phi.containsRatBool φ && box.x.containsRatBool x && box.y.containsRatBool y

theorem SFSweepBox.contains_of_containsRatBool_eq_true
    {box : SFSweepBox} {φ x y : ℚ}
    (h : box.containsRatBool φ x y = true) :
    box.contains (φ : ℝ) (x : ℝ) (y : ℝ) := by
  unfold SFSweepBox.containsRatBool at h
  have hsplit :
      (box.phi.containsRatBool φ = true ∧
        box.x.containsRatBool x = true) ∧
        box.y.containsRatBool y = true := by
    simpa using h
  exact
    ⟨RatInterval.contains_of_containsRatBool_eq_true hsplit.1.1,
      RatInterval.contains_of_containsRatBool_eq_true hsplit.1.2,
      RatInterval.contains_of_containsRatBool_eq_true hsplit.2⟩

theorem SFSweepBox.not_contains_of_containsRatBool_eq_false
    {box : SFSweepBox} {φ x y : ℚ}
    (h : box.containsRatBool φ x y = false) :
    ¬ box.contains (φ : ℝ) (x : ℝ) (y : ℝ) := by
  intro hcontains
  have htrue : box.containsRatBool φ x y = true := by
    simp [SFSweepBox.containsRatBool,
      RatInterval.containsRatBool_eq_true_of_contains hcontains.1,
      RatInterval.containsRatBool_eq_true_of_contains hcontains.2.1,
      RatInterval.containsRatBool_eq_true_of_contains hcontains.2.2]
  rw [h] at htrue
  contradiction

/-- Stress-column names emitted by `slf_exact.py`.  The `u` columns have zero tilt multiplier. -/
inductive SFStressColumnCode
  | E13u | E13t
  | E14u | E14t
  | E47u | E47t
  | E40u | E40t
  | E50u | E50t
  | E53u | E53t
  | E24 | E37
  deriving DecidableEq, Repr

/-- The outer-edge index attached to an `(SF)` stress column. -/
def SFStressColumnCode.normalIndex : SFStressColumnCode → Fin 5
  | .E13u | .E13t | .E14u | .E14t => 0
  | .E24 => 1
  | .E37 => 2
  | .E47u | .E47t | .E40u | .E40t => 3
  | .E50u | .E50t | .E53u | .E53t => 4

/-- Split coordinates for `ntil_i = (√2 * a, b)` from `exact_tables.json`. -/
def sfNtilSplit : Fin 5 → ℚ × ℚ
  | 0 => (9 / 20, -31 / 20)
  | 1 => (11 / 20, -9 / 20)
  | 2 => (11 / 20, 9 / 20)
  | 3 => (9 / 20, 31 / 20)
  | 4 => (-2, 0)

/-- Split coordinates for `evec_i = (a, √2 * b)` from `exact_tables.json`. -/
def sfEvecSplit : Fin 5 → ℚ × ℚ
  | 0 => (-31 / 20, -9 / 20)
  | 1 => (-9 / 20, -11 / 20)
  | 2 => (9 / 20, -11 / 20)
  | 3 => (31 / 20, -9 / 20)
  | 4 => (0, 2)

structure SFStressEntry where
  column : SFStressColumnCode
  lambda : ℚ
  tilt : ℚ
  deriving Repr

def SFStressEntry.ntilA (entry : SFStressEntry) : ℚ :=
  (sfNtilSplit entry.column.normalIndex).1

def SFStressEntry.ntilB (entry : SFStressEntry) : ℚ :=
  (sfNtilSplit entry.column.normalIndex).2

def SFStressEntry.evecA (entry : SFStressEntry) : ℚ :=
  (sfEvecSplit entry.column.normalIndex).1

def SFStressEntry.evecB (entry : SFStressEntry) : ℚ :=
  (sfEvecSplit entry.column.normalIndex).2

structure SFStressWitness where
  entries : List SFStressEntry
  psiLower : ℚ
  deriving Repr

namespace SFStressWitness

def lambdaSum (w : SFStressWitness) : ℚ :=
  w.entries.foldl (fun acc entry => acc + entry.lambda) 0

def lambdaNtilA (w : SFStressWitness) : ℚ :=
  w.entries.foldl (fun acc entry => acc + entry.lambda * entry.ntilA) 0

def lambdaNtilB (w : SFStressWitness) : ℚ :=
  w.entries.foldl (fun acc entry => acc + entry.lambda * entry.ntilB) 0

def tiltEvecA (w : SFStressWitness) : ℚ :=
  w.entries.foldl (fun acc entry => acc + entry.tilt * entry.evecA) 0

def tiltEvecB (w : SFStressWitness) : ℚ :=
  w.entries.foldl (fun acc entry => acc + entry.tilt * entry.evecB) 0

def entryValidBool (entry : SFStressEntry) (tiltCap : ℚ) : Bool :=
  decide (0 ≤ entry.lambda ∧ |entry.tilt| ≤ tiltCap * entry.lambda)

def scalarValidBool (w : SFStressWitness) (psiMin : ℚ) : Bool :=
  decide
    (w.lambdaSum = 1 ∧
      w.lambdaNtilA = 0 ∧
      w.lambdaNtilB = 0 ∧
      w.tiltEvecA = 0 ∧
      w.tiltEvecB = 0 ∧
      psiMin ≤ w.psiLower)

def validBool (w : SFStressWitness) (psiMin tiltCap : ℚ) : Bool :=
  (w.entries.all fun entry => entryValidBool entry tiltCap) &&
    scalarValidBool w psiMin

/-- Exact rational checks replayed from `slf_exact.verify_exact` after interval lower bounds
have already been evaluated into `psiLower`. -/
structure Valid (w : SFStressWitness) (psiMin tiltCap : ℚ) : Prop where
  lambda_nonneg :
    ∀ i : Fin w.entries.length, 0 ≤ (w.entries.get i).lambda
  lambda_sum :
    w.lambdaSum = 1
  lambda_balance_a :
    w.lambdaNtilA = 0
  lambda_balance_b :
    w.lambdaNtilB = 0
  tilt_balance_a :
    w.tiltEvecA = 0
  tilt_balance_b :
    w.tiltEvecB = 0
  tilt_cap :
    ∀ i : Fin w.entries.length,
      |(w.entries.get i).tilt| ≤ tiltCap * (w.entries.get i).lambda
  psi_bound :
    psiMin ≤ w.psiLower

lemma entry_valid_of_entryValidBool_eq_true
    {entry : SFStressEntry} {tiltCap : ℚ}
    (h : entryValidBool entry tiltCap = true) :
    0 ≤ entry.lambda ∧ |entry.tilt| ≤ tiltCap * entry.lambda := by
  unfold entryValidBool at h
  exact of_decide_eq_true h

lemma scalar_valid_of_scalarValidBool_eq_true
    {w : SFStressWitness} {psiMin : ℚ}
    (h : scalarValidBool w psiMin = true) :
    w.lambdaSum = 1 ∧
      w.lambdaNtilA = 0 ∧
      w.lambdaNtilB = 0 ∧
      w.tiltEvecA = 0 ∧
      w.tiltEvecB = 0 ∧
      psiMin ≤ w.psiLower := by
  unfold scalarValidBool at h
  exact of_decide_eq_true h

lemma valid_of_validBool_eq_true
    {w : SFStressWitness} {psiMin tiltCap : ℚ}
    (h : w.validBool psiMin tiltCap = true) :
    w.Valid psiMin tiltCap := by
  have hsplit :
      (w.entries.all fun entry => entryValidBool entry tiltCap) = true ∧
        scalarValidBool w psiMin = true := by
    simpa [validBool] using h
  obtain ⟨hentriesBool, hscalarBool⟩ := hsplit
  have hentries :
      ∀ entry ∈ w.entries,
        0 ≤ entry.lambda ∧ |entry.tilt| ≤ tiltCap * entry.lambda := by
    simpa only [entryValidBool, List.all_iff_forall_prop, decide_eq_true_eq]
      using hentriesBool
  obtain ⟨hsum, hlamA, hlamB, htiltA, htiltB, hpsi⟩ :=
    scalar_valid_of_scalarValidBool_eq_true hscalarBool
  refine
    { lambda_nonneg := ?_
      lambda_sum := hsum
      lambda_balance_a := hlamA
      lambda_balance_b := hlamB
      tilt_balance_a := htiltA
      tilt_balance_b := htiltB
      tilt_cap := ?_
      psi_bound := hpsi }
  · intro i
    exact (hentries (w.entries.get i) (List.get_mem w.entries i)).1
  · intro i
    exact (hentries (w.entries.get i) (List.get_mem w.entries i)).2

end SFStressWitness

structure SFCertifiedSweepRow where
  box : SFSweepBox
  witness : SFStressWitness
  deriving Repr

inductive SFSweepDeferKind
  | corner
  | transition
  deriving DecidableEq, Repr

structure SFDeferredSweepRow where
  box : SFSweepBox
  kind : SFSweepDeferKind
  deriving Repr

/-- Typed payload corresponding to `slf_witness.jsonl`.  Certified rows carry exact rational
stress witnesses; deferred rows are handed to the corner/transition arguments. -/
structure SFSweepManifest where
  certified : List SFCertifiedSweepRow
  deferred : List SFDeferredSweepRow
  inputHash : String
  outputHash : String
  deriving Repr

structure SFSweepManifest.CertifiedRowsValid
    (manifest : SFSweepManifest) (psiMin tiltCap : ℚ) : Prop where
  certified_valid :
    ∀ row ∈ manifest.certified, row.witness.Valid psiMin tiltCap

theorem SFSweepManifest.CertifiedRowsValid.row_valid
    {manifest : SFSweepManifest} {psiMin tiltCap : ℚ}
    (valid : manifest.CertifiedRowsValid psiMin tiltCap)
    {row : SFCertifiedSweepRow} (hrow : row ∈ manifest.certified) :
    row.witness.Valid psiMin tiltCap :=
  valid.certified_valid row hrow

/-- Certified-row coverage over an explicit `(φ,x,y)` sweep domain.  This is stronger than the
raw generated stress replay: every point in the domain lands in a certified row, not merely a
deferred corner/transition row. -/
structure SFSweepManifest.CertifiedDomainCover
    (manifest : SFSweepManifest)
    (phiDomain xDomain yDomain : RatInterval) : Prop where
  covers :
    ∀ φ x y : ℝ,
      phiDomain.contains φ → xDomain.contains x → yDomain.contains y →
        ∃ row ∈ manifest.certified, row.box.contains φ x y

/-- Audited sweep coverage before deferred rows are discharged.  A covered point may land either in
a stress-certified row or in a deferred corner/transition row that must be handled by a separate
argument. -/
structure SFSweepManifest.DomainCoverWithDeferred
    (manifest : SFSweepManifest)
    (phiDomain xDomain yDomain : RatInterval) : Prop where
  covers :
    ∀ φ x y : ℝ,
      phiDomain.contains φ → xDomain.contains x → yDomain.contains y →
        (∃ row ∈ manifest.certified, row.box.contains φ x y) ∨
          (∃ row ∈ manifest.deferred, row.box.contains φ x y)

theorem SFSweepManifest.CertifiedDomainCover.to_withDeferred
    {manifest : SFSweepManifest} {phiDomain xDomain yDomain : RatInterval}
    (cover : manifest.CertifiedDomainCover phiDomain xDomain yDomain) :
    manifest.DomainCoverWithDeferred phiDomain xDomain yDomain where
  covers := by
    intro φ x y hφ hx hy
    exact Or.inl (cover.covers φ x y hφ hx hy)

theorem SFSweepManifest.CertifiedDomainCover.exists_valid_row
    {manifest : SFSweepManifest} {psiMin tiltCap : ℚ}
    {phiDomain xDomain yDomain : RatInterval}
    (rowsValid : manifest.CertifiedRowsValid psiMin tiltCap)
    (cover : manifest.CertifiedDomainCover phiDomain xDomain yDomain)
    {φ x y : ℝ}
    (hφ : phiDomain.contains φ) (hx : xDomain.contains x) (hy : yDomain.contains y) :
    ∃ row ∈ manifest.certified,
      row.box.contains φ x y ∧ row.witness.Valid psiMin tiltCap := by
  obtain ⟨row, hrow, hcontains⟩ := cover.covers φ x y hφ hx hy
  exact ⟨row, hrow, hcontains, rowsValid.row_valid hrow⟩

structure SFSweepManifest.Valid
    (manifest : SFSweepManifest) (psiMin tiltCap : ℚ) : Prop where
  certified_valid :
    ∀ row ∈ manifest.certified, row.witness.Valid psiMin tiltCap
  covers :
    ∀ φ x y : ℝ, ∃ row : SFCertifiedSweepRow, row ∈ manifest.certified ∧
      row.box.contains φ x y

theorem SFSweepManifest.Valid.certifiedRowsValid
    {manifest : SFSweepManifest} {psiMin tiltCap : ℚ}
    (valid : manifest.Valid psiMin tiltCap) :
    manifest.CertifiedRowsValid psiMin tiltCap where
  certified_valid := valid.certified_valid

theorem SFSweepManifest.Valid.certifiedDomainCover
    {manifest : SFSweepManifest} {psiMin tiltCap : ℚ}
    {phiDomain xDomain yDomain : RatInterval}
    (valid : manifest.Valid psiMin tiltCap) :
    manifest.CertifiedDomainCover phiDomain xDomain yDomain where
  covers := by
    intro φ x y _hφ _hx _hy
    exact valid.covers φ x y

/-- Exact machine payload for `(SF)`. -/
structure SFCheckerPayload where
  rhoF : Qsqrt2
  rb : Qsqrt2
  nu : Qsqrt2
  psiMin : Qsqrt2
  shellSlope : Qsqrt2
  charts : List SFChartRecord
  inputHash : String
  outputHash : String
  deriving Repr

/-- A pointwise `(SB-box)` record: active incidences plus exact LP/dual-family rows. -/
structure SBBoxPointPayload where
  delta : Qsqrt2
  activeIncidences : List ActiveIncidenceCode
  activeFlags : List ExactFlag5
  boxVertexWitnesses : List ConvexComboWitness
  dualWitnesses : List ConvexComboWitness
  deriving Repr

/-- One chart of the `(SB-box)` checker. -/
structure SBBoxChartRecord where
  deltaRange : Qsqrt2Interval
  points : List SBBoxPointPayload
  inputHash : String
  outputHash : String
  deriving Repr

/-- Exact machine payload for `(SB-box)`. -/
structure SBBoxCheckerPayload where
  rhoB : Qsqrt2
  bPi : Qsqrt2
  bGamma : Qsqrt2
  bT : Qsqrt2
  charts : List SBBoxChartRecord
  deriving Repr

/-- Combinatorial mode labels emitted by the `(SB-box)` bulk replay verifier. -/
inductive SBBoxBulkMode
  | pentA
  | pentB
  | hex1
  | twoA
  | twoB
  deriving DecidableEq, Repr

/-- One replayed `(SB-box)` bulk/seam cell:
`delta × phi × mode × recorded minimum slack × recorded relative eta`. -/
structure SBBoxBulkRow where
  delta : RatInterval
  phi : RatInterval
  mode : SBBoxBulkMode
  minSlack : ℚ
  etaRel : ℚ
  deriving Repr

def SBBoxBulkRow.validBool (row : SBBoxBulkRow) (etaBudget : ℚ) : Bool :=
  decide (0 < row.minSlack ∧ row.etaRel ≤ etaBudget)

structure SBBoxBulkRow.Valid (row : SBBoxBulkRow) (etaBudget : ℚ) : Prop where
  minSlack_pos : 0 < row.minSlack
  etaRel_le_budget : row.etaRel ≤ etaBudget

theorem SBBoxBulkRow.valid_of_validBool_eq_true
    {row : SBBoxBulkRow} {etaBudget : ℚ}
    (h : row.validBool etaBudget = true) :
    row.Valid etaBudget := by
  unfold SBBoxBulkRow.validBool at h
  have hprop : 0 < row.minSlack ∧ row.etaRel ≤ etaBudget :=
    of_decide_eq_true h
  exact
    { minSlack_pos := hprop.1
      etaRel_le_budget := hprop.2 }

structure SBBoxBulkManifest where
  rows : List SBBoxBulkRow
  inputHash : String
  outputHash : String
  deriving Repr

structure SBBoxBulkManifest.RowsValid
    (manifest : SBBoxBulkManifest) (etaBudget : ℚ) : Prop where
  rows_valid :
    ∀ row ∈ manifest.rows, row.validBool etaBudget = true

theorem SBBoxBulkManifest.RowsValid.row_valid
    {manifest : SBBoxBulkManifest} {etaBudget : ℚ}
    (valid : manifest.RowsValid etaBudget) {row : SBBoxBulkRow}
    (hrow : row ∈ manifest.rows) :
    row.Valid etaBudget :=
  SBBoxBulkRow.valid_of_validBool_eq_true (valid.rows_valid row hrow)

structure SBBoxBulkManifest.Tiling
    (manifest : SBBoxBulkManifest)
    (deltaDomain phiDomain : RatInterval) : Prop where
  covers :
    ∀ delta phi : ℝ, deltaDomain.contains delta → phiDomain.contains phi →
      ∃ row ∈ manifest.rows, row.delta.contains delta ∧ row.phi.contains phi

structure SBBoxBulkDeltaStrip where
  deltaLo : ℚ
  deltaHi : ℚ
  rowIndices : List Nat
  deriving Repr

def SBBoxBulkPhiIndexChainCoverBool
    (rows : List SBBoxBulkRow) (indices : List Nat)
    (strip : SBBoxBulkDeltaStrip) (lo hi : ℚ) : Bool :=
  match indices with
  | [] => false
  | idx :: rest =>
      if hidx : idx < rows.length then
        let row := rows.get ⟨idx, hidx⟩
        decide
            (row.delta.lo ≤ strip.deltaLo ∧ strip.deltaHi ≤ row.delta.hi ∧
              row.phi.lo ≤ lo ∧ lo ≤ row.phi.hi) &&
          (decide (hi ≤ row.phi.hi) ||
            SBBoxBulkPhiIndexChainCoverBool rows rest strip row.phi.hi hi)
      else
        false

theorem SBBoxBulkPhiIndexChainCoverBool.exists_mem_contains
    {rows : List SBBoxBulkRow} {indices : List Nat}
    {strip : SBBoxBulkDeltaStrip} {lo hi : ℚ} {delta phi : ℝ}
    (hchain :
      SBBoxBulkPhiIndexChainCoverBool rows indices strip lo hi = true)
    (hdelta : (strip.deltaLo : ℝ) ≤ delta ∧ delta ≤ (strip.deltaHi : ℝ))
    (hlo : (lo : ℝ) ≤ phi) (hhi : phi ≤ (hi : ℝ)) :
    ∃ row ∈ rows, row.delta.contains delta ∧ row.phi.contains phi := by
  induction indices generalizing lo with
  | nil =>
      simp [SBBoxBulkPhiIndexChainCoverBool] at hchain
  | cons idx rest ih =>
      unfold SBBoxBulkPhiIndexChainCoverBool at hchain
      by_cases hidx : idx < rows.length
      · simp [hidx] at hchain
        let row := rows.get ⟨idx, hidx⟩
        have hsplit :
            decide
                (row.delta.lo ≤ strip.deltaLo ∧ strip.deltaHi ≤ row.delta.hi ∧
                  row.phi.lo ≤ lo ∧ lo ≤ row.phi.hi) = true ∧
              (decide (hi ≤ row.phi.hi) ||
                SBBoxBulkPhiIndexChainCoverBool rows rest strip row.phi.hi hi) = true := by
          simpa [row] using hchain
        have hhead :
            row.delta.lo ≤ strip.deltaLo ∧ strip.deltaHi ≤ row.delta.hi ∧
              row.phi.lo ≤ lo ∧ lo ≤ row.phi.hi :=
          of_decide_eq_true hsplit.1
        by_cases hdoneBool : decide (hi ≤ row.phi.hi) = true
        · refine ⟨row, List.get_mem rows ⟨idx, hidx⟩, ?_, ?_⟩
          · exact
              ⟨le_trans (by exact_mod_cast hhead.1) hdelta.1,
                le_trans hdelta.2 (by exact_mod_cast hhead.2.1)⟩
          · exact
              ⟨le_trans (by exact_mod_cast hhead.2.2.1) hlo,
                le_trans hhi (by exact_mod_cast
                  (of_decide_eq_true hdoneBool : hi ≤ row.phi.hi))⟩
        · have hrestBool :
              SBBoxBulkPhiIndexChainCoverBool rows rest strip row.phi.hi hi = true := by
            cases hrestValue :
                SBBoxBulkPhiIndexChainCoverBool rows rest strip row.phi.hi hi <;>
              simp [hdoneBool, hrestValue] at hsplit
            rfl
          by_cases hx : phi ≤ (row.phi.hi : ℝ)
          · refine ⟨row, List.get_mem rows ⟨idx, hidx⟩, ?_, ?_⟩
            · exact
                ⟨le_trans (by exact_mod_cast hhead.1) hdelta.1,
                  le_trans hdelta.2 (by exact_mod_cast hhead.2.1)⟩
            · exact ⟨le_trans (by exact_mod_cast hhead.2.2.1) hlo, hx⟩
          · have hrowHi_le_x : (row.phi.hi : ℝ) ≤ phi := le_of_lt (lt_of_not_ge hx)
            exact ih hrestBool hrowHi_le_x
      · simp [hidx] at hchain

def SBBoxBulkStripChainCoverBool
    (rows : List SBBoxBulkRow) (strips : List SBBoxBulkDeltaStrip)
    (deltaLo deltaHi : ℚ) (phiDomain : RatInterval) : Bool :=
  match strips with
  | [] => false
  | strip :: rest =>
      decide (strip.deltaLo ≤ deltaLo ∧ deltaLo ≤ strip.deltaHi) &&
        SBBoxBulkPhiIndexChainCoverBool rows strip.rowIndices strip phiDomain.lo phiDomain.hi &&
          (decide (deltaHi ≤ strip.deltaHi) ||
            SBBoxBulkStripChainCoverBool rows rest strip.deltaHi deltaHi phiDomain)

theorem SBBoxBulkStripChainCoverBool.exists_mem_contains
    {rows : List SBBoxBulkRow} {strips : List SBBoxBulkDeltaStrip}
    {deltaLo deltaHi : ℚ} {phiDomain : RatInterval} {delta phi : ℝ}
    (hchain :
      SBBoxBulkStripChainCoverBool rows strips deltaLo deltaHi phiDomain = true)
    (hdeltaLo : (deltaLo : ℝ) ≤ delta) (hdeltaHi : delta ≤ (deltaHi : ℝ))
    (hphi : phiDomain.contains phi) :
    ∃ row ∈ rows, row.delta.contains delta ∧ row.phi.contains phi := by
  induction strips generalizing deltaLo with
  | nil =>
      simp [SBBoxBulkStripChainCoverBool] at hchain
  | cons strip rest ih =>
      unfold SBBoxBulkStripChainCoverBool at hchain
      have hsplit :
          (decide (strip.deltaLo ≤ deltaLo ∧ deltaLo ≤ strip.deltaHi) = true ∧
            SBBoxBulkPhiIndexChainCoverBool rows strip.rowIndices strip
                phiDomain.lo phiDomain.hi = true) ∧
              (decide (deltaHi ≤ strip.deltaHi) ||
                SBBoxBulkStripChainCoverBool rows rest strip.deltaHi deltaHi phiDomain) = true := by
        simpa using hchain
      have hstripHead : strip.deltaLo ≤ deltaLo ∧ deltaLo ≤ strip.deltaHi :=
        of_decide_eq_true hsplit.1.1
      by_cases hdoneBool : decide (deltaHi ≤ strip.deltaHi) = true
      · have hdeltaStrip : (strip.deltaLo : ℝ) ≤ delta ∧ delta ≤ (strip.deltaHi : ℝ) :=
          ⟨le_trans (by exact_mod_cast hstripHead.1) hdeltaLo,
            le_trans hdeltaHi (by exact_mod_cast
              (of_decide_eq_true hdoneBool : deltaHi ≤ strip.deltaHi))⟩
        exact
          SBBoxBulkPhiIndexChainCoverBool.exists_mem_contains
            hsplit.1.2 hdeltaStrip hphi.1 hphi.2
      · have hrestBool :
            SBBoxBulkStripChainCoverBool rows rest strip.deltaHi deltaHi phiDomain = true := by
          cases hrestValue :
              SBBoxBulkStripChainCoverBool rows rest strip.deltaHi deltaHi phiDomain <;>
            simp [hdoneBool, hrestValue] at hsplit
          rfl
        by_cases hx : delta ≤ (strip.deltaHi : ℝ)
        · have hdeltaStrip : (strip.deltaLo : ℝ) ≤ delta ∧ delta ≤ (strip.deltaHi : ℝ) :=
            ⟨le_trans (by exact_mod_cast hstripHead.1) hdeltaLo, hx⟩
          exact
            SBBoxBulkPhiIndexChainCoverBool.exists_mem_contains
              hsplit.1.2 hdeltaStrip hphi.1 hphi.2
        · have hstripHi_le_delta : (strip.deltaHi : ℝ) ≤ delta :=
            le_of_lt (lt_of_not_ge hx)
          exact ih hrestBool hstripHi_le_delta

theorem SBBoxBulkManifest.tiling_of_strip_chain_bool
    {manifest : SBBoxBulkManifest} {strips : List SBBoxBulkDeltaStrip}
    {deltaDomain phiDomain : RatInterval}
    (hchain :
      SBBoxBulkStripChainCoverBool manifest.rows strips
        deltaDomain.lo deltaDomain.hi phiDomain = true) :
    manifest.Tiling deltaDomain phiDomain where
  covers := by
    intro delta phi hdelta hphi
    exact
      SBBoxBulkStripChainCoverBool.exists_mem_contains
        hchain hdelta.1 hdelta.2 hphi

/-- Tail chart index used by the exact `sbd3` verifier. -/
inductive SBBoxTailChart
  | chart1
  | chart2
  deriving DecidableEq, Repr

/-- Configuration labels used by the exact `sbd3` tail verifier. -/
inductive SBBoxTailConfig
  | pentA
  | pentB
  | pentB_w
  | hex1
  deriving DecidableEq, Repr

inductive SBBoxTailKind
  | single
  | wall
  deriving DecidableEq, Repr

/-- One replay-good `sbd3` tail cell.  `scalePrimary` is `c` for single rows and `cP`
for wall rows; `scaleSecondary` is present only for wall rows and stores `cH`. -/
structure SBBoxTailRow where
  chart : SBBoxTailChart
  r : RatInterval
  kind : SBBoxTailKind
  config : SBBoxTailConfig
  configSecondary : Option SBBoxTailConfig
  scalePrimary : ℚ
  scaleSecondary : Option ℚ
  gainLower : ℚ
  slackPi : ℚ
  slackGamma : ℚ
  slackT : ℚ
  deriving Repr

def SBBoxTailRow.validBool (row : SBBoxTailRow) : Bool :=
  decide
    (0 < row.gainLower ∧
      0 < row.slackPi ∧
      0 < row.slackGamma ∧
      0 < row.slackT)

structure SBBoxTailRow.Valid (row : SBBoxTailRow) : Prop where
  gainLower_pos : 0 < row.gainLower
  slackPi_pos : 0 < row.slackPi
  slackGamma_pos : 0 < row.slackGamma
  slackT_pos : 0 < row.slackT

theorem SBBoxTailRow.valid_of_validBool_eq_true
    {row : SBBoxTailRow} (h : row.validBool = true) :
    row.Valid := by
  unfold SBBoxTailRow.validBool at h
  have hprop :
      0 < row.gainLower ∧
        0 < row.slackPi ∧
        0 < row.slackGamma ∧
        0 < row.slackT :=
    of_decide_eq_true h
  exact
    { gainLower_pos := hprop.1
      slackPi_pos := hprop.2.1
      slackGamma_pos := hprop.2.2.1
      slackT_pos := hprop.2.2.2 }

structure SBBoxTailManifest where
  rows : List SBBoxTailRow
  inputHash : String
  outputHash : String
  deriving Repr

structure SBBoxTailManifest.RowsValid (manifest : SBBoxTailManifest) : Prop where
  rows_valid :
    ∀ row ∈ manifest.rows, row.validBool = true

theorem SBBoxTailManifest.RowsValid.row_valid
    {manifest : SBBoxTailManifest} (valid : manifest.RowsValid)
    {row : SBBoxTailRow} (hrow : row ∈ manifest.rows) :
    row.Valid :=
  SBBoxTailRow.valid_of_validBool_eq_true (valid.rows_valid row hrow)

def SBBoxTailManifest.chartRows
    (manifest : SBBoxTailManifest) (chart : SBBoxTailChart) : List SBBoxTailRow :=
  manifest.rows.filter fun row => decide (row.chart = chart)

/-- A finite gap-free 1D cover certificate for the tail chart rows, in manifest order.

Starting with covered left endpoint `lo`, each row must belong to the chart, start no later than
`lo`, and reach at least `lo`.  Either it already reaches the requested right endpoint `hi`, or the
remaining rows continue the chain from this row's right endpoint. -/
def SBBoxTailRowsChainCover
    (rows : List SBBoxTailRow) (chart : SBBoxTailChart) (lo hi : ℚ) : Prop :=
  match rows with
  | [] => False
  | row :: rest =>
      row.chart = chart ∧ row.r.lo ≤ lo ∧ lo ≤ row.r.hi ∧
        (hi ≤ row.r.hi ∨
          SBBoxTailRowsChainCover rest chart row.r.hi hi)

def SBBoxTailRowsChainCoverBool
    (rows : List SBBoxTailRow) (chart : SBBoxTailChart) (lo hi : ℚ) : Bool :=
  match rows with
  | [] => false
  | row :: rest =>
      decide (row.chart = chart ∧ row.r.lo ≤ lo ∧ lo ≤ row.r.hi) &&
        (decide (hi ≤ row.r.hi) ||
          SBBoxTailRowsChainCoverBool rest chart row.r.hi hi)

theorem SBBoxTailRowsChainCover.of_bool
    {rows : List SBBoxTailRow} {chart : SBBoxTailChart} {lo hi : ℚ}
    (h : SBBoxTailRowsChainCoverBool rows chart lo hi = true) :
    SBBoxTailRowsChainCover rows chart lo hi := by
  induction rows generalizing lo with
  | nil =>
      simp [SBBoxTailRowsChainCoverBool] at h
  | cons row rest ih =>
      have hsplit :
          decide (row.chart = chart ∧ row.r.lo ≤ lo ∧ lo ≤ row.r.hi) = true ∧
            (decide (hi ≤ row.r.hi) ||
              SBBoxTailRowsChainCoverBool rest chart row.r.hi hi) = true := by
        simpa [SBBoxTailRowsChainCoverBool] using h
      have hhead : row.chart = chart ∧ row.r.lo ≤ lo ∧ lo ≤ row.r.hi :=
        of_decide_eq_true hsplit.1
      have htail :
          hi ≤ row.r.hi ∨
            SBBoxTailRowsChainCover rest chart row.r.hi hi := by
        by_cases hdoneBool : decide (hi ≤ row.r.hi) = true
        · exact Or.inl (of_decide_eq_true hdoneBool)
        · have hrestBool :
              SBBoxTailRowsChainCoverBool rest chart row.r.hi hi = true := by
            cases hrestValue :
                SBBoxTailRowsChainCoverBool rest chart row.r.hi hi <;>
              simp [hdoneBool, hrestValue] at hsplit
            rfl
          exact Or.inr (ih hrestBool)
      exact ⟨hhead.1, hhead.2.1, hhead.2.2, htail⟩

theorem SBBoxTailRowsChainCover.exists_mem_contains
    {rows : List SBBoxTailRow} {chart : SBBoxTailChart} {lo hi : ℚ} {x : ℝ}
    (hchain : SBBoxTailRowsChainCover rows chart lo hi)
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    ∃ row ∈ rows, row.chart = chart ∧ row.r.contains x := by
  induction rows generalizing lo with
  | nil =>
      cases hchain
  | cons row rest ih =>
      rcases hchain with ⟨hchart, hrowLo, hlo_rowHi, hdone | hrest⟩
      · refine ⟨row, by simp, hchart, ?_⟩
        constructor
        · exact le_trans (by exact_mod_cast hrowLo) hlo
        · exact le_trans hhi (by exact_mod_cast hdone)
      · by_cases hx : x ≤ (row.r.hi : ℝ)
        · refine ⟨row, by simp, hchart, ?_⟩
          constructor
          · exact le_trans (by exact_mod_cast hrowLo) hlo
          · exact hx
        · have hrowHi_le_x : (row.r.hi : ℝ) ≤ x := le_of_lt (lt_of_not_ge hx)
          obtain ⟨row', hmem, hchart', hcontains⟩ :=
            ih hrest hrowHi_le_x
          exact ⟨row', by simp [hmem], hchart', hcontains⟩

structure SBBoxTailManifest.ChartTiling
    (manifest : SBBoxTailManifest) (chart : SBBoxTailChart)
    (domain : RatInterval) : Prop where
  covers :
    ∀ r : ℝ, domain.contains r →
      ∃ row ∈ manifest.rows, row.chart = chart ∧ row.r.contains r

theorem SBBoxTailManifest.chartTiling_of_chain
    {manifest : SBBoxTailManifest} {chart : SBBoxTailChart} {domain : RatInterval}
    (hchain :
      SBBoxTailRowsChainCover (manifest.chartRows chart) chart domain.lo domain.hi) :
    manifest.ChartTiling chart domain where
  covers := by
    intro r hr
    obtain ⟨row, hmemChartRows, hchart, hcontains⟩ :=
      SBBoxTailRowsChainCover.exists_mem_contains hchain hr.1 hr.2
    have hmemRows : row ∈ manifest.rows := by
      exact (List.mem_filter.mp hmemChartRows).1
    exact ⟨row, hmemRows, hchart, hcontains⟩

/-- Boolean gap-free cover checker for a generated sorted list of row indices. -/
def SBBoxTailIndexChainCoverBool
    (rows : List SBBoxTailRow) (indices : List Nat)
    (chart : SBBoxTailChart) (lo hi : ℚ) : Bool :=
  match indices with
  | [] => false
  | idx :: rest =>
      if hidx : idx < rows.length then
        let row := rows.get ⟨idx, hidx⟩
        decide (row.chart = chart ∧ row.r.lo ≤ lo ∧ lo ≤ row.r.hi) &&
          (decide (hi ≤ row.r.hi) ||
            SBBoxTailIndexChainCoverBool rows rest chart row.r.hi hi)
      else
        false

theorem SBBoxTailIndexChainCoverBool.exists_mem_contains
    {rows : List SBBoxTailRow} {indices : List Nat}
    {chart : SBBoxTailChart} {lo hi : ℚ} {x : ℝ}
    (hchain :
      SBBoxTailIndexChainCoverBool rows indices chart lo hi = true)
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    ∃ row ∈ rows, row.chart = chart ∧ row.r.contains x := by
  induction indices generalizing lo with
  | nil =>
      simp [SBBoxTailIndexChainCoverBool] at hchain
  | cons idx rest ih =>
      unfold SBBoxTailIndexChainCoverBool at hchain
      by_cases hidx : idx < rows.length
      · simp [hidx] at hchain
        let row := rows.get ⟨idx, hidx⟩
        have hsplit :
            decide (row.chart = chart ∧ row.r.lo ≤ lo ∧ lo ≤ row.r.hi) = true ∧
              (decide (hi ≤ row.r.hi) ||
                SBBoxTailIndexChainCoverBool rows rest chart row.r.hi hi) = true := by
          simpa [row] using hchain
        have hhead : row.chart = chart ∧ row.r.lo ≤ lo ∧ lo ≤ row.r.hi :=
          of_decide_eq_true hsplit.1
        by_cases hdoneBool : decide (hi ≤ row.r.hi) = true
        · refine ⟨row, List.get_mem rows ⟨idx, hidx⟩, hhead.1, ?_⟩
          constructor
          · exact le_trans (by exact_mod_cast hhead.2.1) hlo
          · exact le_trans hhi (by exact_mod_cast (of_decide_eq_true hdoneBool : hi ≤ row.r.hi))
        · have hrestBool :
              SBBoxTailIndexChainCoverBool rows rest chart row.r.hi hi = true := by
            cases hrestValue :
                SBBoxTailIndexChainCoverBool rows rest chart row.r.hi hi <;>
              simp [hdoneBool, hrestValue] at hsplit
            rfl
          by_cases hx : x ≤ (row.r.hi : ℝ)
          · refine ⟨row, List.get_mem rows ⟨idx, hidx⟩, hhead.1, ?_⟩
            constructor
            · exact le_trans (by exact_mod_cast hhead.2.1) hlo
            · exact hx
          · have hrowHi_le_x : (row.r.hi : ℝ) ≤ x := le_of_lt (lt_of_not_ge hx)
            exact ih hrestBool hrowHi_le_x
      · simp [hidx] at hchain

theorem SBBoxTailManifest.chartTiling_of_index_chain_bool
    {manifest : SBBoxTailManifest} {indices : List Nat}
    {chart : SBBoxTailChart} {domain : RatInterval}
    (hchain :
      SBBoxTailIndexChainCoverBool manifest.rows indices chart domain.lo domain.hi = true) :
    manifest.ChartTiling chart domain where
  covers := by
    intro r hr
    exact SBBoxTailIndexChainCoverBool.exists_mem_contains hchain hr.1 hr.2

structure SBBoxTailManifest.Tiling
    (manifest : SBBoxTailManifest) (domain : RatInterval) : Prop where
  chart1 : manifest.ChartTiling .chart1 domain
  chart2 : manifest.ChartTiling .chart2 domain

theorem SBBoxTailManifest.ChartTiling.exists_valid_row
    {manifest : SBBoxTailManifest} {chart : SBBoxTailChart} {domain : RatInterval}
    (rowsValid : manifest.RowsValid)
    (tiling : manifest.ChartTiling chart domain)
    {r : ℝ} (hr : domain.contains r) :
    ∃ row ∈ manifest.rows, row.chart = chart ∧ row.r.contains r ∧ row.Valid := by
  obtain ⟨row, hrow, hchart, hcontains⟩ := tiling.covers r hr
  exact ⟨row, hrow, hchart, hcontains, rowsValid.row_valid hrow⟩

theorem SBBoxTailManifest.Tiling.exists_valid_row
    {manifest : SBBoxTailManifest} {domain : RatInterval}
    (rowsValid : manifest.RowsValid)
    (tiling : manifest.Tiling domain)
    (chart : SBBoxTailChart) {r : ℝ} (hr : domain.contains r) :
    ∃ row ∈ manifest.rows, row.chart = chart ∧ row.r.contains r ∧ row.Valid := by
  cases chart
  · exact tiling.chart1.exists_valid_row rowsValid hr
  · exact tiling.chart2.exists_valid_row rowsValid hr

/-- Lean-facing summary of the executed `(SB-box)` replay assembly.

This records the mechanical stitch facts emitted by `ASSEMBLY_REPORT.json`: row counts for the
exact tail and interval bulk/seam manifests, plus the scalar interface inequalities used to join
tail, seam, bulk, and the box-reach/shell-radius handoff.  It is deliberately not the geometric
`SBBoxPayloadVerified` bridge; that bridge still has to consume the tiling and row soundness
theorems. -/
structure SBBoxReplayAssemblyReport where
  tailRows : Nat
  bulkLevelRows : Nat
  bulkSeamRows : Nat
  bulkStrips : Nat
  tailEnd : ℚ
  seamLo : ℚ
  rho0Minus : ℚ
  rho0 : ℚ
  rho0Plus : ℚ
  boxReachLower : ℚ
  shellRadius : ℚ
  deriving Repr

def SBBoxReplayAssemblyReport.interfaceValidBool
    (report : SBBoxReplayAssemblyReport) : Bool :=
  decide
    (report.seamLo < report.tailEnd ∧
      report.rho0Minus < report.rho0 ∧
      report.rho0 ≤ report.rho0Plus ∧
      report.shellRadius < report.boxReachLower)

structure SBBoxReplayAssemblyReport.InterfaceValid
    (report : SBBoxReplayAssemblyReport) : Prop where
  seam_straddles_tail : report.seamLo < report.tailEnd
  rho0_straddled : report.rho0Minus < report.rho0 ∧ report.rho0 ≤ report.rho0Plus
  box_reaches_shell : report.shellRadius < report.boxReachLower

theorem SBBoxReplayAssemblyReport.interfaceValid_of_bool
    {report : SBBoxReplayAssemblyReport}
    (h : report.interfaceValidBool = true) :
    report.InterfaceValid := by
  unfold SBBoxReplayAssemblyReport.interfaceValidBool at h
  have hprop :
      report.seamLo < report.tailEnd ∧
        report.rho0Minus < report.rho0 ∧
        report.rho0 ≤ report.rho0Plus ∧
        report.shellRadius < report.boxReachLower := by
    exact of_decide_eq_true h
  exact
    { seam_straddles_tail := hprop.1
      rho0_straddled := ⟨hprop.2.1, hprop.2.2.1⟩
      box_reaches_shell := hprop.2.2.2 }

def SBBoxReplayAssemblyReport.totalBulkRows
    (report : SBBoxReplayAssemblyReport) : Nat :=
  report.bulkLevelRows + report.bulkSeamRows

structure SBBoxReplayAssembly
    (tail : SBBoxTailManifest) (bulk : SBBoxBulkManifest)
    (report : SBBoxReplayAssemblyReport)
    (tailDomain bulkDeltaDomain bulkPhiDomain : RatInterval)
    (etaBudget : ℚ) : Prop where
  tail_rows_valid : tail.RowsValid
  bulk_rows_valid : bulk.RowsValid etaBudget
  tail_tiling : tail.Tiling tailDomain
  bulk_tiling : bulk.Tiling bulkDeltaDomain bulkPhiDomain
  interface_valid : report.InterfaceValid
  tail_rows_match : report.tailRows = tail.rows.length
  bulk_rows_match : report.totalBulkRows = bulk.rows.length

theorem SBBoxBulkManifest.Tiling.exists_valid_row
    {manifest : SBBoxBulkManifest} {etaBudget : ℚ}
    {deltaDomain phiDomain : RatInterval}
    (rowsValid : manifest.RowsValid etaBudget)
    (tiling : manifest.Tiling deltaDomain phiDomain)
    {delta phi : ℝ}
    (hdelta : deltaDomain.contains delta) (hphi : phiDomain.contains phi) :
    ∃ row ∈ manifest.rows,
      row.delta.contains delta ∧ row.phi.contains phi ∧ row.Valid etaBudget := by
  obtain ⟨row, hrow, hdeltaRow, hphiRow⟩ := tiling.covers delta phi hdelta hphi
  exact ⟨row, hrow, hdeltaRow, hphiRow, rowsValid.row_valid hrow⟩

theorem SBBoxReplayAssembly.tail_exists_valid_row
    {tail : SBBoxTailManifest} {bulk : SBBoxBulkManifest}
    {report : SBBoxReplayAssemblyReport}
    {tailDomain bulkDeltaDomain bulkPhiDomain : RatInterval}
    {etaBudget : ℚ}
    (assembly :
      SBBoxReplayAssembly tail bulk report tailDomain bulkDeltaDomain bulkPhiDomain etaBudget)
    (chart : SBBoxTailChart) {r : ℝ} (hr : tailDomain.contains r) :
    ∃ row ∈ tail.rows, row.chart = chart ∧ row.r.contains r ∧ row.Valid :=
  assembly.tail_tiling.exists_valid_row assembly.tail_rows_valid chart hr

theorem SBBoxReplayAssembly.bulk_exists_valid_row
    {tail : SBBoxTailManifest} {bulk : SBBoxBulkManifest}
    {report : SBBoxReplayAssemblyReport}
    {tailDomain bulkDeltaDomain bulkPhiDomain : RatInterval}
    {etaBudget : ℚ}
    (assembly :
      SBBoxReplayAssembly tail bulk report tailDomain bulkDeltaDomain bulkPhiDomain etaBudget)
    {delta phi : ℝ}
    (hdelta : bulkDeltaDomain.contains delta) (hphi : bulkPhiDomain.contains phi) :
    ∃ row ∈ bulk.rows,
      row.delta.contains delta ∧ row.phi.contains phi ∧ row.Valid etaBudget :=
  assembly.bulk_tiling.exists_valid_row assembly.bulk_rows_valid hdelta hphi

/-- Exact facet/stress row used by the finite `u*` depth checker. -/
structure UStarDepthFacetRecord where
  normal : ExactFlag5
  offsetLower : Qsqrt2
  witness : ConvexComboWitness
  deriving Repr

/-- Exact machine payload for the `u*` depth computation. -/
structure UStarDepthPayload where
  radius : Qsqrt2
  activeIncidences : List UStarActiveFlagIndex
  facets : List UStarDepthFacetRecord
  inputHash : String
  outputHash : String
  deriving Repr

end RupertStellatedTetrahedron
