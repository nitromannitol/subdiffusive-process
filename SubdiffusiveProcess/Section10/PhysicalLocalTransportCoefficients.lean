module

public import SubdiffusiveProcess.Section10.PhysicalLocalTransportEnvironment
public import SubdiffusiveProcess.Main.CutoffSpeedDensity
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Main.PhysicalTimeFactor

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Homogenization Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess
open scoped BigOperators NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalLocalTransport

variable {d : ℕ}

/-- The active cutoff from paper 8194 and 8215; top is distinct from cutoff zero. -/
def activeScale (L : WithTop ℕ) (m : ℕ) : ℕ :=
  min m (L.untopD m)

@[simp] theorem activeScale_coe (l m : ℕ) : activeScale (l : WithTop ℕ) m = min m l := rfl

def localFactor (M : GMCModel d) (L : WithTop ℕ) (m : ℕ)
    (z : Vec d) (omega : AnchoredC11Sample d) : ℝ :=
  coefficientAt M L omega z / aCutoff M (activeScale L m) omega.val z

def localSpeed (M : GMCModel d) (L : WithTop ℕ) (m : ℕ)
    (z : Vec d) (omega : AnchoredC11Sample d) (x : Vec d) : ℝ :=
  (localFactor M L m z omega)⁻¹ * coefficientAt M L omega (z + (3 : ℝ) ^ m • x)

def localCoefficient (M : GMCModel d) (L : WithTop ℕ) (m : ℕ)
    (z : Vec d) (omega : AnchoredC11Sample d) (x : Vec d) : ℝ :=
  (ahom M (activeScale L m))⁻¹ * localSpeed M L m z omega x

def rawClock (M : GMCModel d) (L : WithTop ℕ) (m : ℕ) : ℝ≥0 :=
  ⟨(3 : ℝ) ^ (2 * m) / ahom M (activeScale L m),
    (div_pos (pow_pos (by norm_num) _) (ahom_pos M _)).le⟩

theorem rawClock_pos (M : GMCModel d) (L : WithTop ℕ) (m : ℕ) :
    0 < rawClock M L m :=
  div_pos (pow_pos (by norm_num) _) (ahom_pos M _)

/-- Retain the nontrivial `ahom_0` in the already established normalized clock. -/
theorem normalizedClock_eq (M : GMCModel d) (m : ℕ) :
    (physicalTimeFactor M m : ℝ) = ahom M 0 * (rawClock M ⊤ m : ℝ) := by
  simp only [physicalTimeFactor, rawClock, activeScale,
    WithTop.untopD_top, min_self, NNReal.coe_mk]
  change ahom M 0 * (3 : ℝ) ^ (2 * m) / ahom M m =
    ahom M 0 * ((3 : ℝ) ^ (2 * m) / ahom M m)
  ring

theorem localFactor_pos (M : GMCModel d) (L : WithTop ℕ) (m : ℕ)
    (z : Vec d) (omega : AnchoredC11Sample d) : 0 < localFactor M L m z omega :=
  div_pos (coefficientAt_pos M L omega z) (aCutoff_pos M _ omega.val z)

theorem localSpeed_pos (M : GMCModel d) (L : WithTop ℕ) (m : ℕ)
    (z : Vec d) (omega : AnchoredC11Sample d) (x : Vec d) :
    0 < localSpeed M L m z omega x :=
  mul_pos (inv_pos.mpr (localFactor_pos M L m z omega)) (coefficientAt_pos M L omega _)

theorem continuous_localSpeed (M : GMCModel d) (L : WithTop ℕ) (m : ℕ)
    (z : Vec d) (omega : AnchoredC11Sample d) : Continuous (localSpeed M L m z omega) :=
  continuous_const.mul ((continuous_coefficientAt M L omega).comp
    (by fun_prop))

theorem localCoefficientOn (M : GMCModel d) (L : WithTop ℕ) (m : ℕ)
    (z : Vec d) (omega : AnchoredC11Sample d) {U : Set (Vec d)} (hU : Bornology.IsBounded U) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.CoefficientOn U
      (localCoefficient M L m z omega) := by
  exact SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos
    (continuous_const.mul (continuous_localSpeed M L m z omega))
    (fun x => mul_pos (inv_pos.mpr (ahom_pos M _)) (localSpeed_pos M L m z omega x)) hU

/-- The source's `c=1` branch includes equality of the two scales. -/
theorem localFactor_eq_one (M : GMCModel d) {l m : ℕ} (h : l ≤ m)
    (z : Vec d) (omega : AnchoredC11Sample d) : localFactor M l m z omega = 1 := by
  change aCutoff M l omega.val z / aCutoff M (min m l) omega.val z = 1
  rw [min_eq_right h]
  exact div_self (aCutoff_pos M l omega.val z).ne'

/-- Finite local density in the actual shifted window; no infinite infrared field is discarded. -/
def finiteLocalPotential (M : GMCModel d) (l m : ℕ) (xi : BilateralField d)
    (x : Vec d) : ℝ :=
  (∑ k ∈ Finset.range (l + 1), (xi ((k : ℤ) - m) x - xi ((k : ℤ) - m) 0)) +
    ∑ k ∈ Finset.range (min m l + 1), (xi ((k : ℤ) - m) 0 - tauSq M.P)

def finiteLocalSpeed (M : GMCModel d) (l m : ℕ) (xi : BilateralField d) (x : Vec d) : ℝ :=
  Real.exp (finiteLocalPotential M l m xi x)

def finiteLocalCoefficient (M : GMCModel d) (l m : ℕ) (xi : BilateralField d)
    (x : Vec d) : ℝ := (ahom M (min m l))⁻¹ * finiteLocalSpeed M l m xi x

theorem localSpeed_exp (M : GMCModel d) (L : WithTop ℕ) (m : ℕ)
    (z : Vec d) (omega : AnchoredC11Sample d) (x : Vec d) :
    localSpeed M L m z omega x = Real.exp
      (PhysicalAttachment.physicalPotential M L omega (z + (3 : ℝ) ^ m • x) -
        PhysicalAttachment.physicalPotential M L omega z +
        PhysicalAttachment.physicalPotential M (activeScale L m) omega z) := by
  rw [Real.exp_add, Real.exp_sub, PhysicalAttachment.exp_physicalPotential,
    PhysicalAttachment.exp_physicalPotential, PhysicalAttachment.exp_physicalPotential]
  change (coefficientAt M L omega z / aCutoff M (activeScale L m) omega.val z)⁻¹ *
      coefficientAt M L omega (z + (3 : ℝ) ^ m • x) = _
  change (coefficientAt M L omega z / aCutoff M (activeScale L m) omega.val z)⁻¹ *
      coefficientAt M L omega (z + (3 : ℝ) ^ m • x) =
    coefficientAt M L omega (z + (3 : ℝ) ^ m • x) / coefficientAt M L omega z *
      aCutoff M (activeScale L m) omega.val z
  field_simp

theorem physicalPotential_finite_apply (M : GMCModel d) (l : ℕ)
    (omega : AnchoredC11Sample d) (x : Vec d) :
    PhysicalAttachment.physicalPotential M l omega x =
      ∑ k ∈ Finset.range (l + 1), (omega.val k x - tauSq M.P) := by
  change (∑ k ∈ Finset.range (l + 1),
    ((omega.val k).1.1 - ContinuousMap.const (Vec d) (tauSq M.P)) : C(Vec d, ℝ)) x = _
  simp only [ContinuousMap.sum_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply]

variable [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]

/-- The two actual marginals are coupled by equality of the literal local coefficients. -/
theorem finite_local_identification (M : GMCModel d) (l m : ℕ) (z : Vec d) :
    ∀ᵐ eta ∂nativeLaw M, ∀ x : Vec d,
      localSpeed M l m z (physicalEnvironment M m z eta) x =
        finiteLocalSpeed M l m (bilateralEnvironment eta) x ∧
      localCoefficient M l m z (physicalEnvironment M m z eta) x =
        finiteLocalCoefficient M l m (bilateralEnvironment eta) x := by
  filter_upwards [physicalEnvironment_local M m z] with eta h
  have hz (k : ℕ) : (physicalEnvironment M m z eta).val k z =
      bilateralEnvironment eta ((k : ℤ) - m) 0 := by
    simpa only [smul_zero, add_zero] using h k 0
  intro x
  have hs : localSpeed M l m z (physicalEnvironment M m z eta) x =
      finiteLocalSpeed M l m (bilateralEnvironment eta) x := by
    rw [localSpeed_exp]
    rw [activeScale_coe]
    unfold finiteLocalSpeed finiteLocalPotential
    congr 1
    rw [physicalPotential_finite_apply, physicalPotential_finite_apply,
      physicalPotential_finite_apply]
    simp only [h, hz,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  exact ⟨hs, by change (ahom M (min m l))⁻¹ * localSpeed M l m z (physicalEnvironment M m z eta) x = _; rw [hs]; rfl⟩

/-- For `m≤l`, the large layers form precisely the truncated infrared field. -/
theorem finiteLocalPotential_eq (M : GMCModel d) {l m : ℕ} (hml : m ≤ l)
    (xi : BilateralField d) (x : Vec d) :
    finiteLocalPotential M l m xi x =
      infraredPartialSum xi (l - m) x +
        ∑ j ∈ Finset.range (m + 1), xi (-(j : ℤ)) x - (m + 1 : ℝ) * tauSq M.P := by
  have hsplit : l + 1 = (m + 1) + (l - m) := by omega
  unfold finiteLocalPotential
  rw [min_eq_left hml, hsplit, Finset.sum_range_add]
  have htail : (∑ k ∈ Finset.range (l - m),
      (xi (((m + 1 + k : ℕ) : ℤ) - m) x - xi (((m + 1 + k : ℕ) : ℤ) - m) 0)) =
      infraredPartialSum xi (l - m) x := by
    simp only [infraredPartialSum, ContinuousMap.sum_apply, ContinuousMap.sub_apply,
      ContinuousMap.const_apply]
    apply Finset.sum_congr rfl
    intro k hk
    have hidx : (((m + 1 + k : ℕ) : ℤ) - m) = ((k + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hidx]
    rfl
  rw [htail]
  have hfine : (∑ k ∈ Finset.range (m + 1), xi ((k : ℤ) - m) x) =
      ∑ j ∈ Finset.range (m + 1), xi (-(j : ℤ)) x := by
    rw [← Finset.sum_range_reflect (fun k => xi ((k : ℤ) - m) x) (m + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    have hjm : j ≤ m := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    congr 1
    simp only [Nat.add_sub_cancel, Nat.cast_sub hjm]
    ring
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hfine]
  have hidx0 (k : ℕ) : xi ((k : ℤ) - m) 0 = xi (-(m : ℤ) + k) 0 := by
    congr 1
    ring
  simp_rw [hidx0]
  push_cast
  ring

/-- For `m>l`, the correct density is a further dilation of the active `l` density. -/
theorem localSpeed_further_dilation (M : GMCModel d) {l m : ℕ} (hlm : l ≤ m)
    (z : Vec d) (omega : AnchoredC11Sample d) (x : Vec d) :
    localSpeed M l m z omega x =
      localSpeed M l l z omega ((3 : ℝ) ^ (m - l) • x) := by
  rw [localSpeed, localSpeed, localFactor_eq_one M hlm, localFactor_eq_one M le_rfl]
  simp only [inv_one, one_mul, smul_smul, ← pow_add, Nat.add_sub_of_le hlm]

theorem rawClock_further_dilation (M : GMCModel d) {l m : ℕ} (hlm : l ≤ m) :
    (rawClock M l m : ℝ) = (3 : ℝ) ^ (2 * (m - l)) * (rawClock M l l : ℝ) := by
  change (3 : ℝ) ^ (2 * m) / ahom M (min m l) =
    (3 : ℝ) ^ (2 * (m - l)) * ((3 : ℝ) ^ (2 * l) / ahom M (min l l))
  rw [min_eq_right hlm, min_self]
  rw [← mul_div_assoc, ← pow_add]
  congr 2
  omega

end SubdiffusiveProcess.Section10.PhysicalLocalTransport
