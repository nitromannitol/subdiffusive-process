module

public import SubdiffusiveProcess.DirichletForm.FOTCoreMeasureQuadratic
public import SubdiffusiveProcess.DirichletForm.FOTCoreMeasureSupport
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}


theorem core_energy_nonneg (F : _root_.DirichletForm m) {U : Set X} (h : Data F U)
    {u φ uφ u2 : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u)
    (hφ : F.toClosedForm.MemCoreOn U φ) (hφ0 : 0 ≤ᵐ[m] φ)
    (huφ : uφ ∈ F.domain) (hu2 : u2 ∈ F.domain)
    (hprod : ⇑uφ =ᵐ[m] fun x => u x * φ x) (hsq : ⇑u2 =ᵐ[m] fun x => u x ^ 2) :
    0 ≤ F.form u uφ - (1 / 2 : ℝ) * F.form u2 φ := by
  exact core_functional_nonneg F h hu hφ hφ0 huφ hu2 hprod hsq

theorem core_energy_bound (F : _root_.DirichletForm m) {U : Set X} (h : Data F U)
    {u φ uφ u2 : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u)
    (hφ : F.toClosedForm.MemCoreOn U φ) {M : ℝ} (hM : 0 ≤ M)
    (hφM : ∀ᵐ x ∂m, |φ x| ≤ M) (huφ : uφ ∈ F.domain) (hu2 : u2 ∈ F.domain)
    (hprod : ⇑uφ =ᵐ[m] fun x => u x * φ x) (hsq : ⇑u2 =ᵐ[m] fun x => u x ^ 2) :
    |F.form u uφ - (1 / 2 : ℝ) * F.form u2 φ| ≤ M * F.form u u := by
  exact core_functional_bound F h hu hφ hM hφM huφ hu2 hprod hsq
theorem exists_coreMeasure [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
    (F : _root_.DirichletForm m) {U : Set X} (h : Data F U) :
    Nonempty (CoreMeasure F U) := by
  classical
  let a : ∀ u : Lp ℝ 2 m, F.toClosedForm.MemCoreOn U u → CoreRiesz.Input F U u :=
    fun u hu => Classical.choice (CoreRiesz.input_exists hu)
  let χ : ∀ (u : Lp ℝ 2 m) (hu : F.toClosedForm.MemCoreOn U u), CoreRiesz.Cutoff (a u hu) :=
    fun u hu => Classical.choice (CoreRiesz.cutoff_exists h (a u hu))
  refine ⟨{
    measure := fun u => if hu : F.toClosedForm.MemCoreOn U u then
      CoreRiesz.measure h (a u hu) (χ u hu) else 0
    finite := ?_
    mass := ?_
    carried := ?_
    regular := ?_
    defining := ?_ }⟩
  · intro u hu
    rw [dif_pos hu, CoreRiesz.measure_mass]
    exact ENNReal.ofReal_lt_top
  · intro u hu
    rw [dif_pos hu, CoreRiesz.measure_mass, ENNReal.toReal_ofReal (F.form_nonneg u hu.1)]
  · intro u hu
    rw [dif_pos hu]
    exact CoreRiesz.measure_carried h (a u hu) (χ u hu)
  · intro u hu
    rw [dif_pos hu]
    infer_instance
  · intro u φ hu hφ uc φc huc hφc huae hφae uφ u2 huφ hu2 hprod hsq
    rw [dif_pos hu]
    exact CoreRiesz.measure_defining h (a u hu) (χ u hu) hφ uc φc huc hφc
      huae hφae uφ u2 huφ hu2 hprod hsq


theorem CoreMeasure.parallelogram [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
    {F : _root_.DirichletForm m} {U : Set X} (h : Data F U) (Γ : CoreMeasure F U)
    {u v : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u)
    (hv : F.toClosedForm.MemCoreOn U v) {B : Set X} (hB : MeasurableSet B) :
    (Γ.measure (u + v) B).toReal + (Γ.measure (u - v) B).toReal =
      2 * (Γ.measure u B).toReal + 2 * (Γ.measure v B).toReal := by
  exact Γ.quadratic_parallelogram h ⟨u, hu⟩ ⟨v, hv⟩ B

theorem CoreMeasure.difference_bound [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
    {F : _root_.DirichletForm m} {U : Set X} (h : Data F U) (Γ : CoreMeasure F U)
    {u v : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u)
    (hv : F.toClosedForm.MemCoreOn U v) {B : Set X} (hB : MeasurableSet B) :
    |(Γ.measure u B).toReal - (Γ.measure v B).toReal| ≤
      Real.sqrt (F.form (u - v) (u - v)) *
        (Real.sqrt (F.form u u) + Real.sqrt (F.form v v)) := by
  exact Γ.quadratic_difference_bound h ⟨u, hu⟩ ⟨v, hv⟩ B

end DirichletForm.FOTConstruction
