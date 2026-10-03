module

public import SubdiffusiveProcess.DirichletForm.FOTCoreMeasureProducts
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal CompactlySupported BoundedContinuousFunction

noncomputable section

namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
variable [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
variable {F : _root_.DirichletForm m} {U : Set X}

namespace CoreMeasure

variable (Γ : CoreMeasure F U)

theorem measure_lt_top {u : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u) (B : Set X) :
    Γ.measure u B < ⊤ := (measure_mono (subset_univ B)).trans_lt (Γ.finite u hu)

/-- A finite positive combination of core measures. -/
def measureSum {ι : Type*} (s : Finset ι) (v : ι → coreDomain F U) (c : ι → ℝ≥0) : Measure X :=
  ∑ i ∈ s, c i • Γ.measure (v i).1

theorem measureSum_finite {ι : Type*} (s : Finset ι) (v : ι → coreDomain F U) (c : ι → ℝ≥0) :
    IsFiniteMeasure (Γ.measureSum s v c) := by
  classical
  haveI (i : ι) : IsFiniteMeasure (Γ.measure (v i).1) := ⟨Γ.finite _ (v i).property⟩
  unfold measureSum
  infer_instance

theorem measureSum_regular {ι : Type*} (s : Finset ι) (v : ι → coreDomain F U) (c : ι → ℝ≥0) :
    (Γ.measureSum s v c).Regular := by
  classical
  haveI (i : ι) : IsFiniteMeasure (Γ.measure (v i).1) := ⟨Γ.finite _ (v i).property⟩
  haveI (i : ι) : (Γ.measure (v i).1).Regular := Γ.regular _ (v i).property
  induction s using Finset.induction_on with
  | empty => simp only [measureSum, Finset.sum_empty]; infer_instance
  | @insert i s hi ih =>
    haveI := ih
    haveI := Γ.measureSum_finite s v c
    rw [measureSum, Finset.sum_insert hi]
    exact CoreRiesz.regular_add _ _

theorem measureSum_carried {ι : Type*} (s : Finset ι) (v : ι → coreDomain F U) (c : ι → ℝ≥0) :
    Γ.measureSum s v c Uᶜ = 0 := by
  simp [measureSum, Measure.finset_sum_apply, Measure.smul_apply,
    fun i => Γ.carried (v i).1 (v i).property]

theorem integral_measureSum {ι : Type*} (s : Finset ι) (v : ι → coreDomain F U) (c : ι → ℝ≥0)
    (φ : CoreRiesz.tests F U) :
    (∫ x, φ.1 x ∂Γ.measureSum s v c) = ∑ i ∈ s, (c i : ℝ) * coreBilinear φ (v i) (v i) := by
  classical
  haveI (i : ι) : IsFiniteMeasure (Γ.measure (v i).1) := ⟨Γ.finite _ (v i).property⟩
  unfold measureSum
  have hfi : ∀ i ∈ s, Integrable (fun x => φ.1 x) (c i • Γ.measure (v i).1) :=
    fun i _ => (CoreRiesz.testCompact φ).integrable
  rw [integral_finset_sum_measure hfi]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_smul_nnreal_measure, Γ.integral_test]
  rfl

theorem toReal_measureSum {ι : Type*} (s : Finset ι) (v : ι → coreDomain F U) (c : ι → ℝ≥0)
    (B : Set X) :
    (Γ.measureSum s v c B).toReal = ∑ i ∈ s, (c i : ℝ) * (Γ.measure (v i).1 B).toReal := by
  classical
  rw [measureSum, Measure.finset_sum_apply, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    simp [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  · intro i hi
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (Γ.measure_lt_top (v i).property B).ne

/-- Any quadratic identity of the defining functionals is an identity of core measures. -/
theorem measureSum_eq {ι κ : Type*} (h : Data F U) (s : Finset ι) (t : Finset κ)
    (v : ι → coreDomain F U) (w : κ → coreDomain F U) (c : ι → ℝ≥0) (d : κ → ℝ≥0)
    (he : ∀ φ : CoreRiesz.tests F U,
      (∑ i ∈ s, (c i : ℝ) * coreBilinear φ (v i) (v i)) =
        ∑ i ∈ t, (d i : ℝ) * coreBilinear φ (w i) (w i)) :
    Γ.measureSum s v c = Γ.measureSum t w d := by
  haveI := Γ.measureSum_finite s v c
  haveI := Γ.measureSum_finite t w d
  haveI := Γ.measureSum_regular s v c
  haveI := Γ.measureSum_regular t w d
  apply CoreRiesz.measure_eq_of_core_tests h _ _ (Γ.measureSum_carried s v c)
    (Γ.measureSum_carried t w d)
  intro φ
  rw [Γ.integral_measureSum, Γ.integral_measureSum, he]

theorem quadratic_parallelogram (h : Data F U) (u v : coreDomain F U) (B : Set X) :
    (Γ.measure (u.1 + v.1) B).toReal + (Γ.measure (u.1 - v.1) B).toReal =
      2 * (Γ.measure u.1 B).toReal + 2 * (Γ.measure v.1 B).toReal := by
  let us : Fin 2 → coreDomain F U := ![u + v, u - v]
  let vs : Fin 2 → coreDomain F U := ![u, v]
  have he := Γ.measureSum_eq h Finset.univ Finset.univ us vs (fun _ => 1) (fun _ => 2) (by
    intro φ
    simp only [Fin.sum_univ_two, us, vs, Matrix.cons_val_zero, Matrix.cons_val_one,
      NNReal.coe_one, NNReal.coe_ofNat, one_mul]
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    ring)
  have hB := congrArg (fun μ : Measure X => (μ B).toReal) he
  rw [Γ.toReal_measureSum, Γ.toReal_measureSum] at hB
  simpa [Fin.sum_univ_two, us, vs] using hB

theorem quadratic_smul (h : Data F U) (c : ℝ) (u : coreDomain F U) (B : Set X) :
    (Γ.measure (c • u.1) B).toReal = c ^ 2 * (Γ.measure u.1 B).toReal := by
  let cs : ℝ≥0 := ⟨c ^ 2, sq_nonneg c⟩
  have he := Γ.measureSum_eq h (Finset.univ : Finset (Fin 1)) (Finset.univ : Finset (Fin 1))
    (fun _ => c • u) (fun _ => u) (fun _ => 1) (fun _ => cs) (by
      intro φ
      simp only [Fin.sum_univ_one, NNReal.coe_one, one_mul, map_smul,
        LinearMap.smul_apply, smul_eq_mul]
      change c * (c * coreBilinear φ u u) = c ^ 2 * coreBilinear φ u u
      ring)
  have hB := congrArg (fun μ : Measure X => (μ B).toReal) he
  rw [Γ.toReal_measureSum, Γ.toReal_measureSum] at hB
  simpa [Fin.sum_univ_one, cs, NNReal.coe_mk] using! hB

theorem quadratic_three (h : Data F U) (u v w : coreDomain F U) (B : Set X) :
    (Γ.measure (u.1 + v.1 + w.1) B).toReal + (Γ.measure u.1 B).toReal +
      (Γ.measure v.1 B).toReal + (Γ.measure w.1 B).toReal =
        (Γ.measure (u.1 + v.1) B).toReal + (Γ.measure (u.1 + w.1) B).toReal +
          (Γ.measure (v.1 + w.1) B).toReal := by
  let us : Fin 4 → coreDomain F U := ![u + v + w, u, v, w]
  let vs : Fin 3 → coreDomain F U := ![u + v, u + w, v + w]
  have he := Γ.measureSum_eq h Finset.univ Finset.univ us vs (fun _ => 1) (fun _ => 1) (by
    intro φ
    simp [Fin.sum_univ_succ, us, vs, map_add, LinearMap.add_apply]
    ring)
  have hB := congrArg (fun μ : Measure X => (μ B).toReal) he
  rw [Γ.toReal_measureSum, Γ.toReal_measureSum] at hB
  simpa [Fin.sum_univ_succ, us, vs, add_assoc] using hB

end CoreMeasure
end DirichletForm.FOTConstruction
