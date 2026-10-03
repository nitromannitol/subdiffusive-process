module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section

/-!
# Unit-scale input data for the theta measurability preflight

At `d = D = 2`, `C0 = L = 1`, `A = 2`, and `rho = b = 1`, every
multiplier satisfies the mass, derivative, and averaged-estimate premises of
the frozen interior estimate. The last premise has an impossible scale guard.
The chosen grid can therefore be the existing, nonvacuous covering grid.
-/

set_option autoImplicit false
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

theorem unit_scale_threshold_impossible {C0 A r : ℝ} (hC0 : 1 ≤ C0)
    (hA : 2 ≤ A) (hr : 1 ≤ r) (hr1 : r ≤ 1) :
    ¬ C0 * (1 + Real.log A + Real.log (1 / r)) < (⌊Real.logb 3 r⌋ : ℝ) := by
  have heq : r = 1 := le_antisymm hr1 hr
  subst r
  have hlog : 0 ≤ Real.log A := Real.log_nonneg (by linarith)
  have hnonneg : 0 ≤ C0 * (1 + Real.log A) :=
    mul_nonneg (by linarith) (by linarith)
  simpa only [div_one, Real.log_one, Real.logb_one, Int.floor_zero, Int.cast_zero,
    add_zero] using not_lt_of_ge hnonneg

theorem coefficientOn_one {d : ℕ} (W : Set (Vec d)) :
    CoefficientOn W (fun _ => (1 : ℝ)) := by
  refine ⟨aestronglyMeasurable_const, 1, 1, by norm_num, ?_⟩
  exact Filter.Eventually.of_forall fun _ => ⟨le_rfl, le_rfl⟩

theorem weightedMeasure_one {d : ℕ} :
    weightedMeasure (d := d) (fun _ => (1 : ℝ)) = volume := by
  simpa only [weightedMeasure, ENNReal.ofReal_one] using!
    (withDensity_one (μ := (volume : Measure (Vec d))))

theorem volume_centered_square (y : Vec 2) {r : ℝ} (hr : 0 ≤ r) :
    volume (centeredAxisCube y r) = ENNReal.ofReal (r ^ 2) := by
  have htop : volume (centeredAxisCube y r) ≠ ⊤ := volume_axisCube_ne_top _ _
  rw [← ENNReal.ofReal_toReal htop, SubdiffusiveProcess.Section9.volume_centeredAxisCube_toReal y hr]

theorem unit_mass_bound (y : Vec 2) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal ((2 : ℝ) ^ (-(1 : ℝ)) * (r / 1) ^ (2 : ℝ)) *
      weightedMeasure (fun _ : Vec 2 => (1 : ℝ)) (centeredAxisCube 0 1) ≤
      weightedMeasure (fun _ : Vec 2 => (1 : ℝ)) (centeredAxisCube y r) := by
  rw [weightedMeasure_one, volume_centered_square 0 (by norm_num),
    volume_centered_square y hr.le]
  norm_num only [one_pow, ENNReal.ofReal_one, mul_one, div_one,
    Real.rpow_neg_one, Real.rpow_two]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [sq_nonneg r]

theorem unit_derivative_bound (y : Vec 2) :
    supNormOn (centeredAxisCube y 2)
        (fun x => euclideanNorm (euclideanGradient
          (fun _ : Vec 2 => Real.log (1 : ℝ)) x)) ^ 2 ≤
      (1 : ℝ) * (Real.log 2 + Real.log (2 + 1)) := by
  have hy : y ∈ centeredAxisCube y 2 := by
    intro i _
    change y i - 2 / 2 < y i ∧ y i < y i - 2 / 2 + 2
    constructor <;> linarith
  have hg (x : Vec 2) : euclideanGradient (fun _ : Vec 2 => Real.log (1 : ℝ)) x = 0 := by
    funext i
    simp [euclideanGradient, euclideanCoordDeriv]
  have hsup : supNormOn (centeredAxisCube y 2)
      (fun x => euclideanNorm (euclideanGradient
        (fun _ : Vec 2 => Real.log (1 : ℝ)) x)) = 0 := by
    simp only [hg, euclideanNorm_zero, supNormOn, abs_zero]
    have hs : {t : ℝ | ∃ x ∈ centeredAxisCube y 2, t = 0} = {0} := by
      ext t
      exact ⟨fun ⟨_, _, ht⟩ => ht, fun ht => ⟨y, hy, ht⟩⟩
    rw [hs, csSup_singleton]
  rw [hsup]
  have h2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have h3 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
  norm_num only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, one_mul]
  exact add_nonneg h2 h3

/-- The exact three quantitative premises, with the unit-scale data substituted. -/
theorem unit_quantitative_inputs (grid : Finset (Vec 2)) (theta : Vec 2 → ℝ) :
    (∀ (y : Vec 2) (r : ℝ), IsGridCube grid y r → 0 < r → r ≤ 1 →
      centeredAxisCube y (2 * r) ⊆ centeredAxisCube 0 1 →
      ENNReal.ofReal ((2 : ℝ) ^ (-(1 : ℝ)) * (r / 1) ^ (2 : ℝ)) *
          weightedMeasure (fun _ : Vec 2 => (1 : ℝ)) (centeredAxisCube 0 1) ≤
        weightedMeasure (fun _ : Vec 2 => (1 : ℝ)) (centeredAxisCube y r)) ∧
    (∀ y : Vec 2, (centeredAxisCube y 1 ∩ centeredAxisCube 0 1).Nonempty →
      supNormOn (centeredAxisCube y 2)
          (fun x => euclideanNorm (euclideanGradient
            (fun _ : Vec 2 => Real.log (1 : ℝ)) x)) ^ 2 ≤
        (1 : ℝ) * (Real.log 2 + Real.log (2 + 1))) ∧
    (∀ (y : Vec 2) (r : ℝ), IsGridCube grid y r → 1 ≤ r → r ≤ 1 →
      centeredAxisCube y (2 * r) ⊆ centeredAxisCube 0 1 →
      (1 : ℝ) * (1 + Real.log 2 + Real.log (1 / r)) < (⌊Real.logb 3 r⌋ : ℝ) →
      ∀ h : Vec 2 → ℝ,
        WeakHarmonic (fun x => (1 : ℝ) * theta x) (centeredAxisCube y r) h →
        (∃ K : ℝ, ∀ x ∈ centeredAxisCube y r, |h x| ≤ K) →
        ∀ (z : Vec 2) (varrho : ℝ), IsGridCube grid z varrho →
          1 ≤ varrho → varrho ≤ r / 1 →
          centeredAxisCube z varrho ⊆ centeredAxisCube y (r / 4) →
          normalizedL2On (centeredAxisCube z varrho)
              (fun x => h x - averageOn (centeredAxisCube z varrho) h) ≤
            (2 : ℝ) ^ (1 : ℝ) * (1 / r) ^ (1 : ℝ) * (varrho / r) ^ (1 / 2 : ℝ) *
              oscillationOn (centeredAxisCube y r) h) := by
  refine ⟨fun y r _ hr _ _ => unit_mass_bound y hr, fun y _ => unit_derivative_bound y, ?_⟩
  intro y r _ hr hr1 _ hguard
  exact (unit_scale_threshold_impossible (by norm_num) (by norm_num) hr hr1 hguard).elim

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
