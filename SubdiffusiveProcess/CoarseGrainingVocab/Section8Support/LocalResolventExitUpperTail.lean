module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpperDecay

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpper

variable {d : ℕ} {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}

/-- The killed kernel of the whole space is the survival probability. -/
theorem killedKernel_univ_eq_survival {U : Set (Vec d)} (hU : IsOpen U) (t : ℝ) (x : Vec d) :
    killedKernel law U hU (Real.toNNReal t) x Set.univ
      = law x {w | ENNReal.ofReal t < LifetimePath.exitTime U w} := by
  rw [killed_apply law U hU _ x Set.univ MeasurableSet.univ]
  congr 1
  ext w
  simp [coe_real_toNNReal_eq_ofReal t]

/-- The killed kernel row is the density measure of the local weighted measure. -/
theorem killedKernel_eq_withDensity {U : Set (Vec d)} (hU : IsOpen U)
    {p : ℝ → Vec d → Vec d → ℝ} (hp : IsKilledDensity law rho U p)
    {t : ℝ} (ht : 0 < t) {x : Vec d} (hx : x ∈ U) :
    killedKernel law U hU (Real.toNNReal t) x
      = ((weightedMeasure rho).restrict U).withDensity (fun y => ENNReal.ofReal (p t x y)) := by
  refine Measure.ext fun B hB => ?_
  rw [killedKernel_apply_eq_density hU hp t ht x hx B hB, withDensity_apply _ hB]

/-- The survival probability at a split time, bounded by the density times the survival mass. -/
theorem survival_le_density_mul_mass
    (hSM : StrongMarkov law) {U : Set (Vec d)} (hU : IsOpen U)
    {p : ℝ → Vec d → Vec d → ℝ} (hp : IsKilledDensity law rho U p)
    {t1 t2 : ℝ} (ht1 : 0 < t1) (ht2 : 0 < t2) {x : Vec d} (hx : x ∈ U)
    {D : ℝ} (hD : ∀ y ∈ U, p t1 x y ≤ D) :
    law x {w | ENNReal.ofReal (t1 + t2) < LifetimePath.exitTime U w} ≤
      ENNReal.ofReal D *
        ∫⁻ y, law y {w | ENNReal.ofReal t2 < LifetimePath.exitTime U w}
          ∂((weightedMeasure rho).restrict U) := by
  set mu := (weightedMeasure rho).restrict U with hmudef
  set K : Vec d → ℝ≥0∞ :=
    fun y => killedKernel law U hU (Real.toNNReal t2) y Set.univ with hKdef
  have hKmeas : Measurable K :=
    (killedKernel law U hU (Real.toNNReal t2)).measurable_coe MeasurableSet.univ
  have hpmeas : Measurable (fun y => ENNReal.ofReal (p t1 x y)) :=
    ((hp.1 t1 ht1).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hsplit : Real.toNNReal (t1 + t2) = Real.toNNReal t1 + Real.toNNReal t2 :=
    Real.toNNReal_add ht1.le ht2.le
  have hsemi : killedKernel law U hU (Real.toNNReal (t1 + t2)) x Set.univ
      = ∫⁻ y, K y ∂(killedKernel law U hU (Real.toNNReal t1) x) := by
    rw [hsplit, semigroup law hSM U hU (Real.toNNReal t1) (Real.toNNReal t2),
      Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  have hdens : (∫⁻ y, K y ∂(killedKernel law U hU (Real.toNNReal t1) x))
      = ∫⁻ y, ENNReal.ofReal (p t1 x y) * K y ∂mu := by
    rw [killedKernel_eq_withDensity hU hp ht1 hx,
      lintegral_withDensity_eq_lintegral_mul _ hpmeas hKmeas]
    rfl
  have hbound : (∫⁻ y, ENNReal.ofReal (p t1 x y) * K y ∂mu) ≤ ENNReal.ofReal D * ∫⁻ y, K y ∂mu := by
    rw [← lintegral_const_mul _ hKmeas]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hD y hy)) le_rfl
  have hKsurv : ∀ y, K y = law y {w | ENNReal.ofReal t2 < LifetimePath.exitTime U w} :=
    fun y => killedKernel_univ_eq_survival hU t2 y
  calc law x {w | ENNReal.ofReal (t1 + t2) < LifetimePath.exitTime U w}
      = killedKernel law U hU (Real.toNNReal (t1 + t2)) x Set.univ :=
        (killedKernel_univ_eq_survival hU (t1 + t2) x).symm
    _ = ∫⁻ y, ENNReal.ofReal (p t1 x y) * K y ∂mu := hsemi.trans hdens
    _ ≤ ENNReal.ofReal D * ∫⁻ y, K y ∂mu := hbound
    _ = ENNReal.ofReal D *
          ∫⁻ y, law y {w | ENNReal.ofReal t2 < LifetimePath.exitTime U w} ∂mu := by
        exact congrArg _ (lintegral_congr hKsurv)

/-- The survival mass decays geometrically along multiples of the resolvent scale. -/
theorem lintegral_survival_le
    (hDiff : LocalDiffusion c rho law) [IsMarkovKernel law]
    {U : Set (Vec d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hmtop : (weightedMeasure rho) U ≠ ∞)
    {A F s : ℝ} (hA : 0 < A) (hF : 0 < F) (hs : 0 < s)
    (hPoin : PoincareAssumption c rho U A F) (n : ℕ) :
    (∫⁻ y, law y {w | ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * s) < LifetimePath.exitTime U w}
        ∂((weightedMeasure rho).restrict U)) ≤
      ((2 : ℝ≥0∞) * ENNReal.ofReal ((1 + s / (A * F))⁻¹)) ^ (n + 1) *
        ENNReal.ofReal (((weightedMeasure rho) U).toReal) := by
  have hmuniv : ((weightedMeasure rho).restrict U) Set.univ = (weightedMeasure rho) U :=
    Measure.restrict_apply_univ _
  have htoNN : Real.toNNReal (((n + 1 : ℕ) : ℝ) * s)
      = ((n + 1 : ℕ) : NNReal) * Real.toNNReal s := by
    rw [Real.toNNReal_mul (by positivity)]
    congr 1
    simp
  have hconv : ∀ y : Vec d,
      law y {w | ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * s) < LifetimePath.exitTime U w}
        = killedKernel law U hU (((n + 1 : ℕ) : NNReal) * Real.toNNReal s) y Set.univ := by
    intro y
    rw [← htoNN, killedKernel_univ_eq_survival hU]
  calc (∫⁻ y, law y {w | ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * s) < LifetimePath.exitTime U w}
        ∂((weightedMeasure rho).restrict U))
      = ∫⁻ y, killedKernel law U hU (((n + 1 : ℕ) : NNReal) * Real.toNNReal s) y Set.univ
          ∂((weightedMeasure rho).restrict U) := lintegral_congr hconv
    _ ≤ ((2 : ℝ≥0∞) * ENNReal.ofReal ((1 + s / (A * F))⁻¹)) ^ (n + 1) *
          ((weightedMeasure rho).restrict U) Set.univ :=
        lintegral_killedKernel_univ_le hDiff hU hUb hmtop hA hF hs hPoin n
    _ = ((2 : ℝ≥0∞) * ENNReal.ofReal ((1 + s / (A * F))⁻¹)) ^ (n + 1) *
          ENNReal.ofReal (((weightedMeasure rho) U).toReal) := by
        rw [hmuniv, ENNReal.ofReal_toReal hmtop]

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpper
