module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerPointwise

@[expose] public section

/-!
# The diagonal lower bound from survival

Source: `s.fixed.coefficient` and `mfd:sec-speed`: the first sentence of the proof of the local
killed lower bound.

Integrating the killed density over the domain is the survival probability, so
Cauchy–Schwarz on the finite weighted measure of the domain turns a lower bound
on survival into the lower bound `p_{2t}(z,z) ≥ P_z[τ>t]²/μ(U)`; here the
Chapman–Kolmogorov inequality of `LocalKilledLowerPointwise` and the pointwise
symmetry replace the semigroup identity of the display.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower

variable {d : ℕ} {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} {U : Set (Vec d)}
  {p : ℝ → Vec d → Vec d → ℝ}

/-- Cauchy–Schwarz for a nonnegative function on a measure space. -/
theorem sq_lintegral_le {α : Type*} [MeasurableSpace α] (mu : Measure α) {f : α → ℝ≥0∞}
    (hf : Measurable f) : (∫⁻ y, f y ∂mu) ^ 2 ≤ (∫⁻ y, (f y) ^ 2 ∂mu) * mu univ := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hh : (∫⁻ y, f y ∂mu) ≤
      (∫⁻ y, (f y) ^ 2 ∂mu) ^ (1 / 2 : ℝ) * (mu univ) ^ (1 / 2 : ℝ) := by
    simpa only [Pi.mul_apply, mul_one, ENNReal.one_rpow, one_pow, lintegral_one,
      ENNReal.rpow_two] using
      ENNReal.lintegral_mul_le_Lp_mul_Lq mu hpq hf.aemeasurable
        (measurable_const.aemeasurable (f := fun _ : α => (1 : ENNReal)))
  have hsq : (∫⁻ y, f y ∂mu) ^ (2 : ℝ) ≤
      ((∫⁻ y, (f y) ^ 2 ∂mu) ^ (1 / 2 : ℝ) * (mu univ) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
    ENNReal.rpow_le_rpow hh (by norm_num)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.rpow_one] at hsq
  simpa only [ENNReal.rpow_two] using hsq

/-- The killed density integrates to the survival probability. -/
theorem lintegral_density_eq_survival (hU : IsOpen U) (hp : IsKilledDensity law rho U p)
    {t : ℝ} (ht : 0 < t) {z : Vec d} (hz : z ∈ U) :
    (∫⁻ y, ENNReal.ofReal (p t z y) ∂((weightedMeasure rho).restrict U))
      = law z {w | ENNReal.ofReal t < LifetimePath.exitTime U w} := by
  have h1 := killedKernel_apply_eq_density hU hp t ht z hz univ MeasurableSet.univ
  rw [Measure.restrict_univ] at h1
  rw [← h1, killed_apply law U hU (Real.toNNReal t) z univ MeasurableSet.univ]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_univ, true_and]
  exact Iff.rfl

/-- The mass of the domain is the extended real of its finite total mass. -/
theorem weightedMeasure_eq_ofReal (hfin : (weightedMeasure rho) U ≠ ∞) :
    (weightedMeasure rho) U = ENNReal.ofReal ((weightedMeasure rho) U).toReal :=
  (ENNReal.ofReal_toReal hfin).symm

/-- The survival lower bound gives the diagonal lower bound of the killed density. -/
theorem diagonal_lower (hD : LocalDiffusion c rho law) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U)
    (hp : IsKilledDensity law rho U p)
    (hpc : ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ U ×ˢ U))
    {c0 r : ℝ} (hc0 : 0 < c0) (hr : 0 < r) {z : Vec d} (hz : z ∈ U)
    (hsurv : ENNReal.ofReal c0 ≤ law z {w | ENNReal.ofReal r < LifetimePath.exitTime U w}) :
    c0 ^ 2 / ((weightedMeasure rho) U).toReal ≤ p (r + r) z z := by
  have hfin : (weightedMeasure rho) U ≠ ∞ :=
    KilledDensityExistence.weightedMeasure_ne_top_of_localDiffusion hD hU hUb
  set mu := (weightedMeasure rho).restrict U with hmu
  set M := ((weightedMeasure rho) U).toReal with hM
  have hmuniv : mu univ = (weightedMeasure rho) U := by
    rw [hmu, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  have hMpos : 0 < M := by
    rw [hM]
    refine ENNReal.toReal_pos ?_ hfin
    intro h0
    have hzero : mu = 0 := by rw [hmu]; exact Measure.restrict_eq_zero.mpr h0
    have hsurv0 : law z {w | ENNReal.ofReal r < LifetimePath.exitTime U w} = 0 := by
      rw [← lintegral_density_eq_survival hU hp hr hz, ← hmu, hzero, lintegral_zero_measure]
    rw [hsurv0, le_zero_iff, ENNReal.ofReal_eq_zero] at hsurv
    linarith
  -- Cauchy–Schwarz
  have hint : ENNReal.ofReal c0 ≤ ∫⁻ y, ENNReal.ofReal (p r z y) ∂mu := by
    rw [lintegral_density_eq_survival hU hp hr hz]
    exact hsurv
  have hcs : (ENNReal.ofReal c0) ^ 2 ≤ (∫⁻ y, (ENNReal.ofReal (p r z y)) ^ 2 ∂mu) * mu univ :=
    le_trans (pow_le_pow_left' hint 2) (sq_lintegral_le mu (measurable_density hp hr z))
  have hsq : (∫⁻ y, (ENNReal.ofReal (p r z y)) ^ 2 ∂mu)
      = ∫⁻ y, ENNReal.ofReal (p r z y) * ENNReal.ofReal (p r y z) ∂mu := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
    rw [sq, density_symm hD hU hUb hp hpc hr hz hy]
  have hchap : (∫⁻ y, ENNReal.ofReal (p r z y) * ENNReal.ofReal (p r y z) ∂mu)
      ≤ ENNReal.ofReal (p (r + r) z z) :=
    ofReal_density_lintegral_le hD hU hUb hp hpc hr hr hz hz
  have hkey : (ENNReal.ofReal c0) ^ 2 ≤ ENNReal.ofReal (p (r + r) z z) * ENNReal.ofReal M := by
    rw [hmuniv, weightedMeasure_eq_ofReal hfin, ← hM] at hcs
    exact le_trans hcs (mul_le_mul' (hsq ▸ hchap) le_rfl)
  have hpnn : 0 ≤ p (r + r) z z := hp.2.1 (r + r) (by linarith) z hz z hz
  have hreal : c0 ^ 2 ≤ p (r + r) z z * M := by
    have := hkey
    rw [← ENNReal.ofReal_pow hc0.le, ← ENNReal.ofReal_mul hpnn] at this
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp this
  rw [div_le_iff₀ hMpos]
  exact hreal

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
