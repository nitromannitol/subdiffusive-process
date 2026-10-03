module

public import SubdiffusiveProcess.FractionalEmbedding.CubeKernel
public import SubdiffusiveProcess.FractionalEmbedding.Distribution
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open MeasureTheory Set
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.FractionalEmbedding

/-- Contribution from pairs straddling two adjacent dyadic levels. -/
def pairLevelEnergy {d : ℕ} (μ : Measure (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) (t s : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ p : SpatialCoordinates d × SpatialCoordinates d,
    if 2 * levelScale t k < f p.1 ∧ f p.2 ≤ levelScale t k then
      ENNReal.ofReal ((levelScale t k) ^ 2) * fractionalKernel d s p.1 p.2 else 0 ∂μ.prod μ

theorem fractionalKernel_measurable (d : ℕ) (s : ℝ) :
    Measurable (fun p : SpatialCoordinates d × SpatialCoordinates d => fractionalKernel d s p.1 p.2) := by
  unfold fractionalKernel
  apply Measurable.div measurable_const
  apply Measurable.pow_const
  apply Measurable.ennreal_ofReal
  apply Measurable.sqrt
  exact Finset.measurable_sum Finset.univ fun j _ =>
    (((measurable_pi_apply j).comp measurable_fst).sub
      ((measurable_pi_apply j).comp measurable_snd)).pow_const 2

theorem scalarGagliardoEnergy_eq_prod {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f) :
    scalarGagliardoEnergy z r hr s f =
      ∫⁻ p : SpatialCoordinates d × SpatialCoordinates d,
        ENNReal.ofReal ((f p.1 - f p.2) ^ 2) * fractionalKernel d s p.1 p.2
          ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).prod
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  let μ : Measure (SpatialCoordinates d) :=
    volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
  let G : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((f p.1 - f p.2) ^ 2) * fractionalKernel d s p.1 p.2
  have hG : Measurable G :=
    (((hf.comp measurable_fst).sub (hf.comp measurable_snd)).pow_const 2).ennreal_ofReal.mul
      (fractionalKernel_measurable d s)
  have hprod := lintegral_prod G hG.aemeasurable (μ := μ) (ν := μ)
  change _ = ∫⁻ p, G p ∂μ.prod μ
  rw [hprod]
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro y
  dsimp only [G, fractionalKernel, scalarGagliardoEnergy]
  rw [mul_one_div]

/-- All dyadic separated-pair contributions fit under a single energy bound. -/
theorem pairLevelEnergy_sum_le {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f)
    {t : ℝ} (ht : 0 < t) (N : ℕ) :
    (∑ k ∈ Finset.range N,
      pairLevelEnergy (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) f t s k) ≤
        ENNReal.ofReal (4 / 3 : ℝ) * scalarGagliardoEnergy z r hr s f := by
  classical
  let μ : Measure (SpatialCoordinates d) :=
    volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
  let G : ℕ → SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun k p =>
    if 2 * levelScale t k < f p.1 ∧ f p.2 ≤ levelScale t k then
      ENNReal.ofReal ((levelScale t k) ^ 2) * fractionalKernel d s p.1 p.2 else 0
  have hG (k : ℕ) : Measurable (G k) :=
    Measurable.ite
      ((measurableSet_lt measurable_const (hf.comp measurable_fst)).inter
        (measurableSet_le (hf.comp measurable_snd) measurable_const))
      (measurable_const.mul (fractionalKernel_measurable d s)) measurable_const
  have hpoint (p : SpatialCoordinates d × SpatialCoordinates d) :
      (∑ k ∈ Finset.range N, G k p) ≤
        ENNReal.ofReal (4 / 3 : ℝ) *
          (ENNReal.ofReal ((f p.1 - f p.2) ^ 2) * fractionalKernel d s p.1 p.2) := by
    let W : ℕ → ℝ := fun k =>
      if 2 * levelScale t k < f p.1 ∧ f p.2 ≤ levelScale t k then (levelScale t k) ^ 2 else 0
    have hW (k : ℕ) : 0 ≤ W k := by dsimp only [W]; split_ifs <;> positivity
    have hsum : (∑ k ∈ Finset.range N, W k) ≤ (4 / 3 : ℝ) * (f p.1 - f p.2) ^ 2 := by
      have hfull := pair_level_sum t (f p.1) (f p.2) ht N
      have hprefix : (∑ k ∈ Finset.range N, W k) ≤ ∑ k ∈ Finset.range (N + 1), W k := by
        rw [Finset.sum_range_succ]
        exact le_add_of_nonneg_right (hW N)
      exact hprefix.trans hfull
    have hfactor : (∑ k ∈ Finset.range N, G k p) =
        ENNReal.ofReal (∑ k ∈ Finset.range N, W k) * fractionalKernel d s p.1 p.2 := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hW k), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [G, W]
      split_ifs <;> simp only [ENNReal.ofReal_zero, zero_mul]
    rw [hfactor]
    have hle := mul_le_mul_left (ENNReal.ofReal_le_ofReal hsum) (fractionalKernel d s p.1 p.2)
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4 / 3), mul_assoc] using! hle
  calc
    (∑ k ∈ Finset.range N, pairLevelEnergy μ f t s k) =
        ∫⁻ p, ∑ k ∈ Finset.range N, G k p ∂μ.prod μ := by
      exact (lintegral_finset_sum _ (fun k _ => hG k)).symm
    _ ≤ ∫⁻ p, ENNReal.ofReal (4 / 3 : ℝ) *
        (ENNReal.ofReal ((f p.1 - f p.2) ^ 2) * fractionalKernel d s p.1 p.2) ∂μ.prod μ :=
      lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← scalarGagliardoEnergy_eq_prod z r hr s f hf]

/-- The geometric complement estimate bounds a single distribution-function term. -/
theorem pairLevelEnergy_lower {d : ℕ} (hd : 0 < d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f)
    {t : ℝ} (ht : 0 < t)
    (hsmall : levelMass (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) f t 0 ≤
      (r / 2) ^ d / 2) (k : ℕ) :
    ENNReal.ofReal (cubeKernelLowerConstant d s * t ^ 2 * (4 : ℝ) ^ k *
      levelMass (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) f t (k + 1) *
      (levelMass (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) f t k) ^
        (-2 * (s : ℝ) / (d : ℝ))) ≤
      pairLevelEnergy (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) f t s k := by
  classical
  let Q : Set (SpatialCoordinates d) := centeredCube z r hr
  let μ : Measure (SpatialCoordinates d) := volume.restrict Q
  let A : Set (SpatialCoordinates d) := {x | levelScale t k < f x}
  let B : Set (SpatialCoordinates d) := {x | levelScale t (k + 1) < f x}
  let a : ℝ := levelMass μ f t k
  let b : ℝ := levelMass μ f t (k + 1)
  have ha0 : 0 ≤ a := levelMass_nonneg μ f t k
  have hb0 : 0 ≤ b := levelMass_nonneg μ f t (k + 1)
  have hba : b ≤ a := levelMass_step μ f ht k
  by_cases haz : a = 0
  · have hbz : b = 0 := le_antisymm (haz ▸ hba) hb0
    change ENNReal.ofReal (_ * b * a ^ _) ≤ _
    rw [hbz, mul_zero, zero_mul, ENNReal.ofReal_zero]
    exact bot_le
  have ha : 0 < a := lt_of_le_of_ne ha0 (Ne.symm haz)
  have hmono : ∀ l, levelMass μ f t l ≤ levelMass μ f t 0 := by
    intro l
    induction l with
    | zero => exact le_rfl
    | succ l ih => exact (levelMass_step μ f ht l).trans ih
  have haSmall : a ≤ (r / 2) ^ d / 2 := (hmono k).trans hsmall
  have hA : MeasurableSet A := measurableSet_lt measurable_const hf
  have hB : MeasurableSet B := measurableSet_lt measurable_const hf
  have hQ : MeasurableSet Q := (centeredCube z r hr).isOpen.measurableSet
  have hdReal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsPos : 0 < (s : ℝ) := s.2.1
  have hκ : 0 < cubeKernelLowerConstant d s := cubeKernelLowerConstant_pos hd s
  let C : ℝ≥0∞ := ENNReal.ofReal ((levelScale t k) ^ 2)
  let H : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun p => C * fractionalKernel d s p.1 p.2
  have hH : Measurable H := measurable_const.mul (fractionalKernel_measurable d s)
  have hP : pairLevelEnergy μ f t s k =
      C * ∫⁻ x in B, ∫⁻ y in Aᶜ, fractionalKernel d s x y ∂μ ∂μ := by
    unfold pairLevelEnergy
    have hfun : (fun p : SpatialCoordinates d × SpatialCoordinates d =>
        if 2 * levelScale t k < f p.1 ∧ f p.2 ≤ levelScale t k then
          ENNReal.ofReal ((levelScale t k) ^ 2) * fractionalKernel d s p.1 p.2 else 0) =
        (B ×ˢ Aᶜ).indicator H := by
      funext p
      simp only [B, A, H, C, Set.indicator, Set.mem_prod, Set.mem_setOf_eq,
        Set.mem_compl_iff, not_lt, levelScale_succ]
    rw [hfun, lintegral_indicator (hB.prod hA.compl), ← Measure.prod_restrict,
      lintegral_prod H hH.aemeasurable]
    dsimp only [H, C]
    simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hinner : ENNReal.ofReal (cubeKernelLowerConstant d s * a ^ (-2 * (s : ℝ) / (d : ℝ))) * μ B ≤
      ∫⁻ x in B, ∫⁻ y in Aᶜ, fractionalKernel d s x y ∂μ ∂μ := by
    rw [← Measure.restrict_apply_univ (μ := μ) (s := B), ← lintegral_const]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_of_ae (ae_restrict_mem hQ)] with x hx
    exact cube_complement_kernel_lower hd z r hr s (by positivity) A hA ha haSmall x hx
  have hbENN : ENNReal.ofReal b = μ B := ENNReal.ofReal_toReal (measure_ne_top μ B)
  have hfactor : ENNReal.ofReal (cubeKernelLowerConstant d s * t ^ 2 * (4 : ℝ) ^ k * b *
      a ^ (-2 * (s : ℝ) / (d : ℝ))) =
      C * (ENNReal.ofReal (cubeKernelLowerConstant d s * a ^ (-2 * (s : ℝ) / (d : ℝ))) * μ B) := by
    rw [← hbENN, ← ENNReal.ofReal_mul (mul_nonneg hκ.le (Real.rpow_nonneg ha.le _))]
    dsimp only [C]
    rw [← ENNReal.ofReal_mul (sq_nonneg (levelScale t k))]
    congr 1
    rw [levelScale_sq]
    ring
  change ENNReal.ofReal (cubeKernelLowerConstant d s * t ^ 2 * (4 : ℝ) ^ k * b * a ^ _) ≤ _
  rw [hfactor, hP]
  exact mul_le_mul_right hinner C

/-- Finite dyadic distribution sums are paid for by the original Gagliardo energy. -/
theorem dyadic_energy_bound {d : ℕ} (hd : 0 < d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f)
    (hfinite : scalarGagliardoEnergy z r hr s f < ⊤)
    {t : ℝ} (ht : 0 < t)
    (hsmall : levelMass (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) f t 0 ≤
      (r / 2) ^ d / 2) (N : ℕ) :
    t ^ 2 * (∑ k ∈ Finset.range N, (4 : ℝ) ^ k *
      levelMass (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) f t (k + 1) *
      (levelMass (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) f t k) ^
        (-2 * (s : ℝ) / (d : ℝ))) ≤
      (4 / (3 * cubeKernelLowerConstant d s)) * (scalarGagliardoEnergy z r hr s f).toReal := by
  classical
  let μ := volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
  let w : ℕ → ℝ := fun k => (4 : ℝ) ^ k * levelMass μ f t (k + 1) *
    (levelMass μ f t k) ^ (-2 * (s : ℝ) / (d : ℝ))
  have hw (k : ℕ) : 0 ≤ w k := by
    dsimp only [w]
    exact mul_nonneg (mul_nonneg (by positivity) (levelMass_nonneg μ f t _))
      (Real.rpow_nonneg (levelMass_nonneg μ f t _) _)
  have hκ := cubeKernelLowerConstant_pos hd (s : ℝ)
  have hsum : ENNReal.ofReal (cubeKernelLowerConstant d s * t ^ 2 *
      ∑ k ∈ Finset.range N, w k) ≤
      ∑ k ∈ Finset.range N, pairLevelEnergy μ f t s k := by
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg
      (fun k _ => mul_nonneg (mul_nonneg hκ.le (sq_nonneg t)) (hw k))]
    apply Finset.sum_le_sum
    intro k _
    simpa only [w, mul_assoc] using! pairLevelEnergy_lower hd z r hr s f hf ht hsmall k
  have hle := hsum.trans (pairLevelEnergy_sum_le z r hr s f hf ht N)
  have hright : ENNReal.ofReal (4 / 3 : ℝ) * scalarGagliardoEnergy z r hr s f ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinite).ne
  have hre := ENNReal.toReal_mono hright hle
  rw [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hκ.le (sq_nonneg t))
      (Finset.sum_nonneg fun k _ => hw k)), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4 / 3)] at hre
  change t ^ 2 * (∑ k ∈ Finset.range N, w k) ≤ _
  calc
    _ ≤ ((4 / 3 : ℝ) * (scalarGagliardoEnergy z r hr s f).toReal) /
        cubeKernelLowerConstant d s := by
      apply (le_div_iff₀ hκ).mpr
      nlinarith only [hre]
    _ = _ := by ring

end SubdiffusiveProcess.FractionalEmbedding
