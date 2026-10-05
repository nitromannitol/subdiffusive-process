module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserPowerSobolev
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserIterationConstants
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserLpEndpoint
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedInteriorFromAveragesReduction
public import Mathlib.Topology.Order.OrderClosed

@[expose] public section

/-!
# Local boundedness at ellipticity ratio four

Moser iteration on centered axis cubes, using `chi = d/(d-1)`. The
subcritical Sobolev exponent `2d/(d-1)` covers every dimension `d ≥ 2`.
The final theorem has exactly the source's `LocalBoundednessAtRatioFour` type.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Filter Set
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators Topology
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Restriction of the exact local weak-harmonicity predicate. -/
theorem moser_weakHarmonic_mono {d : ℕ} {a h : Vec d → ℝ} {U V : Set (Vec d)}
    (hh : WeakHarmonic a U h) (hsub : V ⊆ U) : WeakHarmonic a V h :=
  ⟨hh.1.mono hsub, fun W hW hc hs => hh.2 W hW hc (hs.trans hsub)⟩

/-- Negation preserves the exact local weak-harmonicity predicate. -/
theorem moser_weakHarmonic_neg {d : ℕ} {a h : Vec d → ℝ} {U : Set (Vec d)}
    (hh : WeakHarmonic a U h) : WeakHarmonic a U (fun x => -h x) := by
  refine ⟨hh.1.neg, ?_⟩
  intro W hW hc hs
  obtain ⟨u, hueq, hu⟩ := hh.2 W hW hc hs
  refine ⟨-u, ?_, ?_⟩
  · filter_upwards [hueq] with x hx
    simp only [H1Function.neg_toFun]
    exact congrArg Neg.neg hx
  · intro phi
    simp only [H1Function.neg_grad, vecDot_neg_left, mul_neg, integral_neg, hu phi, neg_zero]

/-- The nested cube side lengths decrease from one half to one quarter. -/
def moserIterationRadius (n : ℕ) : ℝ := 1 / 4 + 1 / (4 * 2 ^ n)

theorem moserIterationRadius_bounds (n : ℕ) :
    (1 / 4 : ℝ) < moserIterationRadius n ∧ moserIterationRadius n ≤ 1 / 2 := by
  have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  constructor
  · exact lt_add_of_pos_right _ (by positivity)
  · have hi : 1 / (4 * (2 : ℝ) ^ n) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    dsimp only [moserIterationRadius]
    linarith

theorem moserIterationRadius_gap (n : ℕ) :
    moserIterationRadius n - moserIterationRadius (n + 1) = 1 / (8 * (2 : ℝ) ^ n) := by
  dsimp only [moserIterationRadius]
  rw [pow_succ]
  field_simp
  ring

/-- The positive-part endpoint, with the dimensional constant chosen before all inputs. -/
theorem exists_moser_positive_local_bound {d : ℕ} (hd : 2 ≤ d) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (a : Vec d → ℝ) (z : Vec d),
        (∀ x, 1 / 2 ≤ a x ∧ a x ≤ 2) →
        AEStronglyMeasurable a (volume.restrict (centeredAxisCube z 1)) →
        ∀ h : Vec d → ℝ, WeakHarmonic a (centeredAxisCube z 1) h →
        ∀ x ∈ centeredAxisCube z (1 / 4),
          ENNReal.ofReal (max (h x) 0) ≤
            ENNReal.ofReal B * eLpNorm h 2 (volume.restrict (centeredAxisCube z 1)) := by
  let chi : ℝ := (d : ℝ) / ((d : ℝ) - 1)
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) - 1 := by linarith
  have hchi : 1 < chi := by
    rw [show chi = (d : ℝ) / ((d : ℝ) - 1) from rfl, one_lt_div hden]
    linarith
  have hchi0 : 0 < chi := by linarith
  obtain ⟨C, hC, hstep⟩ := exists_weakHarmonic_moser_power_sobolev_step hd
  obtain ⟨B, hB, hiter⟩ := exists_moser_iteration_constant hchi hC
  refine ⟨B, hB, ?_⟩
  intro a z hab ha h hh x hx
  let g : Vec d → ℝ := fun y => max (h y) 0
  let N : ℕ → ℝ≥0∞ := fun n => eLpNorm g (ENNReal.ofReal (2 * chi ^ n))
    (volume.restrict (centeredAxisCube z (moserIterationRadius n)))
  have hg0 (y : Vec d) : 0 ≤ g y := le_max_right _ _
  have hcubeMeas (r : ℝ) : MeasurableSet (centeredAxisCube z r) := by
    simpa only [SubdiffusiveProcess.Section9.centeredAxisCube] using!
      (isOpen_axisCube (fun i => z i - r / 2) r).measurableSet
  have hrec (n : ℕ) : N (n + 1) ^ (chi ^ n) ≤
      ENNReal.ofReal (8 * C * (2 * chi) ^ n) * N n ^ (chi ^ n) := by
    have hgap0 : 0 < moserIterationRadius n - moserIterationRadius (n + 1) := by
      rw [moserIterationRadius_gap]
      positivity
    have hrR := sub_pos.mp hgap0
    have hR1 : moserIterationRadius n ≤ 1 := (moserIterationRadius_bounds n).2.trans (by norm_num)
    have hsub := centeredAxisCube_mono (x := z) hR1
    have hs1 : 1 ≤ chi ^ n := one_le_pow₀ hchi.le
    have hImprove := hstep a z (moserIterationRadius (n + 1)) (moserIterationRadius n)
      (lt_trans (by norm_num) (moserIterationRadius_bounds (n + 1)).1) hrR hR1
      (ha.mono_measure (Measure.restrict_mono hsub le_rfl)) hab h
      (moser_weakHarmonic_mono hh hsub) (chi ^ n) hs1
    have hnormpow (p : ℝ≥0∞) (V : Set (Vec d)) (hVm : MeasurableSet V)
        (hVsub : V ⊆ centeredAxisCube z 1) :
        eLpNorm (fun y => (max (h y) 0) ^ (chi ^ n)) p (volume.restrict V) =
          eLpNorm g (p * ENNReal.ofReal (chi ^ n)) (volume.restrict V) ^ (chi ^ n) := by
      have hgc : ContinuousOn g V :=
        continuous_max.comp_continuousOn ((hh.1.mono hVsub).prodMk continuousOn_const)
      have hgm := hgc.aestronglyMeasurable (μ := volume) hVm
      convert eLpNorm_norm_rpow (μ := volume.restrict V) (p := p) g hgm
        (pow_pos hchi0 n) using 2
      ext y
      exact congrArg (fun t : ℝ => t ^ (chi ^ n)) (Real.norm_of_nonneg (hg0 y)).symm
    rw [hnormpow _ _ (hcubeMeas _)
      (centeredAxisCube_mono (hrR.le.trans hR1)),
      hnormpow _ _ (hcubeMeas _) hsub] at hImprove
    have hexp : moserSobolevExponent d * ENNReal.ofReal (chi ^ n) =
        ENNReal.ofReal (2 * chi ^ (n + 1)) := by
      rw [moserSobolevExponent, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * (d : ℝ) / ((d : ℝ) - 1))]
      congr 1
      dsimp only [chi]
      rw [pow_succ]
      ring
    have hexp2 : (2 : ℝ≥0∞) * ENNReal.ofReal (chi ^ n) = ENNReal.ofReal (2 * chi ^ n) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hcoef : C * chi ^ n / (moserIterationRadius n - moserIterationRadius (n + 1)) =
        8 * C * (2 * chi) ^ n := by
      rw [moserIterationRadius_gap, one_div, div_inv_eq_mul, mul_pow]
      ring
    rw [hexp, hexp2, hcoef] at hImprove
    exact hImprove
  have hN := hiter N hrec
  have hN0 : N 0 ≤ eLpNorm h 2 (volume.restrict (centeredAxisCube z 1)) := by
    dsimp only [N]
    norm_num only [pow_zero, mul_one, ENNReal.ofReal_ofNat]
    have hgc : ContinuousOn g (centeredAxisCube z (moserIterationRadius 0)) :=
      continuous_max.comp_continuousOn ((hh.1.mono (centeredAxisCube_mono
        ((moserIterationRadius_bounds 0).2.trans (by norm_num)))).prodMk continuousOn_const)
    have hgm := hgc.aestronglyMeasurable (μ := volume)
      (hcubeMeas _)
    refine (eLpNorm_mono hgm (fun y => ?_)).trans
      (eLpNorm_mono_measure _ (Measure.restrict_mono
        (centeredAxisCube_mono ((moserIterationRadius_bounds 0).2.trans (by norm_num))) le_rfl))
    rw [Real.norm_of_nonneg (hg0 y)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  let K : ℝ≥0∞ := ENNReal.ofReal B * eLpNorm h 2 (volume.restrict (centeredAxisCube z 1))
  by_cases hKtop : K = ⊤
  · change ENNReal.ofReal (g x) ≤ K
    rw [hKtop]
    exact le_top
  have hbound (n : ℕ) : eLpNorm g (ENNReal.ofReal (2 * chi ^ n))
      (volume.restrict (centeredAxisCube z (1 / 4))) ≤ ENNReal.ofReal K.toReal := by
    rw [ENNReal.ofReal_toReal hKtop]
    exact (eLpNorm_mono_measure _ (Measure.restrict_mono
      (centeredAxisCube_mono (moserIterationRadius_bounds n).1.le) le_rfl)).trans
      ((hN n).trans (mul_le_mul' le_rfl hN0))
  have hgcont : ContinuousOn g (centeredAxisCube z (1 / 4)) :=
    (hh.1.mono (centeredAxisCube_mono (by norm_num : (1 / 4 : ℝ) ≤ 1))).sup continuousOn_const
  have hae := moser_ae_bound_of_eLpNorm_bounds
    (hgcont.aestronglyMeasurable (isOpen_axisCube _ _).measurableSet)
    (fun n => mul_pos (by norm_num) (pow_pos hchi0 n))
    (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
      (tendsto_pow_atTop_atTop_of_one_lt hchi)) ENNReal.toReal_nonneg hbound
  have hpoint := moser_pointwise_bound_of_ae (isOpen_axisCube _ _) hgcont hae x hx
  change ENNReal.ofReal (g x) ≤ K
  rw [← ENNReal.ofReal_toReal hKtop]
  exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hpoint)

/-- Moser local boundedness, in the exact type required by the weighted-interior reduction. -/
theorem localBoundednessAtRatioFour_of_moser {d : ℕ} (hd : 2 ≤ d) :
    LocalBoundednessAtRatioFour d := by
  obtain ⟨B, hB, hbound⟩ := exists_moser_positive_local_bound hd
  refine ⟨B, hB, ?_⟩
  intro a z hab ha h hh x hx
  by_cases hx0 : 0 ≤ h x
  · simpa only [max_eq_left hx0, abs_of_nonneg hx0] using hbound a z hab ha h hh x hx
  · have hhneg := moser_weakHarmonic_neg hh
    have hn := hbound a z hab ha (fun y => -h y) hhneg x hx
    have hnormneg : eLpNorm (fun y => -h y) 2 (volume.restrict (centeredAxisCube z 1)) =
        eLpNorm h 2 (volume.restrict (centeredAxisCube z 1)) := eLpNorm_neg h 2 _
    rw [hnormneg] at hn
    have hxle : h x ≤ 0 := le_of_not_ge hx0
    simpa only [max_eq_left (neg_nonneg.mpr hxle), eLpNorm_neg, abs_of_nonpos hxle] using hn

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
