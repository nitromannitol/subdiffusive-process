module

public import SubdiffusiveProcess.Section10.PhysicalTightnessLocalCover
public import SubdiffusiveProcess.Section10.PhysicalTightnessAnnealed
public import SubdiffusiveProcess.Section10.PhysicalExitChaining

@[expose] public section

/-! Actual finite/top annealed modulus assembly. The local analytic bank and
independent deterministic chaining theorem are respectively an explicit
analytic obligation and a proved imported supplier. No source principal is
defined here. -/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness
open PhysicalLocalTransport

local instance cemeteryModulusVecStandardBorel (d : ℕ) : StandardBorelSpace (Cemetery (Vec d)) := by
  let : BorelSpace (Cemetery (Vec d)) := SubdiffusiveProcess.Model.LifetimeProcess.borelSpace_sum
  infer_instance

/-- Actual local moments give an outer ball containing the starting set and
all-environment measurable exit majorants, with arbitrarily small expectation.
Both physical branches and all base cutoffs share the same outer radius. -/
theorem actual_annealed_containment_of_local_analytic_bank {d : ℕ}
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]
    (M : GMCModel d) (H : BilateralField d → C(Vec d, ℝ))
    (hH : InfraredCharacterization M H)
    (Hf : BilateralField d → C(Vec d, ℝ)) (hHf : Hf = H ∨ Hf = fun _ => 0)
    (LN : ℕ → Kernel (BilateralField d × Vec d) (Path d))
    (hLN : ∀ N, IsMarkovKernel (LN N))
    (hdata : ∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      LocalDiffusionData (cutoffCoefficient M Hf xi N) (cutoffSpeedDensity M Hf xi N)
        (Kernel.comap (LN N) (fun x => (xi, x)) measurable_prodMk_left))
    (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ (L : WithTop ℕ) (m : ℕ) (z : Vec d),
      ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
        (∫⁻ omega, ENNReal.ofReal (K omega ^ (2 : ℝ))
          ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤ ENNReal.ofReal C ∧
        ∀ᵐ omega ∂(PhysicalAttachment.physicalLaw M).toMeasure,
          LocalExitCertificate (localCoefficient M L m z omega) (localSpeed M L m z omega) (K omega))
    (B : Set (Vec d)) (hB : Bornology.IsBounded B) (T a : ℝ) (hT : 0 < T) (ha : 0 < a) :
    ∃ R : ℝ, 0 < R ∧ B ⊆ Metric.ball (0 : Vec d) R ∧
      ∀ N : ℕ, ∃ G : BilateralField d → ENNReal, Measurable G ∧
        (∀ xi, ∀ x ∈ B, LN N (xi, x)
          {w | LifetimePath.exitTime (Metric.ball (0 : Vec d) R) w ≤ ENNReal.ofReal T} ≤ G xi) ∧
        ∫⁻ xi, G xi ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal a := by
  have hbank := actual_common_exit_moment_bank_of_local_analytic_bank
    M H hH Hf hHf LN hdata 1 C (by norm_num) hC (by simpa only [mul_one] using hlocal)
  have hfast : ∀ N j : ℕ, ∃ K : BilateralField d → ℝ, Measurable K ∧ (∀ xi, 0 ≤ K xi) ∧
      (∫⁻ xi, ENNReal.ofReal (K xi) ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal (1 + 8 * C) ∧
      ∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ t : ℝ, 0 < t →
        ∀ x ∈ Metric.ball (0 : Vec d) ((3 : ℝ) ^ j / 18),
          LN N (xi, x) {w | LifetimePath.exitTime (Metric.ball (0 : Vec d) ((3 : ℝ) ^ j / 2)) w ≤
            ENNReal.ofReal t} ≤ ENNReal.ofReal (K xi * Real.sqrt (t / (3 : ℝ) ^ (2 * j))) := by
    intro N j
    obtain ⟨L, hbranch, F, hF, hFone, hFmoment, hFbound⟩ := hbank N (N + j) 0
    have hclock : (3 : ℝ) ^ (2 * j) ≤ relativeClock M L N (N + j) := by
      rcases hbranch with ⟨hL, -⟩ | ⟨hL, -⟩ <;> subst L
      · exact top_relativeClock_large M N j
      · exact (finite_relativeClock_large M N j).ge
    have hscale : (3 : ℝ) ^ (((N + j : ℕ) : ℤ) - N) = (3 : ℝ) ^ j := by
      rw [show (((N + j : ℕ) : ℤ) - N) = (j : ℤ) by omega, zpow_natCast]
    refine ⟨F, hF, fun xi => zero_le_one.trans (hFone xi), ?_, ?_⟩
    · have hnum : (1 : ℝ) + 2 * (4 * C) = 1 + 8 * C := by ring
      simpa only [Real.rpow_one, hnum] using hFmoment
    · filter_upwards [hFbound] with xi hxi
      intro t ht x hx
      have hb := hxi t ht x (by simpa only [hscale] using hx)
      simp only [hscale] at hb
      exact hb.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (div_le_div_of_nonneg_left ht.le (by positivity) hclock))
        (zero_le_one.trans (hFone xi))))
  obtain ⟨j, hj⟩ := annealed_containment_of_large_cube_exit
    (chaosSampleLaw M).toMeasure LN hLN (fun _ j => (3 : ℝ) ^ (2 * j))
    (fun _ _ => le_rfl) (1 + 8 * C) (by positivity) hfast B hB T hT a ha
  obtain ⟨R0, hBR⟩ := hB.subset_closedBall (0 : Vec d)
  let R : ℝ := max ((3 : ℝ) ^ j / 2) (max 1 (R0 + 1))
  have hR1 : 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hR0 : R0 + 1 ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hsubset : Metric.ball (0 : Vec d) ((3 : ℝ) ^ j / 2) ⊆ Metric.ball (0 : Vec d) R :=
    Metric.ball_subset_ball (le_max_left _ _)
  refine ⟨R, hR, ?_, ?_⟩
  · intro x hx
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp (hBR hx)).trans_lt
      ((by linarith : R0 < R0 + 1).trans_le hR0))
  · intro N
    obtain ⟨G, hG, hGbound, hGint⟩ := hj N
    refine ⟨G, hG, ?_, hGint⟩
    intro xi x hx
    exact (measure_mono fun w hw => (exitTime_le_of_subset hsubset w).trans hw).trans (hGbound xi x hx)

/-- Actual model tail modulus majorants from the exact deterministic
chaining interface. The positive delta is chosen BEFORE N. Finite N<k remain
separate; no finite-head regularity is hidden in this conclusion. -/
theorem actual_annealed_modulus_tail_of_chaining {d : ℕ}
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]
    (M : GMCModel d) (H : BilateralField d → C(Vec d, ℝ))
    (hH : InfraredCharacterization M H)
    (Hf : BilateralField d → C(Vec d, ℝ)) (hHf : Hf = H ∨ Hf = fun _ => 0)
    (LN : ℕ → Kernel (BilateralField d × Vec d) (Path d))
    (hLN : ∀ N, IsMarkovKernel (LN N))
    (hdata : ∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      LocalDiffusionData (cutoffCoefficient M Hf xi N) (cutoffSpeedDensity M Hf xi N)
        (Kernel.comap (LN N) (fun x => (xi, x)) measurable_prodMk_left))
    (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ (L : WithTop ℕ) (m : ℕ) (z : Vec d),
      ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
        (∫⁻ omega, ENNReal.ofReal (K omega ^ (2 : ℝ))
          ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤ ENNReal.ofReal C ∧
        ∀ᵐ omega ∂(PhysicalAttachment.physicalLaw M).toMeasure,
          LocalExitCertificate (localCoefficient M L m z omega) (localSpeed M L m z omega) (K omega))
    (B : Set (Vec d)) (hB : Bornology.IsBounded B) (T r a : ℝ)
    (hT : 0 < T) (hr : 0 < r) (ha : 0 < a) :
    ∃ k : ℕ, ∃ delta : ENNReal, 0 < delta ∧ ∀ N : ℕ, k ≤ N →
      ∃ G : BilateralField d → ENNReal, Measurable G ∧
        (∀ xi, ∀ x ∈ B,
          (LN N (xi, x)).map (LifetimePath.continuousPathExtension (ContinuousMap.const NNReal (0 : Vec d)))
            (ContinuousPath.modulusSet (Real.toNNReal T) delta (ENNReal.ofReal r))ᶜ ≤ G xi) ∧
        ∫⁻ xi, G xi ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal a := by
  have he : 0 < a / 4 := by positivity
  obtain ⟨R, hR, hBR, houter⟩ := actual_annealed_containment_of_local_analytic_bank
    M H hH Hf hHf LN hLN hdata C hC hlocal B hB T (a / 4) hT he
  obtain ⟨k, Cball, hCball, hball⟩ := actual_uniform_ball_exit_bank_of_local_analytic_bank
    M H hH Hf hHf LN hdata C hC hlocal R r hR hr
  let K : ℝ := 4 * (Cball + 1) / a
  have hK : 0 < K := by positivity
  have hCK : Cball / K ≤ a / 4 := by
    apply (div_le_iff₀ hK).2
    have hproduct : (a / 4) * K = Cball + 1 := by
      dsimp only [K]
      field_simp
    rw [hproduct]
    linarith
  obtain ⟨delta, hdelta, hdeltaBound⟩ :=
    PhysicalExitChaining.uniform_modulus_bound_of_local_exit R r T K (a / 4) hR hr hT hK.le he
  have hcons := actual_nonexplosion_of_local_analytic_bank M H hH Hf hHf LN hLN hdata C hC hlocal
  refine ⟨k, delta, hdelta, ?_⟩
  intro N hNk
  obtain ⟨F, hF, -, hFint, hFbound⟩ := hball N hNk
  obtain ⟨Gouter, hGouter, hGouterBound, hGouterInt⟩ := houter N
  let f : BilateralField d → Vec d → ENNReal := fun xi x =>
    (LN N (xi, x)).map (LifetimePath.continuousPathExtension (ContinuousMap.const NNReal (0 : Vec d)))
      (ContinuousPath.modulusSet (Real.toNNReal T) delta (ENNReal.ofReal r))ᶜ
  have hprob : ∀ xi x, f xi x ≤ 1 := by
    intro xi x
    have := hLN N
    calc
      f xi x ≤ ((LN N (xi, x)).map (LifetimePath.continuousPathExtension
        (ContinuousMap.const NNReal (0 : Vec d)))) univ := measure_mono (subset_univ _)
      _ = 1 := by
        rw [Measure.map_apply (LifetimePath.measurable_continuousPathExtension _)
          MeasurableSet.univ, preimage_univ]
        exact measure_univ
  have hgood : ∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ x ∈ B, F xi ≤ K →
      f xi x ≤ Gouter xi + ENNReal.ofReal (a / 4) := by
    filter_upwards [hdata, hcons, hFbound] with xi hxi hxiCons hxiF
    intro x hx hFK
    let law : Kernel (Vec d) (Path d) :=
      Kernel.comap (LN N) (fun y => (xi, y)) measurable_prodMk_left
    have hstrong : StrongMarkov law := (hxi N).1.1
    have hlocalExit : ∀ t : ℝ, 0 < t → ∀ y ∈ Metric.ball (0 : Vec d) R,
        law y {w | LifetimePath.exitTime (Metric.ball y (r / 4)) w ≤ ENNReal.ofReal t} ≤
          ENNReal.ofReal (K * Real.sqrt t) := by
      intro t ht y hy
      exact (hxiF t ht y hy).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hFK (Real.sqrt_nonneg t)))
    have hb := hdeltaBound law hstrong (hxiCons N) hlocalExit x (hBR hx)
    exact hb.trans (add_le_add (hGouterBound xi x hx) le_rfl)
  obtain ⟨G, hG, hGbound, hGint⟩ := measurable_majorant_of_integrable_good_event
    (chaosSampleLaw M).toMeasure B f hprob F hF Cball K (a / 4) hCball.le hK he.le
      hFint Gouter hGouter hGouterInt hgood
  exact ⟨G, hG, hGbound, hGint.trans (ENNReal.ofReal_le_ofReal (by linarith only [hCK, ha]))⟩

end SubdiffusiveProcess.Section10.PhysicalTightness
