module

public import SubdiffusiveProcess.Section10.PhysicalTightnessActualModulus

@[expose] public section

/-! The actual large-cutoff estimate supplies the uniform tail. This file
combines it with an explicitly remaining finite-head estimate, then checks
the complete tightness conclusion against the actual model header. It does
not claim or replace the missing smooth-coefficient finite-head supplier. -/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness
open PhysicalLocalTransport

/-- The whole-family quantitative modulus requires only the remaining
finite-head estimate: the actual tail, its expectation, and common delta
are already supplied by the proved chaining and finite-cover consumers. -/
theorem actual_modulus_majorants_of_local_bank_and_finite_head {d : ℕ}
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
    (hhead : ∀ B : Set (Vec d), IsCompact B → ∀ n : ℕ, ∀ a : ℝ, 0 < a → ∀ k : ℕ,
      ∃ delta : ENNReal, 0 < delta ∧ ∀ N : ℕ, N < k →
        ∃ G : BilateralField d → ENNReal, Measurable G ∧
          (∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ x ∈ B,
            (LN N (xi, x)).map (LifetimePath.continuousPathExtension
              (ContinuousMap.const NNReal (0 : Vec d)))
              (ContinuousPath.modulusSet (n : NNReal) delta ((n + 1 : ENNReal)⁻¹))ᶜ ≤ G xi) ∧
          ∫⁻ xi, G xi ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal a) :
    ∀ B : Set (Vec d), IsCompact B → ∀ n : ℕ, ∀ a : ℝ, 0 < a →
      ∃ delta : ENNReal, 0 < delta ∧ ∀ N : ℕ,
        ∃ G : BilateralField d → ENNReal, Measurable G ∧
          (∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ x ∈ B,
            (LN N (xi, x)).map (LifetimePath.continuousPathExtension
              (ContinuousMap.const NNReal (0 : Vec d)))
              (ContinuousPath.modulusSet (n : NNReal) delta ((n + 1 : ENNReal)⁻¹))ᶜ ≤ G xi) ∧
          ∫⁻ xi, G xi ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal a := by
  intro B hB n a ha
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hr : 0 < (n + 1 : ℝ)⁻¹ := inv_pos.mpr hn
  have hrho : ENNReal.ofReal ((n + 1 : ℝ)⁻¹) = (n + 1 : ENNReal)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hn,
      ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  have htime : (n : NNReal) ≤ Real.toNNReal (n + 1) := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ hn.le, NNReal.coe_natCast]
    linarith
  obtain ⟨k, dtail, hdtail, htail⟩ := actual_annealed_modulus_tail_of_chaining
    M H hH Hf hHf LN hLN hdata C hC hlocal B hB.isBounded (n + 1) ((n + 1 : ℝ)⁻¹) a hn hr ha
  obtain ⟨dhead, hdhead, hheadBound⟩ := hhead B hB n a ha k
  let delta : ENNReal := min dtail dhead
  refine ⟨delta, lt_min hdtail hdhead, ?_⟩
  intro N
  by_cases hNk : k ≤ N
  · obtain ⟨G, hG, hGbound, hGint⟩ := htail N hNk
    have hsubset : ContinuousPath.modulusSet (alpha := Vec d) (Real.toNNReal (n + 1))
        dtail (ENNReal.ofReal ((n + 1 : ℝ)⁻¹)) ⊆
          ContinuousPath.modulusSet (n : NNReal) delta ((n + 1 : ENNReal)⁻¹) := by
      rw [hrho]
      intro p hp s t hs ht hst
      exact hp s t (hs.trans htime) (ht.trans htime) (hst.trans (min_le_left _ _))
    refine ⟨G, hG, ?_, hGint⟩
    filter_upwards [] with xi
    intro x hx
    exact (measure_mono (compl_subset_compl.mpr hsubset)).trans (hGbound xi x hx)
  · obtain ⟨G, hG, hGbound, hGint⟩ := hheadBound N (lt_of_not_ge hNk)
    have hsubset : ContinuousPath.modulusSet (alpha := Vec d) (n : NNReal) dhead
        ((n + 1 : ENNReal)⁻¹) ⊆ ContinuousPath.modulusSet (n : NNReal) delta ((n + 1 : ENNReal)⁻¹) := by
      intro p hp s t hs ht hst
      exact hp s t hs ht (hst.trans (min_le_right _ _))
    refine ⟨G, hG, ?_, hGint⟩
    filter_upwards [hGbound] with xi hxi
    intro x hx
    exact (measure_mono (compl_subset_compl.mpr hsubset)).trans (hxi x hx)

end SubdiffusiveProcess.Section10.PhysicalTightness
