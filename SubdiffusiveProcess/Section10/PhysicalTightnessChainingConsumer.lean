module

public import SubdiffusiveProcess.Section10.PhysicalTightnessFiniteHeadAssembly

@[expose] public section

/-! A compiling application in the complete restated tightness header.
The actual tail modulus is derived with the proved chaining theorem.
Only the local analytic bank and finite head remain explicit obligations. The specified principal is not redefined or changed. -/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness
open PhysicalLocalTransport



theorem actual_full_header_application_of_local_bank_and_finite_head {d : ℕ}
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]
    (_hd : 2 ≤ d) (delta0 : ℝ) (_hdelta0 : 0 < delta0)
    (M : GMCModel d) (_hdelta : M.delta ≤ delta0)
    (H : BilateralField d → C(Vec d, ℝ))
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
    (∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, ∀ x : Vec d,
      ∀ᵐ w ∂LN N (xi, x), w.lifetime = ⊤) ∧
    ∀ B : Set (Vec d), IsCompact B → ∀ epsilon : ℝ, 0 < epsilon →
      ∃ Kset : Set (DiffusionPath d), IsCompact Kset ∧
        (∀ N : ℕ, ∃ G : BilateralField d → ENNReal, Measurable G ∧
          (∀ xi, ∀ x ∈ B, LN N (xi, x) (LifetimePath.ofContinuousPath '' Kset)ᶜ ≤ G xi) ∧
          ∫⁻ xi, G xi ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal epsilon) ∧
        ∀ eta : ℝ, 0 < eta →
          ∃ Keta : Set (ProbabilityMeasure (DiffusionPath d)), IsCompact Keta ∧
            ∀ N : ℕ, (chaosSampleLaw M).toMeasure {xi | ∃ x ∈ B,
              ∀ mu : ProbabilityMeasure (DiffusionPath d),
                (mu : Measure (DiffusionPath d)) =
                  (LN N (xi, x)).map (LifetimePath.continuousPathExtension
                    (ContinuousMap.const NNReal (0 : Vec d))) → mu ∉ Keta} ≤ ENNReal.ofReal eta := by
  have hmod := actual_modulus_majorants_of_local_bank_and_finite_head
    M H hH Hf hHf LN hLN hdata C hC hlocal hhead
  exact actual_tightness_tail_of_local_bank_and_modulus M H hH Hf hHf LN hLN hdata C hC hlocal hmod

end SubdiffusiveProcess.Section10.PhysicalTightness
