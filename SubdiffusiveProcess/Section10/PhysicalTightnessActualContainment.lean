module

public import SubdiffusiveProcess.Section10.PhysicalTightnessActualExitBank
public import SubdiffusiveProcess.Section10.PhysicalTightnessContainment
public import SubdiffusiveProcess.Section10.PhysicalTightnessLifetimeAssembly

@[expose] public section

/-! Consumers of the actual physical-to-common-scale analytic transport.
The local cutoff/Moser moment bank and the modulus estimate remain explicit
proof obligations. Conservativity, the law adapter and the early-exit bank
are discharged here and are not additional consumer promises. -/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness
open PhysicalLocalTransport

/-- The actual local analytic bank gives one full event of nonexplosion for
all cutoffs and all starts in either source branch. `m=N+j>N` is covered by
the finite saturated cutoff and top clock inequalities proved earlier. -/
theorem actual_nonexplosion_of_local_analytic_bank {d : ℕ}
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
          LocalExitCertificate (localCoefficient M L m z omega) (localSpeed M L m z omega) (K omega)) :
    ∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, ∀ x : Vec d,
      ∀ᵐ w ∂LN N (xi, x), w.lifetime = ⊤ := by
  have hbank := actual_common_exit_moment_bank_of_local_analytic_bank
    M H hH Hf hHf LN hdata 1 C (by norm_num) hC (by simpa only [mul_one] using hlocal)
  apply nonexplosion_of_large_cube_exit (chaosSampleLaw M).toMeasure LN hLN
    (fun _ j => (3 : ℝ) ^ (2 * j)) (fun _ _ => le_rfl) (1 + 8 * C) (by positivity)
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
    refine hb.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (zero_le_one.trans (hFone xi))))
    exact div_le_div_of_nonneg_left ht.le (by positivity) hclock

/-- The exact tightness tail from the two remaining quantitative analytic
obligations. No conservativity or law equality is assumed. This helper is not
the stated principal: the local bank and modulus must still be supplied. -/
theorem actual_tightness_tail_of_local_bank_and_modulus {d : ℕ}
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
    (hmod : ∀ B : Set (Vec d), IsCompact B → ∀ n : ℕ, ∀ a : ℝ, 0 < a →
      ∃ delta : ENNReal, 0 < delta ∧ ∀ N : ℕ, ∃ G : BilateralField d → ENNReal, Measurable G ∧
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
  have hcons := actual_nonexplosion_of_local_analytic_bank M H hH Hf hHf LN hLN hdata C hC hlocal
  have hpath := physical_lifetime_tightness_of_modulus_majorants M Hf LN hLN hdata hcons hmod
  refine ⟨hcons, ?_⟩
  intro B hB epsilon hepsilon
  obtain ⟨Kset, hKset, hmajorants⟩ := hpath B hB epsilon hepsilon
  exact ⟨Kset, hKset, hmajorants,
    lifetime_compact_random_laws (chaosSampleLaw M).toMeasure LN hLN B (hpath B hB)
      (ContinuousMap.const NNReal (0 : Vec d))⟩

end SubdiffusiveProcess.Section10.PhysicalTightness
