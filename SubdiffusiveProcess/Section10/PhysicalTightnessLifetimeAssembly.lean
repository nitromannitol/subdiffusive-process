import SubdiffusiveProcess.Section10.PhysicalTightnessAssembly
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.CutoffSpeedDensity

/-!
# Literal lifetime-path tightness from modulus majorants

Nonexplosion is consumed only after the containment proof. Strong Markov's
start clause supplies the actual initial position at every start. The
continuous-path extension and infinite-lifetime embedding are inverses on the
full support of each supplied law, so the compact-path conclusion has exactly
the lifetime-image form of `tight_prop_tightness` (i). The quantitative modulus
estimate remains open and explicit.
-/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness

local instance cemeteryLifetimeAssemblyVecStandardBorel (d : ℕ) :
    StandardBorelSpace (Cemetery (Vec d)) := by
  letI : BorelSpace (Cemetery (Vec d)) := SubdiffusiveProcess.Model.LifetimeProcess.borelSpace_sum
  infer_instance

/-- The actual every-start lifetime clauses and uniform annealed modulus
majorants imply the literal compact lifetime-image path bound. -/
theorem lifetime_tightness_of_modulus_majorants {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    (LN : ℕ → Kernel (Ω × Vec d) (Path d)) (hLN : ∀ N, IsMarkovKernel (LN N))
    (hstart : ∀ᵐ ω ∂μ, ∀ N : ℕ, ∀ x : Vec d,
      ∀ᵐ w ∂LN N (ω, x), LifetimePath.coordinate 0 w = Cemetery.alive x)
    (hcons : ∀ᵐ ω ∂μ, ∀ N : ℕ, ∀ x : Vec d,
      ∀ᵐ w ∂LN N (ω, x), w.lifetime = ⊤)
    (hmod : ∀ B : Set (Vec d), IsCompact B → ∀ n : ℕ, ∀ a : ℝ, 0 < a →
      ∃ δ : ENNReal, 0 < δ ∧ ∀ N : ℕ, ∃ G : Ω → ENNReal, Measurable G ∧
        (∀ᵐ ω ∂μ, ∀ x ∈ B,
          (LN N (ω, x)).map (LifetimePath.continuousPathExtension
            (ContinuousMap.const NNReal (0 : Vec d)))
            (ContinuousPath.modulusSet (n : NNReal) δ ((n + 1 : ENNReal)⁻¹))ᶜ ≤ G ω) ∧
        ∫⁻ ω, G ω ∂μ ≤ ENNReal.ofReal a) :
    ∀ B : Set (Vec d), IsCompact B → ∀ ε : ℝ, 0 < ε →
      ∃ K : Set (ContinuousPath (Vec d)), IsCompact K ∧
        ∀ N : ℕ, ∃ G : Ω → ENNReal, Measurable G ∧
          (∀ ω, ∀ x ∈ B, LN N (ω, x) (LifetimePath.ofContinuousPath '' K)ᶜ ≤ G ω) ∧
          ∫⁻ ω, G ω ∂μ ≤ ENNReal.ofReal ε := by
  let default : ContinuousPath (Vec d) := ContinuousMap.const NNReal (0 : Vec d)
  let ext := LifetimePath.continuousPathExtension default
  have hext : Measurable ext := LifetimePath.measurable_continuousPathExtension default
  let KN : ℕ → Kernel (Ω × Vec d) (ContinuousPath (Vec d)) := fun N => (LN N).map ext
  have hKN : ∀ N, IsMarkovKernel (KN N) := fun N => by
    haveI := hLN N
    exact Kernel.IsMarkovKernel.map _ hext
  intro B hB ε hε
  have hKNstart : ∀ᵐ ω ∂μ, ∀ N : ℕ, ∀ x ∈ B, ∀ᵐ p ∂KN N (ω, x), p 0 = x := by
    filter_upwards [hstart, hcons] with ω hω hωcons
    intro N x hx
    rw [show KN N (ω, x) = (LN N (ω, x)).map ext by
      exact Kernel.map_apply (LN N) hext (ω, x)]
    apply (ae_map_iff hext.aemeasurable
      ((ContinuousPath.continuous_eval (alpha := Vec d) 0).measurable (measurableSet_singleton x))).2
    filter_upwards [hω N x, hωcons N x] with w hwstart hwcons
    have hinv : LifetimePath.ofContinuousPath (ext w) = w := by
      change LifetimePath.ofContinuousPath (LifetimePath.continuousPathExtension default w) = w
      rw [LifetimePath.continuousPathExtension_of_lifetime_eq_top _ _ hwcons,
        LifetimePath.ofContinuousPath_toContinuousPath]
    have hc := congrArg (LifetimePath.coordinate (0 : NNReal)) hinv
    rw [LifetimePath.coordinate_ofContinuousPath, hwstart] at hc
    exact Sum.inl.inj hc
  have hKNmod : ∀ n : ℕ, ∀ a : ℝ, 0 < a → ∃ δ : ENNReal, 0 < δ ∧
      ∀ N : ℕ, ∃ G : Ω → ENNReal, Measurable G ∧
        (∀ᵐ ω ∂μ, ∀ x ∈ B, KN N (ω, x)
          (ContinuousPath.modulusSet (n : NNReal) δ ((n + 1 : ENNReal)⁻¹))ᶜ ≤ G ω) ∧
        ∫⁻ ω, G ω ∂μ ≤ ENNReal.ofReal a := by
    intro n a ha
    simpa only [KN, Kernel.map_apply _ hext, ext, default] using hmod B hB n a ha
  obtain ⟨K, hK, hmajorants⟩ := path_tightness_of_modulus_majorants μ KN hKN B hB
    hKNstart hKNmod ε hε
  refine ⟨K, hK, ?_⟩
  intro N
  obtain ⟨F, hF, hFpoint, hFmoment⟩ := hmajorants N
  have hpoint : ∀ᵐ ω ∂μ, ∀ x ∈ B,
      LN N (ω, x) (LifetimePath.ofContinuousPath '' K)ᶜ ≤ F ω := by
    filter_upwards [hcons] with ω hω
    intro x hx
    rw [lifetime_bad_mass_eq_extension (LN N (ω, x)) (hω N x) default K hK.isClosed.measurableSet]
    exact (show (LN N (ω, x)).map ext Kᶜ = KN N (ω, x) Kᶜ by
      rw [Kernel.map_apply _ hext]).trans_le (hFpoint ω x hx)
  haveI := hLN N
  obtain ⟨G, hG, hGpoint, hGint⟩ := measurable_majorant_of_ae μ B
    (fun ω x => LN N (ω, x) (LifetimePath.ofContinuousPath '' K)ᶜ) F hF hpoint
    (fun ω x => (measure_mono (subset_univ _)).trans (by simp))
  exact ⟨G, hG, hGpoint, hGint.trans_le hFmoment⟩

/-- Actual model projection: the literal `LocalDiffusionData` clause supplies
initial positions at every start. No Feller or caller kernel-identification
premise is used in this assembly. Nonexplosion and modulus bounds must first
be proved; this helper does not claim they follow here from the model. -/
theorem physical_lifetime_tightness_of_modulus_majorants {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Hf : BilateralField d → C(SpatialCoordinates d, ℝ))
    (LN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (Path d))
    (hLN : ∀ N, IsMarkovKernel (LN N))
    (hdata : ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∀ N,
      LocalDiffusionData (cutoffCoefficient M Hf ω N) (cutoffSpeedDensity M Hf ω N)
        (Kernel.comap (LN N) (fun x => (ω, x)) measurable_prodMk_left))
    (hcons : ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∀ N, ∀ x : SpatialCoordinates d,
      ∀ᵐ w ∂LN N (ω, x), w.lifetime = ⊤)
    (hmod : ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ n : ℕ, ∀ a : ℝ, 0 < a →
      ∃ δ : ENNReal, 0 < δ ∧ ∀ N : ℕ, ∃ G : BilateralField d → ENNReal, Measurable G ∧
        (∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∀ x ∈ B,
          (LN N (ω, x)).map (LifetimePath.continuousPathExtension
            (ContinuousMap.const NNReal (0 : SpatialCoordinates d)))
            (ContinuousPath.modulusSet (n : NNReal) δ ((n + 1 : ENNReal)⁻¹))ᶜ ≤ G ω) ∧
        ∫⁻ ω, G ω ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal a) :
    ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ ε : ℝ, 0 < ε →
      ∃ K : Set (DiffusionPath d), IsCompact K ∧
        ∀ N : ℕ, ∃ G : BilateralField d → ENNReal, Measurable G ∧
          (∀ ω, ∀ x ∈ B, LN N (ω, x) (LifetimePath.ofContinuousPath '' K)ᶜ ≤ G ω) ∧
          ∫⁻ ω, G ω ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal ε := by
  refine lifetime_tightness_of_modulus_majorants (chaosSampleLaw M).toMeasure LN hLN ?_ hcons hmod
  filter_upwards [hdata] with ω hω
  intro N x
  exact (hω N).1.1.2.1 x

end SubdiffusiveProcess.Section10.PhysicalTightness
