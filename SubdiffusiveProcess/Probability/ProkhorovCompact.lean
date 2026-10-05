module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

@[expose] public section

/-! Sequential compactness of probability measures on a compact second-countable Hausdorff
space. Integration embeds each measure into a polar in the weak dual of `C(K, ℝ)`.
Sequential Banach–Alaoglu gives a limit functional; positivity, normalization, and RMK
identify it with a probability measure. -/

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped CompactlySupported

noncomputable section

namespace SubdiffusiveProcess.Probability

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]

/-- Integration against a probability measure as a norm-bounded linear functional. -/
def prokhorovIntegralDual (mu : ProbabilityMeasure K) : StrongDual ℝ C(K, ℝ) := by
  let L : C(K, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∫ x, f x ∂(mu : Measure K)
      map_add' := fun f g => by
        simpa using integral_add ((BoundedContinuousFunction.mkOfCompact f).integrable
          (mu : Measure K)) ((BoundedContinuousFunction.mkOfCompact g).integrable
          (mu : Measure K))
      map_smul' := fun a f => by simpa using integral_const_mul a (fun x => f x) }
  exact L.mkContinuous 1 fun f => by
    simpa [L] using (BoundedContinuousFunction.mkOfCompact f).norm_integral_le_norm
      (mu : Measure K)

omit [T2Space K] in
theorem prokhorovIntegralDual_apply (mu : ProbabilityMeasure K) (f : C(K, ℝ)) :
    prokhorovIntegralDual mu f = ∫ x, f x ∂(mu : Measure K) := by
  rfl

omit [T2Space K] in
theorem norm_prokhorovIntegralDual_le (mu : ProbabilityMeasure K) :
    ‖prokhorovIntegralDual mu‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa [prokhorovIntegralDual_apply] using
    (BoundedContinuousFunction.mkOfCompact f).norm_integral_le_norm (mu : Measure K)

/-- The compact RMK representation, including the mass normalization. -/
theorem exists_probability_of_positive_normalized (L : StrongDual ℝ C(K, ℝ))
    (hpos : ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ L f)
    (hone : L 1 = 1) :
    ∃ nu : ProbabilityMeasure K, ∀ f : C(K, ℝ),
      (∫ x, f x ∂(nu : Measure K)) = L f := by
  let L' : C_c(K, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => L f.toContinuousMap
      map_add' := fun f g => L.map_add f.toContinuousMap g.toContinuousMap
      map_smul' := fun a f => L.map_smul a f.toContinuousMap }
  let P : C_c(K, ℝ) →ₚ[ℝ] ℝ :=
    { L' with
      monotone' := by
        intro f g h
        have hp := hpos (g.toContinuousMap - f.toContinuousMap)
          (fun x => sub_nonneg.mpr (h x))
        rw [map_sub] at hp
        exact sub_nonneg.mp hp }
  let rho : Measure K := RealRMK.rieszMeasure P
  have hmass : rho.real univ = 1 := by
    let one : C_c(K, ℝ) := CompactlySupportedContinuousMap.continuousMapEquiv 1
    have h := RealRMK.integral_rieszMeasure P one
    have hone' : P one = 1 := hone
    simpa [one, rho, hone'] using h
  have hrho : IsProbabilityMeasure rho := by
    constructor
    apply (ENNReal.toReal_eq_one_iff _).mp
    simpa [Measure.real_def] using hmass
  refine ⟨⟨rho, hrho⟩, fun f => ?_⟩
  have h := RealRMK.integral_rieszMeasure P
    (CompactlySupportedContinuousMap.continuousMapEquiv f)
  change (∫ x, f x ∂rho) = L f at h
  exact h

/-- Probability measures on a compact second-countable Hausdorff space have convergent subsequences. -/
theorem probability_subsequence_compact [SecondCountableTopology K]
    (mu : ℕ → ProbabilityMeasure K) :
    ∃ (seq : ℕ → ℕ) (nu : ProbabilityMeasure K), StrictMono seq ∧
      Tendsto (fun n => mu (seq n)) atTop (𝓝 nu) := by
  let F : ℕ → WeakDual ℝ C(K, ℝ) := fun n =>
    StrongDual.toWeakDual (prokhorovIntegralDual (mu n))
  let B : Set C(K, ℝ) := {f | ‖f‖ < 1}
  have hB : B ∈ 𝓝 0 := by
    exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
  have hF : ∀ n, F n ∈ WeakDual.polar ℝ B := by
    intro n
    rw [WeakDual.polar_def]
    intro f hf
    change ‖prokhorovIntegralDual (mu n) f‖ ≤ 1
    rw [prokhorovIntegralDual_apply]
    exact ((BoundedContinuousFunction.mkOfCompact f).norm_integral_le_norm
      (mu n : Measure K)).trans (show ‖f‖ ≤ 1 from hf.le)
  obtain ⟨L, _, seq, hseq, hlim⟩ :=
    WeakDual.isSeqCompact_polar (𝕜 := ℝ) (E := C(K, ℝ)) hB hF
  have heval (f : C(K, ℝ)) :
      Tendsto (fun n => ∫ x, f x ∂(mu (seq n) : Measure K)) atTop (𝓝 (L f)) := by
    simpa [Function.comp_def, F, prokhorovIntegralDual_apply] using
      ((WeakDual.eval_continuous f).tendsto L).comp hlim
  have hpos : ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ L f := by
    intro f hf
    exact ge_of_tendsto (heval f) (Eventually.of_forall fun n => integral_nonneg hf)
  have hone : L (1 : C(K, ℝ)) = 1 := by
    apply tendsto_nhds_unique (heval 1)
    simp
  obtain ⟨nu, hnu⟩ := exists_probability_of_positive_normalized (WeakDual.toStrongDual L) hpos hone
  refine ⟨seq, nu, hseq, ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr ?_⟩
  intro f
  change Tendsto (fun n => ∫ x, f.toContinuousMap x ∂(mu (seq n) : Measure K))
    atTop (𝓝 (∫ x, f.toContinuousMap x ∂(nu : Measure K)))
  rw [hnu f.toContinuousMap]
  exact heval f.toContinuousMap

end SubdiffusiveProcess.Probability
