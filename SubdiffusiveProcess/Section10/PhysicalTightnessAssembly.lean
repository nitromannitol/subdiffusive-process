import SubdiffusiveProcess.Section10.PhysicalTightnessTransport
import SubdiffusiveProcess.Section10.PhysicalTightnessContainment
import MarkovProcess.Continuity.PathTightness

/-!
# Compact path sets from annealed measurable modulus majorants

This uses the canonical `ContinuousPath.isCompact_moduliSet` (Arzela-Ascoli),
then sums the given measurable random bounds. There is no measurable-supremum
or Feller-start-continuity premise. The uniform quantitative modulus bounds
remain explicit inputs; this theorem does not supply the paper's Step 3.
-/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness

local instance cemeteryAssemblyVecStandardBorel (d : ℕ) : StandardBorelSpace (Cemetery (Vec d)) := by
  letI : BorelSpace (Cemetery (Vec d)) := SubdiffusiveProcess.Model.LifetimeProcess.borelSpace_sum
  infer_instance

/-- Under nonexplosion the literal lifetime-image bad mass equals the bad mass
of the canonical continuous-path extension, on the same supplied measure. -/
theorem lifetime_bad_mass_eq_extension {d : ℕ} (ν : Measure (Path d))
    (hν : ∀ᵐ w ∂ν, w.lifetime = ⊤) (default : ContinuousPath (Vec d))
    (K : Set (ContinuousPath (Vec d))) (hK : MeasurableSet K) :
    ν (LifetimePath.ofContinuousPath '' K)ᶜ =
      ν.map (LifetimePath.continuousPathExtension default) Kᶜ := by
  rw [Measure.map_apply (LifetimePath.measurable_continuousPathExtension default) hK.compl]
  apply measure_congr
  filter_upwards [hν] with w hw
  have hinv : LifetimePath.ofContinuousPath (LifetimePath.continuousPathExtension default w) = w := by
    rw [LifetimePath.continuousPathExtension_of_lifetime_eq_top _ _ hw,
      LifetimePath.ofContinuousPath_toContinuousPath]
  have hi : w ∈ LifetimePath.ofContinuousPath '' K ↔
      LifetimePath.continuousPathExtension default w ∈ K := by
    constructor
    · rintro ⟨p, hp, rfl⟩
      simpa using hp
    · intro hp
      exact ⟨_, hp, hinv⟩
  exact propext (not_congr hi)

/-- Summable measurable modulus bounds produce one compact path set and
measurable all-environment majorants, uniformly over the entire kernel family. -/
theorem path_tightness_of_modulus_majorants {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (KN : ℕ → Kernel (Ω × Vec d) (ContinuousPath (Vec d)))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (B : Set (Vec d)) (hB : IsCompact B)
    (hstart : ∀ᵐ ω ∂μ, ∀ N : ℕ, ∀ x ∈ B,
      ∀ᵐ p ∂KN N (ω, x), p 0 = x)
    (hmod : ∀ n : ℕ, ∀ a : ℝ, 0 < a → ∃ δ : ENNReal, 0 < δ ∧
      ∀ N : ℕ, ∃ G : Ω → ENNReal, Measurable G ∧
        (∀ᵐ ω ∂μ, ∀ x ∈ B, KN N (ω, x)
          (ContinuousPath.modulusSet (n : NNReal) δ ((n + 1 : ENNReal)⁻¹))ᶜ ≤ G ω) ∧
        ∫⁻ ω, G ω ∂μ ≤ ENNReal.ofReal a)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set (ContinuousPath (Vec d)), IsCompact K ∧
      ∀ N : ℕ, ∃ G : Ω → ENNReal, Measurable G ∧
        (∀ ω, ∀ x ∈ B, KN N (ω, x) Kᶜ ≤ G ω) ∧
        ∫⁻ ω, G ω ∂μ ≤ ENNReal.ofReal ε := by
  classical
  have he : ∀ n : ℕ, 0 < ε * (1 / 2 : ℝ) ^ (n + 1) := fun n => by positivity
  choose δ hδ hrest using fun n => hmod n (ε * (1 / 2 : ℝ) ^ (n + 1)) (he n)
  choose G hG hpoint hmoment using fun n N => hrest n N
  let rho : ℕ → ENNReal := fun n => (n + 1 : ENNReal)⁻¹
  have hrho : Tendsto rho atTop (𝓝 0) := by
    simpa [rho] using ((tendsto_add_atTop_iff_nat
      (f := fun n : ℕ => (n : ENNReal)⁻¹) (l := 𝓝 (0 : ENNReal)) 1).2
        ENNReal.tendsto_inv_nat_nhds_zero)
  let K := ContinuousPath.moduliSet B δ rho
  have hK : IsCompact K := ContinuousPath.isCompact_moduliSet hB hδ hrho
  have hcompl : Kᶜ = {p : ContinuousPath (Vec d) | p 0 ∉ B} ∪
      ⋃ n : ℕ, (ContinuousPath.modulusSet (n : NNReal) (δ n) (rho n))ᶜ := by
    ext p
    simp only [K, ContinuousPath.moduliSet, mem_compl_iff, mem_inter_iff, mem_iInter,
      mem_setOf_eq, mem_union, mem_iUnion, not_and_or, not_forall]
  have hsum : (∑' n : ℕ, ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (n + 1))) = ENNReal.ofReal ε := by
    have hsumm : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
      simpa only [pow_succ] using (summable_geometric_two.mul_right (1 / 2 : ℝ))
    have hs : (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1)) = 1 := by
      rw [tsum_congr (fun n => by rw [pow_succ]), tsum_mul_right, tsum_geometric_two]
      norm_num
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (he n).le) (hsumm.mul_left ε),
      tsum_mul_left, hs, mul_one]
  refine ⟨K, hK, ?_⟩
  intro N
  let F : Ω → ENNReal := fun ω => ∑' n : ℕ, G n N ω
  have hF : Measurable F := Measurable.ennreal_tsum fun n => hG n N
  have hFpoint : ∀ᵐ ω ∂μ, ∀ x ∈ B, KN N (ω, x) Kᶜ ≤ F ω := by
    filter_upwards [hstart, ae_all_iff.mpr (fun n => hpoint n N)] with ω hω hωpoint
    intro x hx
    have hz : KN N (ω, x) {p : ContinuousPath (Vec d) | p 0 ∉ B} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hω N x hx] with p hp
      simpa only [mem_setOf_eq, not_not, hp] using hx
    rw [hcompl]
    calc
      KN N (ω, x) ({p : ContinuousPath (Vec d) | p 0 ∉ B} ∪
          ⋃ n : ℕ, (ContinuousPath.modulusSet (n : NNReal) (δ n) (rho n))ᶜ) ≤
          KN N (ω, x) {p : ContinuousPath (Vec d) | p 0 ∉ B} +
          KN N (ω, x) (⋃ n : ℕ, (ContinuousPath.modulusSet (n : NNReal) (δ n) (rho n))ᶜ) :=
        measure_union_le _ _
      _ ≤ F ω := by
        rw [hz, zero_add]
        exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum (fun n => hωpoint n x hx))
  have hint : ∫⁻ ω, F ω ∂μ ≤ ENNReal.ofReal ε := by
    calc
      (∫⁻ ω, F ω ∂μ) = ∑' n : ℕ, ∫⁻ ω, G n N ω ∂μ :=
        lintegral_tsum fun n => (hG n N).aemeasurable
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (n + 1)) :=
        ENNReal.tsum_le_tsum (fun n => hmoment n N)
      _ = ENNReal.ofReal ε := hsum
  haveI := hKN N
  obtain ⟨Gout, hGout, hGoutpoint, hGoutint⟩ := measurable_majorant_of_ae μ B
    (fun ω x => KN N (ω, x) Kᶜ) F hF hFpoint
    (fun ω x => (measure_mono (subset_univ _)).trans (by simp))
  exact ⟨Gout, hGout, hGoutpoint, hGoutint.trans_le hint⟩

end SubdiffusiveProcess.Section10.PhysicalTightness
