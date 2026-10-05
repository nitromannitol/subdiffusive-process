module

public import SubdiffusiveProcess.Probability.ProkhorovTight
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

@[expose] public section

/-!
# Compact random sets of path laws from annealed uniform tightness

This is §8 Step 4, using the existing Prokhorov theorem. The argument only needs
measurable majorants, so the event with an uncountable set of starting points is
controlled without asserting its measurability. No process attachment is assumed.
-/

open Filter MeasureTheory ProbabilityTheory Topology Set
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness

/-- A closed, uniformly tight set of probability measures on a Polish space is compact
(Prokhorov, from `classical_prokhorov_sequential` and the pseudo-metrizability of the weak topology). -/
theorem isCompact_of_closed_tight
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : Set (ProbabilityMeasure X)) (hS : IsClosed S)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ K : Set X, IsCompact K ∧
      ∀ P ∈ S, (P : Measure X) Kᶜ ≤ ENNReal.ofReal ε) : IsCompact S := by
  let : PseudoMetricSpace (ProbabilityMeasure X) :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric (ProbabilityMeasure X)
  rw [isCompact_iff_isSeqCompact]
  intro mu hmu
  have htightSet : IsTightMeasureSet (Set.range (fun n => (mu n : Measure X))) := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    by_cases hεtop : ε = ⊤
    · refine ⟨∅, isCompact_empty, fun ν _ => ?_⟩
      rw [hεtop]; exact le_top
    · obtain ⟨K, hK, hKS⟩ := htight ε.toReal (ENNReal.toReal_pos hε.ne' hεtop)
      refine ⟨K, hK, ?_⟩
      rintro ν ⟨n, rfl⟩
      exact (hKS (mu n) (hmu n)).trans (by rw [ENNReal.ofReal_toReal hεtop])
  obtain ⟨seq, nu, hseq, hlim⟩ := SubdiffusiveProcess.Probability.prokhorov_sequential mu htightSet
  exact ⟨nu, hS.mem_of_tendsto hlim (Eventually.of_forall fun n => hmu (seq n)), seq, hseq, hlim⟩

/-- Annealed uniform tightness yields compact sets of quenched laws with the
supremum over all starts inside the bad event. -/
theorem exists_compact_random_laws {Ω Z X : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure Ω) (P : ℕ → Ω → Z → ProbabilityMeasure X) (B : Set Z)
    (hpath : ∀ eps : ℝ, 0 < eps →
      ∃ Kset : Set X, IsCompact Kset ∧
        ∀ N : ℕ, ∃ G : Ω → ENNReal, Measurable G ∧
          (∀ omega, ∀ x ∈ B, (P N omega x : Measure X) Ksetᶜ ≤ G omega) ∧
          ∫⁻ omega, G omega ∂μ ≤ ENNReal.ofReal eps) :
    ∀ eta : ℝ, 0 < eta →
      ∃ Keta : Set (ProbabilityMeasure X), IsCompact Keta ∧
        ∀ N : ℕ, μ {omega | ∃ x ∈ B, P N omega x ∉ Keta} ≤ ENNReal.ofReal eta := by
  intro eta heta
  let delta : ℕ → ℝ := fun k => eta * (1 / 2 : ℝ) ^ (k + 1)
  have hdelta : ∀ k, 0 < delta k := by
    intro k
    dsimp [delta]
    positivity
  choose Kk hKk hKkbound using fun k =>
    hpath ((delta k) ^ 2) (pow_pos (hdelta k) 2)
  let Keta : Set (ProbabilityMeasure (X)) :=
    {mu : ProbabilityMeasure (X) |
      ∀ k : ℕ, (mu : Measure (X)) (Kk k)ᶜ ≤
        ENNReal.ofReal (delta k)}
  have hKeta_closed : IsClosed Keta := by
    refine IsSeqClosed.isClosed ?_
    intro u x hu hx k
    have hopen : IsOpen (Kk k)ᶜ := (hKk k).isClosed.isOpen_compl
    have hlim : (x : Measure (X)) (Kk k)ᶜ ≤
        liminf (fun n => (u n : Measure (X)) (Kk k)ᶜ) atTop :=
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto hx hopen
    have hbound : liminf (fun n => (u n : Measure (X)) (Kk k)ᶜ) atTop ≤
        ENNReal.ofReal (delta k) := by
      have hev : ∀ᶠ n in atTop,
          (u n : Measure (X)) (Kk k)ᶜ ≤ ENNReal.ofReal (delta k) :=
        Eventually.of_forall (fun n => hu n k)
      exact (liminf_le_liminf hev).trans_eq (liminf_const _)
    exact hlim.trans hbound
  have hKeta_tight : ∀ eps : ℝ, 0 < eps →
      ∃ Kset' : Set (X), IsCompact Kset' ∧
        ∀ Pm ∈ Keta, (Pm : Measure (X)) Kset'ᶜ ≤ ENNReal.ofReal eps := by
    intro eps heps
    have hratio : 0 < eps / eta := div_pos heps heta
    have hpow : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hev : ∀ᶠ k : ℕ in atTop, (1 / 2 : ℝ) ^ k < eps / eta :=
      (tendsto_order.1 hpow).2 (eps / eta) hratio
    obtain ⟨k, hk⟩ := hev.exists
    have hpowmono : (1 / 2 : ℝ) ^ (k + 1) ≤ (1 / 2 : ℝ) ^ k := by
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k)
    have hdeltaeps : delta k ≤ eps := by
      dsimp [delta]
      exact le_of_lt (calc
        eta * (1 / 2 : ℝ) ^ (k + 1) ≤ eta * (1 / 2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left hpowmono heta.le
        _ < eta * (eps / eta) := mul_lt_mul_of_pos_left hk heta
        _ = eps := mul_div_cancel₀ eps heta.ne')
    exact ⟨Kk k, hKk k, fun Pm hPm =>
      (hPm k).trans (ENNReal.ofReal_le_ofReal hdeltaeps)⟩
  have hbad : ∀ N k : ℕ,
      μ
          {omega : Ω |
            ENNReal.ofReal (delta k) <
              ⨆ x ∈ B, (P N omega x : Measure X) (Kk k)ᶜ} ≤
        ENNReal.ofReal (delta k) := by
    intro N k
    obtain ⟨G, hG, hpoint, hGint⟩ := hKkbound k N
    let μ := μ
    have hsup : ∀ omega : Ω,
        (⨆ x ∈ B, (P N omega x : Measure X) (Kk k)ᶜ) ≤ G omega := by
      intro omega
      refine iSup₂_le fun x hx => ?_
      exact hpoint omega x hx
    have hsub : {omega : Ω |
          ENNReal.ofReal (delta k) <
            ⨆ x ∈ B, (P N omega x : Measure X) (Kk k)ᶜ} ⊆
        {omega : Ω | ENNReal.ofReal (delta k) ≤ G omega} := by
      intro omega homega
      exact le_trans (le_of_lt homega) (hsup omega)
    have hmarkov : μ {omega : Ω | ENNReal.ofReal (delta k) ≤ G omega} ≤
        (∫⁻ omega, G omega ∂μ) / ENNReal.ofReal (delta k) :=
      meas_ge_le_lintegral_div hG.aemeasurable
        (ENNReal.ofReal_pos.mpr (hdelta k)).ne' ENNReal.ofReal_ne_top
    have hprod : (∫⁻ omega, G omega ∂μ) ≤
        ENNReal.ofReal (delta k) * ENNReal.ofReal (delta k) := by
      calc
        (∫⁻ omega, G omega ∂μ) ≤ ENNReal.ofReal ((delta k) ^ 2) := hGint
        _ = ENNReal.ofReal (delta k) * ENNReal.ofReal (delta k) := by
          rw [pow_two, ENNReal.ofReal_mul (hdelta k).le]
    exact (measure_mono hsub).trans (hmarkov.trans (ENNReal.div_le_of_le_mul hprod))
  refine ⟨Keta, isCompact_of_closed_tight Keta hKeta_closed hKeta_tight, ?_⟩
  intro N
  have hsub : {omega : Ω | ∃ x ∈ B,
        P N omega x ∉ Keta} ⊆
      ⋃ k : ℕ, {omega : Ω |
        ENNReal.ofReal (delta k) <
          ⨆ x ∈ B, (P N omega x : Measure X) (Kk k)ᶜ} := by
    intro omega homega
    obtain ⟨x, hxB, hxK⟩ := homega
    have hxK' : ¬ ∀ k : ℕ,
        ((P N omega x :
          ProbabilityMeasure (X)) : Measure (X)) (Kk k)ᶜ ≤
          ENNReal.ofReal (delta k) := by
      simpa [Keta] using hxK
    push Not at hxK'
    obtain ⟨k, hk⟩ := hxK'
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    exact lt_of_lt_of_le hk (le_iSup₂_of_le x hxB le_rfl)
  calc
    μ {omega : Ω | ∃ x ∈ B,
        P N omega x ∉ Keta} ≤
      μ (⋃ k : ℕ, {omega : Ω |
        ENNReal.ofReal (delta k) <
          ⨆ x ∈ B, (P N omega x : Measure X) (Kk k)ᶜ}) := measure_mono hsub
    _ ≤ ∑' k : ℕ,
        μ {omega : Ω |
          ENNReal.ofReal (delta k) <
            ⨆ x ∈ B, (P N omega x : Measure X) (Kk k)ᶜ} :=
      measure_iUnion_le (μ := μ) _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (delta k) :=
      ENNReal.tsum_le_tsum (fun k => hbad N k)
    _ = ENNReal.ofReal eta := by
      dsimp [delta]
      have hsumm : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) := by
        simpa [pow_succ, mul_comm] using
          (summable_geometric_two.mul_left (1 / 2 : ℝ))
      have hsum : (∑' k : ℕ, (1 / 2 : ℝ) ^ (k + 1)) = 1 := by
        rw [tsum_congr (fun k => by rw [pow_succ]), tsum_mul_right,
          tsum_geometric_two]
        norm_num
      have hsumm' : Summable (fun k : ℕ => eta * (1 / 2 : ℝ) ^ (k + 1)) :=
        hsumm.mul_left eta
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsumm',
        tsum_mul_left, hsum, mul_one]

end SubdiffusiveProcess.Section10.PhysicalTightness
