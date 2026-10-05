module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.prop_as_response_bank_cauchy

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/--
Scope and inputs: the measurable Cauchy-in-probability completion used; `P` is a probability measure; the index family is countable;
the Cauchy input is the conclusion of `prop_as_response_bank_cauchy`;
measurability and pointwise nonnegativity of every finite response are carried
inputs from the concrete variational response carriers; the measurable
nonnegative representative and convergence in measure are conclusions here. This is a proof-step child of
`prop_as_response_bank`, not an assumed response limit.
The finite-family application supplies the eight response/coefficient cases.
-/
theorem prop_as_response_bank_limit_completion
    {Ω I : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] [Countable I]
    (Z : I → ℕ → Ω → ℝ)
    (hZ : ∀ i N, Measurable (Z i N))
    (hZnonneg : ∀ i N ω, 0 ≤ Z i N ω)
    (hCauchy : ∀ i : I, ∀ a b : ℝ, 0 < a → 0 < b →
      ∃ J : ℕ, ∀ M M' : ℕ, J ≤ M → J ≤ M' →
        P {ω | a < |Z i M ω - Z i M' ω|} ≤ ENNReal.ofReal b) :
    ∃ L : I → Ω → ℝ,
      (∀ i, Measurable (L i)) ∧
      (∀ i ω, 0 ≤ L i ω) ∧
      (∀ i, TendstoInMeasure P (Z i) atTop (L i)) := by
  have hscalar : ∀ i : I, ∃ L : Ω → ℝ,
      Measurable L ∧ (∀ ω, 0 ≤ L ω) ∧ TendstoInMeasure P (Z i) atTop L := by
    intro i
    let f : ℕ → Ω → ℝ := Z i
    have hf : ∀ n, Measurable (f n) := by
      intro n
      exact hZ i n
    have hfnn : ∀ n ω, 0 ≤ f n ω := by
      intro n ω
      exact hZnonneg i n ω
    have hC : ∀ a b : ℝ, 0 < a → 0 < b →
        ∃ J : ℕ, ∀ M M' : ℕ, J ≤ M → J ≤ M' →
          P {ω | a < |f M ω - f M' ω|} ≤ ENNReal.ofReal b := by
      intro a b ha hb
      exact hCauchy i a b ha hb
    have hJpos : ∀ k : ℕ, 0 < (1 / 2 : ℝ) ^ (k + 1) := by
      intro k
      positivity
    choose J hJ using fun k : ℕ =>
      hC ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ (k + 1))
        (hJpos k) (hJpos k)
    let φ : ℕ → ℕ := fun k =>
      Nat.rec (J 0) (fun k a => max (a + 1) (J (k + 1))) k
    have hφ_zero : φ 0 = J 0 := by
      simp [φ]
    have hφ_succ : ∀ k : ℕ, φ (k + 1) = max (φ k + 1) (J (k + 1)) := by
      intro k
      simp [φ]
    have hφ_dom : ∀ k : ℕ, J k ≤ φ k := by
      intro k
      induction k with
      | zero => simp [hφ_zero]
      | succ k ih =>
          rw [hφ_succ k]
          exact le_max_right _ _
    have hφ_lt : ∀ k : ℕ, φ k < φ (k + 1) := by
      intro k
      rw [hφ_succ k]
      exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    have hφ_strict : StrictMono φ := strictMono_nat_of_lt_succ hφ_lt
    have hφ_top : Tendsto φ atTop atTop := hφ_strict.tendsto_atTop
    let S : ℕ → Set Ω := fun k =>
      {ω | (1 / 2 : ℝ) ^ (k + 1) <
        |f (φ k) ω - f (φ (k + 1)) ω|}
    have hSbound : ∀ k : ℕ,
        P (S k) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) := by
      intro k
      exact hJ k (φ k) (φ (k + 1)) (hφ_dom k)
        ((hφ_dom k).trans (Nat.le_of_lt (hφ_lt k)))
    have hsummable : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) := by
      simpa only [pow_succ'] using
        (summable_geometric_two.mul_left (1 / 2 : ℝ))
    have hsum : (∑' k : ℕ, P (S k)) ≠ ∞ := by
      have hsum_le : (∑' k : ℕ, P (S k)) ≤
          ENNReal.ofReal (∑' k : ℕ, (1 / 2 : ℝ) ^ (k + 1)) := by
        calc
          (∑' k : ℕ, P (S k)) ≤
              ∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) :=
            ENNReal.tsum_le_tsum hSbound
          _ = ENNReal.ofReal (∑' k : ℕ, (1 / 2 : ℝ) ^ (k + 1)) :=
            (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsummable).symm
      have hgeom : (∑' k : ℕ, (1 / 2 : ℝ) ^ (k + 1)) = 1 := by
        rw [show (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) =
            fun k => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k by
              funext k
              rw [pow_succ']]
        rw [tsum_mul_left, tsum_geometric_two]
        norm_num
      rw [hgeom] at hsum_le
      exact ne_top_of_le_ne_top (by simp) hsum_le
    have hlimsup : P (Filter.limsup S atTop) = 0 :=
      MeasureTheory.measure_limsup_atTop_eq_zero hsum
    have hgood : ∀ᵐ ω : Ω ∂P, ∀ᶠ k : ℕ in atTop, ω ∉ S k := by
      rw [ae_iff]
      apply measure_mono_null _ hlimsup
      intro ω hω
      exact Filter.mem_limsup_iff_frequently_mem.mpr (show
        ∃ᶠ k : ℕ in atTop, ω ∈ S k from hω)
    have hcau : ∀ᵐ ω : Ω ∂P,
        CauchySeq (fun k => f (φ k) ω) := by
      filter_upwards [hgood] with ω hω
      obtain ⟨K, hK⟩ := eventually_atTop.1 hω
      have hshift : CauchySeq (fun k => f (φ (k + K)) ω) := by
        apply cauchySeq_of_dist_le_of_summable
          (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1))
        · intro k
          have hnot : ω ∉ S (k + K) := hK (k + K) (Nat.le_add_left K k)
          have hstep :
              |f (φ (k + K)) ω - f (φ (k + K + 1)) ω| ≤
                (1 / 2 : ℝ) ^ (k + K + 1) := by
            exact le_of_not_gt (by
              simpa [S, add_assoc, add_comm k K, add_left_comm k K] using hnot)
          have hpow : (1 / 2 : ℝ) ^ (k + K + 1) ≤
              (1 / 2 : ℝ) ^ (k + 1) := by
            exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
          rw [dist_eq_norm, Real.norm_eq_abs]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep.trans hpow
        · simpa only [pow_succ'] using
            (summable_geometric_two.mul_left (1 / 2 : ℝ))
      exact (cauchySeq_shift K).mp hshift
    have hlim_exists : ∀ᵐ ω : Ω ∂P, ∃ l : ℝ,
        Tendsto (fun k => f (φ k) ω) atTop (𝓝 l) := by
      filter_upwards [hcau] with ω hω
      exact ⟨limUnder atTop (fun k => f (φ k) ω), hω.tendsto_limUnder⟩
    obtain ⟨Lraw, hLraw_strong, hLraw_ae⟩ :=
      exists_stronglyMeasurable_limit_of_tendsto_ae
        (fun k => (hf (φ k)).aestronglyMeasurable) hlim_exists
    have hLraw_meas : Measurable Lraw := hLraw_strong.measurable
    have hLraw_nonneg : ∀ᵐ ω : Ω ∂P, 0 ≤ Lraw ω := by
      filter_upwards [hLraw_ae] with ω hω
      exact isClosed_Ici.mem_of_tendsto hω
        (Eventually.of_forall fun k => hfnn (φ k) ω)
    let L : Ω → ℝ := fun ω => max (Lraw ω) 0
    have hLmeas : Measurable L := hLraw_meas.max measurable_const
    have hLnonneg : ∀ ω, 0 ≤ L ω := by
      intro ω
      exact le_max_right _ _
    have hLraw_eq : Lraw =ᵐ[P] L := by
      filter_upwards [hLraw_nonneg] with ω hω
      simp [L, max_eq_left hω]
    have hsub : TendstoInMeasure P (fun k => f (φ k)) atTop L := by
      exact TendstoInMeasure.congr_right hLraw_eq
        (tendstoInMeasure_of_tendsto_ae
          (fun k => (hf (φ k)).aestronglyMeasurable) hLraw_ae)
    have hfull : TendstoInMeasure P f atTop L := by
      apply tendstoInMeasure_iff_dist.mpr
      intro ε hε
      rw [ENNReal.tendsto_atTop_zero]
      intro δ hδ
      by_cases hδtop : δ = ∞
      · exact ⟨0, fun M hM => by rw [hδtop]; exact le_top⟩
      have hδpos : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδtop
      let b : ℝ := δ.toReal / 4
      have hb : 0 < b := by
        dsimp [b]
        linarith
      obtain ⟨J₀, hJ₀⟩ := hC (ε / 2) b (by linarith) hb
      have hsub_dist := (tendstoInMeasure_iff_dist.mp hsub) (ε / 2) (by linarith)
      obtain ⟨K₀, hK₀⟩ := ENNReal.tendsto_atTop_zero.mp hsub_dist
        (ENNReal.ofReal b) (ENNReal.ofReal_pos.mpr hb)
      have hφ_event : ∀ᶠ k : ℕ in atTop, J₀ ≤ φ k :=
        hφ_top.eventually (Filter.eventually_ge_atTop J₀)
      obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hφ_event
      refine ⟨max J₀ (max K₀ k₀), fun M hM => ?_⟩
      let k : ℕ := max K₀ k₀
      have hMJ : J₀ ≤ M := (le_max_left _ _).trans hM
      have hkK : K₀ ≤ k := le_max_left _ _
      have hkk₀ : k₀ ≤ k := le_max_right _ _
      have hkJ : J₀ ≤ φ k := hk₀ k hkk₀
      let A : Set Ω := {ω | ε / 2 < |f M ω - f (φ k) ω|}
      let B : Set Ω := {ω | ε / 2 ≤ dist (f (φ k) ω) (L ω)}
      have hsubsets : {ω | ε ≤ dist (f M ω) (L ω)} ⊆ A ∪ B := by
        intro ω hω
        by_cases hA : ω ∈ A
        · exact Or.inl hA
        · right
          by_contra hB
          have hA' : dist (f M ω) (f (φ k) ω) ≤ ε / 2 := by
            rw [dist_eq_norm, Real.norm_eq_abs]
            exact le_of_not_gt hA
          have hB' : dist (f (φ k) ω) (L ω) < ε / 2 := lt_of_not_ge hB
          have hlt : dist (f M ω) (L ω) < ε := by
            calc
              dist (f M ω) (L ω) ≤
                  dist (f M ω) (f (φ k) ω) + dist (f (φ k) ω) (L ω) :=
                dist_triangle _ _ _
              _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hA' hB'
              _ = ε := by ring
          exact (not_lt_of_ge hω) hlt
      have hAmeasure : P A ≤ ENNReal.ofReal b := by
        exact hJ₀ M (φ k) hMJ hkJ
      have hBmeasure : P B ≤ ENNReal.ofReal b := hK₀ k hkK
      calc
        P {ω | ε ≤ dist (f M ω) (L ω)} ≤ P (A ∪ B) := measure_mono hsubsets
        _ ≤ P A + P B := measure_union_le _ _
        _ ≤ ENNReal.ofReal b + ENNReal.ofReal b := add_le_add hAmeasure hBmeasure
        _ = ENNReal.ofReal (b + b) := (ENNReal.ofReal_add hb.le hb.le).symm
        _ ≤ ENNReal.ofReal δ.toReal := ENNReal.ofReal_le_ofReal (by
          dsimp [b]
          linarith)
        _ = δ := ENNReal.ofReal_toReal hδtop
    exact ⟨L, hLmeas, hLnonneg, hfull⟩
  choose L hLmeas hLnonneg hLconv using hscalar
  exact ⟨L, hLmeas, hLnonneg, hLconv⟩

end SubdiffusiveProcess.Paper
