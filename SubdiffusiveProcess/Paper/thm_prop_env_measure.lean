module

public import SubdiffusiveProcess.Paper.thm_prop_base
public import SubdiffusiveProcess.Paper.conv_represented_env_interface
public import SubdiffusiveProcess.Paper.conv_represented_env_interface_grids
public import SubdiffusiveProcess.Paper.conv_represented_catalogue_grids
public import SubdiffusiveProcess.Paper.conv_represented_joint_buffered
public import SubdiffusiveProcess.Paper.conv_represented_joint_grids_buffered
public import SubdiffusiveProcess.Paper.conv_represented_limit_planes
public import SubdiffusiveProcess.Paper.limit_form_package_controls
public import SubdiffusiveProcess.Paper.limit_form_package_side
public import SubdiffusiveProcess.EllipticRegularity.GoodCellCatalogue
public import Mathlib
public import SubdiffusiveProcess.Probability.ConvergenceInProbability
public import SubdiffusiveProcess.Paper.represented_same_law_in_measure

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section Part0
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- Finite sums of sequences converging in measure converge in measure. -/
theorem aux_env_tendstoInMeasure_finset_sum {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (s : Finset ι) (f : ι → ℕ → Ω → ℝ) (g : ι → Ω → ℝ)
    (h : ∀ i ∈ s, TendstoInMeasure P (f i) atTop (g i)) :
    TendstoInMeasure P (fun n ω => ∑ i ∈ s, f i n ω) atTop (fun ω => ∑ i ∈ s, g i ω) := by
  classical
  have hadd : ∀ (a b : ℕ → Ω → ℝ) (c d : Ω → ℝ),
      TendstoInMeasure P a atTop c → TendstoInMeasure P b atTop d →
      TendstoInMeasure P (fun n ω => a n ω + b n ω) atTop (fun ω => c ω + d ω) := by
    intro a b c d ha hb
    rw [tendstoInMeasure_iff_dist] at ha hb ⊢
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    have h1 := ha (ε / 2) hε2
    have h2 := hb (ε / 2) hε2
    have hsum : Tendsto (fun n => P {x | ε / 2 ≤ dist (a n x) (c x)} + P {x | ε / 2 ≤ dist (b n x) (d x)}) atTop (𝓝 0) := by
      simpa using Tendsto.add h1 h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun n => zero_le) ?_
    intro n
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro x hx
    simp only [mem_ofPred_eq] at hx ⊢
    rw [Set.mem_union]
    by_contra hc
    rw [not_or] at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hd1 : dist (a n x) (c x) < ε / 2 := lt_of_not_ge hc1
    have hd2 : dist (b n x) (d x) < ε / 2 := lt_of_not_ge hc2
    have hd := dist_add_add_le (a n x) (b n x) (c x) (d x)
    linarith
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    have hset : {x : Ω | ε ≤ dist ((0:ℝ)) 0} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le, dist_self]
      exact hε
    simp only [Finset.sum_empty]
    rw [hset]
    simp only [measure_empty]
    exact tendsto_const_nhds
  · intro a s ha ih h
    have hsa : TendstoInMeasure P (f a) atTop (g a) := h a (Finset.mem_insert_self a s)
    have his : TendstoInMeasure P (fun n ω => ∑ i ∈ s, f i n ω) atTop (fun ω => ∑ i ∈ s, g i ω) :=
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hstep := hadd (f a) (fun n ω => ∑ i ∈ s, f i n ω) (g a) (fun ω => ∑ i ∈ s, g i ω) hsa his
    simpa only [Finset.sum_insert ha] using hstep

end Part0

section Part1
open Filter MeasureTheory Set Topology
open scoped ENNReal

/-- Convergence in measure is stable under a convergent deterministic scalar factor and a fixed finite factor. -/
theorem aux_env_tendstoInMeasure_mul2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hXY : TendstoInMeasure P X atTop Y) (hYm : AEMeasurable Y P)
    (rhon : ℕ → ℝ) (rho : ℝ) (hrho : Tendsto rhon atTop (𝓝 rho))
    (w : Ω → ℝ) (hw : Measurable w) :
    TendstoInMeasure P (fun n ω => w ω * (rhon n * X n ω)) atTop
      (fun ω => w ω * (rho * Y ω)) := by
  rw [SubdiffusiveProcess.Probability.tendstoInMeasure_iff_probability_bounds]
  intro ε hε δ hδ
  have hδ3 : (0 : ℝ) < δ / 3 := by linarith
  obtain ⟨L, hL1, hwL⟩ : ∃ L : ℕ, 1 ≤ L ∧ P {ω : Ω | (L : ℝ) < |w ω|} ≤ ENNReal.ofReal (δ / 3) := by
    have hanti : Antitone (fun L : ℕ => {ω : Ω | (L : ℝ) < |w ω|}) := by
      intro a b hab ω h
      simp only [mem_ofPred_eq] at h ⊢
      have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      linarith
    have hmeas : ∀ L : ℕ, NullMeasurableSet {ω : Ω | (L : ℝ) < |w ω|} P :=
      fun L => (measurableSet_lt measurable_const hw.abs).nullMeasurableSet
    have hinter : (⋂ L : ℕ, {ω : Ω | (L : ℝ) < |w ω|}) = ∅ := by
      ext ω
      simp only [Set.mem_iInter, mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall]
      obtain ⟨n, hn⟩ := exists_nat_gt |w ω|
      exact ⟨n, not_lt.mpr (le_of_lt hn)⟩
    have htend := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top P _⟩
    simp only [hinter, measure_empty] at htend
    have hlt : (0 : ℝ≥0∞) < ENNReal.ofReal (δ / 3) := ENNReal.ofReal_pos.mpr hδ3
    have hev : ∀ᶠ L : ℕ in atTop, P {ω : Ω | (L : ℝ) < |w ω|} < ENNReal.ofReal (δ / 3) :=
      (tendsto_order.mp htend).2 (ENNReal.ofReal (δ / 3)) hlt
    rw [Filter.eventually_atTop] at hev
    obtain ⟨L0, hL0⟩ := hev
    exact ⟨max L0 1, le_max_right _ _, le_of_lt (hL0 _ (le_max_left _ _))⟩
  set Y' : Ω → ℝ := AEMeasurable.mk Y hYm with hY'def
  have hY'meas : Measurable Y' := by rw [hY'def]; exact hYm.measurable_mk
  have hYae : Y =ᵐ[P] Y' := by rw [hY'def]; exact hYm.ae_eq_mk
  obtain ⟨T, hT1, hYT⟩ : ∃ T : ℕ, 1 ≤ T ∧ P {ω : Ω | (T : ℝ) < |Y ω|} ≤ ENNReal.ofReal (δ / 3) := by
    have hanti : Antitone (fun T : ℕ => {ω : Ω | (T : ℝ) < |Y' ω|}) := by
      intro a b hab ω h
      simp only [mem_ofPred_eq] at h ⊢
      have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      linarith
    have hmeas : ∀ T : ℕ, NullMeasurableSet {ω : Ω | (T : ℝ) < |Y' ω|} P :=
      fun T => (measurableSet_lt measurable_const hY'meas.abs).nullMeasurableSet
    have hinter : (⋂ T : ℕ, {ω : Ω | (T : ℝ) < |Y' ω|}) = ∅ := by
      ext ω
      simp only [Set.mem_iInter, mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall]
      obtain ⟨n, hn⟩ := exists_nat_gt |Y' ω|
      exact ⟨n, not_lt.mpr (le_of_lt hn)⟩
    have htend := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top P _⟩
    simp only [hinter, measure_empty] at htend
    have hlt : (0 : ℝ≥0∞) < ENNReal.ofReal (δ / 3) := ENNReal.ofReal_pos.mpr hδ3
    have hev : ∀ᶠ T : ℕ in atTop, P {ω : Ω | (T : ℝ) < |Y' ω|} < ENNReal.ofReal (δ / 3) :=
      (tendsto_order.mp htend).2 (ENNReal.ofReal (δ / 3)) hlt
    rw [Filter.eventually_atTop] at hev
    obtain ⟨T0, hT0⟩ := hev
    refine ⟨max T0 1, le_max_right _ _, ?_⟩
    have hcongr : P {ω : Ω | ((max T0 1 : ℕ) : ℝ) < |Y ω|} = P {ω : Ω | ((max T0 1 : ℕ) : ℝ) < |Y' ω|} := by
      apply measure_congr
      rw [eventuallyEqSet_iff]
      filter_upwards [hYae] with ω h
      rw [h]
    rw [hcongr]
    exact le_of_lt (hT0 _ (le_max_left _ _))
  set B : ℝ := |rho| + 1 with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  have hBne : B ≠ 0 := ne_of_gt hBpos
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLpos
  set η : ℝ := ε / (2 * (L : ℝ) * (T : ℝ) + 1) with hη
  have hηpos : 0 < η := by
    rw [hη]
    exact div_pos hε (by nlinarith [hLpos, hTpos])
  have hbdd : ∀ᶠ n : ℕ in atTop, |rhon n| ≤ B := by
    have h1 : ∀ᶠ n : ℕ in atTop, dist (rhon n) rho < 1 := by
      rw [Filter.eventually_atTop]
      exact (Metric.tendsto_atTop.mp hrho) 1 one_pos
    filter_upwards [h1] with n hn
    rw [Real.dist_eq] at hn
    rw [hB]
    have h2 : (rhon n - rho) + rho = rhon n := by ring
    calc |rhon n| = |(rhon n - rho) + rho| := by rw [h2]
      _ ≤ |rhon n - rho| + |rho| := abs_add_le _ _
      _ ≤ 1 + |rho| := by linarith
      _ = |rho| + 1 := by ring
  have hconv : ∀ᶠ n : ℕ in atTop, |rhon n - rho| ≤ η := by
    have h1 : ∀ᶠ n : ℕ in atTop, dist (rhon n) rho < η := by
      rw [Filter.eventually_atTop]
      exact (Metric.tendsto_atTop.mp hrho) η hηpos
    filter_upwards [h1] with n hn
    rw [Real.dist_eq] at hn
    exact le_of_lt hn
  set ε' : ℝ := ε / (2 * (L : ℝ) * B) with hε'
  have hε'pos : 0 < ε' := by
    rw [hε']
    exact div_pos hε (by nlinarith [hLpos, hBpos])
  obtain ⟨N₀, hN₀⟩ := (SubdiffusiveProcess.Probability.tendstoInMeasure_iff_probability_bounds P X Y).mp hXY ε' hε'pos (δ / 3) hδ3
  rw [Filter.eventually_atTop] at hbdd hconv
  obtain ⟨Nb, hNb⟩ := hbdd
  obtain ⟨Nc, hNc⟩ := hconv
  refine ⟨max (max N₀ Nb) Nc, ?_⟩
  intro N hN
  have hN₀' : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb' : Nb ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNc' : Nc ≤ N := le_trans (le_max_right _ _) hN
  have hrh1 : |rhon N| ≤ B := hNb N hNb'
  have hrh2 : |rhon N - rho| ≤ η := hNc N hNc'
  have hX : P {ω : Ω | ε' ≤ dist (X N ω) (Y ω)} ≤ ENNReal.ofReal (δ / 3) := hN₀ N hN₀'
  have hsub : {ω : Ω | ε ≤ dist (w ω * (rhon N * X N ω)) (w ω * (rho * Y ω))} ⊆
      {ω : Ω | (L : ℝ) < |w ω|} ∪ {ω : Ω | (T : ℝ) < |Y ω|} ∪ {ω : Ω | ε' ≤ dist (X N ω) (Y ω)} := by
    intro ω hω
    rw [mem_ofPred_eq] at hω
    by_cases h1 : (L : ℝ) < |w ω|
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : (T : ℝ) < |Y ω|
      · exact Or.inl (Or.inr h2)
      · by_cases h3 : ε' ≤ dist (X N ω) (Y ω)
        · exact Or.inr h3
        · exfalso
          push Not at h1 h2 h3
          have h3' : |X N ω - Y ω| < ε' := by rw [Real.dist_eq] at h3; exact h3
          have hbd : dist (w ω * (rhon N * X N ω)) (w ω * (rho * Y ω)) < ε := by
            have hdec : rhon N * X N ω - rho * Y ω = rhon N * (X N ω - Y ω) + (rhon N - rho) * Y ω := by ring
            have hmid : |rhon N * X N ω - rho * Y ω| ≤ B * ε' + η * T := by
              calc |rhon N * X N ω - rho * Y ω|
                  = |rhon N * (X N ω - Y ω) + (rhon N - rho) * Y ω| := by rw [hdec]
                _ ≤ |rhon N * (X N ω - Y ω)| + |(rhon N - rho) * Y ω| := abs_add_le _ _
                _ = |rhon N| * |X N ω - Y ω| + |rhon N - rho| * |Y ω| := by rw [abs_mul, abs_mul]
                _ ≤ B * ε' + η * T := by
                    apply add_le_add
                    · exact mul_le_mul hrh1 (le_of_lt h3') (abs_nonneg _) (le_of_lt hBpos)
                    · exact mul_le_mul hrh2 h2 (abs_nonneg _) (le_of_lt hηpos)
            have hmain : |w ω| * |rhon N * X N ω - rho * Y ω| ≤ (L : ℝ) * (B * ε' + η * T) :=
              mul_le_mul h1 hmid (abs_nonneg _) (le_of_lt hLpos)
            have hBe : B * ε' = ε / (2 * (L : ℝ)) := by
              rw [hε']; field_simp
            have hLBe : (L : ℝ) * (B * ε') = ε / 2 := by
              rw [hBe]; field_simp
            have hLe : (L : ℝ) * (η * (T : ℝ)) < ε / 2 := by
              rw [hη]
              rw [show (L : ℝ) * (ε / (2 * (L : ℝ) * (T : ℝ) + 1) * (T : ℝ))
                  = (L : ℝ) * (T : ℝ) * ε / (2 * (L : ℝ) * (T : ℝ) + 1) from by ring]
              rw [div_lt_iff₀ (by nlinarith [hLpos, hTpos])]
              nlinarith [mul_pos hLpos hTpos, hε]
            have hLtot : (L : ℝ) * (B * ε' + η * T) < ε := by
              rw [mul_add, hLBe]; linarith
            rw [Real.dist_eq, ← mul_sub, abs_mul]
            exact lt_of_le_of_lt hmain hLtot
          exact absurd hbd (not_lt.mpr hω)
  calc P {ω : Ω | ε ≤ dist (w ω * (rhon N * X N ω)) (w ω * (rho * Y ω))}
      ≤ P ({ω : Ω | (L : ℝ) < |w ω|} ∪ {ω : Ω | (T : ℝ) < |Y ω|} ∪ {ω : Ω | ε' ≤ dist (X N ω) (Y ω)}) :=
        measure_mono hsub
    _ ≤ P ({ω : Ω | (L : ℝ) < |w ω|} ∪ {ω : Ω | (T : ℝ) < |Y ω|}) + P {ω : Ω | ε' ≤ dist (X N ω) (Y ω)} :=
        measure_union_le _ _
    _ ≤ (P {ω : Ω | (L : ℝ) < |w ω|} + P {ω : Ω | (T : ℝ) < |Y ω|}) + P {ω : Ω | ε' ≤ dist (X N ω) (Y ω)} :=
        add_le_add (measure_union_le _ _) le_rfl
    _ ≤ (ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3)) + ENNReal.ofReal (δ / 3) :=
        add_le_add (add_le_add hwL hYT) hX
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (le_of_lt hδ3) (le_of_lt hδ3),
            ← ENNReal.ofReal_add (le_of_lt (show (0:ℝ) < δ / 3 + δ / 3 by linarith)) (le_of_lt hδ3)]
        congr 1
        ring

end Part1

section Part2
open Filter MeasureTheory Set Topology
open scoped ENNReal

/-- Countably many sequences converging in measure have a common subsequence converging a.e. -/
theorem aux_env_common_ae_subseq_of_inMeasure
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {P : Measure Ω} [IsFiniteMeasure P]
    (f : ι → ℕ → Ω → ℝ) (g : ι → Ω → ℝ)
    (h : ∀ i, TendstoInMeasure P (f i) atTop (g i)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, ∀ i, Tendsto (fun n => f i (φ n) ω) atTop (𝓝 (g i ω)) := by
  classical
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  let w : ι → ℝ := fun i => (1 / 2 : ℝ) ^ (e i + 1)
  have hwpos : ∀ i, 0 < w i := by intro i; dsimp only [w]; positivity
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hwpos i).le
  have hw1 : ∀ i, w i ≤ 1 := by
    intro i; dsimp only [w]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hwsumm : Summable w := by
    have hbase : Summable (fun i => (1/2:ℝ) ^ e i) :=
      (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)).comp_injective he
    have hw : w = fun i => (1/2:ℝ) * (1/2:ℝ) ^ e i := by
      funext i; dsimp only [w]; rw [pow_succ']
    rw [hw]; exact hbase.mul_left _
  have hwbound : (∑' i, w i) ≤ 1 := by
    have hbase : Summable (fun i => (1/2:ℝ) ^ e i) :=
      (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)).comp_injective he
    have hgeom : Summable (fun m : ℕ => (1/2:ℝ) ^ m) :=
      summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)
    have hle : (∑' i, (1/2:ℝ) ^ e i) ≤ ∑' m : ℕ, (1/2:ℝ) ^ m :=
      Summable.tsum_le_tsum_of_inj e he (fun m _ => by positivity)
        (fun i => le_rfl) hbase hgeom
    rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)] at hle
    have hsplit : (∑' i, w i) = (∑' i, (1/2:ℝ) ^ e i) * (1/2) := by
      have hw : w = (fun i => (1/2:ℝ) ^ e i * (1/2)) := by
        funext i; dsimp only [w]; rw [pow_succ]
      rw [hw, tsum_mul_right]
    rw [hsplit]; linarith
  have hsum_bound : ∀ (t : ι → ℝ) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) (s : Finset ι),
      (∑' i, w i * t i) ≤ ∑ i ∈ s, w i * t i + ((∑' i, w i) - ∑ i ∈ s, w i) := by
    intro t ht0 ht1 s
    have hwt : Summable (fun i => w i * t i) :=
      Summable.of_nonneg_of_le (fun i => mul_nonneg (hw0 i) (ht0 i))
        (fun i => mul_le_of_le_one_right (hw0 i) (ht1 i)) hwsumm
    have hsplit_t : (∑' i, w i * t i)
        = ∑ i ∈ s, w i * t i + ∑' (i : {i // i ∉ s}), w ↑i * t ↑i := by
      simpa using! (hwt.sum_add_tsum_compl (s := s)).symm
    have hsplit_w : (∑' (i : {i // i ∉ s}), w ↑i) = (∑' i, w i) - ∑ i ∈ s, w i := by
      have hh : ∑ x ∈ s, w x + ∑' (x : {i // i ∉ s}), w ↑x = ∑' (x : ι), w x := by
        simpa using! hwsumm.sum_add_tsum_compl (s := s)
      linarith
    have hsumm_g : Summable (fun i : {i // i ∉ s} => w ↑i) := hwsumm.comp_injective Subtype.val_injective
    have hsumm_f : Summable (fun i : {i // i ∉ s} => w ↑i * t ↑i) :=
      Summable.of_nonneg_of_le (fun i => mul_nonneg (hw0 _) (ht0 _))
        (fun i => mul_le_of_le_one_right (hw0 _) (ht1 _)) hsumm_g
    have hle : (∑' (i : {i // i ∉ s}), w ↑i * t ↑i) ≤ ∑' (i : {i // i ∉ s}), w ↑i :=
      Summable.tsum_le_tsum (fun i => mul_le_of_le_one_right (hw0 _) (ht1 _)) hsumm_f hsumm_g
    rw [hsplit_t]
    linarith [hle, hsplit_w]
  let F : ℕ → Ω → ℝ := fun n ω => ∑' i, w i * min 1 |f i n ω - g i ω|
  have hF0 : ∀ n ω, 0 ≤ F n ω := by
    intro n ω
    show (0:ℝ) ≤ ∑' i, w i * min 1 |f i n ω - g i ω|
    exact tsum_nonneg fun i => mul_nonneg (hw0 i) (le_min (by norm_num) (abs_nonneg _))
  have hTIM : TendstoInMeasure P F atTop (fun _ => (0:ℝ)) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    obtain ⟨s, hs⟩ : ∃ s : Finset ι, (∑' i, w i) - ∑ i ∈ s, w i < ε / 4 := by
      have hwT : Tendsto (fun s : Finset ι => ∑ i ∈ s, w i) atTop (𝓝 (∑' i, w i)) := by
        have ht := hwsumm.hasSum
        change Tendsto (fun s : Finset ι => ∑ i ∈ s, w i) atTop (𝓝 (∑' i, w i)) at ht
        exact ht
      have hh : ∀ᶠ s : Finset ι in atTop, (∑' i, w i) - ε / 4 < ∑ i ∈ s, w i :=
        (tendsto_order.mp hwT).1 _ (by linarith)
      obtain ⟨s, hss⟩ := hh.exists
      exact ⟨s, by linarith⟩
    set c : ℝ := ε / (2 * max 1 (s.card : ℝ)) with hcdef
    have hc : 0 < c := by rw [hcdef]; positivity
    have hmax : max 1 (s.card : ℝ) * c = ε / 2 := by rw [hcdef]; field_simp
    have hFbound : ∀ n, P {x | ε ≤ dist (F n x) 0} ≤
        ∑ i ∈ s, P {x | c ≤ dist (f i n x) (g i x)} := by
      intro n
      calc P {x | ε ≤ dist (F n x) 0}
          ≤ P (⋃ i ∈ s, {x | c ≤ dist (f i n x) (g i x)}) := by
            apply measure_mono
            intro x hx
            by_contra hxnot
            have hlt : ∀ i ∈ s, dist (f i n x) (g i x) < c := by
              intro i hi
              by_contra hcon
              exact hxnot (Set.mem_iUnion₂.mpr ⟨i, hi, le_of_not_gt hcon⟩)
            have hFt : F n x ≤ max 1 (s.card : ℝ) * c + ((∑' i, w i) - ∑ i ∈ s, w i) := by
              have h1 := hsum_bound (fun i => min 1 |f i n x - g i x|)
                (fun i => le_min (by norm_num) (abs_nonneg _)) (fun i => min_le_left _ _) s
              have h2 : ∑ i ∈ s, w i * min 1 |f i n x - g i x| ≤ max 1 (s.card : ℝ) * c := by
                calc ∑ i ∈ s, w i * min 1 |f i n x - g i x|
                    ≤ ∑ i ∈ s, w i * c := Finset.sum_le_sum (fun i hi => by
                        have hh : min 1 |f i n x - g i x| < c := by
                          have hlt' := hlt i hi; rw [Real.dist_eq] at hlt'
                          exact lt_of_le_of_lt (min_le_right _ _) hlt'
                        exact mul_le_mul_of_nonneg_left (le_of_lt hh) (hw0 i))
                  _ = (∑ i ∈ s, w i) * c := (Finset.sum_mul s w c).symm
                  _ ≤ (s.card : ℝ) * c := by
                        apply mul_le_mul_of_nonneg_right _ (le_of_lt hc)
                        calc ∑ i ∈ s, w i ≤ ∑ i ∈ s, (1:ℝ) := Finset.sum_le_sum fun i _ => hw1 i
                          _ = (s.card : ℝ) := by simp
                  _ ≤ max 1 (s.card : ℝ) * c := by
                        apply mul_le_mul_of_nonneg_right _ (le_of_lt hc)
                        exact le_max_right _ _
              have hFdef : F n x = ∑' i, w i * min 1 |f i n x - g i x| := rfl
              linarith [h1, h2, hFdef]
            have hFlt : F n x < ε := by linarith [hFt, hs, hmax, hε]
            have hdx : dist (F n x) 0 = F n x := by
              rw [Real.dist_eq, sub_zero, abs_of_nonneg (hF0 n x)]
            simp only [mem_ofPred_eq] at hx
            rw [hdx] at hx
            linarith [hx, hFlt]
        _ ≤ ∑ i ∈ s, P {x | c ≤ dist (f i n x) (g i x)} := measure_biUnion_finset_le s _
    have hsum_tendsto : Tendsto (fun n => ∑ i ∈ s, P {x | c ≤ dist (f i n x) (g i x)}) atTop (𝓝 0) := by
      have := tendsto_finsetSum s (fun i _ => (tendstoInMeasure_iff_dist.mp (h i)) c hc)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum_tendsto
      (fun n => zero_le) hFbound
  obtain ⟨φ, hφmono, hφae⟩ := hTIM.exists_seq_tendsto_ae
  refine ⟨φ, hφmono, ?_⟩
  rw [ae_all_iff]
  intro i
  filter_upwards [hφae] with ω hω
  have hb : Tendsto (fun k => w i * min 1 |f i (φ k) ω - g i ω|) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hω
      (fun k => mul_nonneg (hw0 i) (le_min (by norm_num) (abs_nonneg _))) (fun k => ?_)
    have hsummk : Summable (fun j => w j * min 1 |f j (φ k) ω - g j ω|) :=
      Summable.of_nonneg_of_le (fun j => mul_nonneg (hw0 j) (le_min (by norm_num) (abs_nonneg _)))
        (fun j => mul_le_of_le_one_right (hw0 j) (min_le_left _ _)) hwsumm
    exact hsummk.le_tsum i (fun j _ => mul_nonneg (hw0 j) (le_min (by norm_num) (abs_nonneg _)))
  have hmin : Tendsto (fun k => min 1 |f i (φ k) ω - g i ω|) atTop (𝓝 0) := by
    have hh := hb.const_mul ((w i)⁻¹)
    have heq : (fun k => (w i)⁻¹ * (w i * min 1 |f i (φ k) ω - g i ω|))
        = fun k => min 1 |f i (φ k) ω - g i ω| := by
      funext k; rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (hwpos i)), one_mul]
    rw [heq] at hh
    simpa using hh
  have habs : Tendsto (fun k => |f i (φ k) ω - g i ω|) atTop (𝓝 0) := by
    have hev : ∀ᶠ k in atTop, |f i (φ k) ω - g i ω| ≤ 2 * min 1 |f i (φ k) ω - g i ω| := by
      have hlt1 : ∀ᶠ k in atTop, min 1 |f i (φ k) ω - g i ω| < 1 :=
        (tendsto_order.mp hmin).2 1 (by norm_num)
      filter_upwards [hlt1] with k hk
      have hle1 : |f i (φ k) ω - g i ω| < 1 := by
        by_contra hcon; push Not at hcon
        have h1 : min 1 |f i (φ k) ω - g i ω| = 1 := min_eq_left hcon
        linarith
      rw [min_eq_right hle1.le]; linarith [abs_nonneg (f i (φ k) ω - g i ω)]
    have h2 : Tendsto (fun k => (2:ℝ) * min 1 |f i (φ k) ω - g i ω|) atTop (𝓝 0) := by
      have := hmin.const_mul (2:ℝ); simpa using this
    exact squeeze_zero' (Eventually.of_forall fun k => abs_nonneg _) hev h2
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [Real.dist_eq] using habs

end Part2

section Part3
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- Uniqueness of the limit through changing same-law environments. -/
theorem aux_env_real_limit_transfer {Ω S : Type*} [MeasurableSpace Ω]
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace.PseudoMetrizableSpace S]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure S} [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → S} {Y0 : Ω → S} (hY : ∀ n, MeasurePreserving (Y n) P μ)
    (hY0 : MeasurePreserving Y0 P μ)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Y0 ω)))
    {X : ℕ → S → ℝ} {V : S → ℝ} (hV : AEStronglyMeasurable V μ)
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (hXV : TendstoInMeasure μ X atTop V)
    {f : Ω → ℝ}
    (hf : ∀ᵐ ω ∂P, Tendsto (fun n => X n (Y n ω)) atTop (𝓝 (f ω))) :
    f =ᵐ[P] fun ω => V (Y0 ω) := by
  have hm : ∀ n, AEStronglyMeasurable (fun ω => X n (Y n ω)) P := fun n =>
    (hX n).comp_quasiMeasurePreserving (hY n).quasiMeasurePreserving
  have h2 : TendstoInMeasure P (fun n ω => X n (Y n ω)) atTop f :=
    tendstoInMeasure_of_tendsto_ae hm hf
  have h1 := represented_same_law_in_measure hY hY0 hconv hV hXV
  exact tendstoInMeasure_ae_unique h2 h1

end Part3

section Part4
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- Countably many same-law transfers of convergence in measure have one common a.e. subsequence. -/
theorem aux_env_ae_subseq_transfer {Ω S ι : Type*} [MeasurableSpace Ω]
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace.PseudoMetrizableSpace S] [Countable ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure S} [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → S} {Y0 : Ω → S} (hY : ∀ n, MeasurePreserving (Y n) P μ)
    (hY0 : MeasurePreserving Y0 P μ)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Y0 ω)))
    (X : ι → ℕ → S → ℝ) (V : ι → S → ℝ) (hV : ∀ i, AEStronglyMeasurable (V i) μ)
    (hXV : ∀ i, TendstoInMeasure μ (X i) atTop (V i)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, ∀ i,
      Tendsto (fun m => X i (φ m) (Y (φ m) ω)) atTop (𝓝 (V i (Y0 ω))) := by
  refine aux_env_common_ae_subseq_of_inMeasure (fun i n ω => X i n (Y n ω)) (fun i ω => V i (Y0 ω)) (fun i => ?_)
  exact _root_.SubdiffusiveProcess.Paper.represented_same_law_in_measure hY hY0 hconv (hV i) (hXV i)

end Part4

section Part5
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- Basis version of `aux_thm_prop_quadratic_matrix_limit`: convergence of the quadratic forms at
the basis slopes `e_i`, `e_i + e_j` suffices for the matrices to converge. -/
theorem aux_thm_prop_env_quadratic_matrix_limit_basis {d : ℕ}
    (R : ℕ → (Fin d → ℝ) → ℝ)
    (hR : ∀ n, ∃ A : Fin d → Fin d → ℝ,
      (∀ i j, A i j = A j i) ∧ ∀ p, R n p = ∑ i : Fin d, ∑ j : Fin d, A i j * p i * p j)
    (hlimit : ∀ p : Fin d → ℝ,
      ((∃ i : Fin d, p = (Pi.single i (1 : ℝ) : Fin d → ℝ)) ∨
        (∃ i j : Fin d, p = (Pi.single i (1 : ℝ) : Fin d → ℝ) + (Pi.single j (1 : ℝ) : Fin d → ℝ))) →
      ∃ L : ℝ, Tendsto (fun n => R n p) atTop (𝓝 L)) :
    ∃ (AN : ℕ → Fin d → Fin d → ℝ) (A : Fin d → Fin d → ℝ),
      (∀ n i j, AN n i j = AN n j i) ∧
      (∀ n p, R n p = ∑ i : Fin d, ∑ j : Fin d, AN n i j * p i * p j) ∧
      Tendsto AN atTop (𝓝 A) ∧ (∀ i j, A i j = A j i) ∧
      ∀ p, Tendsto (fun n => R n p) atTop
        (𝓝 (∑ i : Fin d, ∑ j : Fin d, A i j * p i * p j)) := by
  classical
  choose AN hsym hquad using hR
  choose L2 hL2 using fun i j => hlimit _ (Or.inr ⟨i, j, rfl⟩)
  choose L1 hL1 using fun i => hlimit _ (Or.inl ⟨i, rfl⟩)
  let A : Fin d → Fin d → ℝ := fun i j => (L2 i j - L1 i - L1 j) / 2
  have hentry (i j : Fin d) : Tendsto (fun n => AN n i j) atTop (𝓝 (A i j)) := by
    have h := (((hL2 i j).sub (hL1 i)).sub (hL1 j)).div_const 2
    apply h.congr
    intro n
    simp only [hquad]
    exact aux_thm_prop_matrix_polarization (AN n) (hsym n) i j
  refine ⟨AN, A, hsym, hquad,
    tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (fun j => hentry i j)), ?_, ?_⟩
  · intro i j
    exact tendsto_nhds_unique (hentry i j) ((hentry j i).congr (fun n => hsym n j i))
  · intro p
    have h := tendsto_finsetSum Finset.univ (fun i _ =>
      tendsto_finsetSum Finset.univ (fun j _ => ((hentry i j).mul_const (p i)).mul_const (p j)))
    exact h.congr (fun n => (hquad n p).symm)

end Part5

section Part6
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- Symmetric matrices with equal quadratic forms at the basis slopes are equal. -/
theorem aux_thm_prop_env_matrix_eq_of_basis {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (hB : B.transpose = B)
    (h : ∀ p : Fin d → ℝ,
      ((∃ i : Fin d, p = (Pi.single i (1 : ℝ) : Fin d → ℝ)) ∨
        (∃ i j : Fin d, p = (Pi.single i (1 : ℝ) : Fin d → ℝ) + (Pi.single j (1 : ℝ) : Fin d → ℝ))) →
      p ⬝ᵥ A.mulVec p = p ⬝ᵥ B.mulVec p) :
    A = B := by
  apply Matrix.ext
  intro i j
  have hAsym : ∀ i j : Fin d, A i j = A j i := fun i j => by
    simpa [Matrix.transpose_apply] using (congr_fun (congr_fun hA i) j).symm
  have hBsym : ∀ i j : Fin d, B i j = B j i := fun i j => by
    simpa [Matrix.transpose_apply] using (congr_fun (congr_fun hB i) j).symm
  have h1 : (∑ k, ∑ l, A k l * (Pi.single i (1 : ℝ) : Fin d → ℝ) k * (Pi.single i (1 : ℝ) : Fin d → ℝ) l)
      = (∑ k, ∑ l, B k l * (Pi.single i (1 : ℝ) : Fin d → ℝ) k * (Pi.single i (1 : ℝ) : Fin d → ℝ) l) := by
    have hp := h (Pi.single i (1 : ℝ)) (Or.inl ⟨i, rfl⟩)
    rwa [aux_thm_prop_matrix_quadratic_eq A, aux_thm_prop_matrix_quadratic_eq B] at hp
  have h2 : (∑ k, ∑ l, A k l * (Pi.single j (1 : ℝ) : Fin d → ℝ) k * (Pi.single j (1 : ℝ) : Fin d → ℝ) l)
      = (∑ k, ∑ l, B k l * (Pi.single j (1 : ℝ) : Fin d → ℝ) k * (Pi.single j (1 : ℝ) : Fin d → ℝ) l) := by
    have hp := h (Pi.single j (1 : ℝ)) (Or.inl ⟨j, rfl⟩)
    rwa [aux_thm_prop_matrix_quadratic_eq A, aux_thm_prop_matrix_quadratic_eq B] at hp
  have h3 : (∑ k, ∑ l, A k l * ((Pi.single i (1 : ℝ) : Fin d → ℝ) + (Pi.single j (1 : ℝ) : Fin d → ℝ)) k
        * ((Pi.single i (1 : ℝ) : Fin d → ℝ) + (Pi.single j (1 : ℝ) : Fin d → ℝ)) l)
      = (∑ k, ∑ l, B k l * ((Pi.single i (1 : ℝ) : Fin d → ℝ) + (Pi.single j (1 : ℝ) : Fin d → ℝ)) k
        * ((Pi.single i (1 : ℝ) : Fin d → ℝ) + (Pi.single j (1 : ℝ) : Fin d → ℝ)) l) := by
    have hp := h ((Pi.single i (1 : ℝ) : Fin d → ℝ) + (Pi.single j (1 : ℝ) : Fin d → ℝ)) (Or.inr ⟨i, j, rfl⟩)
    rwa [aux_thm_prop_matrix_quadratic_eq A, aux_thm_prop_matrix_quadratic_eq B] at hp
  rw [← aux_thm_prop_matrix_polarization A hAsym i j,
      ← aux_thm_prop_matrix_polarization B hBsym i j,
      h3, h1, h2]

end Part6

section Part7
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- The limiting affine matrix of the represented space is the original-space limit matrix composed with the limit field. -/
theorem thm_prop_env_measure {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHm : Measurable H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (Ncut : ℕ → ℕ) (psi : ℕ → ℕ) (hpsi : StrictMono psi)
    (A0 : BilateralField d → Matrix (Fin d) (Fin d) ℝ) (hA0sym : ∀ β, (A0 β).transpose = A0 β)
    (hA0m : ∀ i j, Measurable (fun β => A0 β i j))
    (hin : ∀ p : Fin d → ℝ, TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun n β => affineDirichletResponse (centeredCube_isBounded z hr) hP
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β (Ncut (psi n)) z hr) p /
        (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) atTop
      (fun β => p ⬝ᵥ (A0 β).mulVec p))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d) (env : ℕ → Ω → BilateralField d)
    (hMP : ∀ n, MeasurePreserving (env n) P (chaosSampleLaw M).toMeasure)
    (hfield : MeasurePreserving field P (chaosSampleLaw M).toMeasure)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => env n ω) atTop (𝓝 (field ω)))
    (AEh : Ω → Matrix (Fin d) (Fin d) ℝ) (hAEsym : ∀ ω, (AEh ω).transpose = AEh ω)
    (hA : ∀ᵐ ω ∂P, ∀ p : Fin d → ℝ, Tendsto (fun n =>
      affineDirichletResponse (centeredCube_isBounded z hr) hP
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n ω) (Ncut n) z hr) p /
        (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
      atTop (𝓝 (p ⬝ᵥ (AEh ω).mulVec p))) :
    AEh =ᵐ[P] fun ω => A0 (field ω) := by
  have : IsProbabilityMeasure (chaosSampleLaw M).toMeasure := inferInstance
  set basisSlope : (Fin d ⊕ (Fin d × Fin d)) → (Fin d → ℝ) :=
    Sum.elim (fun i => (Pi.single i (1:ℝ) : Fin d → ℝ))
      (fun ij => (Pi.single ij.1 (1:ℝ) : Fin d → ℝ) + (Pi.single ij.2 (1:ℝ) : Fin d → ℝ))
    with hbsdef
  have hkey : ∀ q : Fin d ⊕ (Fin d × Fin d),
      (fun ω => basisSlope q ⬝ᵥ (AEh ω).mulVec (basisSlope q)) =ᵐ[P]
      (fun ω => basisSlope q ⬝ᵥ (A0 (field ω)).mulVec (basisSlope q)) := by
    intro q
    set p : Fin d → ℝ := basisSlope q with hpdef
    have hV : AEStronglyMeasurable (fun β => p ⬝ᵥ (A0 β).mulVec p) (chaosSampleLaw M).toMeasure := by
      apply Measurable.aestronglyMeasurable
      have hfun : (fun β => p ⬝ᵥ (A0 β).mulVec p)
          = fun β => ∑ i, ∑ j, p i * A0 β i j * p j := by
        funext β
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
      rw [hfun]
      exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _
        (fun j _ => ((hA0m i j).const_mul (p i)).mul_const (p j)))
    have hX : ∀ n, AEStronglyMeasurable
        (fun β => affineDirichletResponse (centeredCube_isBounded z hr) hP
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β (Ncut (psi n)) z hr) p /
          (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
        (chaosSampleLaw M).toMeasure := by
      intro n
      exact ((aux_thm_prop_affine_response_measurable M H hHm (Ncut (psi n)) z hr hP p).div_const _).aestronglyMeasurable
    have hf : ∀ᵐ ω ∂P, Tendsto (fun n =>
        affineDirichletResponse (centeredCube_isBounded z hr) hP
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env (psi n) ω) (Ncut (psi n)) z hr) p /
          (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) atTop
        (𝓝 (p ⬝ᵥ (AEh ω).mulVec p)) :=
      hA.mono fun ω hω => (hω p).comp hpsi.tendsto_atTop
    have hT := aux_env_real_limit_transfer
      (P := P) (μ := (chaosSampleLaw M).toMeasure)
      (Y := fun n => env (psi n)) (Y0 := field)
      (hY := fun n => hMP (psi n)) (hY0 := hfield)
      (hconv := hconv.mono fun ω h => h.comp hpsi.tendsto_atTop)
      (X := fun n β => affineDirichletResponse (centeredCube_isBounded z hr) hP
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β (Ncut (psi n)) z hr) p /
        (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
      (V := fun β => p ⬝ᵥ (A0 β).mulVec p)
      (f := fun ω => p ⬝ᵥ (AEh ω).mulVec p)
      (hV := hV) (hX := hX) (hXV := hin p) (hf := hf)
    simpa only [hpdef] using hT
  have hbasisC : ∀ᵐ ω ∂P, ∀ q : Fin d ⊕ (Fin d × Fin d),
      basisSlope q ⬝ᵥ (AEh ω).mulVec (basisSlope q) =
      basisSlope q ⬝ᵥ (A0 (field ω)).mulVec (basisSlope q) := by
    rw [ae_all_iff]
    intro q
    exact hkey q
  have hbasis : ∀ᵐ ω ∂P, ∀ p : Fin d → ℝ,
      ((∃ i : Fin d, p = (Pi.single i (1:ℝ) : Fin d → ℝ)) ∨
        (∃ i j : Fin d, p = (Pi.single i (1:ℝ) : Fin d → ℝ) + (Pi.single j (1:ℝ) : Fin d → ℝ))) →
      p ⬝ᵥ (AEh ω).mulVec p = p ⬝ᵥ (A0 (field ω)).mulVec p := by
    filter_upwards [hbasisC] with ω hω p hp
    rcases hp with ⟨i, rfl⟩ | ⟨i, j, rfl⟩
    · simpa only [hbsdef, Sum.elim_inl] using hω (Sum.inl i)
    · simpa only [hbsdef, Sum.elim_inr] using hω (Sum.inr (i, j))
  filter_upwards [hbasis] with ω hω
  exact aux_thm_prop_env_matrix_eq_of_basis (AEh ω) (A0 (field ω)) (hAEsym ω) (hA0sym (field ω)) hω

end Part7

end SubdiffusiveProcess.Paper
end
