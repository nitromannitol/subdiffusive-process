import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open Metric

noncomputable section
namespace Paper

/-- (a) The depth-`j` term is bounded in `L^q` by `(#ι)^{1/q} max(C, 0)`. -/
theorem aux_lem_prefix_limit_g9_series_compact_Yq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) (Y : Ω → ℝ) (C q : ℝ) (hq : 1 < q)
    (hXm : ∀ i, AEStronglyMeasurable (X i) μ)
    (hYle : ∀ ω, |Y ω| ^ q ≤ ∑ i, |X i ω| ^ q)
    (hXq : ∀ i, eLpNorm (X i) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C) :
    eLpNorm Y (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) ^ (1 / q) * max C 0) := by
  have hq0 : 0 < q := by linarith
  have hqE0 : ENNReal.ofReal q ≠ 0 := by simpa using hq0
  have hqtop : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqr : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq0.le
  rw [eLpNorm_eq_lintegral_rpow_enorm hqE0 hqtop, hqr]
  have h1 : ∀ ω, ‖Y ω‖ₑ ^ q ≤ ∑ i, ‖X i ω‖ₑ ^ q := by
    intro ω
    have hl : ‖Y ω‖ₑ ^ q = ENNReal.ofReal (|Y ω| ^ q) := by
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le]
    have hr : ∑ i, ‖X i ω‖ₑ ^ q = ENNReal.ofReal (∑ i, |X i ω| ^ q) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le]
    rw [hl, hr]
    exact ENNReal.ofReal_le_ofReal (hYle ω)
  have h3 : ∀ i, ∫⁻ ω, ‖X i ω‖ₑ ^ q ∂μ ≤ ENNReal.ofReal (max C 0) ^ q := by
    intro i
    have h := hXq i
    rw [eLpNorm_eq_lintegral_rpow_enorm hqE0 hqtop, hqr] at h
    have h' : (∫⁻ ω, ‖X i ω‖ₑ ^ q ∂μ) ^ (1 / q) ≤ ENNReal.ofReal (max C 0) :=
      h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have := ENNReal.rpow_le_rpow h' hq0.le
    rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one] at this
  have h2 : ∫⁻ ω, ‖Y ω‖ₑ ^ q ∂μ ≤ (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (max C 0) ^ q := by
    calc ∫⁻ ω, ‖Y ω‖ₑ ^ q ∂μ ≤ ∫⁻ ω, ∑ i, ‖X i ω‖ₑ ^ q ∂μ := lintegral_mono h1
      _ = ∑ i, ∫⁻ ω, ‖X i ω‖ₑ ^ q ∂μ :=
          lintegral_finset_sum' _ (fun i _ => ((hXm i).enorm.pow_const q))
      _ ≤ ∑ _i : ι, ENNReal.ofReal (max C 0) ^ q := Finset.sum_le_sum (fun i _ => h3 i)
      _ = (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (max C 0) ^ q := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc (∫⁻ ω, ‖Y ω‖ₑ ^ q ∂μ) ^ (1 / q)
      ≤ ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (max C 0) ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow h2 (by positivity)
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) ^ (1 / q) * max C 0) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hq0.ne', ENNReal.rpow_one,
          ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_rpow_of_nonneg (by positivity)
            (by positivity)]
        simp

/-- Pointwise Lipschitz control integrates to an `L¹` bound. -/
theorem aux_lem_prefix_limit_g9_series_compact_lip
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {κ : Type*} [Fintype κ] (X X' : κ → Ω → ℝ) (S S' : Ω → ℝ) (a : κ → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hXm : ∀ k, AEStronglyMeasurable (X k) μ)
    (hX'm : ∀ k, AEStronglyMeasurable (X' k) μ)
    (hlip : ∀ ω, |S ω - S' ω| ≤ ∑ k, a k * |X k ω - X' k ω|) :
    eLpNorm (S - S') 1 μ ≤ ∑ k, ENNReal.ofReal (a k) * eLpNorm (X k - X' k) 1 μ := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  simp_rw [eLpNorm_one_eq_lintegral_enorm]
  calc ∫⁻ ω, ‖(S - S') ω‖ₑ ∂μ
      ≤ ∫⁻ ω, ∑ k, ENNReal.ofReal (a k) * ‖(X k - X' k) ω‖ₑ ∂μ := by
        refine lintegral_mono (fun ω => ?_)
        have h1 : ‖(S - S') ω‖ₑ = ENNReal.ofReal |S ω - S' ω| := by
          rw [Pi.sub_apply, Real.enorm_eq_ofReal_abs]
        have h2 : ∑ k, ENNReal.ofReal (a k) * ‖(X k - X' k) ω‖ₑ =
            ENNReal.ofReal (∑ k, a k * |X k ω - X' k ω|) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (ha k) (abs_nonneg _))]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Pi.sub_apply, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_mul (ha k)]
        rw [h1, h2]
        exact ENNReal.ofReal_le_ofReal (hlip ω)
    _ = ∑ k, ∫⁻ ω, ENNReal.ofReal (a k) * ‖(X k - X' k) ω‖ₑ ∂μ :=
        lintegral_finset_sum' _ (fun k _ => ((hXm k).sub (hX'm k)).enorm.const_mul _)
    _ = ∑ k, ENNReal.ofReal (a k) * ∫⁻ ω, ‖(X k - X' k) ω‖ₑ ∂μ := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- (c) Totally bounded head: a finite family of `L¹`-relatively compact coordinate families and a
family `S` that is pointwise Lipschitz-controlled by them has a totally bounded range in `L¹`. -/
theorem aux_lem_prefix_limit_g9_series_compact_head
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {κ : Type*} [Fintype κ] (X : κ → ℕ → Ω → ℝ) (S : ℕ → Ω → ℝ) (a : κ → ℝ)
    (ha : ∀ k, 0 ≤ a k)
    (hXmem : ∀ k N, MemLp (X k N) 1 μ)
    (hcomp : ∀ k, IsCompact (closure (Set.range fun N => (hXmem k N).toLp (X k N))))
    (hSmem : ∀ N, MemLp (S N) 1 μ)
    (hSlip : ∀ N N' ω, |S N ω - S N' ω| ≤ ∑ k, a k * |X k N ω - X k N' ω|) :
    TotallyBounded (Set.range fun N => (hSmem N).toLp (S N)) := by
  set W : ℕ → (κ → Lp ℝ 1 μ) := fun N k => (hXmem k N).toLp (X k N) with hWdef
  have hWtb : TotallyBounded (Set.range W) :=
    (isCompact_univ_pi hcomp).totallyBounded.subset (by
      rintro _ ⟨N, rfl⟩ k _
      exact subset_closure ⟨N, rfl⟩)
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set A : ℝ := ∑ k, a k + 1 with hAdef
  have hsum0 : 0 ≤ ∑ k, a k := Finset.sum_nonneg (fun k _ => ha k)
  have hA : 0 < A := by linarith
  have hδ : 0 < ε / (2 * A) := by positivity
  obtain ⟨t, htsub, htfin, htcov⟩ :=
    totallyBounded_iff_subset.1 hWtb _ (Metric.dist_mem_uniformity hδ)
  have hidx : ∀ y ∈ t, ∃ N, W N = y := fun y hy => htsub hy
  choose! Nof hNof using hidx
  refine ⟨(fun y => (hSmem (Nof y)).toLp (S (Nof y))) '' t, htfin.image _, ?_⟩
  rintro _ ⟨N, rfl⟩
  have hWN := htcov ⟨N, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hWN
  obtain ⟨y, hyt, hdist⟩ := hWN
  refine Set.mem_iUnion₂.2 ⟨_, ⟨y, hyt, rfl⟩, ?_⟩
  rw [Metric.mem_ball, ← edist_lt_ofReal]
  have hcoord : ∀ k, edist ((hXmem k N).toLp (X k N)) ((hXmem k (Nof y)).toLp (X k (Nof y))) ≤
      ENNReal.ofReal (ε / (2 * A)) := by
    intro k
    have h1 : dist (W N) (W (Nof y)) < ε / (2 * A) := by rw [hNof y hyt]; exact hdist
    have h2 : dist (W N k) (W (Nof y) k) < ε / (2 * A) := (dist_le_pi_dist _ _ k).trans_lt h1
    exact edist_le_ofReal (by positivity) |>.2 h2.le
  rw [Lp.edist_toLp_toLp]
  calc eLpNorm (S N - S (Nof y)) 1 μ
      ≤ ∑ k, ENNReal.ofReal (a k) * eLpNorm (X k N - X k (Nof y)) 1 μ :=
        aux_lem_prefix_limit_g9_series_compact_lip μ (fun k => X k N) (fun k => X k (Nof y))
          (S N) (S (Nof y)) a ha (fun k => (hXmem k N).1) (fun k => (hXmem k (Nof y)).1)
          (hSlip N (Nof y))
    _ ≤ ∑ k, ENNReal.ofReal (a k) * ENNReal.ofReal (ε / (2 * A)) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        gcongr
        rw [← Lp.edist_toLp_toLp]
        exact hcoord k
    _ = ENNReal.ofReal ((∑ k, a k) * (ε / (2 * A))) := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun k _ => ha k),
          ENNReal.ofReal_mul hsum0]
    _ < ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_lt_ofReal_iff hε]
        have : (∑ k, a k) * (ε / (2 * A)) ≤ A * (ε / (2 * A)) :=
          mul_le_mul_of_nonneg_right (by linarith) hδ.le
        have hA2 : A * (ε / (2 * A)) = ε / 2 := by field_simp
        linarith

/-- (b) Series with `L¹`-summable terms: a.e. summability, measurability of the sum, and the
uniform tail bound. -/
theorem aux_lem_prefix_limit_g9_series_compact_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ℕ → Ω → ℝ) (b : ℕ → ℝ) (hf : ∀ j, AEStronglyMeasurable (f j) μ)
    (hb : Summable b) (hb0 : ∀ j, 0 ≤ b j)
    (hfb : ∀ j, eLpNorm (f j) 1 μ ≤ ENNReal.ofReal (b j)) :
    (∀ᵐ ω ∂μ, Summable fun j => f j ω) ∧
      AEStronglyMeasurable (fun ω => ∑' j, f j ω) μ ∧
      ∀ H : ℕ, eLpNorm (fun ω => ∑' j, f j ω - ∑ j ∈ Finset.range H, f j ω) 1 μ ≤
        ENNReal.ofReal (∑' i, b (i + H)) := by
  have hint : ∀ H : ℕ, ∫⁻ ω, ∑' i, ‖f (i + H) ω‖ₑ ∂μ ≤ ENNReal.ofReal (∑' i, b (i + H)) := by
    intro H
    rw [lintegral_tsum (fun i => (hf (i + H)).enorm)]
    calc ∑' i, ∫⁻ ω, ‖f (i + H) ω‖ₑ ∂μ ≤ ∑' i, ENNReal.ofReal (b (i + H)) :=
          ENNReal.tsum_le_tsum (fun i => by
            rw [← eLpNorm_one_eq_lintegral_enorm]; exact hfb (i + H))
      _ = ENNReal.ofReal (∑' i, b (i + H)) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun i => hb0 (i + H))
            ((summable_nat_add_iff H).2 hb)).symm
  have hfin : ∀ᵐ ω ∂μ, ∑' j, ‖f j ω‖ₑ < ⊤ := by
    have h0 := hint 0
    simp only [add_zero] at h0
    exact ae_lt_top' (AEMeasurable.ennreal_tsum (fun j => (hf j).enorm))
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h0)
  have hsumm : ∀ᵐ ω ∂μ, Summable fun j => f j ω := by
    filter_upwards [hfin] with ω hω
    apply Summable.of_norm
    have := ENNReal.summable_toReal hω.ne
    simpa using this
  refine ⟨hsumm, ?_, ?_⟩
  · refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun H ω => ∑ j ∈ Finset.range H, f j ω)
      (fun H => by
        have e : (fun ω => ∑ j ∈ Finset.range H, f j ω) = ∑ j ∈ Finset.range H, f j := by
          funext ω; rw [Finset.sum_apply]
        show AEStronglyMeasurable (fun ω => ∑ j ∈ Finset.range H, f j ω) μ
        rw [e]
        exact Finset.aestronglyMeasurable_sum (Finset.range H) (fun j _ => hf j)) ?_
    filter_upwards [hsumm] with ω hω
    exact hω.hasSum.tendsto_sum_nat
  · intro H
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine le_trans (lintegral_mono_ae ?_) (hint H)
    filter_upwards [hsumm] with ω hω
    have hsplit := hω.sum_add_tsum_nat_add H
    have heq : ∑' j, f j ω - ∑ j ∈ Finset.range H, f j ω = ∑' i, f (i + H) ω := by
      rw [← hsplit]; ring
    rw [heq]
    exact enorm_tsum_le_tsum_enorm



theorem lem_prefix_limit_g9_series_compact
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ι : ℕ → Type*) [∀ j, Fintype (ι j)]
    (X : (j : ℕ) → ι j → ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ)
    (w C : ℕ → ℝ) (q : ℝ) (hq : 1 < q) (hw : ∀ j, 0 ≤ w j)
    (hYm : ∀ j N, AEStronglyMeasurable (Y j N) μ)
    (hYle : ∀ j N ω, |Y j N ω| ^ q ≤ ∑ i, |X j i N ω| ^ q)
    (hYlip : ∀ j N N' ω, |Y j N ω - Y j N' ω| ≤ ∑ i, |X j i N ω - X j i N' ω|)
    (hXq : ∀ j i N, eLpNorm (X j i N) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (C j))
    (hsum : Summable fun j => w j * (Fintype.card (ι j) : ℝ) ^ (1 / q) * C j)
    (hcomp : ∀ j i, ∃ hm : ∀ N, MemLp (X j i N) 1 μ,
      IsCompact (closure (Set.range fun N => (hm N).toLp (X j i N)))) :
    ∃ hm : ∀ N, MemLp (fun ω => ∑' j, w j * Y j N ω) 1 μ,
      IsCompact (closure (Set.range fun N =>
        (hm N).toLp (fun ω => ∑' j, w j * Y j N ω))) := by
  choose hXmem hXcomp using hcomp
  have h1q : (1:ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq.le
  set c : ℕ → ℝ := fun j => (Fintype.card (ι j) : ℝ) ^ (1 / q) * max (C j) 0 with hcdef
  have hc0 : ∀ j, 0 ≤ c j := fun j => by positivity
  have hY1 : ∀ j N, eLpNorm (Y j N) 1 μ ≤ ENNReal.ofReal (c j) := fun j N =>
    (eLpNorm_le_eLpNorm_of_exponent_le h1q (hYm j N)).trans
      (aux_lem_prefix_limit_g9_series_compact_Yq μ (fun i => X j i N) (Y j N) (C j) q hq
        (fun i => (hXmem j i N).1) (hYle j N) (fun i => hXq j i N))
  have hb0 : ∀ j, 0 ≤ w j * c j := fun j => mul_nonneg (hw j) (hc0 j)
  have hbsum : Summable fun j => w j * c j := by
    refine Summable.of_nonneg_of_le hb0 (fun j => ?_) hsum.abs
    have hcard : 0 ≤ (Fintype.card (ι j) : ℝ) ^ (1 / q) := by positivity
    rw [hcdef]
    simp only
    rcases le_total 0 (C j) with h | h
    · rw [max_eq_left h, ← mul_assoc]; exact le_abs_self _
    · rw [max_eq_right h, mul_zero, mul_zero]; exact abs_nonneg _
  -- per-cutoff series facts
  have hfm : ∀ N j, AEStronglyMeasurable (fun ω => w j * Y j N ω) μ :=
    fun N j => (hYm j N).const_mul (w j)
  have hfb : ∀ N j, eLpNorm (fun ω => w j * Y j N ω) 1 μ ≤ ENNReal.ofReal (w j * c j) := by
    intro N j
    have : (fun ω => w j * Y j N ω) = w j • Y j N := rfl
    rw [this, eLpNorm_const_smul, ENNReal.ofReal_mul (hw j), Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (hw j)]
    exact mul_le_mul_right (hY1 j N) _
  have htail := fun N => aux_lem_prefix_limit_g9_series_compact_tail μ
    (fun j ω => w j * Y j N ω) (fun j => w j * c j) (hfm N) hbsum hb0 (hfb N)
  set Z : ℕ → Ω → ℝ := fun N ω => ∑' j, w j * Y j N ω with hZdef
  set S : ℕ → ℕ → Ω → ℝ := fun H N ω => ∑ j ∈ Finset.range H, w j * Y j N ω with hSdef
  have hSmem : ∀ H N, MemLp (S H N) 1 μ := by
    intro H N
    have : S H N = ∑ j ∈ Finset.range H, (fun ω => w j * Y j N ω) := by
      funext ω; simp [hSdef, Finset.sum_apply]
    rw [this]
    refine memLp_finset_sum' _ (fun j _ => ?_)
    exact ⟨hfm N j, lt_of_le_of_lt (hfb N j) ENNReal.ofReal_lt_top⟩
  have hZS : ∀ H N, eLpNorm (Z N - S H N) 1 μ ≤ ENNReal.ofReal (∑' i, w (i + H) * c (i + H)) :=
    fun H N => (htail N).2.2 H
  have hZmem : ∀ N, MemLp (Z N) 1 μ := by
    intro N
    have hS0 : S 0 N = 0 := by funext ω; simp [hSdef]
    have h := hZS 0 N
    rw [hS0, sub_zero] at h
    exact ⟨(htail N).2.1, lt_of_le_of_lt h ENNReal.ofReal_lt_top⟩
  refine ⟨hZmem, ?_⟩
  -- total boundedness of the range
  set F : ℕ → Lp ℝ 1 μ := fun N => (hZmem N).toLp (Z N) with hFdef
  have htb : TotallyBounded (Set.range F) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    have htend := tendsto_sum_nat_add (fun j => w j * c j)
    obtain ⟨H, hH⟩ := (htend.eventually (gt_mem_nhds (half_pos hε))).exists
    -- head family over κ = Σ j : Fin H, ι j
    set κ := Σ j : Fin H, ι j
    have hhead := aux_lem_prefix_limit_g9_series_compact_head μ
      (κ := κ) (fun k N => X k.1 k.2 N) (S H) (fun k => w k.1) (fun k => hw k.1)
      (fun k N => hXmem k.1 k.2 N) (fun k => hXcomp k.1 k.2) (hSmem H)
      (fun N N' ω => by
        calc |S H N ω - S H N' ω| = |∑ j ∈ Finset.range H, w j * (Y j N ω - Y j N' ω)| := by
              simp only [hSdef, ← Finset.sum_sub_distrib, mul_sub]
          _ ≤ ∑ j ∈ Finset.range H, |w j * (Y j N ω - Y j N' ω)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ Finset.range H, w j * ∑ i, |X j i N ω - X j i N' ω| := by
              refine Finset.sum_le_sum (fun j _ => ?_)
              rw [abs_mul, abs_of_nonneg (hw j)]
              exact mul_le_mul_of_nonneg_left (hYlip j N N' ω) (hw j)
          _ = ∑ j : Fin H, w j * ∑ i, |X j i N ω - X j i N' ω| :=
              (Fin.sum_univ_eq_sum_range (fun j => w j * ∑ i, |X j i N ω - X j i N' ω|) H).symm
          _ = ∑ k : κ, w k.1 * |X k.1 k.2 N ω - X k.1 k.2 N' ω| := by
              rw [Fintype.sum_sigma]
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [Finset.mul_sum])
    obtain ⟨t, htfin, htcov⟩ := Metric.totallyBounded_iff.1 hhead (ε / 2) (half_pos hε)
    refine ⟨t, htfin, ?_⟩
    rintro _ ⟨N, rfl⟩
    obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.1 (htcov ⟨N, rfl⟩)
    refine Set.mem_iUnion₂.2 ⟨y, hyt, ?_⟩
    rw [Metric.mem_ball] at hy ⊢
    have hd : dist (F N) ((hSmem H N).toLp (S H N)) < ε / 2 := by
      rw [dist_edist, Lp.edist_toLp_toLp]
      have h1 := hZS H N
      have h2 : ENNReal.ofReal (∑' i, w (i + H) * c (i + H)) < ENNReal.ofReal (ε / 2) :=
        (ENNReal.ofReal_lt_ofReal_iff (half_pos hε)).2 hH
      exact (ENNReal.toReal_lt_of_lt_ofReal (lt_of_le_of_lt h1 h2))
    calc dist (F N) y ≤ dist (F N) ((hSmem H N).toLp (S H N)) +
          dist ((hSmem H N).toLp (S H N)) y := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hd hy
      _ = ε := by ring
  exact htb.closure.isCompact_of_isClosed isClosed_closure

end Paper
