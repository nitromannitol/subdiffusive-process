module

public import SubdiffusiveProcess.Paper.lfgc_p_trunc_dep

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The truncated scores converge surely

For every potential sample, the truncated field and product scores increase to the full
formulas as the depth `L → ∞` (the product's tail product is monotone in its length because
its factors are at least `1`), the truncated drift score converges to the full drift score
whenever the latter is finite, and hence the truncated bad score converges to the full one.
No almost-sure statement is involved.
-/

open MeasureTheory Filter Topology SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace Paper
variable {d : ℕ}

theorem aux_lfgc_p_trunc_conv_ftr_mono (s : ℝ) (n : ℕ) (y : Vec d) (g : PotentialSample d) :
    Monotone (fun L => aux_lfgc_p_trunc_ftr s n y L g) := by
  intro L L' hLL'
  refine sSup_le_sSup ?_
  rintro v ⟨j, hj, rfl⟩
  exact ⟨j, hj.trans hLL', rfl⟩

theorem aux_lfgc_p_trunc_conv_iSup_ftr (s : ℝ) (n : ℕ) (y : Vec d) (g : PotentialSample d) :
    ⨆ L, aux_lfgc_p_trunc_ftr s n y L g = aux_lfgc_p_trunc_ffull s n y g := by
  apply le_antisymm
  · refine iSup_le fun L => sSup_le_sSup ?_
    rintro v ⟨j, -, rfl⟩
    exact ⟨j, rfl⟩
  · refine sSup_le ?_
    rintro v ⟨j, rfl⟩
    exact le_iSup_of_le j (le_sSup ⟨j, le_rfl, rfl⟩)

theorem aux_lfgc_p_trunc_conv_tendsto_ftr (s : ℝ) (n : ℕ) (y : Vec d) (g : PotentialSample d) :
    Tendsto (fun L => aux_lfgc_p_trunc_ftr s n y L g) atTop (𝓝 (aux_lfgc_p_trunc_ffull s n y g)) := by
  rw [← aux_lfgc_p_trunc_conv_iSup_ftr]
  exact tendsto_atTop_iSup (aux_lfgc_p_trunc_conv_ftr_mono s n y g)

theorem aux_lfgc_p_trunc_conv_one_le_ofReal_exp_nonneg {t : ℝ} (ht : 0 ≤ t) : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp t) := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.one_le_exp ht)

theorem aux_lfgc_p_trunc_conv_prod_mono_of_one_le {s t : Finset ℕ} (hst : s ⊆ t) (f : ℕ → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  rw [← Finset.prod_sdiff hst]
  calc ∏ i ∈ s, f i = 1 * ∏ i ∈ s, f i := (one_mul _).symm
    _ ≤ (∏ i ∈ t \ s, f i) * ∏ i ∈ s, f i := by
        gcongr
        exact Finset.one_le_prod' fun i _ => hf i

theorem aux_lfgc_p_trunc_conv_pj_mono (n : ℕ) (y : Vec d) (g : PotentialSample d) (j : ℕ) {L L' : ℕ} (hLL' : L ≤ L') :
    Paper.aux_lem_band_piece_product_Pj d n y g L j ≤
      Paper.aux_lem_band_piece_product_Pj d n y g L' j := by
  unfold Paper.aux_lem_band_piece_product_Pj
  refine sSup_le_sSup_of_isCofinalFor ?_
  rintro w ⟨x, hx, rfl⟩
  refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
  gcongr
  intro i _ _
  exact aux_lfgc_p_trunc_conv_one_le_ofReal_exp_nonneg (by positivity)

theorem aux_lfgc_p_trunc_conv_pcand_mono (s : ℝ) (n : ℕ) (y : Vec d) (g : PotentialSample d) :
    Monotone (fun L => Paper.aux_lem_band_piece_product_trunc_Pcand d s n y g L) := by
  intro L L' hLL'
  refine sSup_le_sSup_of_isCofinalFor ?_
  rintro v ⟨j, hj, rfl⟩
  exact ⟨_, ⟨j, hj.trans hLL', rfl⟩, by gcongr; exact aux_lfgc_p_trunc_conv_pj_mono n y g j hLL'⟩

theorem aux_lfgc_p_trunc_conv_iSup_pcand (s : ℝ) (n : ℕ) (y : Vec d) (g : PotentialSample d) :
    ⨆ L, Paper.aux_lem_band_piece_product_trunc_Pcand d s n y g L =
      Paper.aux_lem_band_piece_product_Praw d s n y g := by
  apply le_antisymm
  · refine iSup_le fun L => ?_
    exact (Paper.aux_lem_band_piece_product_trunc_Pcand_le_restrict d s n L y g).trans
      (Paper.aux_lem_band_piece_product_trunc_restrict_le_Praw d s n L y g)
  · unfold Paper.aux_lem_band_piece_product_Praw
    refine sSup_le ?_
    rintro v ⟨j, rfl⟩
    unfold Paper.aux_lem_band_piece_product_Tj
    rw [ENNReal.mul_sSup]
    refine iSup₂_le fun w hw => ?_
    obtain ⟨x, hx, rfl⟩ := hw
    have hB : sSup {u : ℝ≥0∞ | ∃ K : ℕ, u = ∏ i ∈ Finset.Icc (n + j) (n + j + K),
        ENNReal.ofReal (Real.exp (4 * |g i x - g i y|))} =
        ⨆ K : ℕ, ∏ i ∈ Finset.Icc (n + j) (n + j + K),
          ENNReal.ofReal (Real.exp (4 * |g i x - g i y|)) := by
      rw [← sSup_range]
      congr 1
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_range, eq_comm]
    rw [hB, ENNReal.add_iSup, ENNReal.mul_iSup]
    refine iSup_le fun K => ?_
    refine le_iSup_of_le (j + K) ?_
    refine le_sSup_of_le ⟨j, by omega, rfl⟩ ?_
    gcongr
    unfold Paper.aux_lem_band_piece_product_Pj
    refine le_sSup_of_le ⟨x, hx, rfl⟩ ?_
    rw [show n + (j + K) = n + j + K by ring]

theorem aux_lfgc_p_trunc_conv_tendsto_pcand (s : ℝ) (n : ℕ) (y : Vec d) (g : PotentialSample d) :
    Tendsto (fun L => Paper.aux_lem_band_piece_product_trunc_Pcand d s n y g L) atTop
      (𝓝 (Paper.aux_lem_band_piece_product_Praw d s n y g)) := by
  rw [← aux_lfgc_p_trunc_conv_iSup_pcand]
  exact tendsto_atTop_iSup (aux_lfgc_p_trunc_conv_pcand_mono s n y g)

theorem aux_lfgc_p_trunc_conv_tendsto_dtr (M : GMCModel d) (s : ℝ) (n : ℕ) (y : Vec d) (g : PotentialSample d)
    (hfin : aux_lfgc_p_trunc_dfull M s n y g ≠ ⊤) :
    Tendsto (fun L => (aux_lfgc_p_trunc_dtr M s n y L g).toReal) atTop (𝓝 (aux_lfgc_p_trunc_dfull M s n y g).toReal) := by
  have hsum : Tendsto (fun L => ∑ j ∈ Finset.range (n + L + 1), aux_lfgc_p_trunc_dtail n y g j) atTop
      (𝓝 (∑' j, aux_lfgc_p_trunc_dtail n y g j)) :=
    (ENNReal.tendsto_nat_tsum _).comp (tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩)
  have hD : Tendsto (fun L => aux_lfgc_p_trunc_dtr M s n y L g) atTop (𝓝 (aux_lfgc_p_trunc_dfull M s n y g)) :=
    tendsto_const_nhds.add hsum
  exact (ENNReal.tendsto_toReal hfin).comp hD

theorem lfgc_p_trunc_conv (M : GMCModel d) (s eps : ℝ) (heps : 0 < eps) (n : ℕ) (y : Vec d)
    (g : PotentialSample d) :
    Tendsto (fun L => aux_lfgc_p_trunc_ztr M s eps n y L g) atTop (𝓝 (aux_lfgc_p_trunc_zfull M s eps n y g)) := by
  have h1 : eps / 2 < eps := by linarith
  have hF := ((Paper.aux_lem_band_piece_product_eramp_continuous _ _ h1).tendsto _).comp
    (aux_lfgc_p_trunc_conv_tendsto_ftr s n y g)
  have hP := ((Paper.aux_lem_band_piece_product_eramp_continuous 6 12 (by norm_num)).tendsto
    _).comp (aux_lfgc_p_trunc_conv_tendsto_pcand s n y g)
  exact (hF.add hP).add tendsto_const_nhds

end Paper
