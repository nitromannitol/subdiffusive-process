module

public import SubdiffusiveProcess.Paper.lfgc_sum_band
public import SubdiffusiveProcess.Paper.lfgc_p_trunc_lp
public import SubdiffusiveProcess.Paper.lfgc_fp_events

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Truncated prefix summands

`aux_lfgc_sum_trunc_summandTr` is the prefix aux_lfgc_sum_band_summand computed from the truncated scores of the canonical sample.
It depends only on the bilateral layers `-N, …, -j + L`, converges to the literal aux_lfgc_sum_band_summand as
`L → ∞` on every sample where the primitive scores have their formulas at the canonical sample
and the drift score is finite, and differs from the literal aux_lfgc_sum_band_summand in `L^p` by the uniform
truncation remainders.
-/

open MeasureTheory Filter Topology _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- The primitive score clauses identify the scores with the literal formulas. -/
theorem aux_lfgc_sum_trunc_scores_formula [NeZero d] (M : GMCModel d) (s eps : ℝ) (g : PotentialSample d)
    (Fs Ps Rs Ds : ℕ → Vec d → ℝ≥0∞) (Zs : ℕ → Vec d → ℝ) (good : ℕ → Vec d → Prop)
    (h : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps g Fs Ps Rs Ds Zs good) (m : ℕ) (z : Vec d) :
    Ds m z = aux_lfgc_p_trunc_dfull M s m z g ∧ Zs m z = aux_lfgc_p_trunc_zfull M s eps m z g := by
  obtain ⟨-, -, -, -, h2, h3, h4, h5, -, h7, -⟩ := h
  refine ⟨h5 m z, ?_⟩
  rw [(h7 m z).1, h2 m z, h3 m z, h4 m z]
  rfl

/-- The truncated prefix aux_lfgc_sum_band_summand. -/
noncomputable def aux_lfgc_sum_trunc_summandTr [NeZero d] (useD : Bool) (M : GMCModel d) (s eps : ℝ) (N : ℕ) (j : ℤ)
    (w : SpatialCoordinates d) (L : ℕ) (omega : BilateralField d) : ℝ :=
  if useD then (aux_lfgc_p_trunc_dtr M s ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) L (aux_lfgc_layer_tail_canonEta N omega)).toReal
  else aux_lfgc_p_trunc_ztr M s eps ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) L (aux_lfgc_layer_tail_canonEta N omega)

theorem aux_lfgc_sum_trunc_summandTr_window [NeZero d] (useD : Bool) (M : GMCModel d) (s eps : ℝ) (heps : 0 < eps)
    (N : ℕ) (j : ℤ) (w : SpatialCoordinates d) (L : ℕ) (S : Set ℤ)
    (hS : ∀ i : ℕ, i ≤ ((N : ℤ) - j).toNat + L → (i : ℤ) - (N : ℤ) ∈ S) :
    StronglyMeasurable[layerWindow C(SpatialCoordinates d, ℝ) S]
      (aux_lfgc_sum_trunc_summandTr useD M s eps N j w L) := by
  set n' := ((N : ℤ) - j).toNat
  have hmeas : Measurable (aux_lfgc_sum_trunc_summandTr useD M s eps N j w L) := by
    unfold aux_lfgc_sum_trunc_summandTr
    cases useD
    · exact (lfgc_p_trunc M s eps heps n' _ L).comp (aux_lfgc_layer_tail_measurable_canonEta N)
    · exact (ENNReal.measurable_toReal.comp (aux_lfgc_p_trunc_measurable_dtr M s n' _ L)).comp (aux_lfgc_layer_tail_measurable_canonEta N)
  refine (measurable_layerWindow_of_depends hmeas fun ω ω' h => ?_).stronglyMeasurable
  have hg : ∀ i ≤ n' + L, aux_lfgc_layer_tail_canonEta N ω i = aux_lfgc_layer_tail_canonEta N ω' i := fun i hi =>
    aux_lfgc_fp_events_canonEta_congr N i (h _ (hS i hi))
  unfold aux_lfgc_sum_trunc_summandTr
  cases useD
  · simp only [Bool.false_eq_true, ite_false]
    exact lfgc_p_trunc_dep M s eps n' _ L hg
  · simp only [ite_true]
    rw [aux_lfgc_p_trunc_dep_dtr_congr M s n' _ L hg]

/-- Sure convergence of the truncated aux_lfgc_sum_band_summand. -/
theorem lfgc_sum_trunc [NeZero d] (useD : Bool) (M : GMCModel d) (s eps : ℝ) (heps : 0 < eps)
    (Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (N : ℕ) (j : ℤ) (w : SpatialCoordinates d) (omega : BilateralField d)
    (hD : Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega =
      aux_lfgc_p_trunc_dfull M s ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) (aux_lfgc_layer_tail_canonEta N omega))
    (hZ : Z N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega =
      aux_lfgc_p_trunc_zfull M s eps ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) (aux_lfgc_layer_tail_canonEta N omega))
    (hfin : Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega ≠ ⊤)
    {L : ℕ → ℕ} (hL : Tendsto L atTop atTop) :
    Tendsto (fun H => aux_lfgc_sum_trunc_summandTr useD M s eps N j w (L H) omega) atTop
      (𝓝 (aux_lfgc_sum_band_summand useD Draw Z N j w omega)) := by
  unfold aux_lfgc_sum_trunc_summandTr aux_lfgc_sum_band_summand
  cases useD
  · simp only [Bool.false_eq_true, ite_false]
    rw [hZ]
    exact (lfgc_p_trunc_conv M s eps heps _ _ _).comp hL
  · simp only [ite_true]
    rw [hD] at hfin ⊢
    exact (aux_lfgc_p_trunc_conv_tendsto_dtr M s _ _ _ hfin).comp hL

end SubdiffusiveProcess.Paper
