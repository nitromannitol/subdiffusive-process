import SubdiffusiveProcess.Section10.PhysicalExitChainingProbability




open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalExitChaining

/-- Paths stay within the current exit ball between successive epochs. -/
theorem dist_le_on_exitEpoch_interval {d : ℕ} (C : Set (Vec d))
    {ρ : ℝ} (hρ : 0 < ρ) (j : ℕ) (p : ContinuousPath (Vec d))
    (hfin : exitEpoch C ρ j p ≠ ⊤)
    (hC : p (exitEpoch C ρ j p).toNNReal ∈ C) (t : ℝ≥0)
    (ht1 : exitEpoch C ρ j p ≤ t)
    (ht2 : (t : ℝ≥0∞) ≤ exitEpoch C ρ (j + 1) p) :
    dist (p t) (p (exitEpoch C ρ j p).toNNReal) ≤ ρ := by
  classical
  set a : ℝ≥0 := (exitEpoch C ρ j p).toNNReal with hadef
  have ha : (a : ℝ≥0∞) = exitEpoch C ρ j p := ENNReal.coe_toNNReal hfin
  set q := ContinuousPath.shift a p with hqdef
  have hq0 : q 0 = p a := by simp [hqdef, ContinuousPath.shift_apply]
  have htexq : stoppedLocalExit C ρ q =
      ContinuousPath.exitTime (Metric.ball (q 0) ρ) q := by
    unfold stoppedLocalExit localExit
    rw [if_pos (hq0 ▸ hC)]
  have hsucc : exitEpoch C ρ (j + 1) p =
      exitEpoch C ρ j p + stoppedLocalExit C ρ q :=
    exitEpoch_succ C ρ j p
  have hat : a ≤ t := by
    have : (a : ℝ≥0∞) ≤ t := ha ▸ ht1
    exact_mod_cast this
  set u : ℝ≥0 := t - a with hudef
  have htu : t = a + u := (add_tsub_cancel_of_le hat).symm
  have hu : (u : ℝ≥0∞) ≤ stoppedLocalExit C ρ q := by
    rw [hsucc, ← ha, htu, ENNReal.coe_add] at ht2
    exact (ENNReal.add_le_add_iff_left ENNReal.coe_ne_top).mp ht2
  have hqu : q u = p t := by rw [hqdef, ContinuousPath.shift_apply, ← htu]
  rw [← hqu, ← hq0]
  rcases lt_or_eq_of_le hu with hlt | heq
  · rw [htexq] at hlt
    have := ContinuousPath.mem_of_lt_exitTime _ q u hlt
    rw [Metric.mem_ball] at this
    exact this.le
  · rw [htexq] at heq
    have hne : ContinuousPath.exitTime (Metric.ball (q 0) ρ) q ≠ ⊤ := by
      rw [← heq]; exact ENNReal.coe_ne_top
    have hfr := ContinuousPath.coordinate_exitTime_mem_frontier (Metric.ball (q 0) ρ)
      Metric.isOpen_ball q (Metric.mem_ball_self hρ) hne
    rw [← heq, ENNReal.toNNReal_coe] at hfr
    exact le_of_eq (Metric.frontier_ball_subset_sphere hfr)

/-- Epochs control the modulus in `tight:prop-tightness`, Step 3. If the path stays in `C` up to `T`, the
`n`-th epoch is after `T`, and every gap starting by `T` is longer than `δ`, then the
oscillation over `[0, T]` at scale `δ` is at most `3ρ`. -/

theorem modulus_of_exitEpochs {d : ℕ} (C : Set (Vec d))
    {ρ : ℝ} (hρ : 0 < ρ) (T δ : ℝ≥0) (n : ℕ) (p : ContinuousPath (Vec d))
    (hstay : ∀ s : ℝ≥0, s ≤ T → p s ∈ C)
    (hn : (T : ℝ≥0∞) < exitEpoch C ρ n p)
    (hgap : ∀ j < n, exitEpoch C ρ j p ≤ T →
      p ∉ shortGapEvent C ρ (δ : ℝ≥0∞) j) :
    p ∈ ContinuousPath.modulusSet T (δ : ℝ≥0∞) (ENNReal.ofReal (3 * ρ)) := by
  classical
  set σ := fun j => exitEpoch C ρ j p with hσdef
  -- the key two-point bound for `s ≤ t`
  have key : ∀ s t : ℝ≥0, s ≤ t → t ≤ T → (t : ℝ) ≤ s + δ → dist (p s) (p t) ≤ 3 * ρ := by
    intro s t hst htT htsδ
    have hsT : s ≤ T := hst.trans htT
    have hex : ∃ i, (s : ℝ≥0∞) < σ (i + 1) := by
      have hn0 : n ≠ 0 := by
        rintro rfl
        simp [exitEpoch_zero] at hn
      refine ⟨n - 1, ?_⟩
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
      exact lt_of_le_of_lt (by exact_mod_cast hsT) hn
    set i := Nat.find hex with hidef
    have hi1 : (s : ℝ≥0∞) < σ (i + 1) := Nat.find_spec hex
    have hi0 : σ i ≤ s := by
      rcases Nat.eq_zero_or_pos i with h | h
      · rw [h]; simp [hσdef, exitEpoch_zero]
      · obtain ⟨i', hi'⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        have hlt : i' < Nat.find hex := by rw [← hidef]; omega
        have := Nat.find_min hex hlt
        rw [hi']
        exact not_lt.mp this
    have hin : i + 1 ≤ n := by
      have hn0 : n ≠ 0 := by
        rintro rfl
        simp [exitEpoch_zero] at hn
      have : i ≤ n - 1 := Nat.find_min' hex (by
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
        exact lt_of_le_of_lt (by exact_mod_cast hsT) hn)
      omega
    have hfin_i : σ i ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hi0
    have hσi_le : (σ i).toNNReal ≤ s := by
      have : ((σ i).toNNReal : ℝ≥0∞) ≤ s := by rw [ENNReal.coe_toNNReal hfin_i]; exact hi0
      exact_mod_cast this
    have hCi : p (σ i).toNNReal ∈ C := hstay _ (hσi_le.trans hsT)
    have hds : dist (p s) (p (σ i).toNNReal) ≤ ρ :=
      dist_le_on_exitEpoch_interval C hρ i p hfin_i hCi s hi0 hi1.le
    by_cases hti : (t : ℝ≥0∞) ≤ σ (i + 1)
    · have hdt : dist (p t) (p (σ i).toNNReal) ≤ ρ :=
        dist_le_on_exitEpoch_interval C hρ i p hfin_i hCi t
          (hi0.trans (by exact_mod_cast hst)) hti
      calc dist (p s) (p t) ≤ dist (p s) (p (σ i).toNNReal) + dist (p t) (p (σ i).toNNReal) :=
            dist_triangle_right _ _ _
        _ ≤ 3 * ρ := by linarith
    · rw [not_le] at hti
      have hfin1 : σ (i + 1) ≠ ⊤ := ne_top_of_lt hti
      have hσ1t : (σ (i + 1)).toNNReal ≤ t := by
        have : ((σ (i + 1)).toNNReal : ℝ≥0∞) ≤ t := by
          rw [ENNReal.coe_toNNReal hfin1]; exact hti.le
        exact_mod_cast this
      have hC1 : p (σ (i + 1)).toNNReal ∈ C := hstay _ (hσ1t.trans htT)
      have hin' : i + 1 < n := by
        rcases lt_or_eq_of_le hin with h | h
        · exact h
        · exfalso
          have : σ n < (T : ℝ≥0∞) + 1 := by
            rw [← h]
            exact lt_of_lt_of_le hti (by exact_mod_cast htT.trans (le_add_of_nonneg_right zero_le_one) |>.trans le_rfl)
          have h2 : σ n ≤ T := by rw [← h]; exact hti.le.trans (by exact_mod_cast htT)
          exact absurd hn (not_lt.mpr h2)
      have hg := hgap (i + 1) hin' (hti.le.trans (by exact_mod_cast htT))
      have hlong : (δ : ℝ≥0∞) < stoppedLocalExit C ρ
          (ContinuousPath.shift (σ (i + 1)).toNNReal p) := by
        by_contra hcon
        exact hg ⟨hfin1, not_lt.mp hcon⟩
      have hσ2 : σ (i + 2) = σ (i + 1) + stoppedLocalExit C ρ
          (ContinuousPath.shift (σ (i + 1)).toNNReal p) :=
        exitEpoch_succ C ρ (i + 1) p
      have ht2 : (t : ℝ≥0∞) ≤ σ (i + 2) := by
        rw [hσ2]
        have htsδ' : (t : ℝ≥0∞) ≤ (s : ℝ≥0∞) + δ := by
          have : t ≤ s + δ := by
            rw [← NNReal.coe_le_coe, NNReal.coe_add]; exact htsδ
          exact_mod_cast this
        calc (t : ℝ≥0∞) ≤ (s : ℝ≥0∞) + δ := htsδ'
          _ ≤ σ (i + 1) + stoppedLocalExit C ρ
              (ContinuousPath.shift (σ (i + 1)).toNNReal p) := add_le_add hi1.le hlong.le
      have hdt : dist (p t) (p (σ (i + 1)).toNNReal) ≤ ρ :=
        dist_le_on_exitEpoch_interval C hρ (i + 1) p hfin1 hC1 t hti.le ht2
      have hd1 : dist (p (σ (i + 1)).toNNReal) (p (σ i).toNNReal) ≤ ρ :=
        dist_le_on_exitEpoch_interval C hρ i p hfin_i hCi _
          (by rw [ENNReal.coe_toNNReal hfin1]; exact exitEpoch_mono_succ C ρ i p)
          (by rw [ENNReal.coe_toNNReal hfin1])
      calc dist (p s) (p t) ≤ dist (p s) (p (σ i).toNNReal) +
            dist (p (σ i).toNNReal) (p (σ (i + 1)).toNNReal) +
            dist (p (σ (i + 1)).toNNReal) (p t) := dist_triangle4 _ _ _ _
        _ ≤ 3 * ρ := by
          rw [dist_comm (p (σ i).toNNReal), dist_comm (p (σ (i + 1)).toNNReal) (p t)]
          linarith
  intro s t hs ht hst
  have hst' : dist s t ≤ δ := by
    rw [edist_dist] at hst
    have := (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).mp hst
    simpa using this
  rw [edist_dist]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases le_total s t with h | h
  · refine key s t h ht ?_
    rw [NNReal.dist_eq] at hst'
    have := le_abs_self ((t : ℝ) - s)
    rw [abs_sub_comm] at this
    linarith
  · rw [dist_comm]
    refine key t s h hs ?_
    rw [NNReal.dist_eq] at hst'
    have := le_abs_self ((s : ℝ) - t)
    linarith

theorem modulus_bound_of_restart_estimates {d : ℕ}
    (k : Kernel (Vec d) (ContinuousPath (Vec d)))
    [IsMarkovKernel k]
    (L : Kernel (Vec d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (k z) = L z)
    (hSM : StrongMarkov L) (h0 : ∀ z, ∀ᵐ p ∂k z, p 0 = z)
    (C : Set (Vec d)) (hC : MeasurableSet C) {ρ : ℝ} (hρ : 0 < ρ)
    (T δ : ℝ≥0) {h : ℝ} (hh : 0 < h) (γ : ℝ≥0∞)
    (hγ : ∀ y ∈ C, ∫⁻ p, exitWeight h
      (ContinuousPath.exitTime (Metric.ball y ρ) p) ∂k y ≤ γ)
    (β : ℝ≥0∞)
    (hβ : ∀ y ∈ C, k y {p | ContinuousPath.exitTime (Metric.ball y ρ) p ≤ (δ : ℝ≥0∞)} ≤ β)
    (n : ℕ) (z : Vec d) :
    k z (ContinuousPath.modulusSet T (δ : ℝ≥0∞) (ENNReal.ofReal (3 * ρ)))ᶜ ≤
      k z {p | ∃ s : ℝ≥0, s ≤ T ∧ p s ∉ C} +
        ENNReal.ofReal (Real.exp (T / h)) * γ ^ n + n * β := by
  set A : Set (ContinuousPath (Vec d)) := {p | ∃ s : ℝ≥0, s ≤ T ∧ p s ∉ C} with hAdef
  set B : Set (ContinuousPath (Vec d)) := {p | exitEpoch C ρ n p ≤ (T : ℝ≥0∞)}
    with hBdef
  have hBm : MeasurableSet B :=
    measurableSet_le (measurable_exitEpoch C hC ρ n) measurable_const
  have hsub : (ContinuousPath.modulusSet T (δ : ℝ≥0∞) (ENNReal.ofReal (3 * ρ)))ᶜ ⊆
      A ∪ B ∪ ⋃ j ∈ Finset.range n, shortGapEvent C ρ (δ : ℝ≥0∞) j := by
    intro p hp
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_range, not_or, not_exists] at hcon
    obtain ⟨⟨hA, hB⟩, hG⟩ := hcon
    apply hp
    refine modulus_of_exitEpochs C hρ T δ n p ?_ ?_ ?_
    · intro s hs
      by_contra hsC
      exact hA ⟨s, hs, hsC⟩
    · exact not_le.mp hB
    · intro j hj _
      exact hG j hj
  have hBbound : k z B ≤ ENNReal.ofReal (Real.exp (T / h)) * γ ^ n := by
    have hmom := exitEpoch_weight_integral_le k L hL hSM h0 C hC ρ γ hγ n z
    calc k z B = ∫⁻ p, B.indicator 1 p ∂k z := (lintegral_indicator_one hBm).symm
      _ ≤ ∫⁻ p, ENNReal.ofReal (Real.exp (T / h)) *
            exitWeight h (exitEpoch C ρ n p) ∂k z := by
          refine lintegral_mono fun p => ?_
          by_cases hpB : p ∈ B
          · rw [Set.indicator_of_mem hpB, Pi.one_apply]
            have hw := exitWeight_ge hh (T := (T : ℝ)) T.coe_nonneg
              (s := exitEpoch C ρ n p) (by
                rw [ENNReal.ofReal_coe_nnreal]; exact hpB)
            calc (1 : ℝ≥0∞) = ENNReal.ofReal (Real.exp (T / h)) *
                  ENNReal.ofReal (Real.exp (-(T : ℝ) / h)) := by
                  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
                  simp [neg_div]
              _ ≤ _ := by gcongr
          · rw [Set.indicator_of_notMem hpB]; exact zero_le _
      _ = ENNReal.ofReal (Real.exp (T / h)) * ∫⁻ p,
            exitWeight h (exitEpoch C ρ n p) ∂k z :=
          lintegral_const_mul _ ((measurable_exitWeight h).comp
            (measurable_exitEpoch C hC ρ n))
      _ ≤ _ := by gcongr
  have hgap := shortGapEvent_measure_le k L hL hSM h0 C hC ρ (δ : ℝ≥0∞)
    ENNReal.coe_ne_top β hβ
  calc k z (ContinuousPath.modulusSet T (δ : ℝ≥0∞) (ENNReal.ofReal (3 * ρ)))ᶜ
      ≤ k z (A ∪ B ∪ ⋃ j ∈ Finset.range n, shortGapEvent C ρ (δ : ℝ≥0∞) j) :=
        measure_mono hsub
    _ ≤ k z (A ∪ B) + k z (⋃ j ∈ Finset.range n,
          shortGapEvent C ρ (δ : ℝ≥0∞) j) := measure_union_le _ _
    _ ≤ (k z A + k z B) + ∑ j ∈ Finset.range n,
          k z (shortGapEvent C ρ (δ : ℝ≥0∞) j) :=
        add_le_add (measure_union_le _ _) (measure_biUnion_finset_le _ _)
    _ ≤ (k z A + ENNReal.ofReal (Real.exp (T / h)) * γ ^ n) + ∑ _j ∈ Finset.range n, β :=
        add_le_add (add_le_add le_rfl hBbound) (Finset.sum_le_sum fun j _ => hgap j z)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end SubdiffusiveProcess.Section10.PhysicalExitChaining
