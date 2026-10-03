module

public import SubdiffusiveProcess.Main.CompactPotentialC1Norm
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSeries

@[expose] public section

/-! # Deterministic native infrared series

Compact summability of the anchored C1 norms and derivative Lipschitz
constants supplies the existing GMC shell-series construction. The result
retains the native potential carrier and identifies both value and derivative
series, with compact C1 convergence of the inclusive partial sums.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped BigOperators NNReal Topology
noncomputable section

namespace SubdiffusiveProcess

private theorem shellC11Summable_of_compactC1_lipschitz
    {d : ℕ} (f : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hC1 : ∀ K : Compacts (SpatialCoordinates d),
      Summable (fun n => compactPotentialC1Norm K
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n))))
    (hLip : ∀ K : Compacts (SpatialCoordinates d),
      ∃ c : ℕ → NNReal,
        (∀ n, LipschitzOnWith (c n)
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n)))
          (K : Set (SpatialCoordinates d))) ∧
        Summable (fun n => (c n : ℝ))) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellC11Summable f := by
  intro R
  let K : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall (0 : SpatialCoordinates d) R, isCompact_closedBall _ _⟩
  let b : ℕ → ℝ := fun n =>
    compactPotentialC1Norm K
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n))
  obtain ⟨c, hc, hcs⟩ := hLip K
  have hb : Summable b := hC1 K
  refine ⟨b, b, fun n => c n, ?_, ?_, ?_, hb, hb, hcs, ?_, ?_, ?_⟩
  · intro n
    simp only [b, compactPotentialC1Norm]
    positivity
  · intro n
    simp only [b, compactPotentialC1Norm]
    positivity
  · intro n
    exact (c n).coe_nonneg
  · intro n x hx
    have hn := ContinuousMap.norm_coe_le_norm
      ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n)).1.1.restrict
        (K : Set (SpatialCoordinates d))) ⟨x, hx⟩
    dsimp [b, compactPotentialC1Norm]
    change |f n x - f n 0| ≤
      ‖(SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n)).1.1.restrict
          (K : Set (SpatialCoordinates d))‖ +
        ‖(SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n))).restrict
            (K : Set (SpatialCoordinates d))‖
    calc
      |f n x - f n 0| ≤
          ‖(SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n)).1.1.restrict
            (K : Set (SpatialCoordinates d))‖ := by
              change ‖(SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n)) x‖ ≤
                ‖(SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n)).1.1.restrict
                  (K : Set (SpatialCoordinates d))‖ at hn
              rw [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor_apply, Real.norm_eq_abs] at hn
              exact hn
      _ ≤ _ := le_add_of_nonneg_right (norm_nonneg
        ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n))).restrict
            (K : Set (SpatialCoordinates d))))
  · intro n x hx
    have hn := ContinuousMap.norm_coe_le_norm
      ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n))).restrict
        (K : Set (SpatialCoordinates d))) ⟨x, hx⟩
    dsimp [b, compactPotentialC1Norm]
    change ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (f n) x‖ ≤
      ‖(SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n)).1.1.restrict
          (K : Set (SpatialCoordinates d))‖ +
        ‖(SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n))).restrict
            (K : Set (SpatialCoordinates d))‖
    calc
      ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (f n) x‖ =
          ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n)) x‖ := by
              rw [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor_deriv]
      _ ≤ ‖(SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n))).restrict
            (K : Set (SpatialCoordinates d))‖ := hn
      _ ≤ _ := le_add_of_nonneg_left (norm_nonneg
        ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n)).1.1.restrict
          (K : Set (SpatialCoordinates d))))
  · intro n x hx y hy
    have hn := (hc n).dist_le_mul x hx y hy
    simpa only [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor_deriv,
      dist_eq_norm] using hn

/-- The deterministic summability step in Part A's infrared construction. -/
theorem exists_native_potentialField_sum_of_summable_compact_c1
    {d : ℕ} (f : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hC1 : ∀ K : Compacts (SpatialCoordinates d),
      Summable (fun n => compactPotentialC1Norm K
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n))))
    (hLip : ∀ K : Compacts (SpatialCoordinates d),
      ∃ c : ℕ → NNReal,
        (∀ n, LipschitzOnWith (c n)
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n)))
          (K : Set (SpatialCoordinates d))) ∧
        Summable (fun n => (c n : ℝ))) :
    ∃ H : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      (∀ x : SpatialCoordinates d,
        H x = ∑' n : ℕ, (f n x - f n 0)) ∧
      (∀ x : SpatialCoordinates d,
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv H x =
          ∑' n : ℕ, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (f n) x) ∧
      (∀ K : Compacts (SpatialCoordinates d),
        Tendsto
          (fun L => compactPotentialC1Norm K
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
              (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField f L)
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) H)))
          atTop (nhds 0)) ∧
      (∀ K : Compacts (SpatialCoordinates d),
        ∃ C : NNReal, LipschitzOnWith C
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv H)
          (K : Set (SpatialCoordinates d))) := by
  have hs := shellC11Summable_of_compactC1_lipschitz f hC1 hLip
  let H : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.anchoredLimitField hs
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [H,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.anchoredLimitField_apply,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.shellAnchoredValue]
  · intro x
    simp only [H,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.anchoredLimitField_deriv,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.shellDerivSum]
  · intro K
    let q : ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d := fun L =>
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
        (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField f L)
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) H)
    have hlim :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.isAnchoredC11Limit_anchoredLimitField hs
    have hval := hlim.value_tendsto (K : Set (SpatialCoordinates d)) K.isCompact
    have hderiv := hlim.deriv_tendsto (K : Set (SpatialCoordinates d)) K.isCompact
    have hvalnorm : Tendsto (fun L =>
        ‖(q L).1.1.restrict (K : Set (SpatialCoordinates d))‖)
        atTop (nhds 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hval) ε hε)
      refine ⟨N, fun L hL => ?_⟩
      have hnorm : 0 ≤ ‖(q L).1.1.restrict (K : Set (SpatialCoordinates d))‖ :=
        norm_nonneg _
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hnorm]
      apply (ContinuousMap.norm_lt_iff _ hε).2
      intro x
      have hx := hN L hL x x.property
      change ‖H x - SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSum f L x‖ < ε at hx
      simp only [q, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add_apply,
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale_apply,
        SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField_apply,
        ContinuousMap.restrict_apply, neg_one_mul]
      rw [← sub_eq_add_neg, norm_sub_rev]
      exact hx
    have hderivnorm : Tendsto (fun L =>
        ‖(SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (q L)).restrict
          (K : Set (SpatialCoordinates d))‖)
        atTop (nhds 0) := by
      have hscale (z : SpatialCoordinates d) :
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) H) z =
            -SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv H z := by
        change ((-1 : ℝ) • ContinuousLinearMap.id ℝ
          (SpatialCoordinates d →L[ℝ] ℝ))
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv H z) = _
        simp only [smul_apply, ContinuousLinearMap.id_apply]
        exact neg_one_smul ℝ (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv H z)
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ :=
        eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hderiv) ε hε)
      refine ⟨N, fun L hL => ?_⟩
      have hnorm : 0 ≤ ‖(SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (q L)).restrict
          (K : Set (SpatialCoordinates d))‖ := by positivity
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hnorm]
      apply (ContinuousMap.norm_lt_iff _ hε).2
      intro x
      have hx := hN L hL x x.property
      change ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv
          (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField f L) x +
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) H) x‖ < ε
      rw [hscale x, ← sub_eq_add_neg]
      simpa only [q, H, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add_deriv,
        hscale,
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.deriv_anchoredPartialSumField,
        ContinuousMap.restrict_apply, neg_one_smul, dist_eq_norm, norm_sub_rev] using hx
    have hsum : Tendsto (fun L =>
        ‖(q L).1.1.restrict (K : Set (SpatialCoordinates d))‖ +
          ‖(SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (q L)).restrict
            (K : Set (SpatialCoordinates d))‖)
        atTop (nhds 0) := by simpa only [add_zero] using hvalnorm.add hderivnorm
    change Tendsto (fun L =>
      ‖(q L).1.1.restrict (K : Set (SpatialCoordinates d))‖ +
        ‖(SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (q L)).restrict
          (K : Set (SpatialCoordinates d))‖) atTop (nhds 0)
    exact hsum
  · intro K
    obtain ⟨c, hc, hcs⟩ := hLip K
    have hnonneg : 0 ≤ ∑' n : ℕ, (c n : ℝ) :=
      tsum_nonneg (fun n => (c n).coe_nonneg)
    refine ⟨Real.toNNReal (∑' n : ℕ, (c n : ℝ)), ?_⟩
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    obtain ⟨u, v, w, hb⟩ := hs (max ‖x‖ ‖y‖ + 1)
    have hxR : x ∈ Metric.closedBall (0 : SpatialCoordinates d) (max ‖x‖ ‖y‖ + 1) := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      linarith [le_max_left ‖x‖ ‖y‖]
    have hyR : y ∈ Metric.closedBall (0 : SpatialCoordinates d) (max ‖x‖ ‖y‖ + 1) := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      linarith [le_max_right ‖x‖ ‖y‖]
    have hdx : Summable (fun n =>
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (f n) x) :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.summable_deriv_apply hb hxR
    have hdy : Summable (fun n =>
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (f n) y) :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.summable_deriv_apply hb hyR
    have hdiff :
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv H x -
            SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv H y =
          ∑' n : ℕ,
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (f n) x -
              SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (f n) y) := by
      simp only [H,
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.anchoredLimitField_deriv,
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.shellDerivSum]
      exact (hdx.tsum_sub hdy).symm
    rw [dist_eq_norm, hdiff]
    have hterm : Summable (fun n =>
        ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (f n) x -
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (f n) y‖) := by
      have hbound : Summable (fun n => (c n : ℝ) * ‖x - y‖) := hcs.mul_right _
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hbound
      intro n
      have hn := (hc n).dist_le_mul x hx y hy
      simpa only [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor_deriv,
        dist_eq_norm] using hn
    refine le_trans (norm_tsum_le_tsum_norm hterm) ?_
    have hbound : Summable (fun n => (c n : ℝ) * ‖x - y‖) := hcs.mul_right _
    refine le_trans (Summable.tsum_mono hterm hbound
      (fun n => ?_)) ?_
    · have hn := (hc n).dist_le_mul x hx y hy
      simpa only [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor_deriv,
        dist_eq_norm] using hn
    · rw [tsum_mul_right]
      rw [Real.coe_toNNReal _ hnonneg, dist_eq_norm]

end SubdiffusiveProcess
