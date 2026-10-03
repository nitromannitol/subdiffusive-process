module

public import SubdiffusiveProcess.Analysis.CompactPotentialC1Norm
public import SubdiffusiveProcess.Analysis.CompactGradientLipschitz
public import SubdiffusiveProcess.Main.PositiveAnchoredInfraredTruncation
public import SubdiffusiveProcess.Frozen.Assumptions.IsAnchoredC11Limit
public import SubdiffusiveProcess.Assumptions.AnchoredPartialSum

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

theorem native_infrared_compact_observable_envelope
    {d : ℕ} (omega : NativeBilateralPotentialSample d)
    (H : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
    (hH : SubdiffusiveProcess.Frozen.Assumptions.IsAnchoredC11Limit
      (positiveScaledNativeLayer omega) H)
    (K : Compacts (SpatialCoordinates d))
    (hC1 : Summable (fun n : ℕ => compactPotentialC1Norm K
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor
        (positiveScaledNativeLayer omega n))))
    (hLip : Summable (fun n : ℕ => compactGradientLipschitzObservable K
      (positiveScaledNativeLayer omega n))) :
    compactPotentialC1Norm K H ≤
        ∑' n : ℕ, compactPotentialC1Norm K
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor
            (positiveScaledNativeLayer omega n)) ∧
      compactGradientLipschitzObservable K H ≤
        ∑' n : ℕ, compactGradientLipschitzObservable K
          (positiveScaledNativeLayer omega n) ∧
      ∀ L : ℕ,
        compactPotentialC1Norm K (positiveAnchoredInfraredTruncation omega L) ≤
            ∑' n : ℕ, compactPotentialC1Norm K
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor
                (positiveScaledNativeLayer omega n)) ∧
        compactGradientLipschitzObservable K
              (positiveAnchoredInfraredTruncation omega L) ≤
            ∑' n : ℕ, compactGradientLipschitzObservable K
              (positiveScaledNativeLayer omega n) := by
  have hC1_add (g h : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
      compactPotentialC1Norm K
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add g h) ≤
        compactPotentialC1Norm K g + compactPotentialC1Norm K h := by
    let vg : C(K, ℝ) :=
      ⟨fun x : K => g x.1, g.1.1.continuous.comp continuous_subtype_val⟩
    let vh : C(K, ℝ) :=
      ⟨fun x : K => h x.1, h.1.1.continuous.comp continuous_subtype_val⟩
    let vgh : C(K, ℝ) :=
      ⟨fun x : K => (g.add h) x.1,
        (g.add h).1.1.continuous.comp continuous_subtype_val⟩
    let dg : C(K, SpatialCoordinates d →L[ℝ] ℝ) :=
      ⟨fun x : K => g.deriv x.1,
        g.deriv.continuous.comp continuous_subtype_val⟩
    let dh : C(K, SpatialCoordinates d →L[ℝ] ℝ) :=
      ⟨fun x : K => h.deriv x.1,
        h.deriv.continuous.comp continuous_subtype_val⟩
    let dgh : C(K, SpatialCoordinates d →L[ℝ] ℝ) :=
      ⟨fun x : K => (g.add h).deriv x.1,
        (g.add h).deriv.continuous.comp continuous_subtype_val⟩
    have hv : vgh = vg + vh := by
      apply ContinuousMap.ext
      intro x
      change (g.add h) x.1 = g x.1 + h x.1
      exact SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add_apply g h x.1
    have hd : dgh = dg + dh := by
      apply ContinuousMap.ext
      intro x
      change (g.add h).deriv x.1 = g.deriv x.1 + h.deriv x.1
      exact SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add_deriv g h x.1
    simp only [compactPotentialC1Norm]
    change ‖vgh‖ + ‖dgh‖ ≤ (‖vg‖ + ‖dg‖) + (‖vh‖ + ‖dh‖)
    rw [hv, hd]
    have hvnorm : ‖vg + vh‖ ≤ ‖vg‖ + ‖vh‖ := norm_add_le vg vh
    have hdnorm : ‖dg + dh‖ ≤ ‖dg‖ + ‖dh‖ := norm_add_le dg dh
    calc
      ‖vg + vh‖ + ‖dg + dh‖ ≤
          (‖vg‖ + ‖vh‖) + (‖dg‖ + ‖dh‖) :=
        add_le_add hvnorm hdnorm
      _ = (‖vg‖ + ‖dg‖) + (‖vh‖ + ‖dh‖) := by ac_rfl
  have hLip_nonneg (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
      0 ≤ compactGradientLipschitzObservable K g := by
    apply Real.sSup_nonneg
    rintro a ⟨x, y, hxy, rfl⟩
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hLip_ratio (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
      {x y : K} (hxy : x ≠ y) :
      ‖g.deriv x.1 - g.deriv y.1‖ / ‖x.1 - y.1‖ ≤
        compactGradientLipschitzObservable K g := by
    have hdist : 0 < ‖(x.1 : SpatialCoordinates d) - y.1‖ := by
      rw [← dist_eq_norm]
      exact dist_pos.mpr (fun h ↦ hxy (Subtype.ext h))
    have hbound :=
      (deriv_lipschitzOnWith_compactGradientLipschitzObservable K g).dist_le_mul
        x x.2 y y.2
    have hbound' :
        ‖g.deriv x.1 - g.deriv y.1‖ ≤
          compactGradientLipschitzObservable K g * ‖x.1 - y.1‖ := by
      simpa only [dist_eq_norm, Real.coe_toNNReal _ (hLip_nonneg g)] using hbound
    exact (div_le_iff₀ hdist).2 hbound'
  have hLip_add (g h : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
      compactGradientLipschitzObservable K
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add g h) ≤
        compactGradientLipschitzObservable K g +
          compactGradientLipschitzObservable K h := by
    apply Real.sSup_le
    intro a ha
    rcases ha with ⟨x, y, hxy, rfl⟩
    have hdist : 0 < ‖(x.1 : SpatialCoordinates d) - y.1‖ := by
      rw [← dist_eq_norm]
      exact dist_pos.mpr (fun h ↦ hxy (Subtype.ext h))
    have hg := hLip_ratio g hxy
    have hh := hLip_ratio h hxy
    rw [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add_deriv]
    calc
      ‖(g.deriv x.1 + h.deriv x.1) - (g.deriv y.1 + h.deriv y.1)‖ /
          ‖x.1 - y.1‖ =
          ‖(g.deriv x.1 - g.deriv y.1) +
            (h.deriv x.1 - h.deriv y.1)‖ / ‖x.1 - y.1‖ := by
              rw [add_sub_add_comm]
      _ ≤ (‖g.deriv x.1 - g.deriv y.1‖ +
            ‖h.deriv x.1 - h.deriv y.1‖) / ‖x.1 - y.1‖ := by
              gcongr
              exact norm_add_le _ _
      _ = ‖g.deriv x.1 - g.deriv y.1‖ / ‖x.1 - y.1‖ +
          ‖h.deriv x.1 - h.deriv y.1‖ / ‖x.1 - y.1‖ := by
            rw [add_div]
      _ ≤ compactGradientLipschitzObservable K g +
          compactGradientLipschitzObservable K h := add_le_add hg hh
    · exact add_nonneg (hLip_nonneg g) (hLip_nonneg h)
  have hLip_anchor (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
      compactGradientLipschitzObservable K
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor g) =
        compactGradientLipschitzObservable K g := by
    simp only [compactGradientLipschitzObservable,
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor_deriv]
  let f : ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d :=
    positiveScaledNativeLayer omega
  have hC1_partial : ∀ L : ℕ,
      compactPotentialC1Norm K
          (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField f L) ≤
        ∑ n ∈ Finset.range (L + 1),
          compactPotentialC1Norm K (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n)) := by
    intro L
    induction L with
    | zero =>
        simp only [SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField,
          Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
        exact le_rfl
    | succ L ih =>
        rw [SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField]
        calc
          compactPotentialC1Norm K
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
                (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField f L)
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f (L + 1)))) ≤
              compactPotentialC1Norm K
                (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField f L) +
              compactPotentialC1Norm K
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f (L + 1))) :=
            hC1_add _ _
          _ ≤ (∑ n ∈ Finset.range (L + 1),
              compactPotentialC1Norm K
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n))) +
              compactPotentialC1Norm K
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f (L + 1))) :=
            by gcongr
          _ = ∑ n ∈ Finset.range ((L + 1) + 1),
              compactPotentialC1Norm K
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n)) := by
            simp only [Finset.sum_range_succ]
  have hLip_partial : ∀ L : ℕ,
      compactGradientLipschitzObservable K
          (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField f L) ≤
        ∑ n ∈ Finset.range (L + 1),
          compactGradientLipschitzObservable K (f n) := by
    intro L
    induction L with
    | zero =>
        simp only [SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField,
          Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
        exact le_rfl
    | succ L ih =>
        rw [SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField]
        calc
          compactGradientLipschitzObservable K
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
                (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField f L)
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f (L + 1)))) ≤
              compactGradientLipschitzObservable K
                (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField f L) +
              compactGradientLipschitzObservable K
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f (L + 1))) :=
            hLip_add _ _
          _ ≤ (∑ n ∈ Finset.range (L + 1),
              compactGradientLipschitzObservable K (f n)) +
              compactGradientLipschitzObservable K (f (L + 1)) := by
            rw [hLip_anchor]
            gcongr
          _ = ∑ n ∈ Finset.range ((L + 1) + 1),
              compactGradientLipschitzObservable K (f n) := by
            simp only [Finset.sum_range_succ]
  have hC1_nonneg (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
      0 ≤ compactPotentialC1Norm K g := by
    simp only [compactPotentialC1Norm]
    positivity
  have hC1_partial_tsum (L : ℕ) :
      compactPotentialC1Norm K
          (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField f L) ≤
        ∑' n : ℕ, compactPotentialC1Norm K
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n)) := by
    refine (hC1_partial L).trans ?_
    apply hC1.sum_le_tsum
    intro i hi
    exact hC1_nonneg _
  have hLip_partial_tsum (L : ℕ) :
      compactGradientLipschitzObservable K
          (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField f L) ≤
        ∑' n : ℕ, compactGradientLipschitzObservable K (f n) := by
    refine (hLip_partial L).trans ?_
    apply hLip.sum_le_tsum
    intro i hi
    exact hLip_nonneg _
  have hC1_trunc : ∀ L : ℕ,
      compactPotentialC1Norm K (positiveAnchoredInfraredTruncation omega L) ≤
        ∑ n ∈ Finset.range L,
          compactPotentialC1Norm K
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n)) := by
    intro L
    induction L with
    | zero =>
        change compactPotentialC1Norm K (zeroNativePotentialField d) ≤ 0
        unfold compactPotentialC1Norm
        let zv : C(K, ℝ) :=
          ⟨fun x : K => (zeroNativePotentialField d) x.1,
            (zeroNativePotentialField d).1.1.continuous.comp continuous_subtype_val⟩
        let zd : C(K, SpatialCoordinates d →L[ℝ] ℝ) :=
          ⟨fun x : K => (zeroNativePotentialField d).deriv x.1,
            (zeroNativePotentialField d).deriv.continuous.comp continuous_subtype_val⟩
        have hzv : zv = 0 := by
          apply ContinuousMap.ext
          intro x
          simp [zv, zeroNativePotentialField]
        have hzd : zd = 0 := by
          apply ContinuousMap.ext
          intro x
          simp [zd, zeroNativePotentialField,
            SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv]
        change ‖zv‖ + ‖zd‖ ≤ 0
        rw [hzv, hzd]
        simp only [norm_zero, zero_add]
        exact (show ‖(0 : C(K, SpatialCoordinates d →L[ℝ] ℝ))‖ = 0 from
          (@norm_zero (C(K, SpatialCoordinates d →L[ℝ] ℝ)) _)).le
    | succ L ih =>
        rw [positiveAnchoredInfraredTruncation]
        calc
          compactPotentialC1Norm K
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
                (positiveAnchoredInfraredTruncation omega L)
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f L))) ≤
              compactPotentialC1Norm K (positiveAnchoredInfraredTruncation omega L) +
              compactPotentialC1Norm K
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f L)) :=
            hC1_add _ _
          _ ≤ (∑ n ∈ Finset.range L,
              compactPotentialC1Norm K
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n))) +
              compactPotentialC1Norm K
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f L)) := by
            gcongr
          _ = ∑ n ∈ Finset.range (L + 1),
              compactPotentialC1Norm K
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n)) := by
            simp only [Finset.sum_range_succ]
  have hLip_trunc : ∀ L : ℕ,
      compactGradientLipschitzObservable K
          (positiveAnchoredInfraredTruncation omega L) ≤
        ∑ n ∈ Finset.range L,
          compactGradientLipschitzObservable K (f n) := by
    intro L
    induction L with
    | zero =>
        simp only [positiveAnchoredInfraredTruncation]
        apply Real.sSup_le
        · intro a ha
          rcases ha with ⟨x, y, hxy, rfl⟩
          simp [zeroNativePotentialField,
            SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv]
        · exact le_rfl
    | succ L ih =>
        rw [positiveAnchoredInfraredTruncation]
        calc
          compactGradientLipschitzObservable K
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
                (positiveAnchoredInfraredTruncation omega L)
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f L))) ≤
              compactGradientLipschitzObservable K
                (positiveAnchoredInfraredTruncation omega L) +
              compactGradientLipschitzObservable K
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f L)) :=
            hLip_add _ _
          _ ≤ (∑ n ∈ Finset.range L,
              compactGradientLipschitzObservable K (f n)) +
              compactGradientLipschitzObservable K (f L) := by
            rw [hLip_anchor]
            gcongr
          _ = ∑ n ∈ Finset.range (L + 1),
              compactGradientLipschitzObservable K (f n) := by
            simp only [Finset.sum_range_succ]
  have hC1_trunc_tsum (L : ℕ) :
      compactPotentialC1Norm K (positiveAnchoredInfraredTruncation omega L) ≤
        ∑' n : ℕ, compactPotentialC1Norm K
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n)) := by
    refine (hC1_trunc L).trans ?_
    apply hC1.sum_le_tsum
    intro i hi
    exact hC1_nonneg _
  have hLip_trunc_tsum (L : ℕ) :
      compactGradientLipschitzObservable K
          (positiveAnchoredInfraredTruncation omega L) ≤
        ∑' n : ℕ, compactGradientLipschitzObservable K (f n) := by
    refine (hLip_trunc L).trans ?_
    apply hLip.sum_le_tsum
    intro i hi
    exact hLip_nonneg _
  have hfield_tendsto :
      Tendsto (fun L => SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField f L)
        atTop (nhds H) := by
    erw [tendsto_subtype_rng]
    change Tendsto (fun L =>
      ((SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField f L).1.1,
        (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField f L).1.2)) atTop
      (nhds (H.1.1, H.1.2))
    rw [nhds_prod_eq]
    apply Tendsto.prodMk
    · rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
      intro S hS
      have hv := hH.value_tendsto (S : Set (SpatialCoordinates d)) hS
      simpa only [SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField_apply] using hv
    · rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
      intro S hS
      have hd := hH.deriv_tendsto (S : Set (SpatialCoordinates d)) hS
      simpa only [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv] using hd
  have hC1_H :
      compactPotentialC1Norm K H ≤
        ∑' n : ℕ, compactPotentialC1Norm K
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n)) := by
    have hnorm : Tendsto
        (fun L => compactPotentialC1Norm K
          (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField f L)) atTop
        (nhds (compactPotentialC1Norm K H)) := by
      exact ((compactPotentialC1Norm_continuous K).tendsto H).comp hfield_tendsto
    exact le_of_tendsto hnorm (Filter.Eventually.of_forall hC1_partial_tsum)
  have hLip_H :
      compactGradientLipschitzObservable K H ≤
        ∑' n : ℕ, compactGradientLipschitzObservable K (f n) := by
    have hderiv := hH.deriv_tendsto (K : Set (SpatialCoordinates d)) K.isCompact
    apply Real.sSup_le
    · intro a ha
      rcases ha with ⟨x, y, hxy, rfl⟩
      have hdist : 0 < ‖(x.1 : SpatialCoordinates d) - y.1‖ := by
        rw [← dist_eq_norm]
        exact dist_pos.mpr (fun h ↦ hxy (Subtype.ext h))
      have hx := hderiv.tendsto_at x.2
      have hy := hderiv.tendsto_at y.2
      have hratio : Tendsto
          (fun L =>
            ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv
                (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField f L) x.1 -
              SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv
                (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField f L) y.1‖ /
              ‖x.1 - y.1‖) atTop
          (nhds (‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv H x.1 -
              SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv H y.1‖ /
              ‖x.1 - y.1‖)) := by
        exact (hx.sub hy).norm.div_const _
      apply le_of_tendsto hratio
      exact Filter.Eventually.of_forall (fun L ↦
        (hLip_ratio
          (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField f L) hxy).trans
          (hLip_partial_tsum L))
    · exact tsum_nonneg (fun n ↦ hLip_nonneg (f n))
  constructor
  · simpa only [f] using hC1_H
  constructor
  · simpa only [f] using hLip_H
  · intro L
    exact ⟨hC1_trunc_tsum L, hLip_trunc_tsum L⟩


end SubdiffusiveProcess
