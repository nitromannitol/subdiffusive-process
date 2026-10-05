module

public import SubdiffusiveProcess.Geometry.CoordinateFold
public import SubdiffusiveProcess.Probability.InfraredCommonFieldConvergence
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Topology.Bases
public import SubdiffusiveProcess.Analysis.InfraredExpMomentBound
public import SubdiffusiveProcess.Probability.NativeScalarSeries
public import SubdiffusiveProcess.Probability.OrliczLpNorm
public import SubdiffusiveProcess.Probability.OrliczExponentialMoment

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric Filter
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators ContDiff Topology

noncomputable section
namespace SubdiffusiveProcess.AuditExports

/-- A measurable local Lipschitz observable, read from a fixed dense set.
On Lipschitz functions it is the actual seminorm on the closed cube. -/
theorem cube_lipschitz_observable
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ obs : C(SpatialCoordinates d, ℝ) → ℝ,
      Measurable obs ∧ (∀ f, 0 ≤ obs f) ∧
      ∀ (f : C(SpatialCoordinates d, ℝ)) (L : ℝ≥0),
        LipschitzOnWith L f (closedCube z r hr : Set (SpatialCoordinates d)) →
        obs f ≤ (L : ℝ) ∧
        ∀ x y : closedCube z r hr, x ≠ y →
          |f x - f y| / dist x y ≤ obs f := by
  classical
  let K : Compacts (SpatialCoordinates d) := closedCube z r hr
  have hzK : z ∈ (K : Set (SpatialCoordinates d)) := by
    change dist z z ≤ r / 2
    simp only [dist_self]
    linarith
  let : Nonempty K := ⟨⟨z, hzK⟩⟩
  let q : ℕ → K := TopologicalSpace.denseSeq K
  have hq : DenseRange q := TopologicalSpace.denseRange_denseSeq K
  let ratio : ℕ → ℕ → C(SpatialCoordinates d, ℝ) → ℝ≥0∞ := fun n m f ↦
    if q n = q m then 0 else
      ENNReal.ofReal (|f (q n) - f (q m)| / dist (q n) (q m))
  let obs : C(SpatialCoordinates d, ℝ) → ℝ := fun f ↦
    ENNReal.toReal (⨆ n : ℕ, ⨆ m : ℕ, ratio n m f)
  have hratio_meas : ∀ n m, Measurable (ratio n m) := by
    intro n m
    by_cases hnm : q n = q m
    · simp only [ratio, hnm, ite_eq_left]
      exact measurable_const
    · simp only [ratio, hnm, ite_false]
      have hdist : dist (q n) (q m) ≠ 0 := dist_ne_zero.mpr hnm
      have hc : Continuous (fun f : C(SpatialCoordinates d, ℝ) ↦
          |f (q n) - f (q m)| / dist (q n) (q m)) := by
        fun_prop
      exact hc.measurable.ennreal_ofReal
  have hobs_meas : Measurable obs := by
    unfold obs
    exact ENNReal.measurable_toReal.comp
      (Measurable.iSup (fun n ↦ Measurable.iSup (hratio_meas n)))
  have hobs_nonneg : ∀ f, 0 ≤ obs f := by
    intro f
    exact ENNReal.toReal_nonneg
  have hobs_le_of_lipschitz : ∀ (f : C(SpatialCoordinates d, ℝ)) (L : ℝ≥0),
      LipschitzOnWith L f (K : Set (SpatialCoordinates d)) →
        obs f ≤ (L : ℝ) := by
    intro f L hL
    change ENNReal.toReal (⨆ n : ℕ, ⨆ m : ℕ, ratio n m f) ≤ (L : ℝ)
    have hratio_le : ∀ n m, ratio n m f ≤ ENNReal.ofReal (L : ℝ) := by
      intro n m
      by_cases hnm : q n = q m
      · simp only [ratio, hnm, ite_eq_left, zero_le]
      · simp only [ratio, hnm, ite_false]
        have hdist : 0 < dist (q n) (q m) := dist_pos.mpr hnm
        have hbound := hL.dist_le_mul (q n) (q n).property (q m) (q m).property
        have hbound' : |f (q n) - f (q m)| ≤
            (L : ℝ) * dist (q n) (q m) := by
          simpa only [Real.dist_eq] using! hbound
        apply ENNReal.ofReal_mono
        exact (div_le_iff₀ hdist).2 hbound'
    have hsup : (⨆ n : ℕ, ⨆ m : ℕ, ratio n m f) ≤
        ENNReal.ofReal (L : ℝ) :=
      iSup_le fun n ↦ iSup_le fun m ↦ hratio_le n m
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := by positivity
    calc
      obs f = (⨆ n : ℕ, ⨆ m : ℕ, ratio n m f).toReal := rfl
      _ ≤ (ENNReal.ofReal (L : ℝ)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hsup
      _ = (L : ℝ) := ENNReal.toReal_ofReal hL0
  have hobs_ge_of_lipschitz : ∀ (f : C(SpatialCoordinates d, ℝ)) (L : ℝ≥0),
      LipschitzOnWith L f (K : Set (SpatialCoordinates d)) →
      ∀ x y : K, x ≠ y →
        |f x - f y| / dist x y ≤ obs f := by
    intro f L hL x y hxy
    let S : ℝ≥0∞ := ⨆ n : ℕ, ⨆ m : ℕ, ratio n m f
    have hS_le : S ≤ ENNReal.ofReal (L : ℝ) := by
      exact iSup_le fun n ↦ iSup_le fun m ↦ by
        exact (show ratio n m f ≤ ENNReal.ofReal (L : ℝ) from by
          by_cases hnm : q n = q m
          · simp only [ratio, hnm, ite_eq_left, zero_le]
          · simp only [ratio, hnm, ite_false]
            have hdist : 0 < dist (q n) (q m) := dist_pos.mpr hnm
            have hbound := hL.dist_le_mul (q n) (q n).property (q m) (q m).property
            have hbound' : |f (q n) - f (q m)| ≤
                (L : ℝ) * dist (q n) (q m) := by
              simpa only [Real.dist_eq] using! hbound
            apply ENNReal.ofReal_mono
            exact (div_le_iff₀ hdist).2 hbound')
    have hS_top : S ≠ (⊤ : ℝ≥0∞) := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hS_le
    have hquot : |f x - f y| / dist x y ≤ S.toReal := by
      by_contra hnot
      have hlt : S.toReal < |f x - f y| / dist x y := lt_of_not_ge hnot
      have hratio_cont : ContinuousAt (fun p : K × K ↦
          |f p.1 - f p.2| / dist p.1 p.2) (x, y) := by
        have hnum : ContinuousAt (fun p : K × K ↦
            |f (p.1 : SpatialCoordinates d) - f (p.2 : SpatialCoordinates d)|) (x, y) := by
          exact ((f.continuous.comp
            (continuous_subtype_val.comp continuous_fst)).sub
            (f.continuous.comp
              (continuous_subtype_val.comp continuous_snd))).continuousAt.abs
        have hden : ContinuousAt (fun p : K × K ↦
            dist (p.1 : SpatialCoordinates d) (p.2 : SpatialCoordinates d)) (x, y) := by
          exact (continuous_dist.comp
            ((continuous_subtype_val.comp continuous_fst).prodMk
              (continuous_subtype_val.comp continuous_snd))).continuousAt
        have hpos : 0 < dist (x : SpatialCoordinates d) (y : SpatialCoordinates d) :=
          dist_pos.mpr (fun h => hxy (Subtype.ext h))
        exact hnum.div hden hpos.ne'
      have hev : {p : K × K | S.toReal <
          |f p.1 - f p.2| / dist p.1 p.2} ∈ 𝓝 (x, y) := by
        exact hratio_cont.eventually (isOpen_Ioi.mem_nhds hlt)
      have hqprod : DenseRange (fun nm : ℕ × ℕ ↦ (q nm.1, q nm.2)) :=
        hq.prodMap hq
      obtain ⟨nm, hnm⟩ := hqprod.mem_nhds hev
      have hnm_ne : q nm.1 ≠ q nm.2 := by
        intro heq
        exact (not_lt_of_ge ENNReal.toReal_nonneg) (by simpa [heq] using hnm)
      have hratio_mem : ratio nm.1 nm.2 f ≤ S := by
        exact le_iSup_of_le nm.1 (le_iSup (fun m ↦ ratio nm.1 m f) nm.2)
      have hratio_toReal :
          |f (q nm.1) - f (q nm.2)| / dist (q nm.1) (q nm.2) ≤ S.toReal := by
        rw [show ratio nm.1 nm.2 f = ENNReal.ofReal
            (|f (q nm.1) - f (q nm.2)| / dist (q nm.1) (q nm.2)) by
              simp only [ratio, hnm_ne, ite_false]] at hratio_mem
        calc
          |f (q nm.1) - f (q nm.2)| / dist (q nm.1) (q nm.2) =
              (ENNReal.ofReal
                (|f (q nm.1) - f (q nm.2)| / dist (q nm.1) (q nm.2))).toReal := by
            symm
            exact ENNReal.toReal_ofReal
              (div_nonneg (abs_nonneg _) dist_nonneg)
          _ ≤ S.toReal := ENNReal.toReal_mono hS_top hratio_mem
      exact (not_lt_of_ge hratio_toReal) (by simpa only [mem_ofPred_eq] using hnm)
    simpa only [S, obs] using hquot
  exact ⟨obs, hobs_meas, hobs_nonneg, fun f L hL =>
    ⟨hobs_le_of_lipschitz f L hL, hobs_ge_of_lipschitz f L hL⟩⟩

/-- The compact native C1 norm controls the value Lipschitz constant. -/
theorem native_cube_lipschitz
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (g : SubdiffusiveProcess.Model.PotentialField d) :
    LipschitzOnWith (Real.toNNReal (compactPotentialC1Norm (closedCube z r hr) g))
      (g.1.1) (closedCube z r hr : Set (SpatialCoordinates d)) := by
  let K : Compacts (SpatialCoordinates d) := closedCube z r hr
  refine Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x _hx => (g.hasFDerivAt x).hasFDerivWithinAt) ?_ (convex_closedBall _ _)
  intro x hx
  rw [← NNReal.coe_le_coe]
  change ‖g.deriv x‖ ≤ Real.toNNReal (compactPotentialC1Norm K g)
  have hnonneg : 0 ≤ compactPotentialC1Norm K g := by
    unfold compactPotentialC1Norm
    positivity
  rw [Real.coe_toNNReal', max_eq_left hnonneg]
  unfold compactPotentialC1Norm
  exact (ContinuousMap.norm_coe_le_norm
    (⟨fun u : K => g.deriv u.1,
      g.deriv.continuous.comp continuous_subtype_val⟩ :
      C(K, SpatialCoordinates d →L[ℝ] ℝ)) ⟨x, hx⟩).trans
    (le_add_of_nonneg_left (norm_nonneg _))

/-- A single measurable compact value and Lipschitz envelope serves the
characterized infrared limit, zero, and all positive truncations. Its Gaussian
exponential bound is fixed before the model and truncation index. -/
theorem infrared_family_envelope
    {d : ℕ} (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (M : SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
        ∃ S : BilateralField d → ℝ,
          Measurable S ∧ (∀ om, 0 ≤ S om) ∧
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
            (‖restrictC (closedCube z r hr) (H om)‖ ≤ S om ∧
              ∀ x y : closedCube z r hr,
                |H om x - H om y| ≤ S om * dist x y) ∧
            ∀ L : ℕ,
              ‖restrictC (closedCube z r hr) (infraredPartialSum om L)‖ ≤ S om ∧
              ∀ x y : closedCube z r hr,
                |infraredPartialSum om L x - infraredPartialSum om L y| ≤
                  S om * dist x y) ∧
          (∫⁻ om, ENNReal.ofReal (Real.exp ((S om / (A * M.delta)) ^ 2))
            ∂(chaosSampleLaw M).toMeasure) ≤ 2 ∧
          ∀ lambda : ℝ, 0 ≤ lambda →
            Integrable (fun om => Real.exp (lambda * S om))
              (chaosSampleLaw M).toMeasure ∧
            (∫ om, Real.exp (lambda * S om) ∂(chaosSampleLaw M).toMeasure) ≤
              2 * Real.exp (A ^ 2 * lambda ^ 2 * M.delta ^ 2 / 4) := by
  classical
  let K : Compacts (SpatialCoordinates d) := closedCube z r hr
  let : MeasurableSpace C(K, ℝ) := borel _
  let : BorelSpace C(K, ℝ) := ⟨rfl⟩
  obtain ⟨obs, hobsmeas, hobs0, hobs⟩ := cube_lipschitz_observable z r hr
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall (0 : SpatialCoordinates d)
  let R1 : ℝ := max 1 R
  have hR1 : 0 < R1 := zero_lt_one.trans_le (le_max_left _ _)
  have hKR : ∀ x ∈ (K : Set (SpatialCoordinates d)), ‖x‖ ≤ R1 := by
    intro x hx
    have hb : ‖x‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hR hx
    exact hb.trans (le_max_right _ _)
  obtain ⟨A, hA, hseries⟩ := exists_native_joint_scalar_series_exp_square_bound (d := d) R1 hR1
  refine ⟨A, hA, ?_⟩
  intro M H hH
  let μ : Measure (NativeBilateralPotentialSample d) := Measure.infinitePi
    (fun _ : ℤ => (SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
  let term : ℕ → BilateralField d → C(SpatialCoordinates d, ℝ) := fun n om =>
    om ((n + 1 : ℕ) : ℤ) - ContinuousMap.const _ (om ((n + 1 : ℕ) : ℤ) 0)
  let Y : ℕ → BilateralField d → ℝ := fun n om =>
    ‖restrictC K (term n om)‖ + obs (term n om)
  have hterm : ∀ n, Measurable (term n) := by
    intro n
    exact (measurable_pi_apply _).sub
      (ContinuousMap.continuous_const'.measurable.comp
        ((continuous_eval_const (0 : SpatialCoordinates d)).measurable.comp
          (measurable_pi_apply _)))
  have hYm : ∀ n, Measurable (Y n) := fun n =>
    (((restrictC_continuous K).measurable.comp (hterm n)).norm).add
      (hobsmeas.comp (hterm n))
  have hY0 : ∀ n om, 0 ≤ Y n om := fun n om => add_nonneg (norm_nonneg _) (hobs0 _)
  let T : BilateralField d → ℝ≥0∞ := fun om => ∑' n : ℕ, ENNReal.ofReal (Y n om)
  let S : BilateralField d → ℝ := fun om => (T om).toReal
  have hTm : Measurable T := Measurable.tsum (fun n => (hYm n).ennreal_ofReal)
  have hSm : Measurable S := ENNReal.measurable_toReal.comp hTm
  have hS0 : ∀ om, 0 ≤ S om := fun _ => ENNReal.toReal_nonneg
  let Z : ℕ → NativeBilateralPotentialSample d → ℝ := fun n om =>
    max (compactPotentialC1Norm K (SubdiffusiveProcess.Model.PotentialField.anchor
      (positiveScaledNativeLayer om n)))
      (compactGradientLipschitzObservable K (positiveScaledNativeLayer om n))
  have hZ0 : ∀ n om, 0 ≤ Z n om := by
    intro n om
    apply le_max_of_le_left
    unfold compactPotentialC1Norm
    positivity
  have hZm : ∀ n, Measurable (Z n) := by
    intro n
    have hn : Measurable (fun om : NativeBilateralPotentialSample d =>
        positiveScaledNativeLayer om n) :=
      (measurable_pi_apply n).comp measurable_positiveScaledNativeLayer
    have hanchor : Continuous (fun g : SubdiffusiveProcess.Model.PotentialField d => g.anchor) := by
      apply Continuous.subtype_mk
      have hv : Continuous (fun g : C(SpatialCoordinates d, ℝ) =>
          g - ContinuousMap.const _ (g 0)) :=
        continuous_id.sub (ContinuousMap.continuous_const'.comp
          (continuous_eval_const (0 : SpatialCoordinates d)))
      exact (hv.comp continuous_subtype_val.fst).prodMk continuous_subtype_val.snd
    exact (compactPotentialC1Norm_measurable_comp K
      (hanchor.measurable.comp hn)).max
      ((compactGradientLipschitzObservable_measurable K).comp hn)
  have hZs : ∀ᵐ om ∂μ, Summable (fun n => Z n om) := by
    filter_upwards [ae_positiveScaledNativeLayer_shellC11Summable M] with om hom
    obtain ⟨hc1, hlip⟩ := shellC11Summable_compact_observables
      (positiveScaledNativeLayer om) hom K
    apply Summable.of_nonneg_of_le (fun n => hZ0 n om) _ (hc1.add hlip)
    intro n
    apply max_le
    · apply le_add_of_nonneg_right
      unfold compactGradientLipschitzObservable
      apply Real.sSup_nonneg
      rintro a ⟨x, y, hxy, rfl⟩
      exact div_nonneg (norm_nonneg _) (norm_nonneg _)
    · apply le_add_of_nonneg_left
      unfold compactPotentialC1Norm
      positivity
  have htermnative : ∀ n om, term n (piNative om) =
      (SubdiffusiveProcess.Model.PotentialField.anchor (positiveScaledNativeLayer om n)).1.1 := by
    intro n om
    ext x
    rfl
  have hYnative : ∀ n om, Y n (piNative om) ≤ 2 * Z n om := by
    intro n om
    let g := SubdiffusiveProcess.Model.PotentialField.anchor (positiveScaledNativeLayer om n)
    have hg0 : 0 ≤ compactPotentialC1Norm K g := by
      unfold compactPotentialC1Norm
      positivity
    have hL := (hobs g.1.1 (Real.toNNReal (compactPotentialC1Norm K g))
      (native_cube_lipschitz z r hr g)).1
    rw [Real.coe_toNNReal _ hg0] at hL
    have hn : ‖restrictC K g.1.1‖ ≤ compactPotentialC1Norm K g := by
      rw [restrictC_val_eq_restrictForget]
      exact norm_restrictForget_le K g
    dsimp only [Y]
    rw [htermnative]
    have hZ : compactPotentialC1Norm K g ≤ Z n om := le_max_left _ _
    linarith
  have hpubsum : ∀ᵐ om ∂μ,
      Summable (fun n => Y n (piNative om)) ∧
      S (piNative om) ≤ 2 * ∑' n : ℕ, Z n om ∧ T (piNative om) ≠ ⊤ := by
    filter_upwards [hZs] with om hom
    have hsum : Summable (fun n => Y n (piNative om)) :=
      Summable.of_nonneg_of_le (fun n => hY0 n _) (fun n => hYnative n om)
        (hom.mul_left 2)
    have heq : T (piNative om) = ENNReal.ofReal (∑' n : ℕ, Y n (piNative om)) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun n => hY0 n _) hsum).symm
    refine ⟨hsum, ?_, heq ▸ ENNReal.ofReal_ne_top⟩
    change (T (piNative om)).toReal ≤ _
    rw [heq, ENNReal.toReal_ofReal (tsum_nonneg (fun n => hY0 n _))]
    exact (hsum.tsum_le_tsum (fun n => hYnative n om) (hom.mul_left 2)).trans_eq
      (tsum_mul_left)
  have hpm := piNative_measurePreserving M
  have hOrlicz : (∫⁻ om, ENNReal.ofReal (Real.exp ((S om / (A * M.delta)) ^ 2))
      ∂(chaosSampleLaw M).toMeasure) ≤ 2 := by
    rw [← hpm.map_eq, lintegral_map
      (((hSm.div_const _).pow_const (2 : ℕ)).exp.ennreal_ofReal) hpm.measurable]
    apply (lintegral_mono_ae ?_).trans
      (hseries M K hKR hZm hZs).1
    filter_upwards [hpubsum] with om hom
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hden : 0 < A * M.delta := mul_pos hA M.shellPrefix.delta_pos
    apply (sq_le_sq₀ (div_nonneg (hS0 _) hden.le)
      (div_nonneg (tsum_nonneg (fun n => hZ0 n om)) (half_pos hden).le)).2
    calc S (piNative om) / (A * M.delta) ≤
        (2 * ∑' n : ℕ, Z n om) / (A * M.delta) :=
      div_le_div_of_nonneg_right hom.2.1 hden.le
      _ = (∑' n : ℕ, Z n om) / (A * M.delta / 2) := by ring
  have hfinite : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, T om ≠ ⊤ := by
    rw [← hpm.map_eq]
    exact (ae_map_iff hpm.measurable.aemeasurable
      (hTm (measurableSet_singleton ⊤) |>.compl)).2 (hpubsum.mono fun _ h => h.2.2)
  have hBounds : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ L : ℕ, ‖restrictC K (infraredPartialSum om L)‖ ≤ S om ∧
        ∀ x y : K, |infraredPartialSum om L x - infraredPartialSum om L y| ≤
          S om * dist x y := by
    -- The finite-sum bounds follow on the public side from the summable majorant.
    have hLipterm : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ n : ℕ, LipschitzOnWith (Real.toNNReal (obs (term n om)))
          (term n om) (K : Set (SpatialCoordinates d)) := by
      have hL : ∀ n, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          LipschitzOnWith (Real.toNNReal (obs (term n om)))
            (term n om) (K : Set (SpatialCoordinates d)) := by
        intro n
        have hset : MeasurableSet {om : BilateralField d |
            LipschitzOnWith (Real.toNNReal (obs (term n om)))
              (term n om) (K : Set (SpatialCoordinates d))} := by
          have hclosed : IsClosed {p : C(SpatialCoordinates d, ℝ) × ℝ≥0 |
              LipschitzOnWith p.2 p.1 (K : Set (SpatialCoordinates d))} := by
            simp only [lipschitzOnWith_iff_dist_le_mul, ofPred_forall]
            refine isClosed_biInter fun x _ => isClosed_biInter fun y _ =>
              isClosed_le ?_ ?_
            · exact (((continuous_eval_const x).comp continuous_fst).dist
                ((continuous_eval_const y).comp continuous_fst))
            · exact (NNReal.continuous_coe.comp continuous_snd).mul continuous_const
          exact hclosed.measurableSet.preimage
            ((hterm n).prodMk ((hobsmeas.comp (hterm n)).real_toNNReal))
        rw [← hpm.map_eq]
        apply (ae_map_iff hpm.measurable.aemeasurable hset).2
        apply Filter.Eventually.of_forall
        intro om
        rw [htermnative]
        let g := SubdiffusiveProcess.Model.PotentialField.anchor (positiveScaledNativeLayer om n)
        apply LipschitzOnWith.of_dist_le_mul
        intro x hx y hy
        by_cases hxy : x = y
        · simp only [hxy, dist_self, mul_zero, le_refl]
        have hb := (hobs g.1.1 (Real.toNNReal (compactPotentialC1Norm K g))
          (native_cube_lipschitz z r hr g)).2 ⟨x, hx⟩ ⟨y, hy⟩
          (fun h => hxy (congrArg Subtype.val h))
        rw [Real.coe_toNNReal _ (hobs0 _), Real.dist_eq]
        exact (div_le_iff₀ (dist_pos.mpr hxy)).mp hb
      exact ae_all_iff.mpr hL
    filter_upwards [hfinite, hLipterm] with om hfin hLip
    intro L
    have hsumL : ∑ n ∈ Finset.range L, Y n om ≤ S om := by
      have he : ENNReal.ofReal (∑ n ∈ Finset.range L, Y n om) ≤ T om := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => hY0 n om)]
        exact ENNReal.sum_le_tsum _
      have ht := ENNReal.toReal_mono hfin he
      rw [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun n _ => hY0 n om))] at ht
      exact ht
    constructor
    · change ‖restrictC K (∑ n ∈ Finset.range L, term n om)‖ ≤ _
      have heq : restrictC K (∑ n ∈ Finset.range L, term n om) =
          ∑ n ∈ Finset.range L, restrictC K (term n om) := by
        ext x
        simp only [restrictC, ContinuousMap.coe_mk, ContinuousMap.sum_apply]
      rw [heq]
      exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n _ =>
        le_add_of_nonneg_right (hobs0 _)).trans hsumL)
    · intro x y
      change |(∑ n ∈ Finset.range L, term n om) x -
        (∑ n ∈ Finset.range L, term n om) y| ≤ _
      simp only [ContinuousMap.sum_apply]
      rw [← Finset.sum_sub_distrib]
      calc _ ≤ ∑ n ∈ Finset.range L, |term n om x - term n om y| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Finset.range L, Y n om * dist x y := by
          apply Finset.sum_le_sum
          intro n _
          have hb := (hLip n).dist_le_mul x x.2 y y.2
          rw [Real.dist_eq, Real.coe_toNNReal _ (hobs0 _)] at hb
          exact hb.trans (mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_left (norm_nonneg _)) dist_nonneg)
        _ = (∑ n ∈ Finset.range L, Y n om) * dist x y :=
          (Finset.sum_mul _ _ _).symm
        _ ≤ S om * dist x y := mul_le_mul_of_nonneg_right hsumL dist_nonneg
  refine ⟨S, hSm, hS0, ?_, hOrlicz, ?_⟩
  · filter_upwards [hBounds, hH.2] with om hb hlim
    constructor
    · constructor
      · have hnorm := (((restrictC_continuous K).continuousAt.tendsto.comp hlim).norm)
        exact le_of_tendsto hnorm (Filter.Eventually.of_forall fun L => (hb L).1)
      · intro x y
        have hx := ((continuous_eval_const (x : SpatialCoordinates d)).continuousAt.tendsto.comp hlim)
        have hy := ((continuous_eval_const (y : SpatialCoordinates d)).continuousAt.tendsto.comp hlim)
        exact le_of_tendsto ((hx.sub hy).abs)
          (Filter.Eventually.of_forall fun L => (hb L).2 x y)
    · exact hb
  · intro lambda hlambda
    have hout := orlicz_exp_linear_integrable_integral_le
      (chaosSampleLaw M).toMeasure S (A * M.delta) lambda hSm hS0
      (mul_pos hA M.shellPrefix.delta_pos) hlambda hOrlicz
    refine ⟨hout.1, hout.2.trans_eq ?_⟩
    congr 2
    ring

end SubdiffusiveProcess.AuditExports
