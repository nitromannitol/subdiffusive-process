module

public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Geometry.CoordinateFold
public import SubdiffusiveProcess.Probability.InfraredCommonFieldConvergence
public import SubdiffusiveProcess.Paper.lem_infrared

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Topology.Bases

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric Filter
open scoped ENNReal NNReal BigOperators ContDiff Topology
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/--
Fine proof-step child of lem_extremes, paper label `mfd:lem-extremes`.

Inputs:
- z, r, and hr pin the fixed compact cube before the moment order.
- H is the field in the parent InfraredCharacterization M H premise.
- The local C^1 and exponential-moment bounds are supplied by
  lem_infrared; the local Lipschitz majorant and its MemLp conclusion are
  produced here.
- The a.s. estimate is simultaneous for all points of the fixed cube.
- End of carried-input tick list.
-/
theorem infrared_characterization_local_lipschitz_majorant :
  ∀ (d : ℕ), 2 ≤ d →
  ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)],
  ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
  ∀ (p : ℝ), 1 ≤ p →
  ∃ C : ℝ, 0 < C ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H →
      ∃ G : BilateralField d → ℝ,
        (∀ om, 0 ≤ G om) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
            y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
            |H om x - H om y| ≤ G om * dist x y) ∧
        MemLp G (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
        eLpNorm G (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C * M.delta * Real.sqrt p) := by
  classical
  intro d hd instMeas instBorel z r hr p hp
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
  obtain ⟨C₀, hC₀, hmain⟩ := lem_infrared hd
  let C : ℝ := max 1 (4 * C₀ K)
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C, hCpos, ?_⟩
  intro M H hH
  let μ : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ =>
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
  obtain ⟨H₀, hH₀meas, hH₀obs, hH₀ae, _hH₀layers, hH₀Lp, _hH₀exp⟩ :=
    hmain M μ rfl
  let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g ↦ g.1.1, continuous_subtype_val.fst⟩
  let π : NativeBilateralPotentialSample d → BilateralField d :=
    fun omega j ↦ layerScaling d j (forget (omega j))
  have hπmeas : Measurable π := by
    apply Measurable.of_eval
    intro j
    exact (layerScaling d j).continuous.measurable.comp
      (forget.continuous.measurable.comp (measurable_pi_apply j))
  have hπmeasure : Measure.map π μ = (chaosSampleLaw M).toMeasure := by
    simpa only [chaosSampleLaw, chaosRootFieldLaw, μ, π, Function.comp_apply] using
      (measurePreserving_nativeCopies_commonScaleLaw M).map_eq
  let hπMP : MeasurePreserving π μ (chaosSampleLaw M).toMeasure :=
    ⟨hπmeas, hπmeasure⟩
  have hsum : ∀ omega L,
      infraredPartialSum (π omega) L =
        forget (positiveAnchoredInfraredTruncation omega L) := by
    intro omega L
    induction L with
    | zero =>
        simp [infraredPartialSum, positiveAnchoredInfraredTruncation, forget,
          zeroNativePotentialField]
        rfl
    | succ L ih =>
        unfold infraredPartialSum
        rw [Finset.sum_range_succ]
        change infraredPartialSum (π omega) L +
            (π omega (Int.ofNat (L + 1)) -
              ContinuousMap.const _ ((π omega (Int.ofNat (L + 1))) 0)) = _
        rw [ih]
        ext x
        change (forget (positiveAnchoredInfraredTruncation omega L)) x +
            ((forget (positiveScaledNativeLayer omega L)) x -
              (forget (positiveScaledNativeLayer omega L)) 0) = _
        rfl
  have hcanon_beta : ∀ᵐ beta ∂(chaosSampleLaw M).toMeasure,
      ∃ y : C(SpatialCoordinates d, ℝ),
        Tendsto (fun L ↦ infraredPartialSum beta L) atTop (nhds y) := by
    exact infraredPartialSum_tendsto_of_native_infrared_limit M H₀
      (by simpa only [μ] using hH₀ae.mono fun omega h ↦ ⟨h.1, h.2.1⟩)
  have hcanon_native := hπMP.quasiMeasurePreserving.ae hcanon_beta
  have hgiven_native := hπMP.quasiMeasurePreserving.ae hH.2
  have hEqAE : ∀ᵐ omega ∂μ, H (π omega) = forget (H₀ omega) := by
    filter_upwards [hcanon_native, hgiven_native, hH₀ae] with omega hcan hgiven hzero
    obtain ⟨_y, _hy⟩ := hcan
    have hlim : Tendsto (fun L ↦ infraredPartialSum (π omega) L)
        atTop (nhds (forget (H₀ omega))) := by
      apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
      intro S hS
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      let KS : Compacts (SpatialCoordinates d) := ⟨S, hS⟩
      have hK' := hzero.2.1 KS
      filter_upwards [hK' (Metric.ball_mem_nhds 0 hε)] with L hL
      intro x hx
      have hnorm : ‖(forget (positiveAnchoredInfraredTruncation omega L)) x -
          (forget (H₀ omega)) x‖ ≤
          compactPotentialC1Norm KS
            (_root_.SubdiffusiveProcess.Model.PotentialField.add
              (positiveAnchoredInfraredTruncation omega L)
              (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (H₀ omega))) := by
        have heval := ContinuousMap.norm_coe_le_norm
          (⟨fun u : KS ↦
              (_root_.SubdiffusiveProcess.Model.PotentialField.add
                (positiveAnchoredInfraredTruncation omega L)
                (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (H₀ omega))) u.1,
            (Continuous.comp
              (((_root_.SubdiffusiveProcess.Model.PotentialField.add
                (positiveAnchoredInfraredTruncation omega L)
                (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (H₀ omega))).1.1).continuous)
              continuous_subtype_val)⟩ : C(KS, ℝ))
          ⟨x, hx⟩
        change ‖((positiveAnchoredInfraredTruncation omega L) x -
            (H₀ omega) x)‖ ≤ _
        rw [show (positiveAnchoredInfraredTruncation omega L) x - (H₀ omega) x =
            (_root_.SubdiffusiveProcess.Model.PotentialField.add
              (positiveAnchoredInfraredTruncation omega L)
              (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (H₀ omega))) x by
                rw [_root_.SubdiffusiveProcess.Model.PotentialField.add_apply,
                  _root_.SubdiffusiveProcess.Model.PotentialField.scale_apply]
                ring]
        exact (heval.trans (le_add_of_nonneg_right (by positivity)))
      rw [hsum omega L]
      change dist ((forget (H₀ omega)) x)
          ((forget (positiveAnchoredInfraredTruncation omega L)) x) < ε
      rw [dist_eq_norm]
      have hnonneg : 0 ≤ compactPotentialC1Norm KS
          (_root_.SubdiffusiveProcess.Model.PotentialField.add
            (positiveAnchoredInfraredTruncation omega L)
            (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (H₀ omega))) := by
        unfold compactPotentialC1Norm
        positivity
      have hsmall : compactPotentialC1Norm KS
          (_root_.SubdiffusiveProcess.Model.PotentialField.add
            (positiveAnchoredInfraredTruncation omega L)
            (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (H₀ omega))) < ε := by
        change dist (compactPotentialC1Norm KS
          (_root_.SubdiffusiveProcess.Model.PotentialField.add
            (positiveAnchoredInfraredTruncation omega L)
            (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (H₀ omega)))) 0 < ε at hL
        simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hL
      have hnorm' : ‖(forget (H₀ omega)) x -
          (forget (positiveAnchoredInfraredTruncation omega L)) x‖ ≤
          compactPotentialC1Norm KS
            (_root_.SubdiffusiveProcess.Model.PotentialField.add
              (positiveAnchoredInfraredTruncation omega L)
              (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (H₀ omega))) := by
        rw [norm_sub_rev]
        exact hnorm
      exact hnorm'.trans_lt hsmall
    exact tendsto_nhds_unique hgiven hlim
  let G : BilateralField d → ℝ := fun beta => obs (H beta)
  let F : NativeBilateralPotentialSample d → ℝ :=
    fun omega => compactPotentialC1Norm K (H₀ omega)
  have hGmeas : Measurable G := by
    exact hobs_meas.comp hH.1
  have hFmeas : Measurable F := by
    exact (hH₀obs K).1
  have hLipCanon : ∀ omega,
      LipschitzOnWith
        (Real.toNNReal (compactPotentialC1Norm K (H₀ omega)))
        (forget (H₀ omega)) (K : Set (SpatialCoordinates d)) := by
    intro omega
    refine Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun x hx => (H₀ omega).hasFDerivAt x |>.hasFDerivWithinAt) ?_ ?_
    · intro x hx
      rw [← NNReal.coe_le_coe]
      change ‖(H₀ omega).deriv x‖ ≤
        Real.toNNReal (compactPotentialC1Norm K (H₀ omega))
      have hnonneg : 0 ≤ compactPotentialC1Norm K (H₀ omega) := by
        unfold compactPotentialC1Norm
        positivity
      rw [Real.coe_toNNReal', max_eq_left hnonneg]
      unfold compactPotentialC1Norm
      exact (ContinuousMap.norm_coe_le_norm
        (⟨fun u : K => _root_.SubdiffusiveProcess.Model.PotentialField.deriv
            (H₀ omega) u.1,
          (_root_.SubdiffusiveProcess.Model.PotentialField.deriv (H₀ omega)).continuous.comp
            continuous_subtype_val⟩ :
          C(K, SpatialCoordinates d →L[ℝ] ℝ)) ⟨x, hx⟩).trans
        (le_add_of_nonneg_left (norm_nonneg _))
    · change Convex ℝ (Metric.closedBall z (r / 2))
      exact convex_closedBall _ _
  have hGbound : ∀ᵐ omega ∂μ, G (π omega) ≤ F omega := by
    filter_upwards [hEqAE] with omega heq
    dsimp [G, F]
    rw [heq]
    have hnonneg : 0 ≤ compactPotentialC1Norm K (H₀ omega) := by
      unfold compactPotentialC1Norm
      positivity
    simpa only [Real.coe_toNNReal', max_eq_left hnonneg] using
      hobs_le_of_lipschitz _ _ (hLipCanon omega)
  have hF2bound : eLpNorm F 2 μ ≤
      ENNReal.ofReal (C₀ K * M.delta * Real.sqrt (2 : ℝ)) := by
    simpa only [F, ENNReal.toReal_ofNat, Nat.cast_ofNat] using
      (hH₀Lp K (2 : ℝ≥0∞) (by norm_num) (by norm_num)).1
  have hF2mem : MemLp F 2 μ := by
    exact lt_of_le_of_lt hF2bound ENNReal.ofReal_lt_top
  have hFbound : eLpNorm F (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (C * M.delta * Real.sqrt p) := by
    have hp0 : 0 ≤ p := le_trans (by norm_num) hp
    have hδ : 0 < M.delta := M.shellPrefix.delta_pos
    have hC0K : 0 ≤ C₀ K := hC₀ K
    have hsqrtp : 1 ≤ Real.sqrt p := by
      nlinarith [Real.sq_sqrt hp0, Real.sqrt_nonneg p]
    have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_nonneg (2 : ℝ)]
    have hC4 : 4 * C₀ K ≤ C := by
      exact le_max_right _ _
    have hC0le : C₀ K ≤ C := by
      dsimp [C] at hC4 ⊢
      nlinarith
    have hscale : C₀ K * Real.sqrt (2 : ℝ) ≤ C * Real.sqrt p := by
      calc
        C₀ K * Real.sqrt (2 : ℝ) ≤ C₀ K * 2 :=
          mul_le_mul_of_nonneg_left hsqrt2 hC0K
        _ ≤ (4 * C₀ K) * 1 := by nlinarith
        _ ≤ (4 * C₀ K) * Real.sqrt p :=
          mul_le_mul_of_nonneg_left hsqrtp (by positivity)
        _ ≤ C * Real.sqrt p :=
          mul_le_mul_of_nonneg_right hC4 (Real.sqrt_nonneg p)
    have hscale' : C₀ K * M.delta * Real.sqrt (2 : ℝ) ≤
        C * M.delta * Real.sqrt p := by
      calc
        C₀ K * M.delta * Real.sqrt (2 : ℝ) =
            (C₀ K * Real.sqrt (2 : ℝ)) * M.delta := by ring
        _ ≤ (C * Real.sqrt p) * M.delta :=
          mul_le_mul_of_nonneg_right hscale hδ.le
        _ = C * M.delta * Real.sqrt p := by ring
    by_cases hp2 : 2 ≤ p
    · have hpenn : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
        rw [← ENNReal.ofReal_ofNat]
        exact ENNReal.ofReal_mono hp2
      have hdirect := (hH₀Lp K (ENNReal.ofReal p) hpenn
        ENNReal.ofReal_ne_top).1
      have hdirect' : eLpNorm F (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (C₀ K * M.delta * Real.sqrt p) := by
        simpa only [F, ENNReal.toReal_ofReal hp0] using hdirect
      have hcoeff : C₀ K * M.delta * Real.sqrt p ≤
          C * M.delta * Real.sqrt p := by
        calc
          C₀ K * M.delta * Real.sqrt p ≤
              (C * M.delta) * Real.sqrt p := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hC0le hδ.le)
              (Real.sqrt_nonneg p)
          _ = C * M.delta * Real.sqrt p := by ring
      exact hdirect'.trans (ENNReal.ofReal_mono hcoeff)
    · have hp_le : p ≤ 2 := le_of_not_ge hp2
      have hqle : ENNReal.ofReal p ≤ (2 : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_ofNat]
        exact ENNReal.ofReal_mono hp_le
      have hmono := eLpNorm_le_eLpNorm_of_exponent_le (μ := μ) (f := F)
        hqle
      exact hmono.trans (hF2bound.trans (ENNReal.ofReal_mono hscale'))
  have hGmem : MemLp G (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure := by
    change eLpNorm G (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure < ⊤
    rw [← hπmeasure]
    rw [eLpNorm_map_measure hGmeas.aestronglyMeasurable hπmeas.aemeasurable]
    have hGbound' : ∀ᵐ omega ∂μ, ‖(G ∘ π) omega‖ ≤ F omega := by
      filter_upwards [hGbound] with omega homega
      change |G (π omega)| ≤ F omega
      rw [abs_of_nonneg (hobs_nonneg _)]
      exact homega
    have hnorm := eLpNorm_mono_ae_real (p := ENNReal.ofReal p) (hGmeas.comp hπmeas).aestronglyMeasurable hGbound'
    exact (hnorm.trans hFbound).trans_lt ENNReal.ofReal_lt_top
  have hGnorm : eLpNorm G (ENNReal.ofReal p)
      (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (C * M.delta * Real.sqrt p) := by
    rw [← hπmeasure]
    rw [eLpNorm_map_measure hGmeas.aestronglyMeasurable hπmeas.aemeasurable]
    have hGbound' : ∀ᵐ omega ∂μ, ‖(G ∘ π) omega‖ ≤ F omega := by
      filter_upwards [hGbound] with omega homega
      change |G (π omega)| ≤ F omega
      rw [abs_of_nonneg (hobs_nonneg _)]
      exact homega
    exact (eLpNorm_mono_ae_real (p := ENNReal.ofReal p) (hGmeas.comp hπmeas).aestronglyMeasurable hGbound').trans hFbound
  let Q : BilateralField d → Prop := fun beta =>
    ∀ n m : ℕ,
      |H beta (q n) - H beta (q m)| ≤ G beta * dist (q n) (q m)
  have hQmeas : MeasurableSet {beta | Q beta} := by
    have hset : {beta | Q beta} = ⋂ n : ℕ, ⋂ m : ℕ, {beta : BilateralField d |
        |H beta (q n) - H beta (q m)| ≤ G beta * dist (q n) (q m)} := by
      ext beta
      simp [Q]
    rw [hset]
    refine MeasurableSet.iInter (fun n => MeasurableSet.iInter (fun m => ?_))
    have hleft : Measurable (fun beta : BilateralField d =>
        |H beta (q n) - H beta (q m)|) := by
      exact (((continuous_eval_const (q n : SpatialCoordinates d)).measurable.comp hH.1).sub
        ((continuous_eval_const (q m : SpatialCoordinates d)).measurable.comp hH.1)).abs
    have hright : Measurable (fun beta : BilateralField d =>
        G beta * dist (q n) (q m)) := by
      exact hGmeas.mul measurable_const
    exact measurableSet_le hleft hright
  have hQnative : ∀ᵐ omega ∂μ, Q (π omega) := by
    filter_upwards [hEqAE] with omega heq
    intro n m
    by_cases hnm : q n = q m
    · simp [hnm]
    have hq := hobs_ge_of_lipschitz (forget (H₀ omega))
      (Real.toNNReal (compactPotentialC1Norm K (H₀ omega)))
      (hLipCanon omega) (q n) (q m) hnm
    have hq' := (div_le_iff₀ (dist_pos.mpr hnm)).1 hq
    simpa [heq, G] using hq'
  have hQbeta : ∀ᵐ beta ∂(Measure.map π μ), Q beta :=
    (ae_map_iff hπmeas.aemeasurable hQmeas).2 hQnative
  have hQchaos : ∀ᵐ beta ∂(chaosSampleLaw M).toMeasure, Q beta := by
    simpa only [hπmeasure] using hQbeta
  refine ⟨G, ?_, ?_, hGmem, hGnorm⟩
  · intro om
    exact hobs_nonneg _
  · filter_upwards [hQchaos] with beta hQ
    intro x y hx hy
    have hclosed : IsClosed {a : K × K |
        |H beta a.1 - H beta a.2| ≤ G beta * dist a.1 a.2} := by
      exact isClosed_le (by fun_prop) (by fun_prop)
    let seq : ℕ × ℕ → K × K := fun nm => (q nm.1, q nm.2)
    have hseq : DenseRange seq := hq.prodMap hq
    have hsub : Set.range seq ⊆ {a : K × K |
        |H beta a.1 - H beta a.2| ≤ G beta * dist a.1 a.2} := by
      intro a ha
      rcases ha with ⟨nm, rfl⟩
      exact hQ nm.1 nm.2
    have hcl : closure (Set.range seq) ⊆ {a : K × K |
        |H beta a.1 - H beta a.2| ≤ G beta * dist a.1 a.2} :=
      closure_minimal hsub hclosed
    have hxy : (⟨x, hx⟩, ⟨y, hy⟩) ∈ closure (Set.range seq) := by
      rw [hseq.closure_range]
      trivial
    exact hcl hxy

end SubdiffusiveProcess.Paper

