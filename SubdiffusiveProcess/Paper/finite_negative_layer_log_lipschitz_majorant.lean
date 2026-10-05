module

public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Geometry.CoordinateFold
public import SubdiffusiveProcess.Paper.in_normalization
public import SubdiffusiveProcess.Paper.stationary_family
public import SubdiffusiveProcess.Paper.layer_regularity_moments
public import SubdiffusiveProcess.Sobolev.GMCRootCover
public import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
public import SubdiffusiveProcess.CoarseGrainingVocab.OGammaSup
public import SubdiffusiveProcess.CoarseGrainingVocab.OGammaSplit
public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
public import SubdiffusiveProcess.Assumptions.OGammaBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.ShellSensitivity

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric Asymptotics
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_finite_negative_layer_log_lipschitz_majorant_root_cover
    {d : ℕ} (R : ℝ) :
    ∃ S : Finset (SpatialCoordinates d), ∃ hS : S.Nonempty,
      ∀ g : _root_.SubdiffusiveProcess.Model.PotentialField d,
        LipschitzOnWith
          (S.sup' hS (fun z =>
            (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
              (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g),
              _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0)))
          (fun x => g x) (Metric.closedBall (0 : SpatialCoordinates d) R) := by
  classical
  obtain ⟨S₀, hS₀⟩ := (isCompact_closedBall
      (0 : SpatialCoordinates d) R).elim_finite_subcover
    (fun z : SpatialCoordinates d => Metric.ball z (1 / 2 : ℝ))
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.2 ⟨x, Metric.mem_ball_self (by norm_num)⟩)
  let S : Finset (SpatialCoordinates d) := insert 0 S₀
  have hSne : S.Nonempty := ⟨0, Finset.mem_insert_self 0 S₀⟩
  have hS : Metric.closedBall (0 : SpatialCoordinates d) R ⊆
      ⋃ z ∈ S, Metric.ball z (1 / 2 : ℝ) := by
    intro x hx
    obtain ⟨z, hzS₀, hzx⟩ : ∃ z, ∃ (_ : z ∈ S₀),
        x ∈ Metric.ball z (1 / 2 : ℝ) := by
      simpa only [mem_iUnion] using! hS₀ hx
    exact mem_iUnion.2 ⟨z, mem_iUnion.2 ⟨Finset.mem_insert_of_mem hzS₀, hzx⟩⟩
  refine ⟨S, hSne, ?_⟩
  intro g
  let W : ℝ≥0 := S.sup' hSne (fun z =>
    (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
      (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g),
      _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0))
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro x hx
    exact (g.hasFDerivAt x).differentiableAt
  · intro x hx
    obtain ⟨z, hzS, hzx⟩ : ∃ z, ∃ (_ : z ∈ S),
        x ∈ Metric.ball z (1 / 2 : ℝ) := by
      simpa only [mem_iUnion] using! hS hx
    have hxm : x - z ∈ Metric.ball (0 : SpatialCoordinates d) (1 / 2 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm] using! hzx
    have hcube : x - z ∈ Homogenization.openCubeSet
        (Homogenization.originCube d 0) := by
      rw [← Homogenization.ball_cubeCenter_eq_openCubeSet]
      have hcenter : Homogenization.cubeCenter
          (Homogenization.originCube d 0) = (0 : SpatialCoordinates d) := by
        ext i
        simp [Homogenization.cubeCenter, Homogenization.originCube]
      have hradius : Homogenization.cubeRadius
          (Homogenization.originCube d 0) = (1 / 2 : ℝ) := by
        unfold Homogenization.cubeRadius
        rw [Homogenization.cubeScaleFactor_eq_one_of_scale_eq_zero]
        · norm_num
        · rfl
      rw [hcenter, hradius]
      exact hxm
    have hderiv :
        fderiv ℝ ((_root_.SubdiffusiveProcess.Model.PotentialField.translate z g :
          _root_.SubdiffusiveProcess.Model.PotentialField d) :
          SpatialCoordinates d → ℝ) (x - z) =
          fderiv ℝ (fun y => g y) x := by
      simpa [_root_.SubdiffusiveProcess.Model.PotentialField.translate_apply, sub_add_cancel] using!
        (fderiv_comp_add_right (𝕜 := ℝ) (f := (fun y => g y))
          z (x := x - z))
    have hlocal :
        ‖fderiv ℝ (fun y => g y) x‖₊ ≤
          (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
            (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g),
            _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0) := by
      rw [← hderiv]
      rw [(_root_.SubdiffusiveProcess.Model.PotentialField.translate z g).hasFDerivAt
        (x - z) |>.fderiv]
      exact _root_.SubdiffusiveProcess.Model.PotentialField.norm_deriv_le_g2Observable
        (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) hcube
    have hsup :
        (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g),
          _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0) ≤ W := by
      exact Finset.le_sup' (f := fun z =>
        (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g),
          _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0)) hzS
    exact hlocal.trans hsup
  · exact convex_closedBall (0 : SpatialCoordinates d) R

theorem aux_finite_negative_layer_log_lipschitz_majorant_root_max_moment
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (S : Finset (SpatialCoordinates d)) (hS : S.Nonempty) (p : ℝ) (hp : 1 ≤ p) :
    let μ := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
    let W : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g =>
      S.sup' hS (fun z =>
        _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g))
    MemLp W (ENNReal.ofReal p) μ ∧
      eLpNorm W (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
          ((1 + Real.log 2) ^ ((2 : ℝ)⁻¹) * M.delta) *
          Real.sqrt (5 * (1 + Real.log (2 * (S.card : ℝ))))) := by
  classical
  dsimp only
  let μ : Measure (_root_.SubdiffusiveProcess.Model.PotentialField d) :=
    (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let X : SpatialCoordinates d → _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ :=
    fun z g => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
      (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g)
  let W : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g =>
    S.sup' hS (fun z => X z g)
  have hδ : 0 < M.delta := M.shellPrefix.delta_pos
  have hXmeas : ∀ z, Measurable (X z) := by
    intro z
    exact _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable.comp
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z)
  have hX0 : ∀ z g, 0 ≤ X z g := by
    intro z g
    exact _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _
  have hXog : ∀ z, SubdiffusiveProcess.OGammaLE μ 2 M.delta (X z) := by
    intro z
    have h := SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_comp_measurePreserving
      (mu := μ) (T := _root_.SubdiffusiveProcess.Model.PotentialField.translate z)
      (X := _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable)
      (hT := ⟨_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z, by
        simpa [μ] using! M.G1.stationary z⟩)
      (hX := _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable.aemeasurable)
      (h := by simpa [μ] using! M.G2.regularity_expectation)
    simpa [X] using! h
  have hWmeas : Measurable W := by
    have hsup : W = S.sup' hS X := by
      funext g
      exact (Finset.sup'_apply hS X g).symm
    rw [hsup]
    exact Finset.measurable_sup' hS (fun z hz => hXmeas z)
  have hWog : SubdiffusiveProcess.OGammaLE μ 2
      (M.delta * Real.sqrt (5 * (1 + Real.log (2 * (S.card : ℝ))))) W := by
    dsimp [W]
    exact SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_sup'_log hS hδ
      hWmeas.aemeasurable (fun z hz => hXog z)
  have hcard : (1 : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr hS)
  have hA0 : 0 < M.delta * Real.sqrt
      (5 * (1 + Real.log (2 * (S.card : ℝ)))) := by
    apply mul_pos hδ
    apply Real.sqrt_pos.mpr
    have hlog : 0 < Real.log (2 * (S.card : ℝ)) := by
      apply Real.log_pos
      nlinarith [hcard]
    nlinarith
  have hBig : Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma 2) W
      (((1 + Real.log 2) ^ ((2 : ℝ)⁻¹)) *
        (M.delta * Real.sqrt (5 * (1 + Real.log (2 * (S.card : ℝ)))))) := by
    have hA : 0 < (1 + Real.log 2) ^ ((2 : ℝ)⁻¹) *
        (M.delta * Real.sqrt (5 * (1 + Real.log (2 * (S.card : ℝ))))) := by
      exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) hA0
    exact SubdiffusiveProcess.OGammaBridge.isBigO_gammaSigma_of_ogammaLE
      (by norm_num) hA0 (fun g => by
        rcases hS with ⟨z, hz⟩
        exact (hX0 z g).trans (Finset.le_sup' (f := fun z => X z g) hz)) hWog
  have hnorm := SubdiffusiveProcess.CoarseGrainingVocab.eLpNorm_le_of_isBigO_gammaTwo
    (mu := μ)
    (A := (1 + Real.log 2) ^ ((2 : ℝ)⁻¹) *
      (M.delta * Real.sqrt (5 * (1 + Real.log (2 * (S.card : ℝ))))))
    (p := p)
    (mul_pos (Real.rpow_pos_of_pos (by positivity) _) hA0)
    hp hWmeas.aemeasurable hBig
  have hmem : MemLp W (ENNReal.ofReal p) μ := by
    exact hnorm.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hmem, ?_⟩
  simpa [mul_assoc, mul_left_comm, mul_comm] using! hnorm

theorem aux_finite_negative_layer_log_lipschitz_majorant_continuous_ratio
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (K : Compacts (SpatialCoordinates d)) :
    ∃ V : C(SpatialCoordinates d, ℝ) → ℝ,
      Measurable V ∧
      (∀ f, 0 ≤ V f) ∧
      (∀ (f : C(SpatialCoordinates d, ℝ)) (L : ℝ),
        (∀ x y : K, x ≠ y →
          |f x.1 - f y.1| / dist x.1 y.1 ≤ L) →
        ∀ x y : K, x ≠ y →
          |f x.1 - f y.1| / dist x.1 y.1 ≤ V f) ∧
      (∀ (f : C(SpatialCoordinates d, ℝ)) (L : ℝ), 0 ≤ L →
        (∀ x y : K, x ≠ y →
          |f x.1 - f y.1| / dist x.1 y.1 ≤ L) → V f ≤ L) ∧
      MeasurableSet {f : C(SpatialCoordinates d, ℝ) |
        ∀ x y : K, x ≠ y →
          |f x.1 - f y.1| / dist x.1 y.1 ≤ V f} := by
  classical
  obtain ⟨Q, hQcount, hQdense⟩ := TopologicalSpace.exists_countable_dense
    {p : K × K // p.1 ≠ p.2}
  let D := {p : {p : K × K // p.1 ≠ p.2} // p ∈ Q}
  let : Countable D := hQcount.to_subtype
  let ratioE : {p : K × K // p.1 ≠ p.2} →
      C(SpatialCoordinates d, ℝ) → ℝ := fun p f =>
    |f p.1.1 - f p.1.2| /
      dist (p.1.1 : SpatialCoordinates d) (p.1.2 : SpatialCoordinates d)
  let ratio : D → C(SpatialCoordinates d, ℝ) → ℝ := fun p f =>
    ratioE p.1 f
  let Vraw : C(SpatialCoordinates d, ℝ) → ℝ := fun f => ⨆ p : D, ratio p f
  have hratio_cont : ∀ p : D, Continuous (ratio p) := by
    intro p
    have hp : dist (p.1.1.1 : SpatialCoordinates d)
        (p.1.1.2 : SpatialCoordinates d) ≠ 0 :=
      (dist_pos.mpr (by
        intro h
        exact p.1.2 (Subtype.ext h))).ne'
    change Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
      |f p.1.1.1 - f p.1.1.2| /
        dist (p.1.1.1 : SpatialCoordinates d) (p.1.1.2 : SpatialCoordinates d))
    simpa using! ((continuous_eval_const (F := C(SpatialCoordinates d, ℝ))
      (α := SpatialCoordinates d) (X := ℝ) p.1.1.1).sub
      (continuous_eval_const (F := C(SpatialCoordinates d, ℝ))
        (α := SpatialCoordinates d) (X := ℝ) p.1.1.2)).abs.div_const _
  have hVraw : Measurable Vraw := by
    exact Measurable.iSup (fun p : D => (hratio_cont p).measurable)
  let V : C(SpatialCoordinates d, ℝ) → ℝ := fun f => max 0 (Vraw f)
  refine ⟨V, measurable_const.max hVraw, ?_, ?_, ?_, ?_⟩
  · intro f
    exact le_max_left _ _
  · intro f L hL x y hxy
    have hden : 0 < dist x.1 y.1 := dist_pos.mpr (by
      intro h
      exact hxy (Subtype.ext h))
    have hbound : BddAbove (Set.range (fun p : D => ratio p f)) := by
      refine ⟨L, ?_⟩
      rintro a ⟨p, rfl⟩
      have hpne : p.1.1.1 ≠ p.1.1.2 := by
        intro h
        exact p.1.2 h
      exact hL p.1.1.1 p.1.1.2 hpne
    have hQle : ∀ p : D, ratio p f ≤ Vraw f := by
      intro p
      exact le_ciSup hbound p
    have hpoint_cont : Continuous (fun p : {p : K × K // p.1 ≠ p.2} =>
        ratioE p f) := by
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro p
        exact ne_of_gt (dist_pos.mpr (by
          intro h
          exact p.property (Subtype.ext h)))
    have hclosed : IsClosed {p : {p : K × K // p.1 ≠ p.2} |
        ratioE p f ≤ Vraw f} := by
      exact isClosed_le hpoint_cont continuous_const
    have hall : ∀ p : {p : K × K // p.1 ≠ p.2},
        ratioE p f ≤ Vraw f := by
      intro p
      have hsub : Q ⊆ {q : {p : K × K // p.1 ≠ p.2} |
          ratioE q f ≤ Vraw f} := by
        intro q hq
        exact hQle ⟨q, hq⟩
      exact hclosed.closure_subset_iff.mpr hsub (hQdense p)
    have hratio : |f x.1 - f y.1| / dist x.1 y.1 ≤ Vraw f := by
      exact hall ⟨⟨x, y⟩, hxy⟩
    exact hratio.trans (le_max_right _ _)
  · intro f L hL0 hL
    apply max_le hL0
    change (⨆ p : D, ratio p f) ≤ L
    cases isEmpty_or_nonempty D with
    | inl hD => simpa [iSup_of_empty'] using! hL0
    | inr hD =>
        let := hD
        apply ciSup_le
        intro p
        have hpne : p.1.1.1 ≠ p.1.1.2 := p.1.2
        exact hL p.1.1.1 p.1.1.2 hpne
  · let P : Set C(SpatialCoordinates d, ℝ) := {f |
        ∀ x y : K, x ≠ y →
          |f x.1 - f y.1| / dist x.1 y.1 ≤ V f}
    have hPeq : P = ⋂ p : D, {f : C(SpatialCoordinates d, ℝ) |
        ratio p f ≤ V f} := by
      ext f
      constructor
      · intro hf
        change (∀ x y : K, x ≠ y →
          |f x.1 - f y.1| / dist x.1 y.1 ≤ V f) at hf
        rw [Set.mem_iInter]
        intro p
        exact hf p.1.1.1 p.1.1.2 p.1.2
      · intro hf
        have hf' : ∀ p : D, ratio p f ≤ V f := by
          simpa only [Set.mem_iInter, mem_ofPred_eq] using! hf
        intro x y hxy
        have hpoint_cont : Continuous (fun p : {p : K × K // p.1 ≠ p.2} =>
            ratioE p f) := by
          apply Continuous.div
          · fun_prop
          · fun_prop
          · intro p
            exact ne_of_gt (dist_pos.mpr (by
              intro h
              exact p.property (Subtype.ext h)))
        have hclosed : IsClosed {p : {p : K × K // p.1 ≠ p.2} |
            ratioE p f ≤ V f} := isClosed_le hpoint_cont continuous_const
        have hsub : Q ⊆ {q : {p : K × K // p.1 ≠ p.2} |
            ratioE q f ≤ V f} := by
          intro q hq
          exact hf' ⟨q, hq⟩
        have hall : ratioE ⟨⟨x, y⟩, hxy⟩ f ≤ V f :=
          hclosed.closure_subset_iff.mpr hsub (hQdense ⟨⟨x, y⟩, hxy⟩)
        exact hall
    change MeasurableSet P
    rw [hPeq]
    exact MeasurableSet.iInter (fun p =>
      measurableSet_le (hratio_cont p).measurable (measurable_const.max hVraw))

theorem aux_finite_negative_layer_log_lipschitz_majorant_scaled_ratio
    {d : ℕ} {K : Compacts (SpatialCoordinates d)}
    {R c : ℝ} (hc : 0 ≤ c)
    (hK : ∀ x : K, c • (x : SpatialCoordinates d) ∈
      Metric.closedBall (0 : SpatialCoordinates d) R)
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (W : ℝ≥0)
    (hLip : LipschitzOnWith W (fun x => g x)
      (Metric.closedBall (0 : SpatialCoordinates d) R)) :
    ∀ x y : K, x ≠ y →
      |g (c • (x : SpatialCoordinates d)) - g (c • (y : SpatialCoordinates d))| /
          dist (x : SpatialCoordinates d) y ≤ c * (W : ℝ) := by
  intro x y hxy
  have hdist : 0 < dist (x : SpatialCoordinates d) y :=
    dist_pos.mpr (by
      intro h
      exact hxy (Subtype.ext h))
  have h := hLip.dist_le_mul (c • (x : SpatialCoordinates d)) (hK x)
    (c • (y : SpatialCoordinates d)) (hK y)
  have h' : |g (c • (x : SpatialCoordinates d)) -
      g (c • (y : SpatialCoordinates d))| ≤
      (W : ℝ) * (c * dist (x : SpatialCoordinates d) y) := by
    simpa [← smul_sub, dist_eq_norm, Real.norm_eq_abs, norm_smul, abs_of_nonneg hc,
      mul_assoc, mul_left_comm, mul_comm] using! h
  apply (div_le_iff₀ hdist).2
  simpa [mul_assoc, mul_left_comm, mul_comm] using! h'

theorem aux_finite_negative_layer_log_lipschitz_majorant_grid_cover
    {d : ℕ} (q : ℕ) {R : ℝ} (hR : R ≤ (3 : ℝ) ^ q / 4)
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
    LipschitzOnWith
      ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).sup'
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d (q : ℤ))
        (fun a =>
          (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
              (_root_.SubdiffusiveProcess.Model.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g),
            _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0)))
      (fun x => g x) (Metric.closedBall (0 : SpatialCoordinates d) R) := by
  classical
  let S := SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)
  let hS := SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d (q : ℤ)
  let W : ℝ≥0 := S.sup' hS (fun a =>
    (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
        (_root_.SubdiffusiveProcess.Model.PotentialField.translate
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g),
      _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0))
  change LipschitzOnWith W (fun x => g x)
    (Metric.closedBall (0 : SpatialCoordinates d) R)
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro x hx
    exact (g.hasFDerivAt x).differentiableAt
  · intro x hx
    have hx0 : dist x (0 : SpatialCoordinates d) ≤ R := by
      simpa [Metric.mem_closedBall, dist_comm] using! hx
    have hxnorm : ‖x‖ ≤ R := by simpa [dist_zero_right] using! hx0
    have hpow : (0 : ℝ) < (3 : ℝ) ^ q := by positivity
    have hxopen : x ∈
        Homogenization.openCubeSet (Homogenization.originCube d (q : ℤ)) := by
      rw [Homogenization.mem_openCubeSet_originCube_iff]
      intro i
      have hi : |x i| ≤ R := (norm_le_pi_norm x i).trans hxnorm
      have hi' : |x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ (q : ℤ) := by
        have hlt : R < (1 / 2 : ℝ) * (3 : ℝ) ^ (q : ℤ) := by
          rw [zpow_natCast]
          nlinarith
        exact hi.trans_lt hlt
      rcases abs_lt.mp hi' with ⟨hlo, hhi⟩
      constructor <;> nlinarith
    obtain ⟨a, ha, hxa⟩ :=
      SubdiffusiveProcess.CoarseGrainingVocab.exists_shellCoverShift_mem hxopen
    rw [Homogenization.mem_translateSet_iff_sub_mem] at hxa
    have hderiv :
        fderiv ℝ ((_root_.SubdiffusiveProcess.Model.PotentialField.translate
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g) :
          SpatialCoordinates d → ℝ)
          (x - SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) =
        fderiv ℝ (fun y => g y) x := by
      simpa [_root_.SubdiffusiveProcess.Model.PotentialField.translate_apply,
        sub_add_cancel] using!
        (fderiv_comp_add_right (𝕜 := ℝ) (f := (fun y => g y))
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a)
          (x := x - SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a))
    rw [← hderiv]
    rw [(_root_.SubdiffusiveProcess.Model.PotentialField.translate
      (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g).hasFDerivAt
        (x - SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) |>.fderiv]
    rw [← NNReal.coe_le_coe]
    exact (_root_.SubdiffusiveProcess.Model.PotentialField.norm_deriv_le_g2Observable
      (_root_.SubdiffusiveProcess.Model.PotentialField.translate
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g) hxa).trans
      (Finset.le_sup' (f := fun a =>
        (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
            (_root_.SubdiffusiveProcess.Model.PotentialField.translate
              (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g),
          _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0)) ha)
  · exact convex_closedBall (0 : SpatialCoordinates d) R

/--
Fine proof-step child of lem_extremes, paper label `mfd:lem-extremes`.

Inputs:
- z, r, and hr pin the fixed cube; p is fixed before the disorder threshold.
- stationary_family supplies the scale-rescaled layer law and spatial
  finite-range convention, in_normalization supplies the negative-layer
  indexing, and layer_regularity_moments supplies the unit-layer moment bound.
- The cell maximum, the finite-layer sum, the common a.s. event, and the
  MemLp/eLpNorm conclusions are produced here.
- End of carried-input tick list.
-/
theorem finite_negative_layer_log_lipschitz_majorant :
  ∀ (d : ℕ), 2 ≤ d →
  ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)],
  ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
  ∀ (p : ℝ), 1 ≤ p →
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d),
      M.delta ≤ c / p →
      ∃ U : ℕ → BilateralField d → ℝ,
        (∀ N om, 0 ≤ U N om) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ N x y,
            x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
            y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
            |(∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
                ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) y| ≤
              U N om * (3 : ℝ) ^ N * dist x y) ∧
        (∀ N, MemLp (U N) (ENNReal.ofReal p)
          (chaosSampleLaw M).toMeasure) ∧
        (∀ N, eLpNorm (U N) (ENNReal.ofReal p)
            (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C * M.delta * Real.sqrt (1 + (N : ℝ)))) := by
  intro d hd _ _ z r hr p hp
  obtain ⟨C₀, hC₀, hC₀mom⟩ := layer_regularity_moments hd
  obtain ⟨Q₀, hQ₀⟩ :=
    pow_unbounded_of_one_lt (4 * (‖z‖ + r / 2))
      (by norm_num : (1 : ℝ) < 3)
  let C₁ : ℝ := C₀ + 1 + 6 *
      (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
        Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
        ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * Real.sqrt (Q₀ + 1)
  have hC₁ : 0 < C₁ := by
    dsimp [C₁]
    have hgamma := Homogenization.IndependentSums.gammaMomentConst_pos
      (show (0 : ℝ) < 2 by norm_num)
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hK := SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst_pos
    positivity
  let Dglobal : ℝ :=
    Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
      Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)
  have hCdom : 2 * Dglobal * Real.sqrt (Q₀ + 1) ≤ C₁ := by
    dsimp [C₁, Dglobal]
    have hD : 0 ≤
        Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
          Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (Homogenization.IndependentSums.gammaMomentConst_pos
              (show (0 : ℝ) < 2 by norm_num)).le (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (by
          have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
          linarith) _)
    have hq : 0 ≤ Real.sqrt (Q₀ + 1) := Real.sqrt_nonneg _
    have hprod : 0 ≤
        (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
          Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * Real.sqrt (Q₀ + 1) :=
      mul_nonneg hD hq
    nlinarith [hC₀, hprod]
  refine ⟨C₁, 1, hC₁, one_pos, ?_⟩
  intro M hM
  let K : Compacts (SpatialCoordinates d) := closedCube z r hr
  obtain ⟨V, hVmeas, hV0, hVdom, hVle, hPmeas⟩ :=
    aux_finite_negative_layer_log_lipschitz_majorant_continuous_ratio K
  let F : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
    fun N om x => ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x
  let U : ℕ → BilateralField d → ℝ := fun N om =>
    (3 : ℝ) ^ (-(N : ℤ)) *
      ∑ j ∈ Finset.range (N + 1), V (om (-(Int.ofNat j)))
  let μ₀ : Measure (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) :=
    Measure.infinitePi (fun _ : ℤ =>
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
  let forget₀ : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let π₀ : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) → BilateralField d :=
    fun omega j => layerScaling d j (forget₀ (omega j))
  have hπ₀meas : Measurable π₀ := by
    apply Measurable.of_eval
    intro j
    exact (layerScaling d j).continuous.measurable.comp
      (forget₀.continuous.measurable.comp (measurable_pi_apply j))
  have hπ₀measure : Measure.map π₀ μ₀ = (chaosSampleLaw M).toMeasure := by
    simpa only [chaosSampleLaw, chaosRootFieldLaw, μ₀, π₀, Function.comp_apply] using!
      (measurePreserving_nativeCopies_commonScaleLaw M).map_eq
  let H : ℕ → _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun q g =>
    (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).sup'
      (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d (q : ℤ))
      (fun a => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
        (_root_.SubdiffusiveProcess.Model.PotentialField.translate
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g))
  have hHmeas : ∀ q, Measurable (H q) := by
    intro q
    dsimp [H]
    convert (Finset.measurable_sup'
      (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d (q : ℤ))
      (fun a _ => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable.comp
        (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a)))) using 1
    funext g
    simp only [Finset.sup'_apply, Function.comp_apply]
  have hHnonneg : ∀ q g, 0 ≤ H q g := by
    intro q g
    obtain ⟨a, ha⟩ :=
      SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d (q : ℤ)
    exact (_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _).trans
      (Finset.le_sup' (f := fun a =>
        _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g)) ha)
  let Wj₀ : ℕ → _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun j g =>
    H (Q₀ + j + 1) g
  have hscaled₀ : ∀ omega : ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d,
      ∀ j, ∀ x y : K, x ≠ y →
        |(π₀ omega (-(Int.ofNat j))) x.1 -
            (π₀ omega (-(Int.ofNat j))) y.1| / dist x.1 y.1 ≤
          (3 : ℝ) ^ j * (Wj₀ j (omega (-(Int.ofNat j))) : ℝ) := by
    intro omega j x y hxy
    let Rj : ℝ := (3 : ℝ) ^ j * (‖z‖ + r / 2)
    let qj : ℕ := Q₀ + j + 1
    have hRj : Rj ≤ (3 : ℝ) ^ qj / 4 := by
      dsimp [Rj, qj]
      have hpow : (3 : ℝ) ^ (Q₀ + j + 1) =
          (3 : ℝ) ^ Q₀ * (3 : ℝ) ^ j * 3 := by
        rw [pow_add, pow_add]
        ring
      rw [hpow]
      have h3j : 0 < (3 : ℝ) ^ j := by positivity
      have hbase : ‖z‖ + r / 2 < (3 : ℝ) ^ Q₀ / 4 := by
        nlinarith [hQ₀]
      calc
        (3 : ℝ) ^ j * (‖z‖ + r / 2) ≤
            (3 : ℝ) ^ j * ((3 : ℝ) ^ Q₀ / 4) :=
          (mul_lt_mul_of_pos_left hbase h3j).le
        _ ≤ (3 : ℝ) ^ Q₀ * (3 : ℝ) ^ j * 3 / 4 := by
          calc
            (3 : ℝ) ^ j * ((3 : ℝ) ^ Q₀ / 4) =
                (3 : ℝ) ^ Q₀ * (3 : ℝ) ^ j / 4 := by ring
            _ ≤ (3 : ℝ) ^ Q₀ * (3 : ℝ) ^ j * 3 / 4 := by
              have hnonneg : 0 ≤ (3 : ℝ) ^ Q₀ * (3 : ℝ) ^ j := by positivity
              nlinarith
    have hroot :=
      aux_finite_negative_layer_log_lipschitz_majorant_grid_cover
        (q := qj) hRj (omega (-(Int.ofNat j)))
    have hs : 0 ≤ (3 : ℝ) ^ j := by positivity
    have hfield (w : K) :
        (π₀ omega (-(Int.ofNat j))) w.1 =
          (omega (-(Int.ofNat j))) ((3 : ℝ) ^ j • w.1) := by
      simp [π₀, layerScaling, ContinuousMap.compRightContinuousMap_apply,
        zpow_natCast]
      rfl
    have hxnorm : ‖x.1‖ ≤ ‖z‖ + r / 2 := by
      have hxprop := x.property
      change dist x.1 z ≤ r / 2 at hxprop
      calc
        ‖x.1‖ = ‖(x.1 - z) + z‖ := by congr 1 ; abel
        _ ≤ ‖x.1 - z‖ + ‖z‖ := norm_add_le _ _
        _ = dist x.1 z + ‖z‖ := by rw [dist_eq_norm]
        _ ≤ r / 2 + ‖z‖ := add_le_add hxprop le_rfl
        _ = ‖z‖ + r / 2 := by ring
    have hynorm : ‖y.1‖ ≤ ‖z‖ + r / 2 := by
      have hyprop := y.property
      change dist y.1 z ≤ r / 2 at hyprop
      calc
        ‖y.1‖ = ‖(y.1 - z) + z‖ := by congr 1 ; abel
        _ ≤ ‖y.1 - z‖ + ‖z‖ := norm_add_le _ _
        _ = dist y.1 z + ‖z‖ := by rw [dist_eq_norm]
        _ ≤ r / 2 + ‖z‖ := add_le_add hyprop le_rfl
        _ = ‖z‖ + r / 2 := by ring
    have hxball : (3 : ℝ) ^ j • x.1 ∈
        Metric.closedBall (0 : SpatialCoordinates d) Rj := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hs]
      exact (mul_le_mul_of_nonneg_left hxnorm hs).trans_eq rfl
    have hyball : (3 : ℝ) ^ j • y.1 ∈
        Metric.closedBall (0 : SpatialCoordinates d) Rj := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hs]
      exact (mul_le_mul_of_nonneg_left hynorm hs).trans_eq rfl
    have hdist := hroot.dist_le_mul
      ((3 : ℝ) ^ j • x.1) hxball ((3 : ℝ) ^ j • y.1) hyball
    have hsup_eq :
        (↑((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (qj : ℤ)).sup'
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d (qj : ℤ))
          (fun a =>
            (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
              (_root_.SubdiffusiveProcess.Model.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a)
                (omega (-(Int.ofNat j)))),
              _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0)) : ℝ≥0) : ℝ) =
          H qj (omega (-(Int.ofNat j))) := by
      simpa [H, Function.comp_apply] using!
        (Finset.apply_sup'_eq_sup'_comp
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d (qj : ℤ))
          (fun x : ℝ≥0 => (x : ℝ))
          (fun x y : ℝ≥0 => NNReal.coe_max x y))
    rw [hsup_eq] at hdist
    have hdist' :
        |(omega (-(Int.ofNat j))) ((3 : ℝ) ^ j • x.1) -
            (omega (-(Int.ofNat j))) ((3 : ℝ) ^ j • y.1)| ≤
          (Wj₀ j (omega (-(Int.ofNat j))) : ℝ) *
            ((3 : ℝ) ^ j * dist x.1 y.1) := by
      simpa [Wj₀, H, qj, ← smul_sub, dist_eq_norm, Real.norm_eq_abs,
        norm_smul, abs_of_nonneg hs, mul_assoc, mul_left_comm, mul_comm] using! hdist
    rw [hfield x, hfield y]
    apply (div_le_iff₀ (dist_pos.mpr hxy)).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using! hdist'
  have hsourceBound₀ :
      ∀ omega : ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d, ∀ j,
        V (π₀ omega (-(Int.ofNat j))) ≤
          (3 : ℝ) ^ j * (Wj₀ j (omega (-(Int.ofNat j))) : ℝ) := by
    intro omega j
    exact hVle _ _ (mul_nonneg (by positivity) (hHnonneg _ _))
      (hscaled₀ omega j)
  have hUmeas : ∀ N, Measurable (U N) := by
    intro N
    dsimp [U]
    exact measurable_const.mul (Finset.measurable_sum _ fun j _ =>
      hVmeas.comp (measurable_pi_apply _))
  let μz : Measure (_root_.SubdiffusiveProcess.Model.PotentialField d) :=
    (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  have hHbig : ∀ q, Homogenization.IndependentSums.IsBigOWith μz
      (Homogenization.IndependentSums.gammaSigma 2) (H q)
      (((3 * Real.log
        ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).card : ℝ)) ^
          (2 : ℝ)⁻¹) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by
    intro q
    let T : (_root_.SubdiffusiveProcess.Model.PotentialSample d) →
        _root_.SubdiffusiveProcess.Model.PotentialField d := fun omega =>
      SubdiffusiveProcess.CoarseGrainingVocab.unscalePotential 0 (omega 0)
    have hTmeas : Measurable T := by
      exact (SubdiffusiveProcess.CoarseGrainingVocab.measurable_unscalePotential 0).comp
        (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate 0)
    have hTmap : Measure.map T M.P.toMeasure = μz := by
      simpa [T, μz] using!
        (SubdiffusiveProcess.CoarseGrainingVocab.map_unscalePotential_coordinate_eq_zero M 0)
    have hmap : Measure.map (H q) μz =
        Measure.map (SubdiffusiveProcess.CoarseGrainingVocab.largeCubeShellG2 0 (q : ℤ))
          M.P.toMeasure := by
      calc
        Measure.map (H q) μz = Measure.map (H q)
            (Measure.map T M.P.toMeasure) := by rw [hTmap]
        _ = Measure.map (H q ∘ T) M.P.toMeasure := by
          rw [Measure.map_map (hHmeas q) hTmeas]
        _ = Measure.map
            (SubdiffusiveProcess.CoarseGrainingVocab.largeCubeShellG2 0 (q : ℤ))
            M.P.toMeasure := by
          congr 1
    exact SubdiffusiveProcess.CoarseGrainingVocab.isBigOWith_of_map_eq (hHmeas q)
      (SubdiffusiveProcess.CoarseGrainingVocab.measurable_largeCubeShellG2 0 (q : ℤ)) hmap
      (SubdiffusiveProcess.CoarseGrainingVocab.isBigOWith_gammaTwo_largeCubeShellG2
        M 0 (q : ℤ))
  have hApos : ∀ q, 0 <
      ((3 * Real.log
        ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).card : ℝ)) ^
          (2 : ℝ)⁻¹) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by
    intro q
    apply mul_pos
    · apply Real.rpow_pos_of_pos
      apply mul_pos (by norm_num)
      apply Real.log_pos
      have hcard := SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_card_ge_two M
        (q : ℤ)
      exact_mod_cast hcard
    · apply mul_pos
      · apply Real.rpow_pos_of_pos
        have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
        linarith
      · exact M.shellPrefix.delta_pos
  have hHnorm : ∀ q, eLpNorm (H q) (ENNReal.ofReal p) μz ≤
      ENNReal.ofReal (Homogenization.IndependentSums.gammaMomentConst 2 *
        Real.sqrt p * (((3 * Real.log
          ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).card : ℝ)) ^
            (2 : ℝ)⁻¹) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta))) := by
    intro q
    have hHbig' : Homogenization.IndependentSums.IsBigO μz
        (Homogenization.IndependentSums.gammaSigma 2) (H q)
        (((3 * Real.log
          ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).card : ℝ)) ^
            (2 : ℝ)⁻¹) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by
      change Homogenization.IndependentSums.IsBigOWith μz
        (Homogenization.IndependentSums.gammaSigma 2)
        (fun g => |H q g|) _
      have habs : (fun g => |H q g|) = H q := by
        funext g
        exact abs_of_nonneg (hHnonneg q g)
      rw [habs]
      exact hHbig q
    exact SubdiffusiveProcess.CoarseGrainingVocab.eLpNorm_le_of_isBigO_gammaTwo
      (hApos q) hp (hHmeas q).aemeasurable hHbig'
  have hHnorm' : ∀ q : ℕ, 0 < (q : ℤ) →
      eLpNorm (H q) (ENNReal.ofReal p) μz ≤
        ENNReal.ofReal ((Homogenization.IndependentSums.gammaMomentConst 2 *
          Real.sqrt p * Real.sqrt
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta * Real.sqrt (q : ℝ)) := by
    intro q hq
    apply (hHnorm q).trans
    apply ENNReal.ofReal_le_ofReal
    have hfactor := SubdiffusiveProcess.CoarseGrainingVocab.shellCover_gaussianFactor_le_sqrt M
      (show (0 : ℤ) < (q : ℤ) from hq)
    calc
      Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
          (((3 * Real.log
            ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).card : ℝ)) ^
              (2 : ℝ)⁻¹) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) ≤
          Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
            ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
              Real.sqrt (q : ℝ)) *
              ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by
        have hfactor' :
            (3 * Real.log
              ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).card : ℝ)) ^
                (2 : ℝ)⁻¹ ≤
              Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                Real.sqrt (q : ℝ) := by
          simpa using! hfactor
        have hleft : 0 ≤
            Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p := by
          exact mul_nonneg
            (Homogenization.IndependentSums.gammaMomentConst_pos
              (show (0 : ℝ) < 2 by norm_num)).le (Real.sqrt_nonneg _)
        have hright : 0 ≤ (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta := by
          exact mul_nonneg (Real.rpow_nonneg (by
            have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
            linarith) _) M.shellPrefix.delta_pos.le
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hfactor' hright) hleft
      _ = (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
          Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta * Real.sqrt (q : ℝ) := by
        ring
  have hHmem : ∀ q, MemLp (H q) (ENNReal.ofReal p) μz := by
    intro q
    exact (hHnorm q).trans_lt ENNReal.ofReal_lt_top
  have hHrawmem : ∀ (q : ℕ) (j : ℤ),
      MemLp (fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
        H q (omega j)) (ENNReal.ofReal p) μ₀ := by
    intro q j
    simpa [μ₀, Function.comp_def] using!
      (hHmem q).comp_measurePreserving
        (measurePreserving_eval_infinitePi
          (fun _ : ℤ => μz) j)
  let T : ℕ → (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) → ℝ := fun j omega =>
    (3 : ℝ) ^ j * Wj₀ j (omega (-(Int.ofNat j)))
  let G : ℕ → (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) → ℝ := fun N =>
    ∑ j ∈ Finset.range (N + 1), T j
  have htermMem : ∀ N j, j ∈ Finset.range (N + 1) →
      MemLp (fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
        (3 : ℝ) ^ j * Wj₀ j (omega (-(Int.ofNat j))))
        (ENNReal.ofReal p) μ₀ := by
    intro N j hj
    simpa [Wj₀, Pi.smul_apply, smul_eq_mul] using!
      ((hHrawmem (Q₀ + j + 1) (-Int.ofNat j)).const_mul ((3 : ℝ) ^ j))
  have hGmem : ∀ N, MemLp (G N) (ENNReal.ofReal p) μ₀ := by
    intro N
    dsimp [G]
    convert memLp_finsetSum' (Finset.range (N + 1))
      (fun j hj => by simpa [T] using! htermMem N j hj) using 1
  have hGnonneg : ∀ N omega, 0 ≤ G N omega := by
    intro N omega
    have hs : 0 ≤ ∑ j ∈ Finset.range (N + 1), T j omega :=
      Finset.sum_nonneg (fun j hj => by
        dsimp [T]
        exact mul_nonneg (by positivity) (hHnonneg _ _))
    simpa [G, T] using! hs
  have hUbound : ∀ N omega,
      U N (π₀ omega) ≤ (3 : ℝ) ^ (-(N : ℤ)) * G N omega := by
    intro N omega
    dsimp [U, G]
    simp only [Finset.sum_apply, T]
    apply mul_le_mul_of_nonneg_left
    · exact Finset.sum_le_sum (fun j hj => hsourceBound₀ omega j)
    · positivity
  have hgeom : ∀ N,
      (∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ j) ≤ 2 * (3 : ℝ) ^ N := by
    intro N
    induction N with
    | zero => norm_num
    | succ N ih =>
        rw [Finset.sum_range_succ, pow_succ]
        have hpw : 0 ≤ (3 : ℝ) ^ N := by positivity
        nlinarith
  have hWnorm : ∀ j,
      eLpNorm (fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
        Wj₀ j (omega (-(Int.ofNat j)))) (ENNReal.ofReal p) μ₀ ≤
      ENNReal.ofReal ((Homogenization.IndependentSums.gammaMomentConst 2 *
          Real.sqrt p * Real.sqrt
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
        Real.sqrt ((Q₀ + j + 1 : ℕ) : ℝ)) := by
    intro j
    calc
      eLpNorm (fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
          Wj₀ j (omega (-(Int.ofNat j)))) (ENNReal.ofReal p) μ₀ =
          eLpNorm (H (Q₀ + j + 1)) (ENNReal.ofReal p) μz := by
        simpa [Wj₀, Function.comp_def] using!
          (eLpNorm_comp_measurePreserving
            (hHmeas (Q₀ + j + 1)).aestronglyMeasurable
            (measurePreserving_eval_infinitePi
              (fun _ : ℤ => μz) (-Int.ofNat j)))
      _ ≤ _ := hHnorm' (Q₀ + j + 1) (by omega)
  have htermNorm : ∀ N j, j ∈ Finset.range (N + 1) →
      eLpNorm (fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
        (3 : ℝ) ^ j * Wj₀ j (omega (-(Int.ofNat j))))
        (ENNReal.ofReal p) μ₀ ≤
      ENNReal.ofReal ((3 : ℝ) ^ j *
        ((Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
          Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
          Real.sqrt ((Q₀ + j + 1 : ℕ) : ℝ))) := by
    intro N j hj
    calc
      eLpNorm (fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
          (3 : ℝ) ^ j * Wj₀ j (omega (-(Int.ofNat j))))
          (ENNReal.ofReal p) μ₀ ≤
          ENNReal.ofReal ((3 : ℝ) ^ j) *
            eLpNorm (fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
              Wj₀ j (omega (-(Int.ofNat j)))) (ENNReal.ofReal p) μ₀ := by
        have hsmul := eLpNorm_const_smul_le
          (c := (3 : ℝ) ^ j)
          (f := fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
            Wj₀ j (omega (-(Int.ofNat j))))
          (p := ENNReal.ofReal p) (μ := μ₀)
        have hcoef : ‖(3 : ℝ) ^ j‖ₑ = ENNReal.ofReal ((3 : ℝ) ^ j) := by
          rw [← ofReal_norm]
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [hcoef] at hsmul
        simpa [Pi.smul_apply, smul_eq_mul] using! hsmul
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ j) *
          ENNReal.ofReal ((Homogenization.IndependentSums.gammaMomentConst 2 *
            Real.sqrt p * Real.sqrt
              (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
            ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
            Real.sqrt ((Q₀ + j + 1 : ℕ) : ℝ)) := by
        gcongr
        exact hWnorm j
      _ = ENNReal.ofReal ((3 : ℝ) ^ j *
          ((Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
            Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
            ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
            Real.sqrt ((Q₀ + j + 1 : ℕ) : ℝ))) := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (3 : ℝ) ^ j)]
  have hqSqrt : ∀ N j, j ∈ Finset.range (N + 1) →
      Real.sqrt ((Q₀ + j + 1 : ℕ) : ℝ) ≤
        Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1) := by
    intro N j hj
    have hjlt : j < N + 1 := Finset.mem_range.mp hj
    have hjN : j ≤ N := by
      exact Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using! hjlt)
    have hnat : Q₀ + j + 1 ≤ (Q₀ + 1) * (N + 1) := by
      nlinarith [Nat.zero_le (Q₀ * N)]
    have hreal : ((Q₀ + j + 1 : ℕ) : ℝ) ≤
        (((Q₀ + 1) * (N + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    have hsqrt := Real.sqrt_le_sqrt hreal
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Real.sqrt_mul (by positivity)]
      at hsqrt
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using! hsqrt
  /-
  have hGnorm : ∀ N,
      eLpNorm (G N) (ENNReal.ofReal p) μ₀ ≤
        ENNReal.ofReal ((Homogenization.IndependentSums.gammaMomentConst 2 *
          Real.sqrt p * Real.sqrt
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
          Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1) * (2 * (3 : ℝ) ^ N)) := by
    intro N
    have hpenn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p :=
      ENNReal.one_le_ofReal.mpr hp
    calc
      eLpNorm (G N) (ENNReal.ofReal p) μ₀ ≤
          ∑ j ∈ Finset.range (N + 1),
            eLpNorm (fun omega : (ℤ → SubdiffusiveProcess.Model.PotentialField d) =>
              (3 : ℝ) ^ j * Wj₀ j (omega (-(Int.ofNat j))))
              (ENNReal.ofReal p) μ₀ := by
        dsimp [G]
        simpa [T] using! (eLpNorm_sum_le
          (f := fun (j : ℕ) (omega : ℤ → SubdiffusiveProcess.Model.PotentialField d) =>
            (3 : ℝ) ^ j * Wj₀ j (omega (-(Int.ofNat j))))
          (s := Finset.range (N + 1))
          hpenn)
      _ ≤ ∑ j ∈ Finset.range (N + 1),
          ENNReal.ofReal ((3 : ℝ) ^ j *
            ((Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
              Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
              ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
              Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1))) := by
        exact Finset.sum_le_sum (fun j hj => by
          apply (htermNorm N j hj).trans
          apply ENNReal.ofReal_le_ofReal
          have hs := hqSqrt N j hj
          have hnonneg : 0 ≤ (3 : ℝ) ^ j *
              ((Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
              ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta) := by
            have hbase : 0 ≤
                Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                  Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                  ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) := by
              exact mul_nonneg
                (mul_nonneg
                  (mul_nonneg
                    (Homogenization.IndependentSums.gammaMomentConst_pos
                      (show (0 : ℝ) < 2 by norm_num)).le
                    (Real.sqrt_nonneg _))
                  (Real.sqrt_nonneg _))
                (Real.rpow_nonneg (by
                  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
                  linarith) _)
            exact mul_nonneg (by positivity)
              (mul_nonneg hbase M.shellPrefix.delta_pos.le)
          calc
            (3 : ℝ) ^ j *
                ((Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                  Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                  ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
                  Real.sqrt ((Q₀ + j + 1 : ℕ) : ℝ)) =
                ((3 : ℝ) ^ j *
                  ((Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                    Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                    ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta)) *
                  Real.sqrt ((Q₀ + j + 1 : ℕ) : ℝ) := by ring
            _ ≤ ((3 : ℝ) ^ j *
                  ((Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                    Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                    ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta)) *
                  (Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1)) :=
              mul_le_mul_of_nonneg_left (hqSqrt N j hj) hnonneg
            _ = (3 : ℝ) ^ j *
                ((Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                  Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                  ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
                  Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1)) := by ring)
      _ = ENNReal.ofReal ((∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ j) *
          ((Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
            Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
            ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
            Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1))) := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · rw [Finset.sum_mul]
        · intro j hj
          have hbase : 0 ≤
              Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) := by
            exact mul_nonneg
              (mul_nonneg
                (mul_nonneg
                  (Homogenization.IndependentSums.gammaMomentConst_pos
                    (show (0 : ℝ) < 2 by norm_num)).le
                  (Real.sqrt_nonneg _))
                (Real.sqrt_nonneg _))
              (Real.rpow_nonneg (by
                have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
                linarith) _)
          have hBd : 0 ≤
              (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta :=
            mul_nonneg hbase M.shellPrefix.delta_pos.le
          have hBQ : 0 ≤
              ((Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta) *
                Real.sqrt (Q₀ + 1) :=
            mul_nonneg hBd (Real.sqrt_nonneg _)
          exact mul_nonneg (by positivity)
            (mul_nonneg hBQ (Real.sqrt_nonneg _))
      _ ≤ ENNReal.ofReal ((Homogenization.IndependentSums.gammaMomentConst 2 *
          Real.sqrt p * Real.sqrt
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
          Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1) * (2 * (3 : ℝ) ^ N)) := by
        apply ENNReal.ofReal_le_ofReal
        have hg := hgeom N
        have hnonneg : 0 ≤
            (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
              Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
              ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
            Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1) := by
          have hbase : 0 ≤
              Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) := by
            exact mul_nonneg
              (mul_nonneg
                (mul_nonneg
                  (Homogenization.IndependentSums.gammaMomentConst_pos
                    (show (0 : ℝ) < 2 by norm_num)).le
                  (Real.sqrt_nonneg _))
                (Real.sqrt_nonneg _))
              (Real.rpow_nonneg (by
                have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
                linarith) _)
          exact mul_nonneg (mul_nonneg (mul_nonneg hbase M.shellPrefix.delta_pos.le)
            (by positivity)) (by positivity)
        simpa [mul_assoc, mul_left_comm, mul_comm] using!
          (mul_le_mul_of_nonneg_right hg hnonneg)
  -/
  let B : ℝ :=
    (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
      Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta
  have hB : 0 ≤ B := by
    dsimp [B]
    have hbase : 0 ≤
        Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
          Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (Homogenization.IndependentSums.gammaMomentConst_pos
              (show (0 : ℝ) < 2 by norm_num)).le (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (by
          have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
          linarith) _)
    exact mul_nonneg hbase M.shellPrefix.delta_pos.le
  have hGnorm : ∀ N,
      eLpNorm (G N) (ENNReal.ofReal p) μ₀ ≤
        ENNReal.ofReal (B * Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1) *
          (2 * (3 : ℝ) ^ N)) := by
    intro N
    have hpenn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p :=
      ENNReal.one_le_ofReal.mpr hp
    let A : ℝ := B * Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1)
    have hA : 0 ≤ A := by
      dsimp [A]
      exact mul_nonneg (mul_nonneg hB (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    have hterm : ∀ j, j ∈ Finset.range (N + 1) →
        eLpNorm (fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
          (3 : ℝ) ^ j * Wj₀ j (omega (-(Int.ofNat j))))
          (ENNReal.ofReal p) μ₀ ≤ ENNReal.ofReal ((3 : ℝ) ^ j * A) := by
      intro j hj
      apply (htermNorm N j hj).trans
      apply ENNReal.ofReal_le_ofReal
      dsimp [A, B]
      have hs := hqSqrt N j hj
      have hbase : 0 ≤
          Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
            Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
            ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) := by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (Homogenization.IndependentSums.gammaMomentConst_pos
                (show (0 : ℝ) < 2 by norm_num)).le (Real.sqrt_nonneg _))
            (Real.sqrt_nonneg _))
          (Real.rpow_nonneg (by
            have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
            linarith) _)
      have hcoef : 0 ≤ (3 : ℝ) ^ j *
          (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
            Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
            ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) * M.delta) := by
        exact mul_nonneg (by positivity)
          (mul_nonneg hbase M.shellPrefix.delta_pos.le)
      calc
        (3 : ℝ) ^ j *
            ((Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
              Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
              ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
              Real.sqrt ((Q₀ + j + 1 : ℕ) : ℝ)) =
            ((3 : ℝ) ^ j *
              (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) * M.delta)) *
              Real.sqrt ((Q₀ + j + 1 : ℕ) : ℝ) := by ring
        _ ≤ ((3 : ℝ) ^ j *
              (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) * M.delta)) *
              (Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1)) :=
          mul_le_mul_of_nonneg_left hs hcoef
        _ = (3 : ℝ) ^ j * A := by ring
    calc
      eLpNorm (G N) (ENNReal.ofReal p) μ₀ ≤
          ∑ j ∈ Finset.range (N + 1),
            eLpNorm (fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
              (3 : ℝ) ^ j * Wj₀ j (omega (-(Int.ofNat j))))
              (ENNReal.ofReal p) μ₀ := by
        dsimp [G]
        simpa [T] using! (eLpNorm_sum_le
          (f := fun (j : ℕ) (omega : ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
            (3 : ℝ) ^ j * Wj₀ j (omega (-(Int.ofNat j))))
          (s := Finset.range (N + 1))
          hpenn)
      _ ≤ ∑ j ∈ Finset.range (N + 1),
          ENNReal.ofReal ((3 : ℝ) ^ j * A) :=
        Finset.sum_le_sum (fun j hj => hterm j hj)
      _ = ENNReal.ofReal ((∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ j) * A) := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · rw [Finset.sum_mul]
        · intro j hj
          exact mul_nonneg (by positivity) hA
      _ ≤ ENNReal.ofReal (B * Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1) *
          (2 * (3 : ℝ) ^ N)) := by
        apply ENNReal.ofReal_le_ofReal
        have hg := hgeom N
        have hbound := mul_le_mul_of_nonneg_right hg hA
        dsimp [A] at hbound ⊢
        simpa [mul_assoc, mul_left_comm, mul_comm] using!
          hbound
  have hUnonneg : ∀ N omega, 0 ≤ U N (π₀ omega) := by
    intro N omega
    dsimp [U]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun j hj => hV0 _))
  have hpoint : ∀ N, ∀ᵐ omega ∂μ₀,
      ‖(U N ∘ π₀) omega‖ ≤
        (3 : ℝ) ^ (-(N : ℤ)) * ‖G N omega‖ := by
    intro N
    filter_upwards [] with omega
    simpa [Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg (hUnonneg N omega),
      abs_of_nonneg (hGnonneg N omega)] using! hUbound N omega
  have hπ₀pres : MeasurePreserving π₀ μ₀ (chaosSampleLaw M).toMeasure :=
    ⟨hπ₀meas, hπ₀measure⟩
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro N om
    apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg (fun j hj => hV0 _)
  · obtain ⟨Q, hQ⟩ :=
      pow_unbounded_of_one_lt (4 * (‖z‖ + r / 2))
        (by norm_num : (1 : ℝ) < 3)
    have hLayer : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ j x y,
          x ∈ (K : Set (SpatialCoordinates d)) →
          y ∈ (K : Set (SpatialCoordinates d)) →
          |om (-(Int.ofNat j)) x - om (-(Int.ofNat j)) y| ≤
            V (om (-(Int.ofNat j))) * dist x y := by
      let P : Set C(SpatialCoordinates d, ℝ) := {f |
        ∀ x y : K, x ≠ y →
          |f x.1 - f y.1| / dist x.1 y.1 ≤ V f}
      let E : Set (BilateralField d) := {om |
        ∀ j : ℕ, om (-(Int.ofNat j)) ∈ P}
      have hEmeas : MeasurableSet E := by
        rw [show E = ⋂ j : ℕ,
            (fun om : BilateralField d => om (-(Int.ofNat j))) ⁻¹' P by
          ext om
          simp [E]]
        exact MeasurableSet.iInter (fun j =>
          hPmeas.preimage (measurable_pi_apply _))
      let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
          C(SpatialCoordinates d, ℝ)) :=
        ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
      let π : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) → BilateralField d :=
        fun omega j => layerScaling d j (forget (omega j))
      let μ : Measure (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) :=
        Measure.infinitePi (fun _ : ℤ =>
          (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
      have hπmeas : Measurable π := by
        apply Measurable.of_eval
        intro j
        exact (layerScaling d j).continuous.measurable.comp
          (forget.continuous.measurable.comp (measurable_pi_apply j))
      have hπmeasure : Measure.map π μ = (chaosSampleLaw M).toMeasure := by
        simpa only [chaosSampleLaw, chaosRootFieldLaw, μ, π, Function.comp_apply] using!
          (measurePreserving_nativeCopies_commonScaleLaw M).map_eq
      let Wj : ℕ → _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ≥0 := fun j g =>
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((Q + j : ℕ) : ℤ)).sup'
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((Q + j : ℕ) : ℤ))
          (fun a =>
            (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
                (_root_.SubdiffusiveProcess.Model.PotentialField.translate
                  (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g),
              _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0))
      have hscaled : ∀ omega : ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d,
          ∀ j, ∀ x y : K, x ≠ y →
            |(π omega (-(Int.ofNat j))) x.1 -
                (π omega (-(Int.ofNat j))) y.1| / dist x.1 y.1 ≤
              (3 : ℝ) ^ j * (Wj j (omega (-(Int.ofNat j))) : ℝ) := by
        intro omega j x y hxy
        let Rj : ℝ := (3 : ℝ) ^ j * (‖z‖ + r / 2)
        let qj : ℕ := Q + j
        have hRj : Rj ≤ (3 : ℝ) ^ qj / 4 := by
          dsimp [Rj, qj]
          have hpow : (3 : ℝ) ^ (Q + j) = (3 : ℝ) ^ Q * (3 : ℝ) ^ j := by
            rw [pow_add]
          rw [hpow]
          have h3j : 0 < (3 : ℝ) ^ j := by positivity
          nlinarith
        have hroot :=
          aux_finite_negative_layer_log_lipschitz_majorant_grid_cover
            (q := qj) hRj (omega (-(Int.ofNat j)))
        have hs : 0 ≤ (3 : ℝ) ^ j := by positivity
        have hfield (w : K) :
            (π omega (-(Int.ofNat j))) w.1 =
              (omega (-(Int.ofNat j))) ((3 : ℝ) ^ j • w.1) := by
          simp [π, layerScaling, ContinuousMap.compRightContinuousMap_apply,
            zpow_natCast]
          rfl
        have hxnorm : ‖x.1‖ ≤ ‖z‖ + r / 2 := by
          have hxprop := x.property
          change dist x.1 z ≤ r / 2 at hxprop
          calc
            ‖x.1‖ = ‖(x.1 - z) + z‖ := by congr 1 ; abel
            _ ≤ ‖x.1 - z‖ + ‖z‖ := norm_add_le _ _
            _ = dist x.1 z + ‖z‖ := by rw [dist_eq_norm]
            _ ≤ r / 2 + ‖z‖ := add_le_add hxprop le_rfl
            _ = ‖z‖ + r / 2 := by ring
        have hynorm : ‖y.1‖ ≤ ‖z‖ + r / 2 := by
          have hyprop := y.property
          change dist y.1 z ≤ r / 2 at hyprop
          calc
            ‖y.1‖ = ‖(y.1 - z) + z‖ := by congr 1 ; abel
            _ ≤ ‖y.1 - z‖ + ‖z‖ := norm_add_le _ _
            _ = dist y.1 z + ‖z‖ := by rw [dist_eq_norm]
            _ ≤ r / 2 + ‖z‖ := add_le_add hyprop le_rfl
            _ = ‖z‖ + r / 2 := by ring
        have hxball : (3 : ℝ) ^ j • x.1 ∈
            Metric.closedBall (0 : SpatialCoordinates d) Rj := by
          rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
            Real.norm_eq_abs, abs_of_nonneg hs]
          exact (mul_le_mul_of_nonneg_left hxnorm hs).trans_eq rfl
        have hyball : (3 : ℝ) ^ j • y.1 ∈
            Metric.closedBall (0 : SpatialCoordinates d) Rj := by
          rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
            Real.norm_eq_abs, abs_of_nonneg hs]
          exact (mul_le_mul_of_nonneg_left hynorm hs).trans_eq rfl
        have hdist := hroot.dist_le_mul
          ((3 : ℝ) ^ j • x.1) hxball ((3 : ℝ) ^ j • y.1) hyball
        have hdist' :
            |(omega (-(Int.ofNat j))) ((3 : ℝ) ^ j • x.1) -
                (omega (-(Int.ofNat j))) ((3 : ℝ) ^ j • y.1)| ≤
              (Wj j (omega (-(Int.ofNat j))) : ℝ) *
                ((3 : ℝ) ^ j * dist x.1 y.1) := by
          simpa [Wj, qj, ← smul_sub, dist_eq_norm, Real.norm_eq_abs, norm_smul,
            abs_of_nonneg hs, mul_assoc, mul_left_comm, mul_comm] using! hdist
        rw [hfield x, hfield y]
        apply (div_le_iff₀ (dist_pos.mpr hxy)).2
        simpa [mul_assoc, mul_left_comm, mul_comm] using! hdist'
      have hsource : ∀ omega : ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d,
          π omega ∈ E := by
        intro omega j
        exact hVdom _ _ (hscaled omega j)
      have hsourceBound :
          ∀ omega : ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d, ∀ j,
            V (π omega (-(Int.ofNat j))) ≤
              (3 : ℝ) ^ j * (Wj j (omega (-(Int.ofNat j))) : ℝ) := by
        intro omega j
        exact hVle _ _ (mul_nonneg (by positivity) (Wj _ _).coe_nonneg)
          (hscaled omega j)
        /-
        intro x y hxy
        have hquot :
            |(π omega (-(Int.ofNat j))) x.1 -
                (π omega (-(Int.ofNat j))) y.1| /
                dist x.1 y.1 ≤
              (3 : ℝ) ^ j * (Wj (omega (-(Int.ofNat j))) : ℝ) := by
          rw [hfield x, hfield y]
          have hdist' :
              |(omega (-(Int.ofNat j))) ((3 : ℝ) ^ j • x.1) -
                  (omega (-(Int.ofNat j))) ((3 : ℝ) ^ j • y.1)| ≤
                (Wj (omega (-(Int.ofNat j))) : ℝ) *
                  ((3 : ℝ) ^ j * dist x.1 y.1) := by
            simpa [dist_eq_norm, Real.norm_eq_abs, norm_smul,
              abs_of_nonneg hs, mul_assoc, mul_left_comm, mul_comm] using! hdist
          apply (div_le_iff₀ (dist_pos.mpr hxy)).2
          simpa [mul_assoc, mul_left_comm, mul_comm] using! hdist'
        exact hVdom _ _ (by
          intro a b hab
          exact hquot) x y hxy
        -/
        /-
        intro omega j
        change ∀ x y : K, x ≠ y →
          |(π omega (-(Int.ofNat j))) x.1 -
              (π omega (-(Int.ofNat j))) y.1| /
              dist x.1 y.1 ≤ V (π omega (-(Int.ofNat j)))
        let Rj : ℝ := (3 : ℝ) ^ j * (‖z‖ + r / 2)
        obtain ⟨S, hS, hroot⟩ :=
          aux_finite_negative_layer_log_lipschitz_majorant_root_cover Rj
        let Wj : SubdiffusiveProcess.Model.PotentialField d → ℝ≥0 := fun g =>
          S.sup' hS (fun a =>
            (⟨SubdiffusiveProcess.Model.PotentialField.g2Observable
                (SubdiffusiveProcess.Model.PotentialField.translate a g),
              SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0))
        intro x y hxy
        have hxnorm : ‖x.1‖ ≤ ‖z‖ + r / 2 := by
          have hxball : dist x.1 z ≤ r / 2 := by
            simpa [K, closedCube] using! x.property
          calc
            ‖x.1‖ = ‖(x.1 - z) + z‖ := by congr 1 <;> abel
            _ ≤ ‖x.1 - z‖ + ‖z‖ := norm_add_le _ _
            _ = dist x.1 z + ‖z‖ := by rw [dist_eq_norm]
            _ ≤ r / 2 + ‖z‖ := add_le_add_right hxball _
            _ = ‖z‖ + r / 2 := by ring
        have hynorm : ‖y.1‖ ≤ ‖z‖ + r / 2 := by
          have hyball : dist y.1 z ≤ r / 2 := by
            simpa [K, closedCube] using! y.property
          calc
            ‖y.1‖ = ‖(y.1 - z) + z‖ := by congr 1 <;> abel
            _ ≤ ‖y.1 - z‖ + ‖z‖ := norm_add_le _ _
            _ = dist y.1 z + ‖z‖ := by rw [dist_eq_norm]
            _ ≤ r / 2 + ‖z‖ := add_le_add_right hyball _
            _ = ‖z‖ + r / 2 := by ring
        have hs : 0 ≤ (3 : ℝ) ^ j := by positivity
        have hxball : (3 : ℝ) ^ j • x.1 ∈
            Metric.closedBall (0 : SpatialCoordinates d) Rj := by
          rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
            Real.norm_eq_abs, abs_of_nonneg hs]
          exact (mul_le_mul_of_nonneg_left hxnorm hs).trans_eq rfl
        have hyball : (3 : ℝ) ^ j • y.1 ∈
            Metric.closedBall (0 : SpatialCoordinates d) Rj := by
          rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
            Real.norm_eq_abs, abs_of_nonneg hs]
          exact (mul_le_mul_of_nonneg_left hynorm hs).trans_eq rfl
        have hroot' := hroot (omega (-(Int.ofNat j)))
        have hdist := hroot'.dist_le_mul
          ((3 : ℝ) ^ j • x.1) hxball ((3 : ℝ) ^ j • y.1) hyball
        have hfield (w : K) :
            (π omega (-(Int.ofNat j))) w.1 =
              (omega (-(Int.ofNat j))) ((3 : ℝ) ^ j • w.1) := by
          simp [π, layerScaling, ContinuousMap.compRightContinuousMap_apply,
            zpow_natCast]
        have hquot :
            |(π omega (-(Int.ofNat j))) x.1 -
                (π omega (-(Int.ofNat j))) y.1| /
                dist x.1 y.1 ≤
              (3 : ℝ) ^ j * (Wj (omega (-(Int.ofNat j))) : ℝ) := by
          rw [hfield x, hfield y]
          have hdist' :
              |(omega (-(Int.ofNat j))) ((3 : ℝ) ^ j • x.1) -
                  (omega (-(Int.ofNat j))) ((3 : ℝ) ^ j • y.1)| ≤
                (Wj (omega (-(Int.ofNat j))) : ℝ) *
                  ((3 : ℝ) ^ j * dist x.1 y.1) := by
            simpa [dist_eq_norm, Real.norm_eq_abs, norm_smul,
              abs_of_nonneg hs, mul_assoc, mul_left_comm, mul_comm] using! hdist
          apply (div_le_iff₀ (dist_pos.mpr hxy)).2
          simpa [mul_assoc, mul_left_comm, mul_comm] using! hdist'
        exact hVle _
          (3 : ℝ) ^ j * (Wj (omega (-(Int.ofNat j))) : ℝ)
          (mul_nonneg hs (Wj _).coe_nonneg) (by
            intro a b hab
            exact hquot.trans (le_rfl)) x y hxy
        -/
      have htarget : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, om ∈ E := by
        rw [← hπmeasure]
        apply (MeasureTheory.ae_map_iff hπmeas.aemeasurable hEmeas).2
        exact Filter.Eventually.of_forall hsource
      filter_upwards [htarget] with om hom
      intro j x y hx hy
      by_cases hxy : x = y
      · subst y
        simp
      ·
        have hp := hom j
        change ∀ a b : K, a ≠ b →
          |(om (-(Int.ofNat j))) a.1 - (om (-(Int.ofNat j))) b.1| /
            dist a.1 b.1 ≤ V (om (-(Int.ofNat j))) at hp
        have hq := hp ⟨x, by simpa [K] using! hx⟩ ⟨y, by simpa [K] using! hy⟩
          (by intro h; exact hxy (congrArg Subtype.val h))
        exact (div_le_iff₀ (dist_pos.mpr hxy)).mp hq
    filter_upwards [hLayer] with om hom
    intro N x y hx hy
    dsimp [F, U]
    have hsum :
        (∑ j ∈ Finset.range (N + 1),
          |om (-(Int.ofNat j)) x - om (-(Int.ofNat j)) y|) ≤
          ∑ j ∈ Finset.range (N + 1),
            V (om (-(Int.ofNat j))) * dist x y := by
      exact Finset.sum_le_sum (fun j hj => hom j x y hx hy)
    calc
      |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x -
          ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) y| =
          |∑ j ∈ Finset.range (N + 1),
            (om (-(Int.ofNat j)) x - om (-(Int.ofNat j)) y)| := by
        rw [Finset.sum_sub_distrib]
      _ ≤
          ∑ j ∈ Finset.range (N + 1),
            |om (-(Int.ofNat j)) x - om (-(Int.ofNat j)) y| := by
        simpa using! (Finset.abs_sum_le_sum_abs (G := ℝ)
          (fun j : ℕ => om (-(Int.ofNat j)) x - om (-(Int.ofNat j)) y)
          (Finset.range (N + 1)))
      _ ≤ ∑ j ∈ Finset.range (N + 1),
          V (om (-(Int.ofNat j))) * dist x y := hsum
      _ = (∑ j ∈ Finset.range (N + 1), V (om (-(Int.ofNat j)))) * dist x y := by
        rw [Finset.sum_mul]
      _ = U N om * (3 : ℝ) ^ N * dist x y := by
        dsimp [U]
        rw [zpow_neg, zpow_natCast]
        field_simp
  · intro N
    have hMemLp : MemLp (U N) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure := by
      rw [← hπ₀measure]
      exact (MeasureTheory.memLp_map_measure_iff
        (μ := μ₀) (f := π₀) (g := U N) (p := ENNReal.ofReal p)
        (hUmeas N).aestronglyMeasurable hπ₀meas.aemeasurable).2
        ((hGmem N).of_le_mul
          ((hUmeas N).comp hπ₀meas).aestronglyMeasurable (hpoint N))
    exact hMemLp
  · intro N
    have hENorm : eLpNorm (U N) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (C₁ * M.delta * Real.sqrt (1 + (N : ℝ))) := by
      calc
        eLpNorm (U N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure =
            eLpNorm (U N ∘ π₀) (ENNReal.ofReal p) μ₀ := by
          symm
          exact eLpNorm_comp_measurePreserving
            (hUmeas N).aestronglyMeasurable hπ₀pres
        _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(N : ℤ))) *
              eLpNorm (G N) (ENNReal.ofReal p) μ₀ :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((hUmeas N).aestronglyMeasurable.comp_measurePreserving hπ₀pres) (hpoint N) _
        _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(N : ℤ))) *
              ENNReal.ofReal (B * Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1) *
                (2 * (3 : ℝ) ^ N)) :=
          mul_le_mul_of_nonneg_left (hGnorm N) (by positivity)
        _ = ENNReal.ofReal (2 *
              (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
              Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          have hpow : (3 : ℝ) ^ (-(N : ℤ)) * (2 * (3 : ℝ) ^ N) = 2 := by
            rw [zpow_neg, zpow_natCast]
            field_simp
          congr 1
          calc
            (3 : ℝ) ^ (-(N : ℤ)) *
                (B * Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1) *
                  (2 * (3 : ℝ) ^ N)) =
                (B * Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1)) *
                  ((3 : ℝ) ^ (-(N : ℤ)) * (2 * (3 : ℝ) ^ N)) := by ring
            _ = 2 *
                (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                  Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                  ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
                Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1) := by
              rw [hpow]
              dsimp [B]
              ring
        /-
        _ ≤ ENNReal.ofReal (C₁ * M.delta * Real.sqrt (1 + (N : ℝ))) := by
          apply ENNReal.ofReal_le_ofReal
          dsimp [C₁]
          let D0 : ℝ :=
            Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
              Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
              ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)
          have hD : 0 ≤ D0 := by
            dsimp [D0]
            exact mul_nonneg
              (mul_nonneg
                (mul_nonneg
                  (Homogenization.IndependentSums.gammaMomentConst_pos
                    (show (0 : ℝ) < 2 by norm_num)).le
                  (Real.sqrt_nonneg _))
                (Real.sqrt_nonneg _))
              (Real.rpow_nonneg (by
                have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
                linarith) _)
          have hq : 0 ≤ Real.sqrt (Q₀ + 1) := Real.sqrt_nonneg _
          have hδ : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
          have hsqrt : 0 ≤ Real.sqrt (1 + (N : ℝ)) := Real.sqrt_nonneg _
          have hprod : 0 ≤ D0 * Real.sqrt (Q₀ + 1) * M.delta :=
            mul_nonneg (mul_nonneg hD hq) hδ
          have hcoef : 2 * (D0 * M.delta * Real.sqrt (Q₀ + 1)) ≤
              (C₀ + 1 + 6 * D0 * Real.sqrt (Q₀ + 1)) * M.delta := by
            nlinarith [hC₀, hprod]
          have hcoef' : 2 * (
              (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
                Real.sqrt (Q₀ + 1)) ≤
              (C₀ + 1 + 6 *
                (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                  Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                  ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) *
                Real.sqrt (Q₀ + 1)) * M.delta := by
            simpa [D0, mul_assoc, mul_left_comm, mul_comm] using! hcoef
          have hsqrtQ : Real.sqrt (Q₀ + 1) = Real.sqrt ((Q₀ : ℝ) + 1) := by
            norm_num
          rw [hsqrtQ] at hcoef' ⊢
          calc
            2 * ((Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
                Real.sqrt ((Q₀ : ℝ) + 1)) *
                Real.sqrt (N + 1) ≤
                ((C₀ + 1 + 6 *
                  (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                    Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                    ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) *
                  Real.sqrt ((Q₀ : ℝ) + 1)) * M.delta) *
                  Real.sqrt (N + 1) :=
              mul_le_mul_of_nonneg_right hcoef' hsqrt
            _ = (C₀ + 1 + 6 *
                (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                  Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                  ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) *
                Real.sqrt ((Q₀ : ℝ) + 1)) * M.delta *
                Real.sqrt (1 + (N : ℝ)) := by ring
        -/
        _ ≤ ENNReal.ofReal (C₁ * M.delta * Real.sqrt (1 + (N : ℝ))) := by
          apply ENNReal.ofReal_le_ofReal
          have hδ : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
          have hs : 0 ≤ Real.sqrt (1 + (N : ℝ)) := Real.sqrt_nonneg _
          have hmul := mul_le_mul_of_nonneg_right hCdom
            (mul_nonneg hδ hs)
          calc
            _ = (2 * Dglobal * Real.sqrt (Q₀ + 1)) *
                (M.delta * Real.sqrt (1 + (N : ℝ))) := by
              dsimp [Dglobal]
              ring
            _ ≤ C₁ * (M.delta * Real.sqrt (1 + (N : ℝ))) := hmul
            _ = C₁ * M.delta * Real.sqrt (1 + (N : ℝ)) := by ring
    exact hENorm


end SubdiffusiveProcess.Paper
