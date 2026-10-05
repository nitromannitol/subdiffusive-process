module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.MultiplicativeChaos.WeightedIndep
public import SubdiffusiveProcess.Probability.FineLayerMoment
public import SubdiffusiveProcess.Probability.InfraredCharacterizationUniformExponentialMoment
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.in_common_scale_coupling
public import SubdiffusiveProcess.CoarseGrainingVocab.ShellSensitivity
public import SubdiffusiveProcess.Main.InfraredAdmissible

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter Metric ProbabilityTheory TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.Paper

lemma aux_reference_point_moments_layer_abs
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i : ℕ)
    (x : SpatialCoordinates d) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun f : C(SpatialCoordinates d, ℝ) => Real.exp (t * |f x|))
      (scaledLayerLaw d (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P |>.map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(_root_.SubdiffusiveProcess.Model.PotentialField d, C(SpatialCoordinates d, ℝ))))
        (-(i : ℤ))).toMeasure ∧
    (∫ f : C(SpatialCoordinates d, ℝ), Real.exp (t * |f x|)
      ∂(scaledLayerLaw d (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P |>.map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(_root_.SubdiffusiveProcess.Model.PotentialField d, C(SpatialCoordinates d, ℝ))))
        (-(i : ℤ))).toMeasure) ≤
      4 * Real.exp (t ^ 2 * (((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) ^ 2) / 2) := by
  let μ := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
      C(SpatialCoordinates d, ℝ)) := ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let ν := _root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P |>.map
    forget
  let sc := SubdiffusiveProcess.layerScaling d (-(i : ℤ))
  let E : C(SpatialCoordinates d, ℝ) → ℝ := fun f => |f x|
  let X : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ :=
    fun g => |g (((3 : ℝ) ^ i) • x)|
  let Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
    fun o => |o 0 (((3 : ℝ) ^ i) • x)|
  have hX : Measurable X :=
    (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval _).norm
  have hY : Measurable Y :=
    ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval _).comp
      (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate 0)).norm
  have hE : Measurable E := by
    have heval : Measurable (fun f : C(SpatialCoordinates d, ℝ) => f x) :=
      (continuous_eval_const x).measurable
    simpa [E, Real.norm_eq_abs] using
      heval.norm
  have hscaled : Measure.map E (scaledLayerLaw d ν (-(i : ℤ))).toMeasure =
      Measure.map X μ := by
    change Measure.map E (Measure.map sc (Measure.map forget μ)) = Measure.map X μ
    rw [Measure.map_map sc.continuous.measurable forget.continuous.measurable,
      Measure.map_map hE (sc.continuous.measurable.comp forget.continuous.measurable)]
    congr 1
    funext g
    simp [E, X, sc, SubdiffusiveProcess.layerScaling, forget,
      Function.comp_apply, zpow_natCast]
    rfl
  have hbase : Measure.map (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
      g (((3 : ℝ) ^ i) • x)) μ =
      Measure.map (fun o : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        o 0 (((3 : ℝ) ^ i) • x)) M.P.toMeasure := by
    change Measure.map (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
        g (((3 : ℝ) ^ i) • x))
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure = _
    rw [show (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure =
      Measure.map (fun o : _root_.SubdiffusiveProcess.Model.PotentialSample d => o 0)
        M.P.toMeasure by rfl]
    rw [Measure.map_map
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval _)
      (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate 0)]
    rfl
  have hmap : Measure.map X μ = Measure.map Y M.P.toMeasure := by
    calc
      Measure.map X μ = Measure.map (fun z : ℝ => |z|)
          (Measure.map (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
            g (((3 : ℝ) ^ i) • x)) μ) := by
              rw [Measure.map_map (by
                simpa [Real.norm_eq_abs] using
                  (measurable_id.norm : Measurable (fun z : ℝ => ‖z‖)))
                (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval _)]
              rfl
      _ = Measure.map (fun z : ℝ => |z|)
          (Measure.map (fun o : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
            o 0 (((3 : ℝ) ^ i) • x)) M.P.toMeasure) := by rw [hbase]
      _ = Measure.map Y M.P.toMeasure := by
            simpa [Y, Function.comp_def] using
              (Measure.map_map (by
                simpa [Real.norm_eq_abs] using
                  (measurable_id.norm : Measurable (fun z : ℝ => ‖z‖)))
                ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval _).comp
                  (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate 0)))
  have hzero : Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma 2) X
      (((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by
    have hnative := SubdiffusiveProcess.CoarseGrainingVocab.isBigO_gammaTwo_potentialCoordinate_apply
      M 0 (((3 : ℝ) ^ i) • x)
    have hwith : Homogenization.IndependentSums.IsBigOWith μ
        (Homogenization.IndependentSums.gammaSigma 2) X
        (((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) :=
      SubdiffusiveProcess.CoarseGrainingVocab.isBigOWith_of_map_eq hX
        (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval _ |>.comp
          (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate 0) |>.norm)
        hmap hnative
    simpa [Homogenization.IndependentSums.IsBigO, X, abs_abs] using hwith
  let phi : ℝ → ℝ := fun z => Real.exp (t * |z|)
  have hphi : Measurable phi := by fun_prop
  have hExp := SubdiffusiveProcess.CoarseGrainingVocab.integral_exp_abs_sub_const_le
    (mu := μ) (X := X)
    (A := ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) (b := 0)
    (by have hδ := M.shellPrefix.delta_pos; positivity) ht hX.aemeasurable hzero
  have hphiMapX : Integrable phi (Measure.map X μ) := by
    apply (integrable_map_measure hphi.aestronglyMeasurable hX.aemeasurable).2
    simpa [phi, X, Function.comp_def, abs_abs] using hExp.1
  have hphiMapE : Integrable phi
      (Measure.map E (scaledLayerLaw d ν (-(i : ℤ))).toMeasure) := by
    rw [hscaled]
    exact hphiMapX
  have hcomp : Integrable (phi ∘ E)
      (scaledLayerLaw d ν (-(i : ℤ))).toMeasure :=
    (integrable_map_measure hphi.aestronglyMeasurable hE.aemeasurable).mp hphiMapE
  constructor
  · simpa [phi, E, Function.comp_def] using hcomp
  · calc
      (∫ f : C(SpatialCoordinates d, ℝ), Real.exp (t * |(f x)|)
          ∂(scaledLayerLaw d ν (-(i : ℤ))).toMeasure) =
          ∫ z, phi z ∂Measure.map E
            (scaledLayerLaw d ν (-(i : ℤ))).toMeasure := by
              simpa [phi, E, Function.comp_def] using
                (integral_map hE.aemeasurable hphi.aestronglyMeasurable
                  (μ := (scaledLayerLaw d ν (-(i : ℤ))).toMeasure)).symm
      _ = ∫ z, phi z ∂Measure.map X μ := by rw [hscaled]
      _ = ∫ g, phi (X g) ∂μ := by
        exact integral_map hX.aemeasurable hphi.aestronglyMeasurable
      _ ≤ _ := by simpa [phi, X, abs_abs] using hExp.2

lemma aux_reference_point_moments_layer
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i : ℕ)
    (x : SpatialCoordinates d) (t : ℝ) :
    Integrable (fun f : C(SpatialCoordinates d, ℝ) => Real.exp (t * f x))
      (scaledLayerLaw d (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P |>.map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(_root_.SubdiffusiveProcess.Model.PotentialField d, C(SpatialCoordinates d, ℝ))))
        (-(i : ℤ))).toMeasure ∧
    (∫ f, Real.exp (t * f x)
      ∂(scaledLayerLaw d (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P |>.map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(_root_.SubdiffusiveProcess.Model.PotentialField d, C(SpatialCoordinates d, ℝ))))
        (-(i : ℤ))).toMeasure) ≤
      Real.exp ((3 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2) *
        (|t| + t^2) * M.delta^2) := by
  let μ := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
      C(SpatialCoordinates d, ℝ)) := ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let ν := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).map
    forget
  let L := (scaledLayerLaw d ν (-(i : ℤ))).toMeasure
  let point : SpatialCoordinates d := (3 : ℝ)^i • x
  let X : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g => g point
  let E : C(SpatialCoordinates d, ℝ) → ℝ := fun f => f x
  have hmap : Measure.map E L = Measure.map X μ := by
    change Measure.map E (Measure.map (SubdiffusiveProcess.layerScaling d (-(i : ℤ)))
      (Measure.map forget μ)) = Measure.map X μ
    rw [Measure.map_map (SubdiffusiveProcess.layerScaling d (-(i : ℤ))).continuous.measurable
      forget.continuous.measurable,
      Measure.map_map (continuous_eval_const x).measurable
        ((SubdiffusiveProcess.layerScaling d (-(i : ℤ))).continuous.measurable.comp
          forget.continuous.measurable)]
    congr 1
    funext g
    simp [X, point, SubdiffusiveProcess.layerScaling, forget,
      Function.comp_apply, zpow_natCast]
    rfl
  have hXm : Measurable X :=
    _root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval _
  have hEm : Measurable E := (continuous_eval_const x).measurable
  let c : ℝ := (1 + Real.log 2) ^ (2 : ℝ)⁻¹
  have hc0 : 0 ≤ c := by
    dsimp [c]
    have hh : 0 ≤ 1 + Real.log 2 := by
      have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
      linarith
    exact Real.rpow_nonneg hh _
  have hbase : Integrable (fun g => Real.exp (t * X g)) μ ∧
      (∫ g, Real.exp (t * X g) ∂μ) ≤
        Real.exp ((3 + c^2) * (|t| + t^2) * M.delta^2) := by
    rcases le_or_gt (|t| * M.delta) 1 with hsmall | hlarge
    · have h := SubdiffusiveProcess.fineLayer_exp_moment_le t M point hsmall
      constructor
      · simpa [X, point, μ] using h.1
      · apply le_trans h.2
        apply Real.exp_le_exp.mpr
        have hlog2 : Real.log 2 / 2 ≤ 1 := by
          have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
          linarith
        have hb : Real.log 2 / 2 * t^2 ≤ (3 + c^2) * (|t| + t^2) := by
          have ht2 : t^2 ≤ |t| + t^2 := by linarith [abs_nonneg t]
          have hc : 0 ≤ c^2 := sq_nonneg c
          nlinarith [mul_nonneg hc (by positivity : 0 ≤ |t| + t^2)]
        exact mul_le_mul_of_nonneg_right hb (sq_nonneg M.delta)
    · let absphi : ℝ → ℝ := fun z => Real.exp (|t| * |z|)
      have habs := aux_reference_point_moments_layer_abs M i x |t|
        (abs_nonneg t)
      have habsMeas : Measurable (fun z : ℝ => Real.exp (|t| * |z|)) := by
        fun_prop
      have hphi : Measurable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
          Real.exp (t * X g)) := (measurable_const.mul hXm).exp
      have hmajor : ∀ g, Real.exp (t * X g) ≤ absphi (X g) := by
        intro g
        apply Real.exp_le_exp.mpr
        calc
          t * X g ≤ |t * X g| := le_abs_self _
          _ = |t| * |X g| := abs_mul _ _
      have habsMapE : Integrable (fun z => Real.exp (|t| * |z|))
          (Measure.map E L) :=
        (integrable_map_measure habsMeas.aestronglyMeasurable hEm.aemeasurable).2
          (by simpa [absphi, E, Function.comp_def] using habs.1)
      have habsMapX : Integrable (fun z => Real.exp (|t| * |z|))
          (Measure.map X μ) := by simpa [hmap] using habsMapE
      have habsμ : Integrable (fun g => absphi (X g)) μ :=
        (integrable_map_measure habsMeas.aestronglyMeasurable hXm.aemeasurable).1
          (by simpa [absphi] using habsMapX)
      have htarget : Integrable (fun g => Real.exp (t * X g)) μ := by
        refine habsμ.mono' hphi.aestronglyMeasurable ?_
        filter_upwards [] with g
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact hmajor g
      constructor
      · exact htarget
      · calc
          ∫ g, Real.exp (t * X g) ∂μ ≤ ∫ g, absphi (X g) ∂μ :=
            integral_mono htarget habsμ hmajor
          _ ≤ 4 * Real.exp (|t|^2 * (c * M.delta)^2 / 2) := by
            calc
              ∫ g, absphi (X g) ∂μ =
                  ∫ z, Real.exp (|t| * |z|) ∂Measure.map X μ := by
                    exact (integral_map hXm.aemeasurable habsMeas.aestronglyMeasurable).symm
              _ = ∫ z, Real.exp (|t| * |z|) ∂Measure.map E L := by rw [hmap]
              _ = ∫ f, Real.exp (|t| * |f x|) ∂L := by
                    exact integral_map hEm.aemeasurable habsMeas.aestronglyMeasurable
              _ ≤ _ := by simpa [L, absphi, c] using habs.2
          _ ≤ Real.exp ((3 + c^2) * (|t| + t^2) * M.delta^2) := by
            rw [show (4 : ℝ) * Real.exp (|t|^2 * (c * M.delta)^2 / 2) =
              Real.exp (Real.log 4 + |t|^2 * (c * M.delta)^2 / 2) by
                rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]]
            apply Real.exp_le_exp.mpr
            have hlog4 : Real.log 4 ≤ 3 := by
              have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
              linarith
            have hlarge2 : 1 < t^2 * M.delta^2 := by
              rw [← sq_abs t]
              nlinarith [hlarge]
            have hlogpart : Real.log 4 ≤ 3 * t^2 * M.delta^2 := by
              have htd : 1 ≤ t^2 * M.delta^2 := hlarge2.le
              nlinarith
            have hquad : |t|^2 * (c * M.delta)^2 / 2 ≤
                c^2 * t^2 * M.delta^2 := by
              rw [sq_abs]
              nlinarith [sq_nonneg (c * M.delta)]
            have hsum : t^2 ≤ |t| + t^2 := by linarith [abs_nonneg t]
            have hc : 0 ≤ c^2 := sq_nonneg c
            have hδ : 0 ≤ M.delta^2 := sq_nonneg M.delta
            have h1 : 3 * t^2 * M.delta^2 ≤
                3 * (|t| + t^2) * M.delta^2 := by gcongr
            have h2 : c^2 * t^2 * M.delta^2 ≤
                c^2 * (|t| + t^2) * M.delta^2 := by gcongr
            nlinarith
  have hphiX : Measurable (fun z : ℝ => Real.exp (t * z)) := by fun_prop
  have hMapX : Integrable (fun z : ℝ => Real.exp (t * z)) (Measure.map X μ) :=
    (integrable_map_measure hphiX.aestronglyMeasurable hXm.aemeasurable).2 hbase.1
  have hMapE : Integrable (fun z : ℝ => Real.exp (t * z)) (Measure.map E L) := by
    simpa [hmap] using hMapX
  have hL : Integrable (fun f : C(SpatialCoordinates d, ℝ) => Real.exp (t * E f)) L :=
    (integrable_map_measure hphiX.aestronglyMeasurable hEm.aemeasurable).1 hMapE
  constructor
  · simpa [L, E] using hL
  · calc
      ∫ f : C(SpatialCoordinates d, ℝ), Real.exp (t * E f) ∂L =
          ∫ z, Real.exp (t * z) ∂Measure.map E L := by
            exact (integral_map hEm.aemeasurable hphiX.aestronglyMeasurable).symm
      _ = ∫ z, Real.exp (t * z) ∂Measure.map X μ := by rw [hmap]
      _ = ∫ g, Real.exp (t * X g) ∂μ := by
            exact integral_map hXm.aemeasurable hphiX.aestronglyMeasurable
      _ ≤ _ := hbase.2

lemma aux_reference_point_moments_sum
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ)
    (x : SpatialCoordinates d) (ε : ℝ) :
    Integrable (fun omega : BilateralField d =>
      Real.exp (ε * (∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x -
        (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)))
      (chaosSampleLaw M).toMeasure ∧
    (∫ omega : BilateralField d, Real.exp (ε *
      (∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x -
        (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))
      ∂(chaosSampleLaw M).toMeasure) ≤
      Real.exp ((4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2) *
        (|ε| + ε^2) * M.delta^2 * (k : ℝ)) := by
  let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
      C(SpatialCoordinates d, ℝ)) := ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let ν := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).map
    forget
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j).toMeasure
  let P : Measure (BilateralField d) := Measure.infinitePi laws
  let S : Finset ℕ := Finset.range k
  have hS : iIndepFun
      (fun i : S => fun omega : BilateralField d => omega (-(i : ℤ))) P := by
    have hfull : iIndepFun
        (fun j : ℤ => fun omega : BilateralField d => omega j) P := by
      dsimp only [P]
      exact iIndepFun_infinitePi (fun _ => measurable_id)
    apply hfull.precomp
    intro i₁ i₂ hi
    apply Subtype.ext
    exact_mod_cast (neg_injective hi)
  let F : S → C(SpatialCoordinates d, ℝ) → ℝ := fun i f =>
    Real.exp (ε * f x)
  have hFmeas (i : S) : Measurable (F i) := by
    dsimp [F]
    apply Measurable.exp
    exact measurable_const.mul (continuous_eval_const x).measurable
  have hfactor :
      (∫ omega, ∏ i : S, F i (omega (-(i : ℤ))) ∂P) =
        ∏ i : S, ∫ omega, F i (omega (-(i : ℤ))) ∂P := by
    refine hS.integral_fun_prod_comp ?_ (fun i => ?_)
    · intro i
      exact (measurable_pi_apply (-(i : ℤ))).aemeasurable
    · exact (hFmeas i).aestronglyMeasurable
  let C0 : ℝ := 3 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2
  let B : ℝ := Real.exp (C0 * (|ε| + ε^2) * M.delta^2)
  have hcoord (i : S) :
      Integrable (fun omega : BilateralField d => F i (omega (-(i : ℤ)))) P ∧
      (∫ omega, F i (omega (-(i : ℤ))) ∂P) ≤ B := by
    let law := (scaledLayerLaw d ν (-(i : ℤ))).toMeasure
    have hh := aux_reference_point_moments_layer M (i : ℕ) x ε
    have htarget : Measurable (fun f : C(SpatialCoordinates d, ℝ) => F i f) := hFmeas i
    have heval := measurePreserving_eval_infinitePi laws (-(i : ℤ))
    have hsource :
        Integrable (fun omega : BilateralField d => F i (omega (-(i : ℤ)))) P := by
      have h := (heval.integrable_comp htarget.aestronglyMeasurable).mpr
        (by simpa [F, law] using hh.1)
      exact h
    constructor
    · exact hsource
    · calc
        (∫ omega, F i (omega (-(i : ℤ))) ∂P) =
            ∫ f, F i f ∂Measure.map (fun omega : BilateralField d =>
              omega (-(i : ℤ))) P := by
                rw [integral_map heval.measurable.aemeasurable
                  (hFmeas i).aestronglyMeasurable]
        _ = ∫ f, F i f ∂law := by rw [heval.map_eq]
        _ ≤ B := by simpa [F, law, B, C0] using hh.2
  have hSc : iIndepFun
      (fun i : S => fun omega : BilateralField d =>
        (omega (-(i : ℤ))) x) P := by
    exact hS.comp (fun _ f => f x) (fun _ => (continuous_eval_const x).measurable)
  have huncenteredInt : Integrable
      (fun omega : BilateralField d =>
        Real.exp (ε * ∑ i : S, (omega (-(i : ℤ))) x)) P := by
    have h := hSc.integrable_exp_mul_sum (t := ε) (s := Finset.univ)
      (fun i => by
        have hevalx : Measurable (fun f : C(SpatialCoordinates d, ℝ) => f x) :=
          (continuous_eval_const x).measurable
        simpa using! hevalx.comp (measurable_pi_apply (-(i : ℤ))))
      (by
        intro i hi
        simpa [F, Function.comp_def] using (hcoord i).1)
    simpa [Finset.sum_coe_sort] using h
  have hprodBound :
      (∏ i : S, ∫ omega, F i (omega (-(i : ℤ))) ∂P) ≤ B ^ k := by
    calc
      (∏ i : S, ∫ omega, F i (omega (-(i : ℤ))) ∂P) ≤
          ∏ _i : S, B := by
            gcongr with i
            exact (hcoord i).2
      _ = B ^ k := by simp [S]
  have huncenteredBound :
      (∫ omega : BilateralField d,
        Real.exp (ε * ∑ i : S, (omega (-(i : ℤ))) x) ∂P) ≤ B ^ k := by
    calc
      (∫ omega : BilateralField d,
        Real.exp (ε * ∑ i : S, (omega (-(i : ℤ))) x) ∂P) =
          ∫ omega, ∏ i : S, F i (omega (-(i : ℤ))) ∂P := by
            apply integral_congr_ae
            filter_upwards [] with omega
            rw [← Real.exp_sum]
            congr 1
            simp [Finset.mul_sum]
      _ = ∏ i : S, ∫ omega, F i (omega (-(i : ℤ))) ∂P := hfactor
      _ ≤ B ^ k := hprodBound
  have hcenteredInt : Integrable
      (fun omega : BilateralField d =>
        Real.exp (ε * (∑ i : S, (omega (-(i : ℤ))) x -
          (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))) P := by
    have hc := huncenteredInt.const_mul
      (Real.exp (-ε * (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))
    convert hc using 1
    funext omega
    rw [← Real.exp_add]
    congr 1
    ring
  have hcenteredBound :
      (∫ omega : BilateralField d,
        Real.exp (ε * (∑ i : S, (omega (-(i : ℤ))) x -
          (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) ∂P) ≤
        Real.exp (|ε| * (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) * B ^ k := by
    have hc := huncenteredBound
    calc
      (∫ omega : BilateralField d,
        Real.exp (ε * (∑ i : S, (omega (-(i : ℤ))) x -
          (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) ∂P) =
          Real.exp (-ε * (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            (∫ omega : BilateralField d,
              Real.exp (ε * ∑ i : S, (omega (-(i : ℤ))) x) ∂P) := by
                rw [show (fun omega : BilateralField d =>
                  Real.exp (ε * (∑ i : S, (omega (-(i : ℤ))) x -
                    (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))) =
                  (fun omega => Real.exp (-ε * (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                    Real.exp (ε * ∑ i : S, (omega (-(i : ℤ))) x)) by
                      funext omega
                      rw [← Real.exp_add]
                      congr 1
                      ring]
                rw [integral_const_mul]
      _ ≤ Real.exp (-ε * (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) * B ^ k :=
        mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
      _ ≤ Real.exp (|ε| * (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) * B ^ k := by
        have htau : 0 ≤ _root_.SubdiffusiveProcess.Model.tauSq M.P := M.G4.tauSq_pos.le
        have hexp : Real.exp (-ε * (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) ≤
            Real.exp (|ε| * (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
          apply Real.exp_le_exp.mpr
          have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
          have hke : -ε * (k : ℝ) ≤ |ε| * (k : ℝ) :=
            mul_le_mul_of_nonneg_right (neg_le_abs ε) hk
          calc
            -ε * (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P =
                (-ε * (k : ℝ)) * _root_.SubdiffusiveProcess.Model.tauSq M.P := by ring
            _ ≤ (|ε| * (k : ℝ)) * _root_.SubdiffusiveProcess.Model.tauSq M.P :=
              mul_le_mul_of_nonneg_right hke htau
            _ = |ε| * (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P := by ring
        exact mul_le_mul_of_nonneg_right hexp (pow_nonneg (Real.exp_pos _).le _)
  have hfinalBound :
      (∫ omega : BilateralField d,
        Real.exp (ε * (∑ i : S, (omega (-(i : ℤ))) x -
          (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) ∂P) ≤
        Real.exp ((4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2) *
          (|ε| + ε^2) * M.delta^2 * (k : ℝ)) := by
    calc
      _ ≤ Real.exp (|ε| * (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) * B ^ k := hcenteredBound
      _ = Real.exp (|ε| * (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
          C0 * (|ε| + ε^2) * M.delta^2 * (k : ℝ)) := by
            rw [show B = Real.exp (C0 * (|ε| + ε^2) * M.delta^2) by rfl,
              ← Real.exp_nat_mul, ← Real.exp_add]
            congr 1
            ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have htau : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ M.delta^2 := by
          have hh := SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M
          have hlog : Real.log 2 / 2 ≤ 1 := by
            have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
            linarith
          nlinarith
        have habs : |ε| ≤ |ε| + ε^2 := by linarith [sq_nonneg ε]
        have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
        have hd2 : 0 ≤ M.delta^2 := sq_nonneg _
        dsimp [C0]
        have h1 : |ε| * (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P ≤
            |ε| * (k : ℝ) * M.delta^2 := by gcongr
        have h2 : (3 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2) *
              (|ε| + ε^2) * M.delta^2 * (k : ℝ) +
              |ε| * (k : ℝ) * M.delta^2 ≤
            (4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2) *
              (|ε| + ε^2) * M.delta^2 * (k : ℝ) := by
          have hc : 0 ≤ ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2 := sq_nonneg _
          have hprod := mul_le_mul_of_nonneg_right habs (mul_nonneg hd2 hk)
          nlinarith [hprod]
        nlinarith
  have hsumEq (omega : BilateralField d) :
      (∑ i : S, (omega (-(i : ℤ))) x) =
        ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x := by
    simpa [S] using (Finset.sum_coe_sort (Finset.range k)
      (fun j => (omega (-(j : ℤ))) x))
  have hP : (chaosSampleLaw M).toMeasure = P := by
    change Measure.infinitePi (fun j : ℤ =>
      (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure) = P
    simp [P, ν, laws, chaosRootFieldLaw]
    rfl
  constructor
  · rw [hP]
    refine hcenteredInt.congr ?_
    filter_upwards [] with omega
    rw [hsumEq]
  · rw [hP]
    calc
      (∫ omega : BilateralField d,
        Real.exp (ε * (∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x -
          (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) ∂P) =
          ∫ omega : BilateralField d,
            Real.exp (ε * (∑ i : S, (omega (-(i : ℤ))) x -
              (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) ∂P := by
                apply integral_congr_ae
                filter_upwards [] with omega
                rw [hsumEq]
      _ ≤ _ := hfinalBound

lemma aux_reference_point_moments_amgm
    (r u v a : ℝ) (hr : 0 < r) :
    (r * Real.exp (u + v)) ^ a ≤
      (r ^ a / 2) * (Real.exp (2 * a * u) + Real.exp (2 * a * v)) := by
  have hsq : 0 ≤ (Real.exp (a * u) - Real.exp (a * v))^2 := sq_nonneg _
  have h1 : Real.exp (2 * a * u) =
      Real.exp (a * u) * Real.exp (a * u) := by
    rw [show 2 * a * u = (a * u) + (a * u) by ring, Real.exp_add]
  have h2 : Real.exp (2 * a * v) =
      Real.exp (a * v) * Real.exp (a * v) := by
    rw [show 2 * a * v = (a * v) + (a * v) by ring, Real.exp_add]
  have hcross : Real.exp (a * (u + v)) =
      Real.exp (a * u) * Real.exp (a * v) := by
    rw [show a * (u + v) = a * u + a * v by ring, Real.exp_add]
  have hpow : (r * Real.exp (u + v)) ^ a =
      r ^ a * Real.exp (a * (u + v)) := by
    rw [Real.mul_rpow hr.le (Real.exp_pos _).le]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    ring_nf
  rw [hpow, h1, h2, hcross]
  have hrpow : 0 ≤ r ^ a := Real.rpow_nonneg hr.le _
  have hmul := mul_nonneg hrpow hsq
  nlinarith

lemma aux_reference_point_moments_half_two (x y : ℝ) :
    (x / 2) * (2 * y) = x * y := by
  ring

lemma aux_reference_point_moments_half_mul (x y : ℝ) :
    (x / 2) * y = (1 / 2 : ℝ) * (x * y) := by
  ring

lemma aux_reference_point_moments_budget_ring (A a z w : ℝ) :
    A * (4 * (a + a^2) * (z^2 * w)) =
      4 * A * ((a + a^2) * z^2 * w) := by
  ring

lemma aux_reference_point_moments_assoc (A x z w : ℝ) :
    A * x * z * w = A * (x * (z * w)) := by
  ring

lemma aux_reference_point_moments_quadratic (a : ℝ) (ha : 0 ≤ a) :
    2 * a + (2 * a)^2 ≤ 4 * (a + a^2) := by
  nlinarith [sq_nonneg a]

lemma aux_reference_point_moments_half_le_one (x : ℝ) (hx : x ≤ 1) :
    x / 2 ≤ 1 := by
  linarith

lemma aux_reference_point_moments_combine_two
    (I c x y z : ℝ) (hraw : I ≤ c * (2 * x + y))
    (h1 : c * (2 * x) ≤ z) (h2 : c * y ≤ z) : I ≤ 2 * z := by
  calc
    I ≤ c * (2 * x + y) := hraw
    _ = c * (2 * x) + c * y := by ring
    _ ≤ z + z := add_le_add h1 h2
    _ = 2 * z := by ring

lemma aux_reference_point_moments_two_le_four (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) : 2 * (x * y) ≤ 4 * x * y := by
  nlinarith

/-- Fine proof step.

Doc tick list.
- `in_responses` supplies the normalized original reference convention and
  deterministic coefficient-ratio input used by the point-reference estimate.
- `in_common_scale_coupling` supplies one realization of the layers at all
  cutoff depths; `lem_infrared` supplies the anchored infrared field.
- The estimate is uniform in the cutoff `N`, own depth `k ≤ N`, and point
  `y` in the fixed root cube, with all exponents in the parent interval
  `[1, 2q]`.
- The real and inverse moment bounds and their `MemLp` consequences are
  concluded here; they are not hypotheses of `reference_mesh_statistic`.
- The proof below supplies the point-reference moment estimate.
-/
theorem reference_point_moments
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ Cmom Crate : ℝ,
      0 < Cmom ∧ 0 < Crate ∧
      ∀ delta0 : ℝ, 0 < delta0 → delta0 ≤ 1 →
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M H → M.delta ≤ delta0 →
        let P := (chaosSampleLaw M).toMeasure
        let K : Set (SpatialCoordinates d) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
        let s : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun N k omega x =>
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
                SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
              Real.exp (G k omega x - (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
        ∀ aexp : ℝ, aexp ∈ Set.Icc 1 (2 * q) →
          ∀ (N k : ℕ), k ≤ N → ∀ y ∈ K,
            Integrable (fun omega => (s N k omega y)^aexp +
              (s N k omega y)^(-aexp)) P ∧
            (∫ omega, (s N k omega y)^aexp +
              (s N k omega y)^(-aexp) ∂P) ≤
              Cmom * Real.exp (Crate * (aexp + aexp^2) * M.delta^2 * (k : ℝ)) ∧
            MemLp (fun omega => s N k omega y) (ENNReal.ofReal aexp) P ∧
              MemLp (fun omega => (s N k omega y)⁻¹)
              (ENNReal.ofReal aexp) P := by
  obtain ⟨CH, hCH, hHmom⟩ :=
    SubdiffusiveProcess.exists_uniform_compactExponentialMoment_of_admissible hd
  let Kc : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall (0 : SpatialCoordinates d) 1,
      ProperSpace.isCompact_closedBall (0 : SpatialCoordinates d) 1⟩
  let c0 : ℝ := 3 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2
  let Cmom : ℝ := 4 * Real.exp (16 * CH Kc * q^2)
  let Crate : ℝ := 4 * (4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2) + 2
  refine ⟨Cmom, Crate, ?_, ?_, ?_⟩
  · dsimp [Cmom]
    positivity
  · dsimp [Crate]
    have hbase : 0 ≤ ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2 := sq_nonneg _
    linarith
  · intro delta0 hdelta0pos hdelta0le M Rm H hH hMd
    dsimp
    intro a ha N k hkn y hy
    have ha1 : 0 < a := lt_of_lt_of_le zero_lt_one ha.1
    have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
    have haUpper : a ≤ 2 * q := ha.2
    have hyK : y ∈ (Kc : Set (SpatialCoordinates d)) := by
      change y ∈ Metric.closedBall (0 : SpatialCoordinates d) 1
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [pi_norm_le_iff_of_nonneg (by norm_num)]
      intro i
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [(hy i).1], (hy i).2⟩
    have hHexp (t : ℝ) :
        Integrable (fun omega => Real.exp (t * H omega y))
          (chaosSampleLaw M).toMeasure ∧
        (∫ omega, Real.exp (t * H omega y)
          ∂(chaosSampleLaw M).toMeasure) ≤
          2 * Real.exp (CH Kc * t^2 * M.delta^2) := by
      have hnorm := hHmom M H hH Kc |t| (abs_nonneg t)
      have htarget : Measurable (fun omega => Real.exp (t * H omega y)) := by
        exact (measurable_const.mul
          ((continuous_eval_const y).measurable.comp hH.measurable)).exp
      have hdom : ∀ omega, t * H omega y ≤
          |t| * ‖(H omega).restrict (Kc : Set (SpatialCoordinates d))‖ := by
        intro omega
        have hb := ((H omega).restrict (Kc : Set (SpatialCoordinates d))).norm_coe_le_norm
          ⟨y, hyK⟩
        calc
          t * H omega y ≤ |t * H omega y| := le_abs_self _
          _ = |t| * |H omega y| := abs_mul _ _
          _ ≤ |t| * ‖(H omega).restrict (Kc : Set (SpatialCoordinates d))‖ := by
            rw [← Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left hb (abs_nonneg t)
      have hint : Integrable (fun omega => Real.exp (t * H omega y))
          (chaosSampleLaw M).toMeasure := by
        refine hnorm.1.mono' htarget.aestronglyMeasurable ?_
        filter_upwards [] with omega
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_exp.mpr (hdom omega)
      constructor
      · exact hint
      · calc
          (∫ omega, Real.exp (t * H omega y)
            ∂(chaosSampleLaw M).toMeasure) ≤
              ∫ omega, Real.exp (|t| * ‖(H omega).restrict
                (Kc : Set (SpatialCoordinates d))‖)
                ∂(chaosSampleLaw M).toMeasure :=
            integral_mono hint hnorm.1 (fun omega =>
              Real.exp_le_exp.mpr (hdom omega))
          _ ≤ 2 * Real.exp (CH Kc * |t|^2 * M.delta^2) := hnorm.2
          _ = 2 * Real.exp (CH Kc * t^2 * M.delta^2) := by
            rw [sq_abs]
    let r : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
    have hahompos (m : ℕ) :
        0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M m := by
      exact lt_of_lt_of_le (Real.exp_pos _) (Rm.ahom_lower m)
    have hrpos : 0 < r := by
      dsimp [r]
      exact div_pos (hahompos _) (hahompos _)
    have hratio : r ≤ Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P *
        (k : ℝ)) := by
      by_cases hk0 : k = 0
      · subst k
        dsimp [r]
        rw [div_self (ne_of_gt (hahompos N))]
        simp
      · have hsub : N - k < N := by omega
        have hord := Rm.ahom_ordering (N - k) N hsub
        apply (div_le_iff₀ (hahompos N)).2
        calc
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) ≤
              Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P *
                ((N : ℝ) - (N - k : ℕ))) *
                SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := hord.2
          _ = Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ)) *
                SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := by
            congr 2
            rw [Nat.cast_sub hkn]
            ring
    have hratioInv : r⁻¹ ≤ 1 := by
      by_cases hk0 : k = 0
      · subst k
        dsimp [r]
        rw [div_self (ne_of_gt (hahompos N))]
        simp
      · apply inv_le_one_of_one_le₀
        apply (le_div_iff₀ (hahompos N)).2
        simpa using (Rm.ahom_ordering (N - k) N (by omega)).1
    have hsumPos := aux_reference_point_moments_sum M k y (2 * a)
    have hsumNeg := aux_reference_point_moments_sum M k y (-2 * a)
    have hHPos := hHexp (2 * a)
    have hHNeg := hHexp (-2 * a)
    let center : BilateralField d → ℝ := fun omega =>
      (∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y) -
        (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P
    have hsrepr (omega : BilateralField d) :
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Real.exp (H omega y +
            ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y -
            (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) =
        r * Real.exp (H omega y + center omega) := by
      dsimp [r, center]
      rw [show H omega y +
          ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y -
          (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P =
          H omega y +
            (∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y -
            (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) by ring]
    let A : ℝ := 4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2
    have hsumPosA :
        (∫ omega, Real.exp (2 * a * center omega)
            ∂(chaosSampleLaw M).toMeasure) ≤
          Real.exp (A * (|2 * a| + (2 * a)^2) * M.delta^2 * (k : ℝ)) := by
      simpa only [A] using hsumPos.2
    have hsumNegA :
        (∫ omega, Real.exp (-2 * a * center omega)
            ∂(chaosSampleLaw M).toMeasure) ≤
          Real.exp (A * (|-2 * a| + (-2 * a)^2) * M.delta^2 * (k : ℝ)) := by
      simpa only [A] using hsumNeg.2
    have hpointPos (omega : BilateralField d) :
        (r * Real.exp (H omega y + center omega))^a ≤
          (r^a / 2) * (Real.exp (2 * a * H omega y) +
            Real.exp (2 * a * center omega)) := by
      exact aux_reference_point_moments_amgm r (H omega y)
        (center omega) a hrpos
    have hHpointMeas : Measurable (fun omega : BilateralField d => H omega y) :=
      (continuous_eval_const y).measurable.comp hH.measurable
    have hsumMeas : Measurable (fun omega : BilateralField d =>
        ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y) := by
      apply Finset.measurable_sum
      intro j hj
      exact (continuous_eval_const y).measurable.comp
        (measurable_pi_apply (-(j : ℤ)))
    let F : BilateralField d → ℝ := fun omega =>
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
        Real.exp (H omega y +
          ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y -
          (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
    have hFmeas : Measurable F := by
      dsimp [F]
      have hratioMeas : Measurable (fun _ : BilateralField d =>
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) := measurable_const
      exact hratioMeas.mul
        (((hHpointMeas.add hsumMeas).sub measurable_const).exp)
    have hFpos (omega : BilateralField d) : 0 < F omega := by
      dsimp [F]
      exact mul_pos (div_pos (hahompos _) (hahompos _)) (Real.exp_pos _)
    have hplusMeas : Measurable (fun omega : BilateralField d =>
        (F omega)^a) := by
      dsimp [F]
      fun_prop
    have hplusDom : Integrable (fun omega : BilateralField d =>
        (r^a / 2) * (Real.exp (2 * a * H omega y) +
          Real.exp (2 * a * center omega)))
        (chaosSampleLaw M).toMeasure := by
      have hA := hHPos.1.add hsumPos.1
      exact hA.const_mul (r^a / 2)
    have hplusInt : Integrable (fun omega : BilateralField d => (F omega)^a)
        (chaosSampleLaw M).toMeasure := by
      refine hplusDom.mono' hplusMeas.aestronglyMeasurable ?_
      filter_upwards [] with omega
      dsimp [F]
      rw [hsrepr omega]
      rw [abs_of_nonneg
        (Real.rpow_nonneg (mul_nonneg hrpos.le (Real.exp_pos _).le) _)]
      exact hpointPos omega
    have hinvrepr (omega : BilateralField d) :
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Real.exp (H omega y +
            ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y -
            (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))^(-a) =
          (r⁻¹ * Real.exp (-(H omega y) - center omega))^a := by
      rw [hsrepr omega]
      rw [Real.rpow_neg (mul_nonneg hrpos.le (Real.exp_pos _).le)]
      rw [← Real.inv_rpow (mul_nonneg hrpos.le (Real.exp_pos _).le)]
      congr 1
      rw [mul_inv_rev, ← Real.exp_neg]
      ring
    have hpointNeg (omega : BilateralField d) :
        (r⁻¹ * Real.exp (-(H omega y) - center omega))^a ≤
          ((r⁻¹)^a / 2) * (Real.exp (-2 * a * H omega y) +
            Real.exp (-2 * a * center omega)) := by
      convert aux_reference_point_moments_amgm (r⁻¹) (-(H omega y))
        (-center omega) a (inv_pos.mpr hrpos) using 1 ; ring
    have hminusMeas : Measurable (fun omega : BilateralField d =>
        (F omega)^(-a)) := by
      dsimp [F]
      fun_prop
    have hminusDom : Integrable (fun omega : BilateralField d =>
        ((r⁻¹)^a / 2) * (Real.exp (-2 * a * H omega y) +
          Real.exp (-2 * a * center omega)))
        (chaosSampleLaw M).toMeasure := by
      have hA := hHNeg.1.add hsumNeg.1
      exact hA.const_mul ((r⁻¹)^a / 2)
    have hminusInt : Integrable (fun omega : BilateralField d => (F omega)^(-a))
        (chaosSampleLaw M).toMeasure := by
      refine hminusDom.mono' hminusMeas.aestronglyMeasurable ?_
      filter_upwards [] with omega
      dsimp [F]
      rw [hinvrepr omega]
      rw [abs_of_nonneg
        (Real.rpow_nonneg (mul_nonneg (inv_pos.mpr hrpos).le
          (Real.exp_pos _).le) _)]
      exact hpointNeg omega
    have hplusIntegral :
        (∫ omega, (F omega)^a
          ∂(chaosSampleLaw M).toMeasure) ≤
          (r^a / 2) *
            ((∫ omega, Real.exp (2 * a * H omega y)
                ∂(chaosSampleLaw M).toMeasure) +
              (∫ omega, Real.exp (2 * a * center omega)
                ∂(chaosSampleLaw M).toMeasure)) := by
      calc
        _ ≤ ∫ omega, (r^a / 2) *
            (Real.exp (2 * a * H omega y) +
              Real.exp (2 * a * center omega))
            ∂(chaosSampleLaw M).toMeasure := by
              apply integral_mono hplusInt hplusDom
              intro omega
              change (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
                SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
                  Real.exp (H omega y +
                    ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y -
                    (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))^a ≤ _
              rw [hsrepr omega]
              simpa using hpointPos omega
        _ = _ := by
          rw [integral_const_mul, integral_add hHPos.1 hsumPos.1]
    have hminusIntegral :
        (∫ omega, (F omega)^(-a)
          ∂(chaosSampleLaw M).toMeasure) ≤
          ((r⁻¹)^a / 2) *
            ((∫ omega, Real.exp (-2 * a * H omega y)
                ∂(chaosSampleLaw M).toMeasure) +
              (∫ omega, Real.exp (-2 * a * center omega)
                ∂(chaosSampleLaw M).toMeasure)) := by
      calc
        _ ≤ ∫ omega, ((r⁻¹)^a / 2) *
            (Real.exp (-2 * a * H omega y) +
              Real.exp (-2 * a * center omega))
            ∂(chaosSampleLaw M).toMeasure := by
              apply integral_mono hminusInt hminusDom
              intro omega
              change (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
                SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
                  Real.exp (H omega y +
                    ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y -
                    (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))^(-a) ≤ _
              rw [hinvrepr omega]
              simpa using hpointNeg omega
        _ = _ := by
          rw [integral_const_mul, integral_add hHNeg.1 hsumNeg.1]
    let T : ℝ := (a + a^2) * M.delta^2 * (k : ℝ)
    let E0 : ℝ := 16 * CH Kc * q^2
    have hTdef : T = (a + a^2) * M.delta^2 * (k : ℝ) := rfl
    have hA : 0 ≤ A := by
      dsimp [A]
      positivity
    have hδ : 0 ≤ M.delta := by
      exact M.shellPrefix.delta_pos.le
    have hδle : M.delta ≤ 1 := le_trans hMd hdelta0le
    have hδ2le : M.delta^2 ≤ 1 := by
      nlinarith [sq_nonneg M.delta, sq_nonneg (1 - M.delta)]
    have hT : 0 ≤ T := by
      dsimp [T]
      positivity
    have hE0 : 0 ≤ E0 := by
      dsimp [E0]
      exact mul_nonneg (mul_nonneg (by norm_num) (hCH Kc)) (sq_nonneg q)
    have htau : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ M.delta^2 := by
      have hh := SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M
      have hlog : Real.log 2 / 2 ≤ 1 := by
        have hlog' := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        linarith
      have hprod := mul_le_mul_of_nonneg_right hlog (sq_nonneg M.delta)
      simpa using le_trans hh hprod
    have hsumAbsPos : |2 * a| = 2 * a := by
      rw [abs_of_nonneg]
      linarith
    have hsumAbsNeg : |-2 * a| = 2 * a := by
      rw [abs_of_nonpos]
      · ring
      · linarith
    have hsumSq : (-2 * a)^2 = (2 * a)^2 := by ring
    have hsumBudgetPosNorm :
      A * (2 * a + (2 * a)^2) * M.delta^2 * (k : ℝ) ≤ 4 * A * T := by
      have hlin : 2 * a + (2 * a)^2 ≤ 4 * (a + a^2) :=
        aux_reference_point_moments_quadratic a ha1.le
      have hfac : 0 ≤ M.delta^2 * (k : ℝ) :=
        mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
      have hmul :
          (2 * a + (2 * a)^2) * (M.delta^2 * (k : ℝ)) ≤
            4 * (a + a^2) * (M.delta^2 * (k : ℝ)) :=
        mul_le_mul_of_nonneg_right hlin hfac
      calc
        A * (2 * a + (2 * a)^2) * M.delta^2 * (k : ℝ) =
            A * ((2 * a + (2 * a)^2) * (M.delta^2 * (k : ℝ))) :=
              by simp only [mul_assoc]
        _ ≤ A * (4 * (a + a^2) * (M.delta^2 * (k : ℝ))) :=
          mul_le_mul_of_nonneg_left hmul hA
        _ = 4 * A * T := by
          rw [hTdef]
          simp only [mul_assoc, mul_left_comm, mul_comm]
    have hsumBudgetPos :
        A * (|2 * a| + (2 * a)^2) * M.delta^2 * (k : ℝ) ≤ 4 * A * T := by
      rw [hsumAbsPos]
      exact hsumBudgetPosNorm
    have hsumBudgetNeg :
        A * (|-2 * a| + (-2 * a)^2) * M.delta^2 * (k : ℝ) ≤ 4 * A * T := by
      rw [hsumAbsNeg, hsumSq]
      exact hsumBudgetPosNorm
    have hHbudgetPos : CH Kc * (2 * a)^2 * M.delta^2 ≤ E0 := by
      have hCH0 : 0 ≤ CH Kc := hCH Kc
      have haSq : (2 * a)^2 ≤ (4 * q)^2 := by
        apply (sq_le_sq₀ (by positivity) (by positivity)).2
        linarith
      dsimp [E0]
      calc
        CH Kc * (2 * a)^2 * M.delta^2 ≤ CH Kc * (2 * a)^2 * 1 :=
          mul_le_mul_of_nonneg_left hδ2le
            (mul_nonneg hCH0 (sq_nonneg _))
        _ ≤ CH Kc * (4 * q)^2 * 1 := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left haSq hCH0
        _ = 16 * CH Kc * q^2 := by ring
    have hHbudgetNeg : CH Kc * (-2 * a)^2 * M.delta^2 ≤ E0 := by
      rw [hsumSq]
      exact hHbudgetPos
    have hdetBudget : 2 * a * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ) ≤ 2 * T := by
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
      have h2a : 0 ≤ 2 * a := by positivity
      have h1 : 2 * a * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ) ≤
          2 * a * M.delta^2 * (k : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htau h2a) hk
      dsimp [T]
      have hlin : 2 * a ≤ 2 * (a + a^2) := by
        linarith [sq_nonneg a]
      have h2 := mul_le_mul_of_nonneg_right hlin
        (mul_nonneg (sq_nonneg M.delta) hk)
      calc
        2 * a * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ) ≤
            2 * a * M.delta^2 * (k : ℝ) := h1
        _ ≤ 2 * ((a + a^2) * M.delta^2 * (k : ℝ)) := by
          calc
            2 * a * M.delta^2 * (k : ℝ) =
                2 * a * (M.delta^2 * (k : ℝ)) := by ring
            _ ≤ 2 * (a + a^2) * (M.delta^2 * (k : ℝ)) := h2
            _ = 2 * ((a + a^2) * M.delta^2 * (k : ℝ)) := by ring
    have hrrpow : r^a ≤ Real.exp (2 * T) := by
      have hpow := Real.rpow_le_rpow hrpos.le hratio ha1.le
      have hpow' : r^a ≤ (Real.exp
          (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ)))^a := hpow
      calc
        r^a ≤ (Real.exp
            (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ)))^a := hpow'
        _ = Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ) * a) := by
          rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        _ = Real.exp (2 * a * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ)) := by
          congr 1
          ring
        _ ≤ Real.exp (2 * T) := by
          exact Real.exp_le_exp.mpr hdetBudget
    have hrrpowInv : (r⁻¹)^a ≤ 1 := by
      have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ r⁻¹) hratioInv ha1.le
      simpa using hpow
    have hbudget : 2 * T + 4 * A * T = Crate * T := by
      dsimp [Crate]
      ring
    have hbudget_le : 2 * T ≤ Crate * T := by
      have hnonneg : 0 ≤ 4 * A * T :=
        mul_nonneg (mul_nonneg (by norm_num) hA) hT
      rw [← hbudget]
      exact le_add_of_nonneg_right hnonneg
    have hplusExpBudget :
        2 * T + CH Kc * (2 * a)^2 * M.delta^2 ≤ Crate * T + E0 := by
      calc
        2 * T + CH Kc * (2 * a)^2 * M.delta^2 ≤ 2 * T + E0 :=
          add_le_add_right hHbudgetPos (2 * T)
        _ ≤ Crate * T + E0 := add_le_add_left hbudget_le E0
    have hplusSumExpBudget :
        2 * T + A * (|2 * a| + (2 * a)^2) * M.delta^2 * (k : ℝ) ≤
          Crate * T := by
      calc
        2 * T + A * (|2 * a| + (2 * a)^2) * M.delta^2 * (k : ℝ) ≤
            2 * T + 4 * A * T := add_le_add_right hsumBudgetPos (2 * T)
        _ = Crate * T := hbudget
    have hminusSumExpBudget :
        A * (|-2 * a| + (-2 * a)^2) * M.delta^2 * (k : ℝ) ≤
          Crate * T := by
      calc
        A * (|-2 * a| + (-2 * a)^2) * M.delta^2 * (k : ℝ) ≤
            4 * A * T := hsumBudgetNeg
        _ ≤ 2 * T + 4 * A * T :=
          le_add_of_nonneg_left (mul_nonneg (by norm_num) hT)
        _ = Crate * T := hbudget
    let Ep : ℝ := CH Kc * (2 * a)^2 * M.delta^2
    let En : ℝ := CH Kc * (-2 * a)^2 * M.delta^2
    let Sp : ℝ := A * (|2 * a| + (2 * a)^2) * M.delta^2 * (k : ℝ)
    let Sn : ℝ := A * (|-2 * a| + (-2 * a)^2) * M.delta^2 * (k : ℝ)
    have hEp : Ep ≤ E0 := by simpa [Ep] using hHbudgetPos
    have hEn : En ≤ E0 := by simpa [En] using hHbudgetNeg
    have hSp :
        (∫ omega, Real.exp (2 * a * center omega)
            ∂(chaosSampleLaw M).toMeasure) ≤ Real.exp Sp := by
      simpa [Sp] using hsumPosA
    have hSn :
        (∫ omega, Real.exp (-2 * a * center omega)
            ∂(chaosSampleLaw M).toMeasure) ≤ Real.exp Sn := by
      simpa [Sn] using hsumNegA
    have hplusRaw :
        (∫ omega, (F omega)^a ∂(chaosSampleLaw M).toMeasure) ≤
          (r^a / 2) *
            (2 * Real.exp Ep + Real.exp Sp) := by
      calc
        _ ≤ (r^a / 2) *
            ((∫ omega, Real.exp (2 * a * H omega y)
                ∂(chaosSampleLaw M).toMeasure) +
              (∫ omega, Real.exp (2 * a * center omega)
                ∂(chaosSampleLaw M).toMeasure)) := hplusIntegral
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left
          · exact add_le_add hHPos.2 hSp
          · positivity
    have hplusTerm1 :
        (r^a / 2) * (2 * Real.exp Ep) ≤
          Real.exp E0 * Real.exp (Crate * T) := by
      calc
        (r^a / 2) * (2 * Real.exp Ep) =
            r^a * Real.exp Ep :=
          aux_reference_point_moments_half_two _ _
        _ ≤ Real.exp (2 * T) *
            Real.exp Ep := by
              exact mul_le_mul_of_nonneg_right hrrpow (Real.exp_pos _).le
        _ = Real.exp (2 * T + Ep) := by
              exact (Real.exp_add _ _).symm
        _ ≤ Real.exp (Crate * T + E0) := by
              exact Real.exp_le_exp.mpr hplusExpBudget
        _ = Real.exp E0 * Real.exp (Crate * T) := by
              rw [show Crate * T + E0 = E0 + Crate * T by ring,
                Real.exp_add]
    have hplusTerm2 :
        (r^a / 2) * Real.exp Sp ≤ Real.exp E0 * Real.exp (Crate * T) := by
      have hnonneg : 0 ≤ r^a * Real.exp Sp := by positivity
      calc
        (r^a / 2) * Real.exp Sp ≤ r^a * Real.exp Sp := by
                calc
                  (r^a / 2) * Real.exp Sp =
                      (1 / 2 : ℝ) * (r^a * Real.exp Sp) :=
                    aux_reference_point_moments_half_mul _ _
                  _ ≤ 1 * (r^a * Real.exp Sp) := by
                    exact mul_le_mul_of_nonneg_right (by norm_num)
                      hnonneg
                  _ = _ := by ring
        _ ≤ Real.exp (2 * T) * Real.exp Sp := by
                exact mul_le_mul_of_nonneg_right hrrpow (Real.exp_pos _).le
        _ = Real.exp (2 * T + Sp) := by
                exact (Real.exp_add _ _).symm
        _ ≤ Real.exp (Crate * T) := by
              exact Real.exp_le_exp.mpr hplusSumExpBudget
        _ ≤ Real.exp E0 * Real.exp (Crate * T) := by
              calc
                Real.exp (Crate * T) = 1 * Real.exp (Crate * T) := by ring
                _ ≤ _ := by
                  exact mul_le_mul_of_nonneg_right (Real.one_le_exp hE0)
                    (Real.exp_pos _).le
    have hminusTerm1 :
        ((r⁻¹)^a / 2) * (2 * Real.exp En) ≤
          Real.exp E0 * Real.exp (Crate * T) := by
      calc
        ((r⁻¹)^a / 2) * (2 * Real.exp En) =
            (r⁻¹)^a * Real.exp En :=
          aux_reference_point_moments_half_two _ _
        _ ≤ Real.exp En := by
              calc
                (r⁻¹)^a * Real.exp En ≤ 1 * Real.exp En :=
                  mul_le_mul_of_nonneg_right hrrpowInv (Real.exp_pos En).le
                _ = Real.exp En := one_mul _
        _ ≤ Real.exp E0 := Real.exp_le_exp.mpr hEn
        _ ≤ Real.exp E0 * Real.exp (Crate * T) := by
              calc
                Real.exp E0 = Real.exp E0 * 1 := by ring
                _ ≤ _ := by
                  exact mul_le_mul_of_nonneg_left
                    (Real.one_le_exp (by
                      dsimp [Crate]
                      positivity)) (Real.exp_pos _).le
    have hminusTerm2 :
        ((r⁻¹)^a / 2) * Real.exp Sn ≤ Real.exp E0 * Real.exp (Crate * T) := by
      calc
        ((r⁻¹)^a / 2) * Real.exp Sn ≤ 1 * Real.exp Sn := by
                have hcoef : (r⁻¹)^a / 2 ≤ 1 :=
                  aux_reference_point_moments_half_le_one _ hrrpowInv
                exact mul_le_mul_of_nonneg_right hcoef (Real.exp_pos Sn).le
        _ = Real.exp Sn := one_mul _
        _ ≤ Real.exp (Crate * T) := by
              apply Real.exp_le_exp.mpr
              change A * (|-2 * a| + (-2 * a)^2) * M.delta^2 * (k : ℝ) ≤
                Crate * T
              exact hminusSumExpBudget
        _ ≤ Real.exp E0 * Real.exp (Crate * T) := by
              calc
                Real.exp (Crate * T) = 1 * Real.exp (Crate * T) := by ring
                _ ≤ _ := by
                  exact mul_le_mul_of_nonneg_right (Real.one_le_exp hE0)
                    (Real.exp_pos _).le
    let Iplus : ℝ := ∫ omega, (F omega)^a ∂(chaosSampleLaw M).toMeasure
    let Iminus : ℝ := ∫ omega, (F omega)^(-a) ∂(chaosSampleLaw M).toMeasure
    have hplusRawF : Iplus ≤
        (r^a / 2) * (2 * Real.exp Ep + Real.exp Sp) := by
      change (∫ omega, (F omega)^a ∂(chaosSampleLaw M).toMeasure) ≤ _
      exact hplusRaw
    have hminusRawF : Iminus ≤
        ((r⁻¹)^a / 2) * (2 * Real.exp En + Real.exp Sn) := by
      apply le_trans (show Iminus ≤
        ((r⁻¹)^a / 2) *
        ((∫ omega, Real.exp (-2 * a * H omega y)
              ∂(chaosSampleLaw M).toMeasure) +
            (∫ omega, Real.exp (-2 * a * center omega)
              ∂(chaosSampleLaw M).toMeasure)) by
        change (∫ omega, (F omega)^(-a) ∂(chaosSampleLaw M).toMeasure) ≤ _
        exact hminusIntegral)
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add hHNeg.2 hSn
      · exact div_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hrpos.le) _)
          (by norm_num)
    have hplusCore : Iplus ≤
        2 * (Real.exp E0 * Real.exp (Crate * T)) := by
      exact aux_reference_point_moments_combine_two
        Iplus (r^a / 2) (Real.exp Ep) (Real.exp Sp)
        (Real.exp E0 * Real.exp (Crate * T)) hplusRawF hplusTerm1 hplusTerm2
    have hminusCore : Iminus ≤
        2 * (Real.exp E0 * Real.exp (Crate * T)) := by
      exact aux_reference_point_moments_combine_two
        Iminus ((r⁻¹)^a / 2) (Real.exp En) (Real.exp Sn)
        (Real.exp E0 * Real.exp (Crate * T)) hminusRawF
        hminusTerm1 hminusTerm2
    have hplusBoundF : Iplus ≤ Cmom * Real.exp (Crate * T) := by
      calc
        _ ≤ 2 * (Real.exp E0 * Real.exp (Crate * T)) := hplusCore
        _ ≤ Cmom * Real.exp (Crate * T) := by
          simpa only [Cmom, E0] using
            aux_reference_point_moments_two_le_four
              (Real.exp (16 * CH Kc * q^2)) (Real.exp (Crate * T))
              (Real.exp_pos _).le (Real.exp_pos _).le
    have hminusBoundF : Iminus ≤ Cmom * Real.exp (Crate * T) := by
      calc
        _ ≤ 2 * (Real.exp E0 * Real.exp (Crate * T)) := hminusCore
        _ ≤ Cmom * Real.exp (Crate * T) := by
          simpa only [Cmom, E0] using
            aux_reference_point_moments_two_le_four
              (Real.exp (16 * CH Kc * q^2)) (Real.exp (Crate * T))
              (Real.exp_pos _).le (Real.exp_pos _).le

    have hp0 : ENNReal.ofReal a ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr ha1)
    have hptop : ENNReal.ofReal a ≠ ∞ := ENNReal.ofReal_ne_top
    have hplusNormInt :
        Integrable (fun omega : BilateralField d =>
          ‖F omega‖ ^ (ENNReal.ofReal a).toReal)
          (chaosSampleLaw M).toMeasure := by
      refine hplusInt.congr (Filter.Eventually.of_forall ?_)
      intro omega
      change (F omega)^a = ‖F omega‖ ^ (ENNReal.ofReal a).toReal
      rw [Real.norm_eq_abs, abs_of_pos (hFpos omega),
        ENNReal.toReal_ofReal ha1.le]
    have hminusNormInt :
        Integrable (fun omega : BilateralField d =>
          ‖(F omega)⁻¹‖ ^ (ENNReal.ofReal a).toReal)
          (chaosSampleLaw M).toMeasure := by
      refine hminusInt.congr (Filter.Eventually.of_forall ?_)
      intro omega
      change (F omega)^(-a) = ‖(F omega)⁻¹‖ ^ (ENNReal.ofReal a).toReal
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hFpos omega)),
        ENNReal.toReal_ofReal ha1.le, Real.inv_rpow (hFpos omega).le,
        ← Real.rpow_neg (hFpos omega).le]
    have hmemBase :
        MemLp F
          (ENNReal.ofReal a) (chaosSampleLaw M).toMeasure :=
      (integrable_norm_rpow_iff hFmeas.aestronglyMeasurable hp0 hptop).mp
        hplusNormInt
    have hmemInv :
        MemLp (fun omega : BilateralField d => (F omega)⁻¹)
          (ENNReal.ofReal a) (chaosSampleLaw M).toMeasure :=
      (integrable_norm_rpow_iff hFmeas.inv.aestronglyMeasurable hp0 hptop).mp
        hminusNormInt
    have hsumInt :
        Integrable (fun omega : BilateralField d =>
          (F omega)^a + (F omega)^(-a))
          (chaosSampleLaw M).toMeasure :=
      hplusInt.add hminusInt
    have hsumBound :
        (∫ omega : BilateralField d,
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
            Real.exp (H omega y +
              ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y -
              (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))^a +
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
            Real.exp (H omega y +
              ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y -
              (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))^(-a)
            ∂(chaosSampleLaw M).toMeasure) ≤
          Cmom * Real.exp (Crate * (a + a^2) * M.delta^2 * (k : ℝ)) := by
      have hrawF :
          (∫ omega, (F omega)^a + (F omega)^(-a)
            ∂(chaosSampleLaw M).toMeasure) ≤
            Cmom * Real.exp (Crate * T) := by
        rw [integral_add hplusInt hminusInt]
        have hcore : Iplus + Iminus ≤
            Cmom * Real.exp (Crate * T) := by
          calc
            Iplus + Iminus ≤
                2 * (Real.exp E0 * Real.exp (Crate * T)) +
                  2 * (Real.exp E0 * Real.exp (Crate * T)) :=
              add_le_add hplusCore hminusCore
            _ = Cmom * Real.exp (Crate * T) := by
              dsimp [Cmom]
              ring
        simpa only [Iplus, Iminus] using hcore
      have hExpEq : Crate * T =
          Crate * (a + a^2) * M.delta^2 * (k : ℝ) := by
        rw [hTdef]
        ring
      calc
        _ = (∫ omega, (F omega)^a + (F omega)^(-a)
              ∂(chaosSampleLaw M).toMeasure) := by
          simp only [F]
        _ ≤ Cmom * Real.exp (Crate * T) := hrawF
        _ = _ := by rw [hExpEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [F] using hsumInt
    · exact hsumBound
    · simpa only [F] using hmemBase
    · simpa only [F] using hmemInv

end SubdiffusiveProcess.Paper
