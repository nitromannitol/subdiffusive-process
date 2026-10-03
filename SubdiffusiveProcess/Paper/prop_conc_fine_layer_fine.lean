module

public import SubdiffusiveProcess.Paper.prop_conc_fine_layer_data
public import SubdiffusiveProcess.Paper.prop_conc_fine_layer_mom
public import SubdiffusiveProcess.Paper.prop_conc_fine_geometry
public import SubdiffusiveProcess.Paper.prop_conc_fine_grid
public import SubdiffusiveProcess.Paper.prop_conc_fine_fibre
public import SubdiffusiveProcess.Paper.prop_conc_fine_fibre_es
public import SubdiffusiveProcess.Paper.prop_conc_fine_layer_env
public import SubdiffusiveProcess.Paper.prop_conc_fine_layer_num
public import SubdiffusiveProcess.Paper.lem_15

@[expose] public section

/-! The fine case of the fine-layer step: relative wavelength `3^{-n} ≤ r0`. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology
namespace Paper
noncomputable section

/-- The pieces of the layer under the layer law are independent (`(g1)` and the range of the layer). -/
theorem aux_prop_conc_fine_layer_fine_pieces_law (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n k : ℕ) (j : ℤ) (hj : j = -((n + k : ℕ) : ℤ))
    (ell w : ℝ) (hell : 0 ≤ ell) (hw : 0 < w) (hwl : w ≤ ell)
    (hsep : Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (n + k) * (w / 2)) {m : ℕ}
    (idx : Fin m → (Fin d → ℤ)) (hinj : Function.Injective idx) :
    (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure.map
        (aux_prop_conc_fine_fibre_det_T ell w idx) =
      Measure.pi (fun i : Fin m => (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure.map
        (fun y => aux_lem_15_u_localize 0 ell w (idx i) y)) := by
  have hsep' : Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (-(-((n + k : ℕ) : ℤ))) * (w / 2) := by
    rw [neg_neg, zpow_natCast]; exact hsep
  have hkey := aux_lem_15_u_key_law hd model.P model.G1 (n + k) 0 hell hw hwl hsep' idx hinj
  simp only at hkey
  have hlayer : ((commonScaleLaw d (chaosRootFieldLaw model)).toMeasure).map
      (fun eta : BilateralField d => eta j) =
      (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure :=
    Measure.infinitePi_map_eval (X := fun _ : ℤ => C(SpatialCoordinates d, ℝ))
      (fun i : ℤ => (scaledLayerLaw d (chaosRootFieldLaw model) i : Measure C(SpatialCoordinates d, ℝ))) j
  subst hj
  have hTm : Measurable (aux_prop_conc_fine_fibre_det_T ell w idx) :=
    Measurable.of_eval fun i => (aux_lem_15_u_localize_continuous 0 ell w (idx i)).measurable
  rw [← hlayer, Measure.map_map hTm (measurable_pi_apply _)]
  exact hkey

/-- A measurable version `Kt` of the growth constant, which agrees with `K` and is nonnegative along
almost every fibre. -/
theorem aux_prop_conc_fine_layer_fine_Ktilde (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (field : Ω → BilateralField d) (hfield : Measurable field)
    (hlaw : Measure.map field P = (chaosSampleLaw model).toMeasure) (K : BilateralField d → ℝ)
    (hKm : AEStronglyMeasurable K (chaosSampleLaw model).toMeasure)
    (hK0 : ∀ᵐ eta ∂(chaosSampleLaw model).toMeasure, 0 ≤ K eta) (j : ℤ) :
    ∃ Kt : BilateralField d → ℝ, Measurable Kt ∧
      (∀ᵐ eta ∂(chaosSampleLaw model).toMeasure, K eta = Kt eta) ∧
      ∀ᵐ omega ∂P, ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure,
        K (Function.update (field omega) j y) = Kt (Function.update (field omega) j y) ∧
          0 ≤ Kt (Function.update (field omega) j y) := by
  set μ := (chaosSampleLaw model).toMeasure with hμ
  refine ⟨hKm.mk K, hKm.stronglyMeasurable_mk.measurable, hKm.ae_eq_mk, ?_⟩
  have hae : ∀ᵐ eta ∂μ, K eta = hKm.mk K eta := hKm.ae_eq_mk
  set N1 : Set (BilateralField d) := {eta | ¬ K eta = hKm.mk K eta} with hN1
  set N2 : Set (BilateralField d) := {eta | hKm.mk K eta < 0} with hN2
  have hN1z : μ N1 = 0 := hae
  have hN2z : μ N2 = 0 := by
    have : ∀ᵐ eta ∂μ, ¬ hKm.mk K eta < 0 := by
      filter_upwards [hae, hK0] with eta h1 h2
      rw [← h1]; exact not_lt.mpr h2
    have h3 := ae_iff.mp this
    simpa using h3
  set N : Set (BilateralField d) := toMeasurable μ N1 ∪ N2 with hN
  have hNm : MeasurableSet N :=
    (measurableSet_toMeasurable μ N1).union (measurableSet_lt hKm.stronglyMeasurable_mk.measurable measurable_const)
  have hNz : Measure.infinitePi (fun i : ℤ => (scaledLayerLaw d (chaosRootFieldLaw model) i : Measure C(SpatialCoordinates d, ℝ))) N = 0 := by
    have : μ N = 0 := by
      refine measure_union_null ?_ hN2z
      rw [measure_toMeasurable]; exact hN1z
    exact this
  have hnull := aux_prop_conc_fine_fibre_null
    (fun i : ℤ => (scaledLayerLaw d (chaosRootFieldLaw model) i : Measure C(SpatialCoordinates d, ℝ))) j P field
    hfield hlaw N hNm hNz
  filter_upwards [hnull] with omega hom
  filter_upwards [hom] with y hy
  have h1 : Function.update (field omega) j y ∉ toMeasurable μ N1 := fun h => hy (Or.inl h)
  have h2 : Function.update (field omega) j y ∉ N2 := fun h => hy (Or.inr h)
  refine ⟨?_, ?_⟩
  · by_contra hne
    exact h1 (subset_toMeasurable μ N1 hne)
  · exact not_lt.mp h2

/-- The Efron--Stein inequality for the pieces, in the form used along a fibre. -/
theorem aux_prop_conc_fine_layer_fine_esprop (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality)
    (p : ℝ) (hp : 2 ≤ p) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ {X : Type} [MeasurableSpace X] {m : ℕ} (muk : Fin m → Measure X)
      [∀ i, IsProbabilityMeasure (muk i)], aux_lem_15_u_ESProp muk p Cp := by
  obtain ⟨Cp, hCp, hESp⟩ := hES.exists_const p hp
  refine ⟨Cp, hCp, ?_⟩
  intro X _ m muk _ F _ hF
  exact hESp m (fun _ => X) (fun _ => inferInstance) muk inferInstance F hF

/-- **The fibre inequality.**  For a.e. `ω`, the resampling difference of the fibre through `field ω`
is bounded by the deletion and Efron--Stein envelopes evaluated along the fibre. -/
theorem aux_prop_conc_fine_layer_fine_fibre (d : ℕ) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∃ Cex : ℝ, 0 < Cex ∧
    ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
      (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (field : Ω → BilateralField d) (m M : ℝ) (Q : Opens (SpatialCoordinates d))
      (zcell : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (c : ℝ), c ∈ Set.Icc m M →
      ∀ (pvec : Fin d → ℝ), pvec ∈ aux_prop_conc_pair_data_slopes d →
      ∀ (t : ℝ) (f K Kt : BilateralField d → ℝ) (j : ℤ), Measurable f → Measurable Kt →
        aux_prop_conc_fine_layer_data_FD d model C0 m M Q zcell r hr c pvec t P field f K j →
        (∀ᵐ omega ∂P, ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure,
          K (Function.update (field omega) j y) = Kt (Function.update (field omega) j y) ∧
            0 ≤ Kt (Function.update (field omega) j y)) →
      ∀ (ell w : ℝ) {mm : ℕ} (idx : Fin mm → (Fin d → ℤ)),
        aux_prop_conc_fine_grid_Grid zcell r hr ell w idx →
      ∀ (Astrip Acore : ℝ), 0 ≤ Astrip → 0 ≤ Acore →
        aux_prop_conc_fine_geometry_CellBound zcell r hr t ell w Astrip Acore →
        (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure.map
            (aux_prop_conc_fine_fibre_det_T ell w idx) =
          Measure.pi (fun i : Fin mm => (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure.map
            (fun y => aux_lem_15_u_localize 0 ell w (idx i) y)) →
      ∀ (pe Cp : ℝ), 2 ≤ pe →
        aux_lem_15_u_ESProp (fun i : Fin mm =>
          (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure.map
            (fun y => aux_lem_15_u_localize 0 ell w (idx i) y)) pe Cp →
      ∀ (Ma Me : ℝ), 0 ≤ Ma → 0 ≤ Me →
        Integrable (fun y => Real.exp (2 * Cex * aux_prop_conc_fine_fibre_det_S zcell r y))
          (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure →
        Integrable (fun y => aux_prop_conc_fine_fibre_det_S zcell r y ^ 2 *
          Real.exp (2 * Cex * aux_prop_conc_fine_fibre_det_S zcell r y))
          (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure →
        (∫ y, Real.exp (2 * Cex * aux_prop_conc_fine_fibre_det_S zcell r y)
          ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure ≤ Ma) →
        (∫ y, aux_prop_conc_fine_fibre_det_S zcell r y ^ 2 *
          Real.exp (2 * Cex * aux_prop_conc_fine_fibre_det_S zcell r y)
          ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure ≤ Me) →
        ∀ᵐ omega ∂P,
          eLpNorm (fun yy : C(SpatialCoordinates d, ℝ) × C(SpatialCoordinates d, ℝ) =>
              f (Function.update (field omega) j yy.1) - f (Function.update (field omega) j yy.2))
            (ENNReal.ofReal pe) ((scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure.prod
              (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure) ≤
          2 * eLpNorm (fun y => aux_prop_conc_fine_fibre_es_env1 Cex (M - m) Astrip
              (Real.sqrt (C0 ^ 2 * ((2 : ℝ) ^ d *
                ∑ v ∈ aux_prop_conc_pair_data_slopes d, ∑ i : Fin d, (v i) ^ 2)))
              (aux_prop_conc_fine_fibre_det_S zcell r y) (Kt (Function.update (field omega) j y)))
            (ENNReal.ofReal pe) (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure +
          2 * ENNReal.ofReal Cp * eLpNorm (fun y => aux_prop_conc_fine_fibre_es_env2 Cex (M - m) Acore
              Astrip Ma Me (aux_prop_conc_fine_fibre_det_S zcell r y)
              (Kt (Function.update (field omega) j y)))
            (ENNReal.ofReal pe) (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure := by
  obtain ⟨Cex, hCex, hFB⟩ := prop_conc_fine_fibre_es C0 hC0 d
  refine ⟨Cex, hCex, ?_⟩
  intro _ _ model Ω _ P field m M Q zcell r hr c hc pvec hpvec t f K Kt j hf hKt hfd hKK ell w mm idx hgrid
    Astrip Acore hAs hAc hcb hπ pe Cp hpe hES Ma Me hMa0 hMe0 hIa hIe hMa hMe
  haveI : IsProbabilityMeasure (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure := inferInstance
  filter_upwards [hfd, hKK] with omega hX hK
  obtain ⟨X, hfX, hgr⟩ := hX
  have hfm : Measurable (fun y : C(SpatialCoordinates d, ℝ) => f (Function.update (field omega) j y)) :=
    hf.comp (measurable_update (field omega) : Measurable (Function.update (field omega) j))
  have hK0 : ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure,
      0 ≤ Kt (Function.update (field omega) j y) := by
    filter_upwards [hK] with y hy using hy.2
  have hgr' : ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure,
      ∀ (hw : Measurable (aux_prop_conc_fine_fibre_det_wY zcell r hr ((field omega) j) y)) (Kw : ℝ)
        (hKw : ∀ x, |aux_prop_conc_fine_fibre_det_wY zcell r hr ((field omega) j) y x| ≤ Kw),
        aux_prop_conc_pair_data_growth
          (aux_prop_conc_pair_mask_pair X (aux_prop_conc_fine_fibre_det_wY zcell r hr ((field omega) j) y)
            hw Kw hKw)
          (aux_prop_conc_pair_data_slopes d) t (Kt (Function.update (field omega) j y)) := by
    filter_upwards [hgr, hK] with y h1 h2
    intro hw Kw hKw
    have := h1 hw Kw hKw
    rwa [h2.1] at this
  exact hFB X c hc pvec hpvec ((field omega) j) ell w idx hgrid t Astrip Acore hAs hAc hcb
    (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure hπ
    (fun y => f (Function.update (field omega) j y)) hfm hfX
    (fun y => Kt (Function.update (field omega) j y)) hK0 hgr' pe Cp hpe hES Ma Me hMa0 hMe0 hIa hIe hMa hMe

theorem aux_prop_conc_fine_layer_fine_env_meas (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (zcell : SpatialCoordinates d) (r : ℝ)
    (j : ℤ) (Kt : BilateralField d → ℝ) (hKt : Measurable Kt)
    (F : ℝ → ℝ → ℝ) (hF : Continuous (fun sK : ℝ × ℝ => F sK.1 sK.2)) :
    Measurable (fun eta : BilateralField d =>
      F (aux_prop_conc_fine_fibre_det_S zcell r (eta j)) (Kt eta)) := by
  have hS : Measurable (fun eta : BilateralField d => aux_prop_conc_fine_fibre_det_S zcell r (eta j)) :=
    (aux_lem_15_u_supn_continuous _ _).measurable.comp (measurable_pi_apply j)
  exact hF.measurable.comp (hS.prodMk hKt)

/-- **Global step.**  The fibre inequality integrates to the `L^p` bound of the resampling difference on the
product of two copies of the chaos law, the envelopes being evaluated at the resampled configuration. -/
theorem aux_prop_conc_fine_layer_fine_global (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d) (hfield : Measurable field)
    (hlaw : Measure.map field P = (chaosSampleLaw model).toMeasure)
    (zcell : SpatialCoordinates d) (r : ℝ) (j : ℤ) (f Kt : BilateralField d → ℝ) (hf : Measurable f)
    (hKt : Measurable Kt) (pe Cp : ℝ) (hpe : 1 ≤ pe)
    (E1 E2 : ℝ → ℝ → ℝ) (hE1 : Continuous (fun sK : ℝ × ℝ => E1 sK.1 sK.2))
    (hE2 : Continuous (fun sK : ℝ × ℝ => E2 sK.1 sK.2))
    (hfib : ∀ᵐ omega ∂P,
      eLpNorm (fun yy : C(SpatialCoordinates d, ℝ) × C(SpatialCoordinates d, ℝ) =>
          f (Function.update (field omega) j yy.1) - f (Function.update (field omega) j yy.2))
        (ENNReal.ofReal pe) ((scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure.prod
          (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure) ≤
      2 * eLpNorm (fun y => E1 (aux_prop_conc_fine_fibre_det_S zcell r y)
          (Kt (Function.update (field omega) j y))) (ENNReal.ofReal pe)
          (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure +
      2 * ENNReal.ofReal Cp * eLpNorm (fun y => E2 (aux_prop_conc_fine_fibre_det_S zcell r y)
          (Kt (Function.update (field omega) j y))) (ENNReal.ofReal pe)
          (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure) :
    eLpNorm (fun q : BilateralField d × BilateralField d => f q.1 - f (Function.update q.1 j (q.2 j)))
        (ENNReal.ofReal pe) ((chaosSampleLaw model).toMeasure.prod (chaosSampleLaw model).toMeasure) ≤
      2 * eLpNorm (fun eta : BilateralField d =>
          E1 (aux_prop_conc_fine_fibre_det_S zcell r (eta j)) (Kt eta)) (ENNReal.ofReal pe)
          (chaosSampleLaw model).toMeasure +
      2 * ENNReal.ofReal Cp * eLpNorm (fun eta : BilateralField d =>
          E2 (aux_prop_conc_fine_fibre_det_S zcell r (eta j)) (Kt eta)) (ENNReal.ofReal pe)
          (chaosSampleLaw model).toMeasure := by
  set laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun i => (scaledLayerLaw d (chaosRootFieldLaw model) i : Measure C(SpatialCoordinates d, ℝ)) with hlaws
  haveI : ∀ i, IsProbabilityMeasure (laws i) := fun i => inferInstance
  have hμ : (chaosSampleLaw model).toMeasure = Measure.infinitePi laws := rfl
  have hE1m := aux_prop_conc_fine_layer_fine_env_meas d zcell r j Kt hKt E1 hE1
  have hE2m := aux_prop_conc_fine_layer_fine_env_meas d zcell r j Kt hKt E2 hE2
  set G1 : BilateralField d → ℝ := fun eta => E1 (aux_prop_conc_fine_fibre_det_S zcell r (eta j)) (Kt eta)
    with hG1
  set G2 : BilateralField d → ℝ := fun eta => E2 (aux_prop_conc_fine_fibre_det_S zcell r (eta j)) (Kt eta)
    with hG2
  have hFT := prop_conc_fine_fibre laws j P field hfield (by rw [← hμ]; exact hlaw) f hf pe hpe
    (fun _ eta => G1 eta) (fun _ eta => G2 eta) (hE1m.comp measurable_snd) (hE2m.comp measurable_snd)
    2 (2 * ENNReal.ofReal Cp) (by
      filter_upwards [hfib] with omega hom
      simp only [hG1, hG2, Function.update_self]
      exact hom)
  have hU := SubdiffusiveProcess.Probability.measurePreserving_update_infinitePi laws j
  have e1 : eLpNorm (fun q : (ℤ → C(SpatialCoordinates d, ℝ)) × (ℤ → C(SpatialCoordinates d, ℝ)) =>
      G1 (Function.update q.1 j (q.2 j))) (ENNReal.ofReal pe)
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) =
      eLpNorm G1 (ENNReal.ofReal pe) (Measure.infinitePi laws) :=
    eLpNorm_comp_measurePreserving (g := G1) hE1m.aestronglyMeasurable hU
  have e2 : eLpNorm (fun q : (ℤ → C(SpatialCoordinates d, ℝ)) × (ℤ → C(SpatialCoordinates d, ℝ)) =>
      G2 (Function.update q.1 j (q.2 j))) (ENNReal.ofReal pe)
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) =
      eLpNorm G2 (ENNReal.ofReal pe) (Measure.infinitePi laws) :=
    eLpNorm_comp_measurePreserving (g := G2) hE2m.aestronglyMeasurable hU
  simp only at hFT
  rw [e1, e2] at hFT
  rw [hμ]
  exact hFT


/-- The five layer-norm moments used by the fine case, with one constant. -/
theorem aux_prop_conc_fine_layer_fine_bank (d : ℕ) (hd : 2 ≤ d)
    (p Cex γ : ℝ) (hp : 0 < p) (hCex : 0 ≤ Cex) (hγ : 0 < γ) :
    ∃ Cm : ℝ, 0 < Cm ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (zcell : SpatialCoordinates d) (k n : ℕ) (r : ℝ)
        (_hrk : r = (3 : ℝ) ^ (-(k : ℝ))) (j : ℤ) (_hj : j = -((n + k : ℕ) : ℤ)),
        eLpNorm (fun eta : BilateralField d => aux_prop_conc_fine_fibre_det_S zcell r (eta j) *
            Real.exp (Cex * aux_prop_conc_fine_fibre_det_S zcell r (eta j)))
          (ENNReal.ofReal (2 * p)) (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal (Cm * model.delta * ((3 : ℝ) ^ (-(n : ℝ))) ^ (-γ)) ∧
        eLpNorm (fun eta : BilateralField d => aux_prop_conc_fine_fibre_det_S zcell r (eta j) *
            Real.exp (3 / 2 * Cex * aux_prop_conc_fine_fibre_det_S zcell r (eta j)))
          (ENNReal.ofReal (2 * p)) (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal (Cm * model.delta * ((3 : ℝ) ^ (-(n : ℝ))) ^ (-γ)) ∧
        eLpNorm (fun eta : BilateralField d =>
            Real.exp (3 / 2 * Cex * aux_prop_conc_fine_fibre_det_S zcell r (eta j)))
          (ENNReal.ofReal (2 * p)) (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal (Cm * ((3 : ℝ) ^ (-(n : ℝ))) ^ (-γ)) ∧
        Integrable (fun y : C(SpatialCoordinates d, ℝ) =>
            Real.exp (2 * Cex * aux_prop_conc_fine_fibre_det_S zcell r y))
          (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure ∧
        (∫ y : C(SpatialCoordinates d, ℝ),
            Real.exp (2 * Cex * aux_prop_conc_fine_fibre_det_S zcell r y)
          ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure ≤
          Cm * ((3 : ℝ) ^ (-(n : ℝ))) ^ (-γ)) ∧
        Integrable (fun y : C(SpatialCoordinates d, ℝ) =>
            aux_prop_conc_fine_fibre_det_S zcell r y ^ 2 *
              Real.exp (2 * Cex * aux_prop_conc_fine_fibre_det_S zcell r y))
          (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure ∧
        (∫ y : C(SpatialCoordinates d, ℝ), aux_prop_conc_fine_fibre_det_S zcell r y ^ 2 *
            Real.exp (2 * Cex * aux_prop_conc_fine_fibre_det_S zcell r y)
          ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure ≤
          Cm * model.delta ^ 2 * ((3 : ℝ) ^ (-(n : ℝ))) ^ (-γ)) := by
  have h2p : 0 < 2 * p := by linarith
  obtain ⟨C1, hC1, hM1⟩ := prop_conc_fine_layer_mom d hd (2 * p) 1 Cex γ h2p (by norm_num) hCex hγ
  obtain ⟨C2, hC2, hM2⟩ := prop_conc_fine_layer_mom d hd (2 * p) 1 (3 / 2 * Cex) γ h2p (by norm_num)
    (by positivity) hγ
  obtain ⟨C3, hC3, hM3⟩ := prop_conc_fine_layer_mom d hd (2 * p) 0 (3 / 2 * Cex) γ h2p (le_refl _)
    (by positivity) hγ
  obtain ⟨C4, hC4, hM4⟩ := prop_conc_fine_layer_mom d hd 1 0 (2 * Cex) γ one_pos (le_refl _)
    (by positivity) hγ
  obtain ⟨C5, hC5, hM5⟩ := prop_conc_fine_layer_mom d hd 1 2 (2 * Cex) γ one_pos (by norm_num)
    (by positivity) hγ
  set Cm : ℝ := max (max (max (max C1 C2) C3) C4) C5 with hCm
  have h1 : C1 ≤ Cm := (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans
    (le_max_left _ _)
  have h2 : C2 ≤ Cm := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans
    (le_max_left _ _)
  have h3 : C3 ≤ Cm := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)
  have h4 : C4 ≤ Cm := (le_max_right _ _).trans (le_max_left _ _)
  have h5 : C5 ≤ Cm := le_max_right _ _
  refine ⟨Cm, lt_of_lt_of_le hC1 h1, ?_⟩
  intro _ _ model zcell k n r hrk j hj
  have hδ0 : 0 < model.delta := model.shellPrefix.delta_pos
  have hrs : 0 < ((3 : ℝ) ^ (-(n : ℝ))) ^ (-γ) := by positivity
  have hSm : Measurable (fun y : C(SpatialCoordinates d, ℝ) => aux_prop_conc_fine_fibre_det_S zcell r y) :=
    (aux_lem_15_u_supn_continuous _ _).measurable
  have hEm : ∀ lam : ℝ, Measurable (fun y : C(SpatialCoordinates d, ℝ) =>
      Real.exp (lam * aux_prop_conc_fine_fibre_det_S zcell r y)) :=
    fun lam => Real.measurable_exp.comp (hSm.const_mul lam)
  have hS0 : ∀ y : C(SpatialCoordinates d, ℝ), 0 ≤ aux_prop_conc_fine_fibre_det_S zcell r y :=
    fun y => aux_prop_conc_fine_fibre_det_S_nonneg zcell r y
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := (hM1 model zcell k n r hrk j hj).1
    simp only [Real.rpow_one] at this
    exact this.trans (ENNReal.ofReal_le_ofReal (by gcongr))
  · have := (hM2 model zcell k n r hrk j hj).1
    simp only [Real.rpow_one] at this
    exact this.trans (ENNReal.ofReal_le_ofReal (by gcongr))
  · have := (hM3 model zcell k n r hrk j hj).1
    simp only [Real.rpow_zero, one_mul, mul_one] at this
    exact this.trans (ENNReal.ofReal_le_ofReal (by gcongr))
  · have := (hM4 model zcell k n r hrk j hj).2
    simp only [Real.rpow_zero, one_mul, mul_one, ENNReal.ofReal_one] at this
    exact aux_lem_15_u_integrable_of_eLpNorm_one _ _ (hEm (2 * Cex)).aestronglyMeasurable _ this
  · have := (hM4 model zcell k n r hrk j hj).2
    simp only [Real.rpow_zero, one_mul, mul_one, ENNReal.ofReal_one] at this
    refine (aux_lem_15_u_integral_le_of_eLpNorm_one _ _ (fun y => (Real.exp_pos _).le) _ (by positivity) this).trans ?_
    gcongr
  · have := (hM5 model zcell k n r hrk j hj).2
    simp only [Real.rpow_two, ENNReal.ofReal_one] at this
    exact aux_lem_15_u_integrable_of_eLpNorm_one _ _ ((hSm.pow_const 2).mul (hEm (2 * Cex))).aestronglyMeasurable _ this
  · have := (hM5 model zcell k n r hrk j hj).2
    simp only [Real.rpow_two, ENNReal.ofReal_one] at this
    refine (aux_lem_15_u_integral_le_of_eLpNorm_one _ _ (fun y => by have := hS0 y; positivity) _ (by positivity) this).trans ?_
    gcongr

theorem aux_prop_conc_fine_layer_fine_enn (X1 X2 Cp : ℝ) (h1 : 0 ≤ X1) (h2 : 0 ≤ X2) (hCp : 0 ≤ Cp) :
    2 * ENNReal.ofReal X1 + 2 * ENNReal.ofReal Cp * ENNReal.ofReal X2 =
      ENNReal.ofReal (2 * X1 + 2 * Cp * X2) := by
  have h2' : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), h2']

/-- The exponent parameter `t = d - 1/2` of the growth bound (dimension only). -/
def aux_prop_conc_fine_layer_fine_t (d : ℕ) : ℝ := (d : ℝ) - 1 / 2

/-- The exponent `b = t (t - d + 1) / (t + 1)` of `lem-strips` at `t = d - 1/2`. -/
def aux_prop_conc_fine_layer_fine_b (d : ℕ) : ℝ :=
  aux_prop_conc_fine_layer_fine_t d * (aux_prop_conc_fine_layer_fine_t d - (d : ℝ) + 1) /
    (aux_prop_conc_fine_layer_fine_t d + 1)

/-- The fine case: for the relative wavelength `3^{-n} ≤ r0` (`r0` depending on `d` only), the `L^p` resampling
difference is at most `Kf δ (M - m) (3^{-n})^{3b/8}`. -/
theorem prop_conc_fine_layer_fine (d : ℕ) (hd : 2 ≤ d)
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality)
    (C0 : ℝ) (hC0 : 1 ≤ C0) (p : ℝ) (hp : 2 ≤ p) (B : ℝ) (hB0 : 0 ≤ B) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∃ Kf : ℝ, 0 < Kf ∧
    ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
      (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (field : Ω → BilateralField d) (m M : ℝ) (Q : Opens (SpatialCoordinates d))
      (zcell : SpatialCoordinates d) (k : ℕ) (r : ℝ) (hr : 0 < r) (_hrk : r = (3 : ℝ) ^ (-(k : ℝ)))
      (c : ℝ), c ∈ Set.Icc m M →
      ∀ (pvec : Fin d → ℝ), pvec ∈ aux_prop_conc_pair_data_slopes d →
      ∀ (f K : BilateralField d → ℝ) (j : ℤ) (n : ℕ), j = -((n + k : ℕ) : ℤ) →
        prop_conc_fine_layer_data d model C0 m M Q zcell r hr c pvec (aux_prop_conc_fine_layer_fine_t d)
          p B P field f K j →
        (3 : ℝ) ^ (-(n : ℝ)) ≤ r0 →
        eLpNorm (fun q : BilateralField d × BilateralField d => f q.1 - f (Function.update q.1 j (q.2 j)))
            (ENNReal.ofReal p)
            ((chaosSampleLaw model).toMeasure.prod (chaosSampleLaw model).toMeasure) ≤
          ENNReal.ofReal (Kf * model.delta * (M - m) *
            ((3 : ℝ) ^ (-(n : ℝ))) ^ (3 * aux_prop_conc_fine_layer_fine_b d / 8)) := by
  have hd1 : 1 ≤ d := by omega
  have ht1 : (d : ℝ) - 1 < aux_prop_conc_fine_layer_fine_t d := by
    unfold aux_prop_conc_fine_layer_fine_t; linarith
  have hsq : 0 < 2 * Real.sqrt d := by positivity
  obtain ⟨Cd, hCd, hgeo⟩ := prop_conc_fine_geometry d hd1 (2 * Real.sqrt d) hsq
  obtain ⟨hbpos, r0, hr0, hr01, hgeoR⟩ := hgeo _ ht1
  obtain ⟨Cp, hCp, hESc⟩ := aux_prop_conc_fine_layer_fine_esprop hES p hp
  obtain ⟨Cex, hCex, hfibre⟩ := aux_prop_conc_fine_layer_fine_fibre d C0 hC0
  have hb : 0 < aux_prop_conc_fine_layer_fine_b d := hbpos
  obtain ⟨Cm, hCm, hbank⟩ := aux_prop_conc_fine_layer_fine_bank d hd p Cex
    (aux_prop_conc_fine_layer_fine_b d / 12) (by linarith) hCex.le (by positivity)
  obtain ⟨cA, hcAdef⟩ : ∃ cA : ℝ, cA = Real.sqrt (C0 ^ 2 * ((2 : ℝ) ^ d *
      ∑ v ∈ aux_prop_conc_pair_data_slopes d, ∑ i : Fin d, (v i) ^ 2)) := ⟨_, rfl⟩
  have hcA0 : 0 ≤ cA := by rw [hcAdef]; exact Real.sqrt_nonneg _
  obtain ⟨Kf, hKfdef⟩ : ∃ Kf : ℝ, Kf = 2 * Cex * Cm * (1 + B) * (Cd + cA * Real.sqrt Cd) +
      2 * Cp * (2 * (Real.sqrt (2 * (Cex + Cex)) * Cex * Real.sqrt Cex * Real.sqrt 2 *
        Real.sqrt (2 * Cd) * (Cm * Real.sqrt Cm) * (1 + B))) := ⟨_, rfl⟩
  have hKf0 : 0 < Kf := by
    rw [hKfdef]
    have : 0 < 2 * Cex * Cm * (1 + B) * (Cd + cA * Real.sqrt Cd) := by positivity
    have : 0 ≤ 2 * Cp * (2 * (Real.sqrt (2 * (Cex + Cex)) * Cex * Real.sqrt Cex * Real.sqrt 2 *
        Real.sqrt (2 * Cd) * (Cm * Real.sqrt Cm) * (1 + B))) := by positivity
    linarith
  refine ⟨r0, hr0, Kf, hKf0, ?_⟩
  intro _ _ model Ω _ P field m M Q zcell k r hr hrk c hc pvec hpvec f K j n hj hD hrs
  haveI := hD.hP
  have hδ0 : 0 < model.delta := model.shellPrefix.delta_pos
  have hδ1 : model.delta ≤ 1 := model.shellPrefix.delta_le_half.trans (by norm_num)
  have hgap : 0 ≤ M - m := sub_nonneg.mpr (hc.1.trans hc.2)
  obtain ⟨rs, hrsdef⟩ : ∃ rs : ℝ, rs = (3 : ℝ) ^ (-(n : ℝ)) := ⟨_, rfl⟩
  have hrs0 : 0 < rs := by rw [hrsdef]; positivity
  have hrs1 : rs ≤ 1 := by
    rw [hrsdef]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp)
  rw [← hrsdef] at hrs ⊢
  obtain ⟨⟨hell, hell1, hwl⟩, hcb⟩ := hgeoR zcell r hr rs hrs0 hrs
  obtain ⟨ell, hell_def⟩ : ∃ ell : ℝ, ell = r * rs ^ ((aux_prop_conc_fine_layer_fine_t d - (d : ℝ) + 1) /
      (aux_prop_conc_fine_layer_fine_t d + 1)) := ⟨_, rfl⟩
  obtain ⟨w, hw_def⟩ : ∃ w : ℝ, w = r * (2 * Real.sqrt d * rs) := ⟨_, rfl⟩
  rw [← hell_def] at hell hell1 hwl hcb
  rw [← hw_def] at hwl hcb
  have hw : 0 < w := by rw [hw_def]; positivity
  have hsep : Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (n + k) * (w / 2) := by
    refine le_of_eq ?_
    rw [hw_def, hrsdef, hrk, Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num),
      Real.rpow_natCast, Real.rpow_natCast, pow_add]
    field_simp
  obtain ⟨mm, idx, hgrid⟩ := prop_conc_fine_grid zcell r hr ell w hw hwl.le hell1
  have hπ := aux_prop_conc_fine_layer_fine_pieces_law d hd model n k j hj ell w hell.le hw hwl.le hsep idx
    hgrid.2.2.2.1
  obtain ⟨Kt, hKt, hKtae, hKK⟩ := aux_prop_conc_fine_layer_fine_Ktilde d model P field hD.hfield hD.hlaw K
    hD.hKm hD.hK0 j
  obtain ⟨ha, hb', hc', hIa, hMa, hIe, hMe⟩ := hbank model zcell k n r hrk j hj
  rw [← hrsdef] at ha hb' hc' hMa hMe
  have hAs : 0 ≤ Cd * rs ^ aux_prop_conc_fine_layer_fine_b d := by positivity
  haveI hprobk : ∀ i : Fin mm, IsProbabilityMeasure
      ((scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure.map
        (fun y => aux_lem_15_u_localize 0 ell w (idx i) y)) := fun i =>
    inferInstance
  have hfib := hfibre model P field m M Q zcell r hr c hc pvec hpvec (aux_prop_conc_fine_layer_fine_t d)
    f K Kt j hD.hf hKt hD.hfd hKK ell w idx hgrid (Cd * rs ^ aux_prop_conc_fine_layer_fine_b d)
    (Cd * rs ^ aux_prop_conc_fine_layer_fine_b d) hAs hAs hcb hπ p Cp hp
    (hESc (fun i : Fin mm => (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure.map
      (fun y => aux_lem_15_u_localize 0 ell w (idx i) y)))
    (Cm * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12)))
    (Cm * model.delta ^ 2 * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12)))
    (by positivity) (by positivity) hIa hIe hMa hMe
  rw [← hcAdef] at hfib
  have hglob := aux_prop_conc_fine_layer_fine_global d model P field hD.hfield hD.hlaw zcell r j f Kt
    hD.hf hKt p Cp (by linarith)
    (fun s K => aux_prop_conc_fine_fibre_es_env1 Cex (M - m) (Cd * rs ^ aux_prop_conc_fine_layer_fine_b d) cA s K)
    (fun s K => aux_prop_conc_fine_fibre_es_env2 Cex (M - m) (Cd * rs ^ aux_prop_conc_fine_layer_fine_b d)
      (Cd * rs ^ aux_prop_conc_fine_layer_fine_b d) (Cm * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12)))
      (Cm * model.delta ^ 2 * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12))) s K)
    (by unfold aux_prop_conc_fine_fibre_es_env1; fun_prop)
    (by unfold aux_prop_conc_fine_fibre_es_env2; fun_prop) hfib
  have hSm : Measurable (fun eta : BilateralField d =>
      aux_prop_conc_fine_fibre_det_S zcell r (eta j)) :=
    (aux_lem_15_u_supn_continuous _ _).measurable.comp (measurable_pi_apply j)
  have hK0' : ∀ᵐ eta ∂(chaosSampleLaw model).toMeasure, 0 ≤ Kt eta := by
    filter_upwards [hKtae, hD.hK0] with eta h1 h2
    rw [← h1]; exact h2
  have hKB' : eLpNorm Kt (ENNReal.ofReal (2 * p)) (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal B := by
    rw [← eLpNorm_congr_ae hKtae]; exact hD.hKB
  have hLE := prop_conc_fine_layer_env (chaosSampleLaw model).toMeasure
    (fun eta : BilateralField d => aux_prop_conc_fine_fibre_det_S zcell r (eta j)) Kt
    hSm.aestronglyMeasurable hKt.aestronglyMeasurable
    (fun eta => aux_prop_conc_fine_fibre_det_S_nonneg zcell r _) hK0' p (by linarith) Cex (M - m)
    (Cd * rs ^ aux_prop_conc_fine_layer_fine_b d) (Cd * rs ^ aux_prop_conc_fine_layer_fine_b d)
    (Cm * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12)))
    (Cm * model.delta ^ 2 * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12))) cA B
    (Cm * model.delta * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12)))
    (Cm * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12))) hCex.le hgap hAs hAs (by positivity)
    (by positivity) hcA0 hB0 (by positivity) (by positivity) hKB' ha hb' hc'
  obtain ⟨hLE1, hLE2⟩ := hLE
  have hnum := prop_conc_fine_layer_num rs (aux_prop_conc_fine_layer_fine_b d) Cex Cm B Cd cA Cp model.delta
    (M - m) hrs0 hrs1 hb hCex.le hCm.le hB0 hCd.le hcA0 hCp.le hδ0.le hgap
  refine hglob.trans ?_
  calc 2 * eLpNorm (fun eta : BilateralField d => aux_prop_conc_fine_fibre_es_env1 Cex (M - m)
          (Cd * rs ^ aux_prop_conc_fine_layer_fine_b d) cA
          (aux_prop_conc_fine_fibre_det_S zcell r (eta j)) (Kt eta)) (ENNReal.ofReal p)
          (chaosSampleLaw model).toMeasure +
        2 * ENNReal.ofReal Cp * eLpNorm (fun eta : BilateralField d => aux_prop_conc_fine_fibre_es_env2 Cex
          (M - m) (Cd * rs ^ aux_prop_conc_fine_layer_fine_b d) (Cd * rs ^ aux_prop_conc_fine_layer_fine_b d)
          (Cm * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12)))
          (Cm * model.delta ^ 2 * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12)))
          (aux_prop_conc_fine_fibre_det_S zcell r (eta j)) (Kt eta)) (ENNReal.ofReal p)
          (chaosSampleLaw model).toMeasure
      ≤ 2 * ENNReal.ofReal (Cex * (M - m) * (Cd * rs ^ aux_prop_conc_fine_layer_fine_b d +
            cA * Real.sqrt (Cd * rs ^ aux_prop_conc_fine_layer_fine_b d)) *
            ((Cm * model.delta * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12))) * (1 + B))) +
        2 * ENNReal.ofReal Cp * ENNReal.ofReal ((Real.sqrt (2 * (Cex + Cex)) * Cex * Real.sqrt Cex *
            Real.sqrt 2 * (M - m) * Real.sqrt (Cd * rs ^ aux_prop_conc_fine_layer_fine_b d +
              Cd * rs ^ aux_prop_conc_fine_layer_fine_b d)) *
          ((Real.sqrt (Cm * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12))) *
              (Cm * model.delta * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12))) +
            Real.sqrt (Cm * model.delta ^ 2 * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12))) *
              (Cm * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12)))) * (1 + B))) := by
        gcongr
    _ = ENNReal.ofReal (2 * (Cex * (M - m) * (Cd * rs ^ aux_prop_conc_fine_layer_fine_b d +
            cA * Real.sqrt (Cd * rs ^ aux_prop_conc_fine_layer_fine_b d)) *
            ((Cm * model.delta * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12))) * (1 + B))) +
        2 * Cp * ((Real.sqrt (2 * (Cex + Cex)) * Cex * Real.sqrt Cex *
            Real.sqrt 2 * (M - m) * Real.sqrt (Cd * rs ^ aux_prop_conc_fine_layer_fine_b d +
              Cd * rs ^ aux_prop_conc_fine_layer_fine_b d)) *
          ((Real.sqrt (Cm * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12))) *
              (Cm * model.delta * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12))) +
            Real.sqrt (Cm * model.delta ^ 2 * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12))) *
              (Cm * rs ^ (-(aux_prop_conc_fine_layer_fine_b d / 12)))) * (1 + B)))) := by
        exact aux_prop_conc_fine_layer_fine_enn _ _ _ (by positivity) (by positivity) hCp.le
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hKfdef]
        exact hnum

end
end Paper
