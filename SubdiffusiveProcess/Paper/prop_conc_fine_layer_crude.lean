import SubdiffusiveProcess.Paper.prop_conc_fine_layer_fine
import SubdiffusiveProcess.Paper.prop_conc_fine_fibre_crude

/-! The crude case of the fine-layer step: for the finitely many relative wavelengths `3^{-n} > r0` the
resampling difference is bounded by the layer-norm loss alone, `K δ (M - m) (3^{-n})^{-2γ}`, `γ = b/12`
(relative variation with `B = q`); no grid, growth constant or Efron--Stein inequality is used. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology
namespace Paper
noncomputable section

theorem aux_prop_conc_fine_layer_crude_env_meas (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (zcell : SpatialCoordinates d) (r : ℝ) (j : ℤ) (CL gap : ℝ) :
    Measurable (fun p : BilateralField d × BilateralField d =>
      aux_prop_conc_fine_fibre_crude_env CL gap (aux_prop_conc_fine_fibre_det_S zcell r (p.2 j))
        (aux_prop_conc_fine_fibre_det_S zcell r (p.1 j))) := by
  have hS : Measurable (fun eta : BilateralField d => aux_prop_conc_fine_fibre_det_S zcell r (eta j)) :=
    (aux_lem_15_u_supn_continuous _ _).measurable.comp (measurable_pi_apply j)
  have hF : Continuous (fun sK : ℝ × ℝ => aux_prop_conc_fine_fibre_crude_env CL gap sK.1 sK.2) := by
    unfold aux_prop_conc_fine_fibre_crude_env; fun_prop
  exact hF.measurable.comp ((hS.comp measurable_snd).prodMk (hS.comp measurable_fst))

theorem prop_conc_fine_layer_crude (d : ℕ) (hd : 2 ≤ d) (C0 : ℝ) (hC0 : 1 ≤ C0) (p : ℝ) (hp : 2 ≤ p)
    (B : ℝ) :
    ∃ Kc : ℝ, 0 < Kc ∧
    ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
      (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (field : Ω → BilateralField d) (m M : ℝ) (Q : Opens (SpatialCoordinates d))
      (zcell : SpatialCoordinates d) (k : ℕ) (r : ℝ) (hr : 0 < r) (_hrk : r = (3 : ℝ) ^ (-(k : ℝ)))
      (c : ℝ), c ∈ Set.Icc m M →
      ∀ (pvec : Fin d → ℝ), pvec ∈ aux_prop_conc_pair_data_slopes d →
      ∀ (f K : BilateralField d → ℝ) (j : ℤ) (n : ℕ), j = -((n + k : ℕ) : ℤ) →
        prop_conc_fine_layer_data d model C0 m M Q zcell r hr c pvec (aux_prop_conc_fine_layer_fine_t d)
          p B P field f K j →
        eLpNorm (fun q : BilateralField d × BilateralField d => f q.1 - f (Function.update q.1 j (q.2 j)))
            (ENNReal.ofReal p)
            ((chaosSampleLaw model).toMeasure.prod (chaosSampleLaw model).toMeasure) ≤
          ENNReal.ofReal (Kc * model.delta * (M - m) *
            (((3 : ℝ) ^ (-(n : ℝ))) ^ (-(aux_prop_conc_fine_layer_fine_b d / 12))) ^ 2) := by
  obtain ⟨CL, hCL, hCR⟩ := prop_conc_fine_fibre_crude C0 hC0 d
  have hb : (0 : ℝ) < aux_prop_conc_fine_layer_fine_b d / 12 := by
    have hd1 : 1 ≤ d := by omega
    have ht1 : (d : ℝ) - 1 < aux_prop_conc_fine_layer_fine_t d := by
      unfold aux_prop_conc_fine_layer_fine_t; have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      linarith
    have := (show (0 : ℝ) < aux_prop_conc_fine_layer_fine_t d * (aux_prop_conc_fine_layer_fine_t d -
      (d : ℝ) + 1) / (aux_prop_conc_fine_layer_fine_t d + 1) by
        unfold aux_prop_conc_fine_layer_fine_t
        have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
        have h2 : (0 : ℝ) < (d : ℝ) - 1 / 2 := by linarith
        have h3 : (0 : ℝ) < (d : ℝ) - 1 / 2 - d + 1 := by linarith
        positivity)
    unfold aux_prop_conc_fine_layer_fine_b; linarith
  have h2p : 0 < 2 * p := by linarith
  obtain ⟨C1, hC1, hM1⟩ := prop_conc_fine_layer_mom d hd (2 * p) 1 CL (aux_prop_conc_fine_layer_fine_b d / 12)
    h2p (by norm_num) hCL.le hb
  obtain ⟨C2, hC2, hM2⟩ := prop_conc_fine_layer_mom d hd (2 * p) 0 CL (aux_prop_conc_fine_layer_fine_b d / 12)
    h2p (le_refl _) hCL.le hb
  refine ⟨4 * CL * (max C1 C2) ^ 2, by positivity, ?_⟩
  intro _ _ model Ω _ P field m M Q zcell k r hr hrk c hc pvec hpvec f K j n hj hD
  haveI := hD.hP
  have hδ0 : 0 < model.delta := model.shellPrefix.delta_pos
  have hgap : 0 ≤ M - m := sub_nonneg.mpr (hc.1.trans hc.2)
  set Cm : ℝ := max C1 C2 with hCm
  have hCm0 : 0 < Cm := lt_max_of_lt_left hC1
  set R : ℝ := ((3 : ℝ) ^ (-(n : ℝ))) ^ (-(aux_prop_conc_fine_layer_fine_b d / 12)) with hR
  have hR0 : 0 < R := by positivity
  set Lj : Measure C(SpatialCoordinates d, ℝ) := (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure with hLj
  haveI : IsProbabilityMeasure Lj := inferInstance
  have hm1 := (hM1 model zcell k n r hrk j hj).2
  have hm2 := (hM2 model zcell k n r hrk j hj).2
  simp only [Real.rpow_one] at hm1
  simp only [Real.rpow_zero, one_mul, mul_one] at hm2
  have hL1 : eLpNorm (fun y : C(SpatialCoordinates d, ℝ) => aux_prop_conc_fine_fibre_det_S zcell r y *
      Real.exp (CL * aux_prop_conc_fine_fibre_det_S zcell r y)) (ENNReal.ofReal (2 * p)) Lj ≤
      ENNReal.ofReal (Cm * model.delta * R) :=
    hm1.trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _))
  have hL0 : eLpNorm (fun y : C(SpatialCoordinates d, ℝ) =>
      Real.exp (CL * aux_prop_conc_fine_fibre_det_S zcell r y)) (ENNReal.ofReal (2 * p)) Lj ≤
      ENNReal.ofReal (Cm * R) :=
    hm2.trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_right _ _))
  -- the fibre inequality
  set laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun i => (scaledLayerLaw d (chaosRootFieldLaw model) i : Measure C(SpatialCoordinates d, ℝ)) with hlaws
  haveI : ∀ i, IsProbabilityMeasure (laws i) := fun i => inferInstance
  have hμ : (chaosSampleLaw model).toMeasure = Measure.infinitePi laws := rfl
  set G : BilateralField d × BilateralField d → ℝ := fun q => aux_prop_conc_fine_fibre_crude_env CL (M - m)
    (aux_prop_conc_fine_fibre_det_S zcell r (q.2 j)) (aux_prop_conc_fine_fibre_det_S zcell r (q.1 j)) with hG
  have hGm : Measurable G := aux_prop_conc_fine_layer_crude_env_meas d zcell r j CL (M - m)
  have hFT := prop_conc_fine_fibre laws j P field hD.hfield (by rw [← hμ]; exact hD.hlaw) f hD.hf p (by linarith)
    (fun eta eta' => aux_prop_conc_fine_fibre_crude_env CL (M - m)
      (aux_prop_conc_fine_fibre_det_S zcell r (eta' j)) (aux_prop_conc_fine_fibre_det_S zcell r (eta j)))
    (fun eta eta' => aux_prop_conc_fine_fibre_crude_env CL (M - m)
      (aux_prop_conc_fine_fibre_det_S zcell r (eta' j)) (aux_prop_conc_fine_fibre_det_S zcell r (eta j)))
    hGm hGm 2 0 ?_
  · -- the final bound
    have hU := SubdiffusiveProcess.Probability.measurePreserving_update_infinitePi laws j
    have e1 : eLpNorm (fun q : (ℤ → C(SpatialCoordinates d, ℝ)) × (ℤ → C(SpatialCoordinates d, ℝ)) =>
        aux_prop_conc_fine_fibre_crude_env CL (M - m)
          (aux_prop_conc_fine_fibre_det_S zcell r ((Function.update q.1 j (q.2 j)) j))
          (aux_prop_conc_fine_fibre_det_S zcell r (q.1 j))) (ENNReal.ofReal p)
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) =
        eLpNorm (fun q : BilateralField d × BilateralField d =>
          aux_prop_conc_fine_fibre_crude_env CL (M - m)
            (aux_prop_conc_fine_fibre_det_S zcell r (q.2 j))
            (aux_prop_conc_fine_fibre_det_S zcell r (q.1 j))) (ENNReal.ofReal p)
          ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) := by
      simp only [Function.update_self]
    simp only [zero_mul, add_zero] at hFT
    rw [e1] at hFT
    have hSm : Measurable (fun y : C(SpatialCoordinates d, ℝ) => aux_prop_conc_fine_fibre_det_S zcell r y) :=
      (aux_lem_15_u_supn_continuous _ _).measurable
    have hnorm := aux_prop_conc_fine_layer_env_crude_norm Lj (fun y => aux_prop_conc_fine_fibre_det_S zcell r y)
      hSm CL (M - m) p (Cm * model.delta * R)
      (Cm * R) hCL.le hgap (by linarith) (by positivity) (by positivity) hL1 hL0
    have hmp : MeasurePreserving (Prod.map (fun eta : BilateralField d => eta j)
        (fun eta : BilateralField d => eta j)) ((Measure.infinitePi laws).prod (Measure.infinitePi laws))
        (Lj.prod Lj) :=
      MeasurePreserving.prod ⟨measurable_pi_apply j, Measure.infinitePi_map_eval laws j⟩
        ⟨measurable_pi_apply j, Measure.infinitePi_map_eval laws j⟩
    have hG' : Measurable (fun q : C(SpatialCoordinates d, ℝ) × C(SpatialCoordinates d, ℝ) =>
        (CL * (aux_prop_conc_fine_fibre_det_S zcell r q.2 + aux_prop_conc_fine_fibre_det_S zcell r q.1) *
          Real.exp (CL * (aux_prop_conc_fine_fibre_det_S zcell r q.2 + aux_prop_conc_fine_fibre_det_S zcell r q.1))) *
          (M - m)) := by
      have := (by fun_prop : Continuous (fun sK : ℝ × ℝ => (CL * (sK.1 + sK.2) * Real.exp (CL * (sK.1 + sK.2))) * (M - m)))
      exact this.measurable.comp ((hSm.comp measurable_snd).prodMk (hSm.comp measurable_fst))
    have htr : eLpNorm (fun q : BilateralField d × BilateralField d =>
          aux_prop_conc_fine_fibre_crude_env CL (M - m)
            (aux_prop_conc_fine_fibre_det_S zcell r (q.2 j))
            (aux_prop_conc_fine_fibre_det_S zcell r (q.1 j))) (ENNReal.ofReal p)
          ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤
        ENNReal.ofReal (2 * (CL * (M - m)) * ((Cm * model.delta * R) * (Cm * R))) := by
      have := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal p)
        (g := fun q : C(SpatialCoordinates d, ℝ) × C(SpatialCoordinates d, ℝ) =>
          (CL * (aux_prop_conc_fine_fibre_det_S zcell r q.2 + aux_prop_conc_fine_fibre_det_S zcell r q.1) *
            Real.exp (CL * (aux_prop_conc_fine_fibre_det_S zcell r q.2 + aux_prop_conc_fine_fibre_det_S zcell r q.1))) *
            (M - m)) hG'.aestronglyMeasurable hmp
      refine le_of_eq_of_le ?_ (this ▸ hnorm)
      rfl
    rw [hμ]
    refine hFT.trans ?_
    calc 2 * eLpNorm (fun q : BilateralField d × BilateralField d =>
          aux_prop_conc_fine_fibre_crude_env CL (M - m)
            (aux_prop_conc_fine_fibre_det_S zcell r (q.2 j))
            (aux_prop_conc_fine_fibre_det_S zcell r (q.1 j))) (ENNReal.ofReal p)
          ((Measure.infinitePi laws).prod (Measure.infinitePi laws))
        ≤ 2 * ENNReal.ofReal (2 * (CL * (M - m)) * ((Cm * model.delta * R) * (Cm * R))) := by gcongr
      _ = ENNReal.ofReal (2 * (2 * (CL * (M - m)) * ((Cm * model.delta * R) * (Cm * R)))) := by
          rw [ENNReal.ofReal_mul (p := 2) (by norm_num), ENNReal.ofReal_ofNat]
      _ = ENNReal.ofReal (4 * CL * Cm ^ 2 * model.delta * (M - m) * R ^ 2) := by
          congr 1; ring
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          exact le_refl _
  · -- the fibre hypothesis
    filter_upwards [hD.hfd] with omega hX
    obtain ⟨X, hfX, -⟩ := hX
    have hfm : Measurable (fun y : C(SpatialCoordinates d, ℝ) => f (Function.update (field omega) j y)) :=
      hD.hf.comp (measurable_update (field omega) : Measurable (Function.update (field omega) j))
    have := hCR X c hc pvec hpvec ((field omega) j) Lj (fun y => f (Function.update (field omega) j y)) hfm
      hfX p (by linarith)
    simp only [Function.update_self, zero_mul, add_zero]
    exact this

end
end Paper
