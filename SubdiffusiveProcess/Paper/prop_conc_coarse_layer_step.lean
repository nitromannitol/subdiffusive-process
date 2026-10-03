module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.Paper.prop_conc_setup
public import SubdiffusiveProcess.Paper.prop_conc_pair_data
public import SubdiffusiveProcess.Paper.prop_conc_pair_mask
public import SubdiffusiveProcess.Paper.prop_conc_response_layer_version
public import SubdiffusiveProcess.Paper.prop_conc_typical_pair
public import SubdiffusiveProcess.Paper.prop_conc_weighted_identification
public import SubdiffusiveProcess.Paper.prop_conc_weighted_identification_infrared
public import SubdiffusiveProcess.Paper.prop_conc_coarse_theta_variation
public import SubdiffusiveProcess.Paper.prop_conc_layer_oscillation_moments
public import SubdiffusiveProcess.Paper.prop_conc_coarse_layer_holder
public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane3.Interfaces
public import SubdiffusiveProcess.Lane2.ExternalInputs
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.ScaledLayerLaw
public import Mathlib.Tactic

@[expose] public section

/-! Step 3 of `prop-conc`, coarse layers (wavelength larger than the cell side): the anchored oscillation of the
resampled layer over the observation cell is `O(δ 3^{-(j+k)})` with sub-Gaussian tails, and by the relative variation
estimate (30) with `B = q` (retaining `Δ = M - m`) it changes the relative response by at most
`C S e^{CS} Δ`.  The identification of the response at the resampled configuration with the weighted pair of the
original configuration is `prop_conc_weighted_identification` (layers `j ≤ 0`) and its infrared sibling (`j ≥ 1`). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

section aux

/-- Pointwise deterministic bound: the two layer values `h₁` (original) and `h₂` (resampled) change the
relative response of a pair on the cell by `(A₁ + A₂) · C_D Δ e^{C_D (A₁ + A₂)}`, `A_i` the anchored
oscillation of `h_i` on a ball of radius `R ≥ r/2` about the cell center. -/
theorem aux_prop_conc_coarse_layer_step_pointwise (C0 : ℝ) (hC0 : 1 ≤ C0) (d : ℕ) :
    ∃ CD : ℝ, 0 < CD ∧
    ∀ {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
      {m M : ℝ} (X : prop_conc_pair_data Q z r hr C0 m M) (c : ℝ), c ∈ Icc m M →
      ∀ p ∈ aux_prop_conc_pair_data_slopes d, ∀ (R : ℝ), r / 2 ≤ R →
      ∀ (h1 h2 : C(SpatialCoordinates d, ℝ)),
        |aux_prop_conc_pair_data_theta X c p (fun x => h2 x - h1 x) -
            aux_prop_conc_pair_data_theta X c p (fun _ => 0)| ≤
          (aux_lane4_reference_oscillation_moments_localA z R h1 +
              aux_lane4_reference_oscillation_moments_localA z R h2) *
            (CD * (M - m) * Real.exp (CD * (aux_lane4_reference_oscillation_moments_localA z R h1 +
              aux_lane4_reference_oscillation_moments_localA z R h2))) := by
  obtain ⟨C, hC, hvar⟩ := prop_conc_coarse_theta_variation C0 hC0 d
  refine ⟨C, hC, ?_⟩
  intro Q z r hr m M X c hc p hp R hR h1 h2
  have hloc : ∀ (h : C(SpatialCoordinates d, ℝ)) (x : SpatialCoordinates d),
      dist x z ≤ R → |h x - h z| ≤ aux_lane4_reference_oscillation_moments_localA z R h := by
    intro h x hx
    have hxK : x ∈ (aux_lane4_reference_oscillation_moments_Kball z R : Set (SpatialCoordinates d)) := by
      change x ∈ Metric.closedBall z R
      exact hx
    have h1 : ‖(h.restrict (aux_lane4_reference_oscillation_moments_Kball z R : Set (SpatialCoordinates d)) -
        ContinuousMap.const (aux_lane4_reference_oscillation_moments_Kball z R) (h z)) ⟨x, hxK⟩‖ ≤
        aux_lane4_reference_oscillation_moments_localA z R h :=
      ContinuousMap.norm_coe_le_norm _ _
    have h2 : (h.restrict (aux_lane4_reference_oscillation_moments_Kball z R : Set (SpatialCoordinates d)) -
        ContinuousMap.const (aux_lane4_reference_oscillation_moments_Kball z R) (h z)) ⟨x, hxK⟩ =
        h x - h z := rfl
    rw [h2, Real.norm_eq_abs] at h1
    exact h1
  set S : ℝ := aux_lane4_reference_oscillation_moments_localA z R h1 +
    aux_lane4_reference_oscillation_moments_localA z R h2 with hS
  have hS0 : 0 ≤ S := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hgS : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      |(h2 x - h1 x) - (h2 z - h1 z)| ≤ S := by
    intro x hx
    have hxd : dist x z ≤ R := by
      have : dist x z < r / 2 := by simpa [centeredCube] using hx
      linarith
    have e1 := hloc h1 x hxd
    have e2 := hloc h2 x hxd
    calc |(h2 x - h1 x) - (h2 z - h1 z)| = |(h2 x - h2 z) - (h1 x - h1 z)| := by ring_nf
      _ ≤ |h2 x - h2 z| + |h1 x - h1 z| := abs_sub _ _
      _ ≤ S := by rw [hS]; linarith
  have hm : Measurable (fun x => h2 x - h1 x) :=
    (h2.continuous.sub h1.continuous).measurable
  have h := hvar X c hc p hp (fun x => h2 x - h1 x) hm (h2 z - h1 z) S hS0 hgS
  calc _ ≤ C * S * Real.exp (C * S) * (M - m) := h
    _ = _ := by ring

/-- The `j`-th coordinate of the chaos sample law is the scaled layer law. -/
theorem aux_prop_conc_coarse_layer_step_eval {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℤ) :
    MeasurePreserving (fun eta : BilateralField d => eta j) (chaosSampleLaw model).toMeasure
      (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure :=
  measurePreserving_eval_infinitePi
    (fun n => (scaledLayerLaw d (chaosRootFieldLaw model) n : Measure C(SpatialCoordinates d, ℝ))) j

/-- A statement for a.e. `omega` of `P` and a.e. layer draw `y` transfers along the layer pair to `μ ⊗ μ`. -/
theorem aux_prop_conc_coarse_layer_step_transfer
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] (P : Measure Ω) [IsProbabilityMeasure P]
    (laws : ℤ → Measure X) [∀ i, IsProbabilityMeasure (laws i)]
    (field : Ω → (ℤ → X)) (hfield : Measurable field)
    (hmap : Measure.map field P = Measure.infinitePi laws) (j : ℤ)
    (Φ : (ℤ → X) → X → Prop) (hΦ : MeasurableSet {w : (ℤ → X) × X | Φ w.1 w.2})
    (h : ∀ᵐ omega ∂P, ∀ᵐ y ∂(laws j), Φ (field omega) y) :
    ∀ᵐ q ∂((Measure.infinitePi laws).prod (Measure.infinitePi laws)), Φ q.1 (q.2 j) := by
  have hT : Measurable (Prod.map field (id : X → X)) := hfield.prodMap measurable_id
  have hprod : ∀ᵐ z ∂(P.prod (laws j)), Φ (field z.1) z.2 := by
    have hset : MeasurableSet {z : Ω × X | Φ (field z.1) z.2} := hT hΦ
    rw [Measure.ae_prod_iff_ae_ae hset]
    exact h
  have hmapeq : (P.prod (laws j)).map (Prod.map field (id : X → X)) =
      (Measure.infinitePi laws).prod (laws j) := by
    rw [← Measure.map_prod_map _ _ hfield measurable_id, hmap, Measure.map_id]
  have h2 : ∀ᵐ w ∂((Measure.infinitePi laws).prod (laws j)), Φ w.1 w.2 := by
    rw [← hmapeq, ae_map_iff hT.aemeasurable hΦ]
    exact hprod
  have hE : Measurable (fun eta : ℤ → X => eta j) := measurable_pi_apply j
  have hmapeq2 : ((Measure.infinitePi laws).prod (Measure.infinitePi laws)).map
      (Prod.map (id : (ℤ → X) → (ℤ → X)) (fun eta : ℤ → X => eta j)) =
      (Measure.infinitePi laws).prod (laws j) := by
    rw [← Measure.map_prod_map _ _ measurable_id hE, Measure.map_id,
      (measurePreserving_eval_infinitePi laws j).map_eq]
  have hT2 : Measurable (Prod.map (id : (ℤ → X) → (ℤ → X)) (fun eta : ℤ → X => eta j)) :=
    measurable_id.prodMap hE
  rw [← hmapeq2, ae_map_iff hT2.aemeasurable hΦ] at h2
  exact h2

end aux

/-- Step 3, coarse side: for layers `j` coarser than the level-`k` cell (`0 < j + k`), resampling layer `j` moves
every measurable version `f` of the relative response by at most `C δ Δ 3^{-(j+k)}` in `L^p`. -/
theorem prop_conc_coarse_layer_step
    (d : ℕ) (hd : 2 ≤ d)
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (_MeyersMorrey : SubdiffusiveProcess.Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (Ccamp : SubdiffusiveProcess.Lane4.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd) :
      ∀ (C0 : ℝ) (hC0 : 1 ≤ C0),
      ∀ (p : ℝ) (hp : 2 ≤ p),
      ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
        (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace
          (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ) (m M : ℝ)
        (zcell : SpatialCoordinates d) (k : ℕ) (cellIdx paddedIdx : ℕ)
        (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity)),
          ‖(u : SobolevData
              (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))).1‖ ≤
            K * ‖subspaceGradient
              (killedSobolevGraph
                (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))) u‖)
        (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
        (hyps : prop_conc_setup d model H Ω P field z r hr Sspace GN GE GF NE NF C0 m M
          zcell k cellIdx paddedIdx hPk AE AF),
      ∀ c ∈ Icc m M, ∀ (pvec : Fin d → ℝ),
        ((∃ i : Fin d, pvec = (Pi.single i (1 : ℝ) : Fin d → ℝ)) ∨
          (∃ i j : Fin d, pvec = (Pi.single i (1 : ℝ) : Fin d → ℝ) +
            (Pi.single j (1 : ℝ) : Fin d → ℝ))) →
      ∀ f : BilateralField d → ℝ, Measurable f →
        ((fun omega => (pvec ⬝ᵥ (AF omega).mulVec pvec -
            c * (pvec ⬝ᵥ (AE omega).mulVec pvec)) / Matrix.trace (AE omega)) =ᵐ[P]
          f ∘ field) →
        ∀ j : ℤ, 0 < j + (k : ℤ) →
          eLpNorm (fun q : BilateralField d × BilateralField d =>
              f q.1 - f (Function.update q.1 j (q.2 j))) (ENNReal.ofReal p)
            ((chaosSampleLaw model).toMeasure.prod (chaosSampleLaw model).toMeasure) ≤
          ENNReal.ofReal (C * model.delta * (M - m) *
            (3 : ℝ) ^ (-(1 : ℝ) * ((j + (k : ℤ)).natAbs : ℝ))) := by
  intro C0 hC0 p hp
  obtain ⟨CD, hCD, hpw⟩ := aux_prop_conc_coarse_layer_step_pointwise C0 hC0 d
  obtain ⟨C1, hC1, hosc⟩ := prop_conc_layer_oscillation_moments d hd
  have hTyAll := prop_conc_typical_pair d hd I _X _Sob _MeyersMorrey Pin Ccamp Interp
    ((d : ℝ) - 1 / 2) 1 (by linarith) (by linarith) le_rfl C0 hC0
  obtain ⟨δT, BT, hδT, hBT, hTy⟩ := hTyAll
  have hWIall := prop_conc_weighted_identification d hd I _X _Sob _MeyersMorrey Pin Ccamp Interp
  obtain ⟨δW, hδW, hWI⟩ := hWIall
  have hWHall :=
    prop_conc_weighted_identification_infrared d hd I _X _Sob _MeyersMorrey Pin Ccamp Interp
  obtain ⟨δH, hδH, hWH⟩ := hWHall
  refine ⟨min (min δT δW) (min δH 1),
    4 * C1 * Real.sqrt (2 * p) * CD * Real.exp (C1 ^ 2 * (4 * p * CD) ^ 2 / 4),
    lt_min (lt_min hδT hδW) (lt_min hδH one_pos), by positivity, ?_⟩
  intro inst1 inst2 model hmodel Rm Sreg It H Ω inst3 P field z r hr Sspace GN GE GF NE NF m M
    zcell k cellIdx paddedIdx hPk AE AF hyps c hc pvec hpvec f hfm hfae j hj
  have hδT' : model.delta ≤ δT := hmodel.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδW' : model.delta ≤ δW := hmodel.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδH' : model.delta ≤ δH := hmodel.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : model.delta ≤ 1 := hmodel.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδpos : 0 < model.delta := model.shellPrefix.delta_pos
  have hJ := hyps.1
  haveI : IsProbabilityMeasure P := hJ.1
  have hfieldm : Measurable field := hJ.2.1
  have hmap : Measure.map field P = (chaosSampleLaw model).toMeasure := hJ.2.2.1
  have hTy' := hTy model hδT' Rm Sreg It H Ω P field z r hr Sspace GN GE GF NE NF m M zcell k
    cellIdx paddedIdx hPk AE AF hyps
  obtain ⟨K, -, -, -, hYae⟩ := hTy'
  have hWIj : ∀ᵐ omega ∂P,
      ∀ Y : prop_conc_pair_data
          (centeredCube (z paddedIdx) (r paddedIdx) (hr paddedIdx))
          zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity) C0 m M,
        (∀ u, Y.E.toClosedForm.energy u = limitFormEnergy (GE paddedIdx omega) u) →
        (∀ u, Y.F.toClosedForm.energy u = limitFormEnergy (GF paddedIdx omega) u) →
        aux_prop_conc_pair_data_affine Y →
        ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure,
          f (Function.update (field omega) j y) =
            aux_prop_conc_pair_data_theta Y c pvec (fun x => y x - (field omega) j x) := by
    by_cases hj0 : j ≤ 0
    · exact hWI model hδW' Rm Sreg It H Ω P field z r hr Sspace GN GE GF NE NF C0 m M hC0 zcell k
        cellIdx paddedIdx hPk AE AF hyps c pvec f hfm hfae j hj0
    · exact hWH model hδH' Rm Sreg It H Ω P field z r hr Sspace GN GE GF NE NF C0 m M hC0 zcell k
        cellIdx paddedIdx hPk AE AF hyps c pvec f hfm hfae j (by omega)
  have hvolpos : 0 < (volume (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity) :
      Set (SpatialCoordinates d))).toReal := by
    rw [centeredCube_volume, ENNReal.toReal_ofReal (by positivity)]; positivity
  have hr3 : (3 : ℝ) ^ (-(k : ℝ)) = (3 : ℝ) ^ (-(k : ℤ)) := by
    rw [zpow_neg, zpow_natCast, Real.rpow_neg (by norm_num), Real.rpow_natCast]
  have hslope : pvec ∈ aux_prop_conc_pair_data_slopes d :=
    (aux_prop_conc_pair_data_mem_slopes d pvec).2 hpvec
  have hgap : 0 ≤ M - m := by linarith [hc.1, hc.2]
  have hRk : (3 : ℝ) ^ (-(k : ℝ)) / 2 ≤ (3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ)) := by
    rw [hr3]; have : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)) := by positivity
    linarith
  have hae : ∀ᵐ omega ∂P, ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure,
      |f (field omega) - f (Function.update (field omega) j y)| ≤
        (aux_lane4_reference_oscillation_moments_localA zcell ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ)))
            ((field omega) j) +
          aux_lane4_reference_oscillation_moments_localA zcell ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) y) *
          (CD * (M - m) * Real.exp (CD *
            (aux_lane4_reference_oscillation_moments_localA zcell
                ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) ((field omega) j) +
              aux_lane4_reference_oscillation_moments_localA zcell
                ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) y))) := by
    filter_upwards [hYae, hWIj, hfae] with omega hY hW hf
    obtain ⟨Y, hYE, hYF, hYQ, hYaff, -⟩ := hY
    filter_upwards [hW Y hYE hYF hYaff] with y hy
    have hθ0 : f (field omega) = aux_prop_conc_pair_data_theta Y c pvec (fun _ => 0) := by
      have hsumQ : ∑ i : Fin d, Y.P.QE (Pi.single i 1) =
          (volume (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity) :
            Set (SpatialCoordinates d))).toReal * Matrix.trace (AE omega) := by
        simp_rw [fun i : Fin d => (hYQ (Pi.single i 1)).1]
        rw [← Finset.mul_sum, aux_prop_conc_response_layer_version_trace]
      have hf' : f (field omega) = (pvec ⬝ᵥ (AF omega).mulVec pvec -
          c * (pvec ⬝ᵥ (AE omega).mulVec pvec)) / Matrix.trace (AE omega) := hf.symm
      rw [aux_prop_conc_pair_mask_theta_zero, hsumQ, (hYQ pvec).1, (hYQ pvec).2, hf']
      rw [show ∀ vol aF aE : ℝ, vol * aF - c * (vol * aE) = vol * (aF - c * aE) from
        fun vol aF aE => by ring, mul_div_mul_left _ _ hvolpos.ne']
    rw [hy, hθ0, abs_sub_comm]
    exact hpw Y c hc pvec hslope _ hRk ((field omega) j) y
  have hΦ : MeasurableSet {w : BilateralField d × C(SpatialCoordinates d, ℝ) |
      |f w.1 - f (Function.update w.1 j w.2)| ≤
        (aux_lane4_reference_oscillation_moments_localA zcell ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) (w.1 j) + aux_lane4_reference_oscillation_moments_localA zcell ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) w.2) * (CD * (M - m) * Real.exp (CD * (aux_lane4_reference_oscillation_moments_localA zcell ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) (w.1 j) + aux_lane4_reference_oscillation_moments_localA zcell ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) w.2)))} := by
    have hAm : Measurable (aux_lane4_reference_oscillation_moments_localA zcell ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) : C(SpatialCoordinates d, ℝ) → ℝ) :=
      (aux_prop_conc_layer_oscillation_moments_localA_continuous zcell _).measurable
    have hupd : Measurable (fun w : BilateralField d × C(SpatialCoordinates d, ℝ) =>
        Function.update w.1 j w.2) := measurable_update'
    have h1 : Measurable (fun w : BilateralField d × C(SpatialCoordinates d, ℝ) =>
        |f w.1 - f (Function.update w.1 j w.2)|) :=
      continuous_abs.measurable.comp ((hfm.comp measurable_fst).sub (hfm.comp hupd))
    have hAj : Measurable (fun w : BilateralField d × C(SpatialCoordinates d, ℝ) => aux_lane4_reference_oscillation_moments_localA zcell ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) (w.1 j)) :=
      hAm.comp ((measurable_pi_apply j).comp measurable_fst)
    have hAy : Measurable (fun w : BilateralField d × C(SpatialCoordinates d, ℝ) => aux_lane4_reference_oscillation_moments_localA zcell ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) w.2) :=
      hAm.comp measurable_snd
    exact measurableSet_le h1
      ((hAj.add hAy).mul (measurable_const.mul (measurable_const.mul (hAj.add hAy)).exp))
  have hae2 := aux_prop_conc_coarse_layer_step_transfer P
    (fun n => (scaledLayerLaw d (chaosRootFieldLaw model) n : Measure C(SpatialCoordinates d, ℝ)))
    field hfieldm hmap j
    (fun eta y => |f eta - f (Function.update eta j y)| ≤
      (aux_lane4_reference_oscillation_moments_localA zcell ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) (eta j) + aux_lane4_reference_oscillation_moments_localA zcell ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) y) * (CD * (M - m) * Real.exp (CD * (aux_lane4_reference_oscillation_moments_localA zcell ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) (eta j) + aux_lane4_reference_oscillation_moments_localA zcell ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) y)))) hΦ hae
  obtain ⟨hAm, hLp, hExp⟩ := hosc model zcell k j hj
  obtain ⟨nn, hnn⟩ : ∃ nn : ℕ, nn = (j + (k : ℤ)).natAbs := ⟨_, rfl⟩
  rw [← hnn] at hLp hExp
  have hapos : 0 ≤ model.delta * ((3 : ℝ) ^ nn)⁻¹ := by positivity
  have ha1 : model.delta * ((3 : ℝ) ^ nn)⁻¹ ≤ 1 := by
    have : ((3 : ℝ) ^ nn)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    nlinarith
  have hLp' : ∀ p' : ℝ≥0∞, p' ≠ ⊤ → 2 ≤ p' →
      eLpNorm (fun eta : BilateralField d => aux_lane4_reference_oscillation_moments_localA zcell ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) (eta j)) p' (chaosSampleLaw model).toMeasure ≤
        ENNReal.ofReal (C1 * (model.delta * ((3 : ℝ) ^ nn)⁻¹) * Real.sqrt p'.toReal) := by
    intro p' h1 h2
    have := hLp p' h1 h2
    rw [show C1 * (model.delta * ((3 : ℝ) ^ nn)⁻¹) * Real.sqrt p'.toReal =
      C1 * model.delta * ((3 : ℝ) ^ nn)⁻¹ * Real.sqrt p'.toReal by ring]
    exact this
  have hExp' : ∀ lam : ℝ, 0 ≤ lam →
      ∫⁻ eta : BilateralField d, ENNReal.ofReal (Real.exp (lam * aux_lane4_reference_oscillation_moments_localA zcell ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) (eta j)))
          ∂(chaosSampleLaw model).toMeasure ≤
        ENNReal.ofReal (2 * Real.exp
          ((C1 * (model.delta * ((3 : ℝ) ^ nn)⁻¹)) ^ 2 * lam ^ 2 / 4)) := by
    intro lam hlam
    have := hExp lam hlam
    rw [show (C1 * (model.delta * ((3 : ℝ) ^ nn)⁻¹)) ^ 2 =
      (C1 * model.delta * ((3 : ℝ) ^ nn)⁻¹) ^ 2 by ring]
    exact this
  have hH := prop_conc_coarse_layer_holder (chaosSampleLaw model).toMeasure
    (fun eta : BilateralField d => aux_lane4_reference_oscillation_moments_localA zcell ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) (eta j)) hAm C1
    (model.delta * ((3 : ℝ) ^ nn)⁻¹) hC1 hapos ha1 hLp' hExp' p CD (M - m) hp hCD hgap
    (fun q => f q.1 - f (Function.update q.1 j (q.2 j))) hae2
  have hupdPair : Measurable (fun q : BilateralField d × BilateralField d =>
      Function.update q.1 j (q.2 j)) :=
    measurable_update'.comp
      (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have hDm : Measurable (fun q : BilateralField d × BilateralField d =>
      f q.1 - f (Function.update q.1 j (q.2 j))) :=
    (hfm.comp measurable_fst).sub (hfm.comp hupdPair)
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hDm.aestronglyMeasurable] at hH
  refine hH.trans (le_of_eq ?_)
  congr 1
  have h3 : (3 : ℝ) ^ (-(1 : ℝ) * (nn : ℝ)) = ((3 : ℝ) ^ nn)⁻¹ := by
    rw [neg_one_mul, Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [← hnn, h3]
  ring

end
end Paper
