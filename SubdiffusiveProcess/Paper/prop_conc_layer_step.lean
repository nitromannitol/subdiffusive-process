module

public import SubdiffusiveProcess.Paper.prop_conc_setup
public import SubdiffusiveProcess.Paper.prop_conc_typical_pair
public import SubdiffusiveProcess.Paper.prop_conc_fine_layer_step
public import SubdiffusiveProcess.Paper.prop_conc_coarse_layer_step
public import SubdiffusiveProcess.Paper.prop_conc_response_layer_version
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
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section


/-- Step 3 (per-layer influence, paper `prop-conc` Step 3), single level `k`: a measurable layer version `f`
(`R = f ∘ field` a.s.) of the relative scalar response `R = (v·A_F v − c v·A_E v)/tr A_E`
(`c ∈ [m,M]`, `v = e_i` or `e_i+e_j`); resampling the layer `j` of the common field moves `f` by at most
`C δ Δ 3^{-a|j+k|}` in `L^p`, uniformly in `k` and the cell. -/
theorem prop_conc_layer_step
    (d : ℕ) (hd : 2 ≤ d)
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (_MeyersMorrey : SubdiffusiveProcess.Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (Ccamp : SubdiffusiveProcess.Lane4.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd)
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality) :
    ∃ aexp : ℝ, 0 < aexp ∧
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
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _)),
          ‖(u : SobolevData
              (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))).1‖ ≤
            K * ‖subspaceGradient
              (killedSobolevGraph
                (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))) u‖)
        (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
        (hyps : prop_conc_setup d model H Ω P field z r hr Sspace GN GE GF NE NF C0 m M
          zcell k cellIdx paddedIdx hPk AE AF),
      ∀ c ∈ Icc m M, ∀ (pvec : Fin d → ℝ),
        ((∃ i : Fin d, pvec = (Pi.single i (1 : ℝ) : Fin d → ℝ)) ∨
          (∃ i j : Fin d, pvec = (Pi.single i (1 : ℝ) : Fin d → ℝ) +
            (Pi.single j (1 : ℝ) : Fin d → ℝ))) →
      ∃ f : BilateralField d → ℝ, Measurable f ∧
        ((fun omega => (pvec ⬝ᵥ (AF omega).mulVec pvec -
            c * (pvec ⬝ᵥ (AE omega).mulVec pvec)) / Matrix.trace (AE omega)) =ᵐ[P]
          f ∘ field) ∧
        ∀ j : ℤ,
          eLpNorm (fun q : BilateralField d × BilateralField d =>
              f q.1 - f (Function.update q.1 j (q.2 j))) (ENNReal.ofReal p)
            ((chaosSampleLaw model).toMeasure.prod (chaosSampleLaw model).toMeasure) ≤
          ENNReal.ofReal (C * model.delta * (M - m) *
            (3 : ℝ) ^ (-aexp * ((j + (k : ℤ)).natAbs : ℝ))) := by
  obtain ⟨aF, haF, hfine⟩ :=
    prop_conc_fine_layer_step d hd I _X _Sob _MeyersMorrey Pin Ccamp Interp hES
  refine ⟨min aF 1, lt_min haF one_pos, ?_⟩
  intro C0 hC0 p hp
  obtain ⟨δF, CF, hδF, hCF, hF⟩ := hfine C0 hC0 p hp
  obtain ⟨δC, CC, hδC, hCC, hC⟩ :=
    prop_conc_coarse_layer_step d hd I _X _Sob _MeyersMorrey Pin Ccamp Interp C0 hC0 p hp
  obtain ⟨δT, BT, hδT, hBT, hTy⟩ := prop_conc_typical_pair d hd I _X _Sob _MeyersMorrey Pin
    Ccamp Interp ((d : ℝ) - 1 / 2) 1 (by linarith) (by linarith) le_rfl C0 hC0
  refine ⟨min (min δF δC) δT, max CF CC, lt_min (lt_min hδF hδC) hδT,
    lt_max_of_lt_left hCF, ?_⟩
  intro inst1 inst2 model hmodel Rm Sreg It H Ω inst3 P field z r hr Sspace GN GE GF NE NF m M
    zcell k cellIdx paddedIdx hPk AE AF hyps c hc pvec hpvec
  have hδT' : model.delta ≤ δT := hmodel.trans (min_le_right _ _)
  have hδF' : model.delta ≤ δF := hmodel.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδC' : model.delta ≤ δC := hmodel.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδpos : 0 < model.delta := model.shellPrefix.delta_pos
  have hJ := hyps.1
  have hfieldm : Measurable field := hJ.2.1
  have hmap : Measure.map field P = (chaosSampleLaw model).toMeasure := hJ.2.2.1
  have hIR := hJ.2.2.2.1
  have hfield : MeasurePreserving field P (chaosSampleLaw model).toMeasure := ⟨hfieldm, hmap⟩
  have hAEl := hyps.2.2.2.2.2.2.2.1
  have hAFl := hyps.2.2.2.2.2.2.2.2
  have hTy' := hTy model hδT' Rm Sreg It H Ω P field z r hr Sspace GN GE GF NE NF m M zcell k
    cellIdx paddedIdx hPk AE AF hyps
  obtain ⟨K, -, -, -, hYae⟩ := hTy'
  have hvolpos : 0 < (volume (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity) :
      Set (SpatialCoordinates d))).toReal := by
    rw [centeredCube_volume, ENNReal.toReal_ofReal (by positivity)]; positivity
  have htrace : ∀ᵐ om ∂P, Matrix.trace (AE om) ≠ 0 := by
    filter_upwards [hYae] with om hY
    obtain ⟨Y, -, -, hYQ, -, -⟩ := hY
    have hpos := Y.hDpos
    have hsumQ : ∑ i : Fin d, Y.P.QE (Pi.single i 1) =
        (volume (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity) :
          Set (SpatialCoordinates d))).toReal * Matrix.trace (AE om) := by
      simp_rw [fun i : Fin d => (hYQ (Pi.single i 1)).1]
      rw [← Finset.mul_sum, aux_prop_conc_response_layer_version_trace]
    rw [hsumQ] at hpos
    intro h0
    rw [h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have hv := prop_conc_response_layer_version model H zcell
    (show (0 : ℝ) < (3 : ℝ) ^ (-(k : ℝ)) by positivity) hPk hIR.1 NE NF P field hfield AE AF
    hAEl hAFl htrace c pvec
  obtain ⟨f, hfm, hfae, -, -, -⟩ := hv
  refine ⟨f, hfm, hfae, ?_⟩
  intro j
  have hgap : 0 ≤ M - m := by linarith [hc.1, hc.2]
  have hn0 : (0 : ℝ) ≤ ((j + (k : ℤ)).natAbs : ℝ) := Nat.cast_nonneg _
  have hmin1 : min aF 1 ≤ aF := min_le_left _ _
  have hmin2 : min aF 1 ≤ 1 := min_le_right _ _
  by_cases hj : j + (k : ℤ) ≤ 0
  · have h := hF model (hmodel.trans ((min_le_left _ _).trans (min_le_left _ _))) Rm Sreg It H Ω
      P field z r hr Sspace GN GE GF NE NF m M zcell k cellIdx paddedIdx hPk AE AF hyps c hc pvec
      hpvec f hfm hfae j hj
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hpow : (3 : ℝ) ^ (-aF * ((j + (k : ℤ)).natAbs : ℝ)) ≤
        (3 : ℝ) ^ (-(min aF 1) * ((j + (k : ℤ)).natAbs : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    have hcoef : CF * model.delta * (M - m) ≤ max CF CC * model.delta * (M - m) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hδpos.le) hgap
    exact mul_le_mul hcoef hpow (by positivity) (by positivity)
  · have h := hC model (hmodel.trans ((min_le_left _ _).trans (min_le_right _ _))) Rm Sreg It H Ω
      P field z r hr Sspace GN GE GF NE NF m M zcell k cellIdx paddedIdx hPk AE AF hyps c hc pvec
      hpvec f hfm hfae j (by omega)
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hpow : (3 : ℝ) ^ (-(1 : ℝ) * ((j + (k : ℤ)).natAbs : ℝ)) ≤
        (3 : ℝ) ^ (-(min aF 1) * ((j + (k : ℤ)).natAbs : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    have hcoef : CC * model.delta * (M - m) ≤ max CF CC * model.delta * (M - m) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hδpos.le) hgap
    exact mul_le_mul hcoef hpow (by positivity) (by positivity)


end
end Paper
