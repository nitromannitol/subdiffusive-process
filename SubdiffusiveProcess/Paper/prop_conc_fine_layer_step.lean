module

public import SubdiffusiveProcess.Paper.prop_conc_setup
public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.prop_conc_weighted_identification
public import SubdiffusiveProcess.Paper.prop_conc_typical_pair
public import SubdiffusiveProcess.Paper.prop_conc_resampled_pair_growth
public import SubdiffusiveProcess.Paper.prop_conc_fine_layer_assembly

@[expose] public section

/-! Step 3 of `prop-conc`, fine layers (wavelength at most the cell side): the Δ-retaining masked
conditional Efron--Stein of Lemma `lem-15` gives `‖f(ω) - f(ω^{(j)})‖_p ≤ C δ Δ 3^{-a (-(j+k))}` for
the layers `j` with `j + k ≤ 0` (layer index `j` has wavelength `3^j`, the cell has side `3^{-k}`). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators Topology

namespace SubdiffusiveProcess.Paper
noncomputable section


/-- Fine side of `prop_conc_layer_step`: valid for every measurable version `f` of the relative response. -/
theorem prop_conc_fine_layer_step
    (d : ℕ) (hd : 2 ≤ d)
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (Ccamp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality) :
    ∃ aexp : ℝ, 0 < aexp ∧
      ∀ (C0 : ℝ) (_hC0 : 1 ≤ C0),
      ∀ (p : ℝ) (_hp : 2 ≤ p),
      ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d),
        model.delta ≤ delta0 →
      ∀ (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model)
        (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d model I Sreg),
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
        (_hyps : prop_conc_setup d model H Ω P field z r hr Sspace GN GE GF NE NF C0 m M
          zcell k cellIdx paddedIdx hPk AE AF),
      ∀ c ∈ Icc m M, ∀ (pvec : Fin d → ℝ),
        ((∃ i : Fin d, pvec = (Pi.single i (1 : ℝ) : Fin d → ℝ)) ∨
          (∃ i j : Fin d, pvec = (Pi.single i (1 : ℝ) : Fin d → ℝ) +
            (Pi.single j (1 : ℝ) : Fin d → ℝ))) →
      ∀ f : BilateralField d → ℝ, Measurable f →
        ((fun omega => (pvec ⬝ᵥ (AF omega).mulVec pvec -
            c * (pvec ⬝ᵥ (AE omega).mulVec pvec)) / Matrix.trace (AE omega)) =ᵐ[P]
          f ∘ field) →
        ∀ j : ℤ, j + (k : ℤ) ≤ 0 →
          eLpNorm (fun q : BilateralField d × BilateralField d =>
              f q.1 - f (Function.update q.1 j (q.2 j))) (ENNReal.ofReal p)
            ((chaosSampleLaw model).toMeasure.prod (chaosSampleLaw model).toMeasure) ≤
          ENNReal.ofReal (C * model.delta * (M - m) *
            (3 : ℝ) ^ (-aexp * ((j + (k : ℤ)).natAbs : ℝ))) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have ht1 : (d : ℝ) - 1 < aux_prop_conc_fine_layer_fine_t d := by
    unfold aux_prop_conc_fine_layer_fine_t; linarith
  have ht2 : aux_prop_conc_fine_layer_fine_t d < (d : ℝ) := by
    unfold aux_prop_conc_fine_layer_fine_t; linarith
  have hb : 0 < 3 * aux_prop_conc_fine_layer_fine_b d / 8 := by
    unfold aux_prop_conc_fine_layer_fine_b aux_prop_conc_fine_layer_fine_t
    have h2 : (0 : ℝ) < (d : ℝ) - 1 / 2 := by linarith
    have h3 : (0 : ℝ) < (d : ℝ) - 1 / 2 - d + 1 := by linarith
    positivity
  refine ⟨3 * aux_prop_conc_fine_layer_fine_b d / 8, hb, ?_⟩
  intro C0 hC0 p hp
  obtain ⟨δT, BT, hδT, hBT, hT⟩ := prop_conc_typical_pair d hd I _X _Sob _MeyersMorrey Pin Ccamp Interp
    (aux_prop_conc_fine_layer_fine_t d) 1 ht1 ht2 le_rfl C0 hC0
  obtain ⟨δG, B, hδG, hB0, hG⟩ := prop_conc_resampled_pair_growth d hd I _X _Sob _MeyersMorrey Pin Ccamp
    Interp (aux_prop_conc_fine_layer_fine_t d) (2 * p) ht1 ht2 (by linarith) C0 hC0
  obtain ⟨δWI, hδWI, hWI⟩ := prop_conc_weighted_identification d hd I _X _Sob _MeyersMorrey Pin Ccamp Interp
  obtain ⟨C, hC, hA⟩ := prop_conc_fine_layer_assembly d hd hES C0 hC0 p hp B hB0
  refine ⟨min (min δT δG) δWI, C, lt_min (lt_min hδT hδG) hδWI, hC, ?_⟩
  intro _ _ model hδ Rm Sreg It H Ω _ P field z r hr Sspace GN GE GF NE NF m M zcell k cellIdx paddedIdx
    hPk AE AF hyps c hc pvec hpvec f hf hfR j hj
  obtain ⟨K1, -, -, -, hTgood⟩ := hT model (hδ.trans ((min_le_left _ _).trans (min_le_left _ _))) Rm Sreg It H Ω P
    field z r hr Sspace GN GE GF NE NF m M zcell k cellIdx paddedIdx hPk AE AF hyps
  obtain ⟨K, hKm, hK0, hKB, hGgood⟩ := hG model (hδ.trans ((min_le_left _ _).trans (min_le_right _ _))) Rm Sreg It
    H Ω P field z r hr Sspace GN GE GF NE NF m M zcell k cellIdx paddedIdx hPk AE AF hyps
  have hW := hWI model (hδ.trans (min_le_right _ _)) Rm Sreg It H Ω P field z r hr Sspace GN GE GF NE NF C0
    m M hC0 zcell k cellIdx paddedIdx hPk AE AF hyps c pvec f hf hfR j (by omega)
  obtain ⟨hcand, -⟩ := hyps
  obtain ⟨hP, hfield, hlaw, -⟩ := hcand
  refine hA model P field m M (centeredCube (z paddedIdx) (r paddedIdx) (hr paddedIdx)) zcell k
    ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _) rfl c hc pvec ((aux_prop_conc_pair_data_mem_slopes d pvec).mpr hpvec) f K j hj
    ⟨hP, hfield, hlaw, hf, hKm, hK0, hKB, ?_⟩
  filter_upwards [hTgood, hGgood j (by omega), hW] with omega hY hGω hWω
  obtain ⟨Y, hE, hF, hQ, haff, hgrow⟩ := hY
  exact ⟨Y, hWω Y hE hF haff, (hGω Y hE hF haff).mono fun y hy => hy.2⟩

end
end SubdiffusiveProcess.Paper
