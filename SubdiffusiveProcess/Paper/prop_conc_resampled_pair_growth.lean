module

public import SubdiffusiveProcess.Paper.prop_conc_typical_pair
public import SubdiffusiveProcess.Paper.prop_conc_pair_mask
public import SubdiffusiveProcess.Paper.prop_conc_setup
public import SubdiffusiveProcess.Paper.prop_conc_tight_control_bank
public import SubdiffusiveProcess.Paper.prop_conc_resampled_canonical_setup
public import SubdiffusiveProcess.Paper.prop_conc_resampled_pair_growth_of_tied
public import SubdiffusiveProcess.Main.ScaledLayerLaw
public import Mathlib.Tactic

@[expose] public section

/-! Growth of the canonically resampled pair (the input `TP2` of the fine-layer step).  The frozen typical-pair statement is applied at
the canonical field space `(BilateralField d, chaos, id)` (`prop_conc_resampled_canonical_setup`), where the resampled fields are
again sample points; its growth constant `K` (measurable, with the same `L^p` bound) is used unchanged, and the pointwise identity
of the canonical masked pair with the tied affine pair of the resampled field (`prop_conc_resampled_pair_growth_of_tied`) transports
its growth along the measure-preserving replacement `(ω, y) ↦ ω[j ← y]`. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

/-- Growth of the canonically resampled pair (paper `prop-conc`, Step 3 input): for a.e. `ω`, every pair `Y`
of limiting forms realizing the operator limits at `ω` in an affine trace class, and a.e. resampling `y` of
the layer `j ≤ 0`, the canonical mask of `Y` by `1_q (y - ω_j)` has the growth of the normalized energy
measure with the field-level constant `K` evaluated at the resampled field. -/
theorem prop_conc_resampled_pair_growth
    (d : ℕ) (hd : 2 ≤ d)
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (_MeyersMorrey : SubdiffusiveProcess.Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (Ccamp : SubdiffusiveProcess.Lane4.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd)
    (t p : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d) (hp : 1 ≤ p)
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∃ delta0 B : ℝ, 0 < delta0 ∧ 0 ≤ B ∧
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
      ∃ K : BilateralField d → ℝ,
        AEStronglyMeasurable K (chaosSampleLaw model).toMeasure ∧
        (∀ᵐ eta ∂(chaosSampleLaw model).toMeasure, 0 ≤ K eta) ∧
        eLpNorm K (ENNReal.ofReal p) (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal B ∧
        ∀ j : ℤ, j ≤ 0 →
        ∀ᵐ omega ∂P,
          ∀ Y : prop_conc_pair_data
              (centeredCube (z paddedIdx) (r paddedIdx) (hr paddedIdx))
              zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity) C0 m M,
            (∀ u, Y.E.toClosedForm.energy u = limitFormEnergy (GE paddedIdx omega) u) →
            (∀ u, Y.F.toClosedForm.energy u = limitFormEnergy (GF paddedIdx omega) u) →
            aux_prop_conc_pair_data_affine Y →
            ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure,
              0 ≤ K (Function.update (field omega) j y) ∧
              ∀ (hw : Measurable ((centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ)))
                    (by positivity) : Set (SpatialCoordinates d)).indicator
                  (fun x => y x - (field omega) j x)))
                (Kw : ℝ)
                (hKw : ∀ x, |(centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ)))
                    (by positivity) : Set (SpatialCoordinates d)).indicator
                  (fun x => y x - (field omega) j x) x| ≤ Kw),
                aux_prop_conc_pair_data_growth
                  (aux_prop_conc_pair_mask_pair Y
                    ((centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ)))
                      (by positivity) : Set (SpatialCoordinates d)).indicator
                      (fun x => y x - (field omega) j x)) hw Kw hKw)
                  (aux_prop_conc_pair_data_slopes d) t
                  (K (Function.update (field omega) j y)) := by
  classical
  obtain ⟨delta0, B, hdelta0, hB0, hTP⟩ := prop_conc_typical_pair d hd I _X _Sob _MeyersMorrey Pin
    Ccamp Interp t p ht htd hp C0 hC0
  letI instBorel : MeasurableSpace C(SpatialCoordinates d, ℝ) := borel _
  haveI : BorelSpace C(SpatialCoordinates d, ℝ) := ⟨rfl⟩
  obtain ⟨deltaB, hdeltaB, hbank⟩ := prop_conc_tight_control_bank d hd I Pin _X _MeyersMorrey Ccamp
    _Sob Interp ((d : ℝ) - 1 / 2) (3 / 4) (by linarith only []) (by linarith only [])
    (by norm_num) (by norm_num)
  refine ⟨min delta0 deltaB, B, lt_min hdelta0 hdeltaB, hB0, ?_⟩
  intro instM instB model hdelta Rm Sreg It H Ω _ P field z r hr Sspace GN GE GF NE NF m M zcell k
    cellIdx paddedIdx hPk AE AF hyps
  obtain rfl := instB.measurable_eq
  -- C: the setup at the canonical field space;  T: the frozen typical pair there
  obtain ⟨GNc, GEc, GFc, AEc, AFc, hsetc⟩ := prop_conc_resampled_canonical_setup d model H Ω P field z r
    hr Sspace GN GE GF NE NF C0 m M hC0 zcell k cellIdx paddedIdx hPk AE AF hyps
  obtain ⟨K, hKm, hK0, hKL, hgood⟩ := hTP model (hdelta.trans (min_le_left _ _)) Rm Sreg It H
    (BilateralField d) (chaosSampleLaw model).toMeasure id z r hr Sspace GNc GEc GFc NE NF m M zcell k
    cellIdx paddedIdx hPk AEc AFc hsetc
  refine ⟨K, hKm, hK0, hKL, ?_⟩
  intro j hj
  obtain ⟨⟨hprob, hmeas, hmap, hIR, ⟨hNE, hNF⟩, hSall, hGNall, hlimall⟩, hCm, hord, hcellEq, hpadEq,
    hsymAE, hsymAF, hAE, hAF⟩ := hyps
  obtain ⟨⟨_, _, _, _, _, _, hGNallc, hlimallc⟩, _⟩ := hsetc
  haveI : IsProbabilityMeasure P := hprob
  have hfmp : MeasurePreserving field P (chaosSampleLaw model).toMeasure := ⟨hmeas, hmap⟩
  have hr0 : 0 < (3 : ℝ) ^ (-(k : ℝ)) := by positivity
  have hT : ∀ᵐ η ∂(chaosSampleLaw model).toMeasure,
      Tendsto (fun n => GNc paddedIdx (NE n) η) atTop (𝓝 (GEc paddedIdx η)) ∧
      Tendsto (fun n => GNc paddedIdx (NF n) η) atTop (𝓝 (GFc paddedIdx η)) ∧ 0 ≤ K η ∧
      ∃ Yc : prop_conc_pair_data
          (centeredCube (z paddedIdx) (r paddedIdx) (hr paddedIdx))
          zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0 C0 m M,
        (∀ u, Yc.E.toClosedForm.energy u = limitFormEnergy (GEc paddedIdx η) u) ∧
        (∀ u, Yc.F.toClosedForm.energy u = limitFormEnergy (GFc paddedIdx η) u) ∧
        aux_prop_conc_pair_data_affine Yc ∧
        aux_prop_conc_pair_data_growth Yc (aux_prop_conc_pair_data_slopes d) t (K η) := by
    filter_upwards [hlimallc, hK0, hgood] with η h1 h2 h3
    obtain ⟨Yc, hE, hF, _, haff, hgr⟩ := h3
    exact ⟨(h1 paddedIdx).1, (h1 paddedIdx).2, h2, Yc, hE, hF, haff, hgr⟩
  -- the tight bank at the padded cube
  obtain ⟨F, Cb, hmem, hnorm, hcontrol⟩ := hbank model Rm Sreg It H hIR
    (hdelta.trans (min_le_right _ _)) (z paddedIdx) (r paddedIdx) (hr paddedIdx) (Sspace paddedIdx)
    (hSall paddedIdx)
  exact aux_prop_conc_resampled_pair_growth_of_tied_tail hd model H hIR P field hfmp (z paddedIdx)
    (r paddedIdx) (hr paddedIdx) zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0 C0 m M (Sspace paddedIdx)
    (hSall paddedIdx) NE NF hNE hNF (GN paddedIdx) (GE paddedIdx) (GF paddedIdx) (hGNall paddedIdx)
    (hlimall.mono fun ω h => h paddedIdx) F Cb hmem hnorm
    (hcontrol.mono fun om h N hb => (h N hb).1) (GNc paddedIdx) (GEc paddedIdx) (GFc paddedIdx)
    (hGNallc paddedIdx) K t hT j hj

end
end Paper
