module

public import SubdiffusiveProcess.Paper.prop_conc_setup
public import SubdiffusiveProcess.Paper.prop_conc_affine_order
public import SubdiffusiveProcess.Paper.prop_conc_centering
public import SubdiffusiveProcess.Paper.prop_conc_assembly
public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Lane3.RelativeResponseSlopes
public import SubdiffusiveProcess.Lane3.RelativeConcentrationEntries
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
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

/-- Integrability of the relative scalar responses on the slopes, from the affine order. -/
theorem aux_prop_conc_thin_integrable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hsymAE : ∀ ω, (AE ω).transpose = AE ω) (m M c : ℝ) (hm0 : 0 ≤ m) (hc : c ∈ Icc m M)
    (hmeasE : ∀ v : Fin d → ℝ, AEStronglyMeasurable (fun ω => v ⬝ᵥ (AE ω).mulVec v) P)
    (hmeasF : ∀ v : Fin d → ℝ, AEStronglyMeasurable (fun ω => v ⬝ᵥ (AF ω).mulVec v) P)
    (hpsd : ∀ᵐ ω ∂P, ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ (AE ω).mulVec v)
    (hordAE : ∀ᵐ ω ∂P, 0 < Matrix.trace (AE ω) ∧
      ∀ pvec : Fin d → ℝ,
        m * (pvec ⬝ᵥ (AE ω).mulVec pvec) ≤ pvec ⬝ᵥ (AF ω).mulVec pvec ∧
          pvec ⬝ᵥ (AF ω).mulVec pvec ≤ M * (pvec ⬝ᵥ (AE ω).mulVec pvec)) :
    ∀ v : Fin d → ℝ, SubdiffusiveProcess.Lane3.RelSlopes.IsAffineSlope v →
      Integrable (fun ω => SubdiffusiveProcess.Lane3.RelSlopes.relativeResponse
        (AE ω) (AF ω) c v) P := by
  have htrE : AEStronglyMeasurable (fun ω => Matrix.trace (AE ω)) P := by
    have h : (fun ω => Matrix.trace (AE ω)) = ∑ i : Fin d,
        fun ω => (Pi.single i (1 : ℝ) : Fin d → ℝ) ⬝ᵥ (AE ω).mulVec (Pi.single i (1 : ℝ)) := by
      funext ω
      rw [SubdiffusiveProcess.Lane3.RelSlopes.trace_eq_sum_quadForm]
      simp
    rw [h]
    exact Finset.aestronglyMeasurable_sum _ fun i _ => hmeasE _
  intro v hv
  refine Integrable.of_bound ?_ (4 * M) ?_
  · exact (((hmeasF v).aemeasurable.sub ((hmeasE v).aemeasurable.const_mul c)).div
      htrE.aemeasurable).aestronglyMeasurable
  · filter_upwards [hpsd, hordAE] with ω hp' ho
    rw [Real.norm_eq_abs]
    exact SubdiffusiveProcess.Lane3.RelSlopes.relativeResponse_abs_le (AE ω) (AF ω)
      (hsymAE ω) hp' m M c hm0 (hm0.trans hc.1) hc.2 ho.1 ho.2 v hv

/-- Core of the thin `prop_conc` proof: the conclusion from the packaged standing data. -/
theorem aux_prop_conc_thin_core
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
      ∀ (p : ℝ) (hp : 0 < p),
      ∃ delta0 Cp : ℝ, 0 < delta0 ∧ 0 < Cp ∧
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
      let ck : ℝ := ∫ om, Matrix.trace (AF om) / Matrix.trace (AE om) ∂P
      let B : Ω → Matrix (Fin d) (Fin d) ℝ := fun om =>
        (Matrix.trace (AE om))⁻¹ • (AF om - ck • AE om)
      let Band : ℕ → MeasurableSpace Ω := fun Hband =>
        ⨆ (j : ℤ) (_h : |j + (k : ℤ)| ≤ (Hband : ℤ)),
          (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
            (fun om : Ω => field om j)
      ck ∈ Icc m M ∧
      (∀ i j : Fin d, ∫ om, B om i j ∂P = 0) ∧
      eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d, |B om i j|) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (Cp * model.delta * (M - m)) ∧
      ∀ Hband : ℕ,
        eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d,
          |B om i j - (P[fun om' => B om' i j | Band Hband]) om|) (ENNReal.ofReal p) P ≤
          ENNReal.ofReal (Cp * model.delta * (M - m) * (3 : ℝ) ^ (-aexp * (Hband : ℝ))) := by
  obtain ⟨aexp, ha, hasm⟩ :=
    prop_conc_assembly d hd I _X _Sob _MeyersMorrey Pin Ccamp Interp hES
  refine ⟨aexp, ha, ?_⟩
  intro C0 hC0 p hp
  have hp2 : 0 < max p 2 := lt_of_lt_of_le hp (le_max_left p 2)
  obtain ⟨d1, C1, hAll⟩ := hasm C0 hC0 (max p 2) hp2
  have hd1 : 0 < d1 := hAll.1
  have hC1 : 0 < C1 := hAll.2.1
  obtain ⟨d2, hAll2⟩ :=
    prop_conc_centering d hd I _X _Sob _MeyersMorrey Pin Ccamp Interp hES C0 hC0
  have hd2 : 0 < d2 := hAll2.1
  obtain ⟨d3, hAll3⟩ :=
    prop_conc_affine_order d hd I _X _Sob _MeyersMorrey Pin Ccamp Interp hES C0 hC0
  have hd3 : 0 < d3 := hAll3.1
  have hdd : (0 : ℝ) < 3 * ((d : ℝ) * (d : ℝ)) * C1 := by
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  refine ⟨min d1 (min d2 d3), 3 * ((d : ℝ) * (d : ℝ)) * C1,
    lt_min hd1 (lt_min hd2 hd3), hdd, ?_⟩
  intro _ _ model hdelta Rm Sreg It H Ω _ P field z r hr Sspace GN GE GF NE NF m M
    zcell k cellIdx paddedIdx hPk AE AF hyps
  have hd1' : model.delta ≤ d1 := hdelta.trans (min_le_left _ _)
  have hd2' : model.delta ≤ d2 := hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hd3' : model.delta ≤ d3 := hdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdpos : (0 : ℝ) < model.delta := model.shellPrefix.delta_pos
  obtain ⟨hJoint, ⟨hm, hmM, hM⟩, horder, hcell, hpaddedIdx, hsymAE, hsymAF, hAE, hAF⟩ := hyps
  have hyps : prop_conc_setup d model H Ω P field z r hr Sspace GN GE GF NE NF C0 m M zcell k
      cellIdx paddedIdx hPk AE AF :=
    ⟨hJoint, ⟨hm, hmM, hM⟩, horder, hcell, hpaddedIdx, hsymAE, hsymAF, hAE, hAF⟩
  obtain ⟨hmeasE, hmeasF, hpsd, hordAE⟩ := hAll3.2 model hd3' Rm Sreg It H Ω P field z r hr Sspace GN
    GE GF NE NF m M zcell k cellIdx paddedIdx hPk AE AF hyps
  obtain ⟨hck, hmean⟩ := hAll2.2 model hd2' Rm Sreg It H Ω P field z r hr Sspace GN GE GF NE NF hJoint
    m M hm hmM hM horder zcell k cellIdx hcell paddedIdx hpaddedIdx hPk AE AF hsymAE hsymAF hAE hAF
  intro ck B Band
  haveI : IsProbabilityMeasure P := hJoint.1
  have hm0 : 0 ≤ m := (inv_nonneg.mpr (zero_le_one.trans hC0)).trans hm
  have hint := aux_prop_conc_thin_integrable P AE AF hsymAE m M ck hm0 hck hmeasE hmeasF hpsd
    hordAE
  have hAck := hAll.2.2 model hd1' Rm Sreg It H Ω P field z r hr Sspace GN GE GF NE NF m M zcell k
    cellIdx paddedIdx hPk AE AF hyps ck hck
  have hq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max p 2) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [le_max_right p 2])
  have hq0 : ENNReal.ofReal p ≤ ENNReal.ofReal (max p 2) :=
    ENNReal.ofReal_le_ofReal (le_max_left p 2)
  obtain ⟨hb1, hb2⟩ := SubdiffusiveProcess.Lane3.RelSlopes.relative_concentration_matrix_bounds P
    AE AF hsymAE hsymAF ck (ENNReal.ofReal (max p 2)) (ENNReal.ofReal p) hq hq0
    (C1 * model.delta * (M - m)) (fun n => C1 * model.delta * (M - m) * (3 : ℝ) ^ (-aexp * (n : ℝ)))
    Band hint hmean (fun v hv => (hAck v hv).1) (fun v hv n => (hAck v hv).2 n)
  refine ⟨hck, hmean, ?_, fun Hband => ?_⟩
  · refine hb1.trans (le_of_eq ?_)
    congr 1
    ring
  · refine (hb2 Hband).trans (le_of_eq ?_)
    congr 1
    ring



theorem prop_conc
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
      ∀ (p : ℝ) (hp : 0 < p),
      ∃ delta0 Cp : ℝ, 0 < delta0 ∧ 0 < Cp ∧
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
        (NE NF : ℕ → ℕ)
        (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr
          Sspace GN GE GF NE NF)
        (m M : ℝ) (hm : C0⁻¹ ≤ m) (hmM : m ≤ M) (hM : M ≤ C0)
        (horder : ∀ᵐ omega ∂P, ∀ i,
          limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
            ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
              u ∈ limitFormDomain (GE i omega) →
                m * (limitFormEnergy (GE i omega) u).toReal ≤
                    (limitFormEnergy (GF i omega) u).toReal ∧
                  (limitFormEnergy (GF i omega) u).toReal ≤
                    M * (limitFormEnergy (GE i omega) u).toReal)
        (zcell : SpatialCoordinates d)
        (cellIdx : ℕ → ℕ)
        (hcell : ∀ k, z (cellIdx k) = zcell ∧
          r (cellIdx k) = (3 : ℝ) ^ (-(k : ℝ)))
        (paddedIdx : ℕ → ℕ)
        (hpaddedIdx : ∀ k,
          z (paddedIdx k) = zcell ∧
          r (paddedIdx k) = 3 * ((3 : ℝ) ^ (-(k : ℝ))))
        (hPk : ∀ k : ℕ, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _)),
          ‖(u : SobolevData
              (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))).1‖ ≤
            K * ‖subspaceGradient
              (killedSobolevGraph
                (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))) u‖)
        (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
        (hsymAE : ∀ k omega, (AE k omega).transpose = AE k omega)
        (hsymAF : ∀ k omega, (AF k omega).transpose = AF k omega)
        (hAE : ∀ᵐ omega ∂P, ∀ k : ℕ, ∀ pvec : Fin d → ℝ,
          Tendsto
            (fun j : ℕ =>
              affineDirichletResponse
                (centeredCube_isBounded zcell
                  (Real.rpow_pos_of_pos zero_lt_three _))
                (hPk k)
                (Lane4.cutoffPositiveCoefficient model H (field omega)
                  (NE j) zcell
                  (Real.rpow_pos_of_pos zero_lt_three _)) pvec /
                (volume
                  (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ)))
                    (Real.rpow_pos_of_pos zero_lt_three _) : Set (SpatialCoordinates d))).toReal)
            atTop
            (𝓝 (pvec ⬝ᵥ (AE k omega).mulVec pvec)))
        (hAF : ∀ᵐ omega ∂P, ∀ k : ℕ, ∀ pvec : Fin d → ℝ,
          Tendsto
            (fun j : ℕ =>
              affineDirichletResponse
                (centeredCube_isBounded zcell
                  (Real.rpow_pos_of_pos zero_lt_three _))
                (hPk k)
                (Lane4.cutoffPositiveCoefficient model H (field omega)
                  (NF j) zcell
                  (Real.rpow_pos_of_pos zero_lt_three _)) pvec /
                (volume
                  (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ)))
                    (Real.rpow_pos_of_pos zero_lt_three _) : Set (SpatialCoordinates d))).toReal)
            atTop
            (𝓝 (pvec ⬝ᵥ (AF k omega).mulVec pvec))),
      let ck : ℕ → ℝ := fun k =>
        ∫ omega, Matrix.trace (AF k omega) / Matrix.trace (AE k omega) ∂P
      let Bk : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ := fun k omega =>
        (Matrix.trace (AE k omega))⁻¹ •
          (AF k omega - ck k • AE k omega)
      let Band : ℕ → ℕ → MeasurableSpace Ω := fun k H =>
        ⨆ (j : ℤ) (_h : |j + (k : ℤ)| ≤ (H : ℤ)),
          (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
            (fun omega : Ω => field omega j)
      (∀ k : ℕ, ck k ∈ Icc m M) ∧
      (∀ (k : ℕ) (i j : Fin d),
        ∫ omega, Bk k omega i j ∂P = 0) ∧
      (∀ k : ℕ,
        eLpNorm
            (fun omega => ∑ i : Fin d, ∑ j : Fin d, |Bk k omega i j|)
            (ENNReal.ofReal p) P ≤
          ENNReal.ofReal (Cp * model.delta * (M - m))) ∧
      (∀ (k H : ℕ),
        eLpNorm
            (fun omega =>
              ∑ i : Fin d, ∑ j : Fin d,
                |Bk k omega i j -
                  ((P[fun omega => Bk k omega i j | Band k H]) omega)|)
            (ENNReal.ofReal p) P ≤
          ENNReal.ofReal
            (Cp * model.delta * (M - m) *
              (3 : ℝ) ^ (-aexp * (H : ℝ)))) := by
  obtain ⟨aexp, ha, hcore⟩ :=
    aux_prop_conc_thin_core d hd I _X _Sob _MeyersMorrey Pin Ccamp Interp hES
  refine ⟨aexp, ha, ?_⟩
  intro C0 hC0 p hp
  obtain ⟨delta0, Cp, hd0, hCp, hh⟩ := hcore C0 hC0 p hp
  refine ⟨delta0, Cp, hd0, hCp, ?_⟩
  intro _ _ model hdelta Rm Sreg It H Ω _ P field z r hr Sspace GN GE GF NE NF hJoint m M hm hmM hM
    horder zcell cellIdx hcell paddedIdx hpaddedIdx hPk AE AF hsymAE hsymAF hAE hAF
  have hk := fun k : ℕ => hh model hdelta Rm Sreg It H Ω P field z r hr Sspace GN GE GF NE NF m M
    zcell k (cellIdx k) (paddedIdx k) (hPk k) (AE k) (AF k)
    ⟨hJoint, ⟨hm, hmM, hM⟩, horder, hcell k, hpaddedIdx k, hsymAE k, hsymAF k,
      hAE.mono (fun omega h => h k), hAF.mono (fun omega h => h k)⟩
  intro ck Bk Band
  simpa only [forall_and] using hk

end
end Paper
