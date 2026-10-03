module

public import SubdiffusiveProcess.Paper.prop_conc_affine_order
public import SubdiffusiveProcess.Paper.prop_conc_setup
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
public import SubdiffusiveProcess.CellSymmetry.Laws
public import SubdiffusiveProcess.CellSymmetry.Centering
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

/--
Step 1 of `prop_conc` (paper `mfd:prop-conc`): the form order gives `c_k ∈ [m, M]`, and
`E B_k = 0` by signed-coordinate-permutation invariance (Assumptions a.g1, a.g3) plus the
zero trace of `B_k` in mean. Single-level form: one level `k`, its observation cell `(zcell, 3^-k)` and padded cell; other
binders and hypotheses as in `prop_conc`.
-/
theorem prop_conc_centering
    (d : ℕ) (hd : 2 ≤ d)
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (_MeyersMorrey : SubdiffusiveProcess.Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (Ccamp : SubdiffusiveProcess.Lane4.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd)
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality) :
    ∀ (C0 : ℝ) (hC0 : 1 ≤ C0),
      ∃ delta0 : ℝ, 0 < delta0 ∧
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
        (zcell : SpatialCoordinates d) (k : ℕ)
        (cellIdx : ℕ)
        (hcell : z cellIdx = zcell ∧
          r cellIdx = (3 : ℝ) ^ (-(k : ℝ)))
        (paddedIdx : ℕ)
        (hpaddedIdx :
          z paddedIdx = zcell ∧
          r paddedIdx = 3 * ((3 : ℝ) ^ (-(k : ℝ))))
        (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity)),
          ‖(u : SobolevData
              (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))).1‖ ≤
            K * ‖subspaceGradient
              (killedSobolevGraph
                (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))) u‖)
        (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
        (hsymAE : ∀ omega, (AE omega).transpose = AE omega)
        (hsymAF : ∀ omega, (AF omega).transpose = AF omega)
        (hAE : ∀ᵐ omega ∂P, ∀ pvec : Fin d → ℝ,
          Tendsto
            (fun j : ℕ =>
              affineDirichletResponse
                (centeredCube_isBounded zcell
                  (show 0 < (3 : ℝ) ^ (-(k : ℝ)) by positivity))
                hPk
                (Lane4.cutoffPositiveCoefficient model H (field omega)
                  (NE j) zcell
                  (show 0 < (3 : ℝ) ^ (-(k : ℝ)) by positivity)) pvec /
                (volume
                  (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ)))
                    (by positivity) : Set (SpatialCoordinates d))).toReal)
            atTop
            (𝓝 (pvec ⬝ᵥ (AE omega).mulVec pvec)))
        (hAF : ∀ᵐ omega ∂P, ∀ pvec : Fin d → ℝ,
          Tendsto
            (fun j : ℕ =>
              affineDirichletResponse
                (centeredCube_isBounded zcell
                  (show 0 < (3 : ℝ) ^ (-(k : ℝ)) by positivity))
                hPk
                (Lane4.cutoffPositiveCoefficient model H (field omega)
                  (NF j) zcell
                  (show 0 < (3 : ℝ) ^ (-(k : ℝ)) by positivity)) pvec /
                (volume
                  (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ)))
                    (by positivity) : Set (SpatialCoordinates d))).toReal)
            atTop
            (𝓝 (pvec ⬝ᵥ (AF omega).mulVec pvec))),
      let ck : ℝ :=
        ∫ omega, Matrix.trace (AF omega) / Matrix.trace (AE omega) ∂P
      let B : Ω → Matrix (Fin d) (Fin d) ℝ := fun omega =>
        (Matrix.trace (AE omega))⁻¹ •
          (AF omega - ck • AE omega)
      (ck ∈ Icc m M) ∧
      (∀ (i j : Fin d), ∫ omega, B omega i j ∂P = 0) := by
  intro C0 hC0
  obtain ⟨delta0, hdelta0, hthm⟩ :=
    prop_conc_affine_order d hd I _X _Sob _MeyersMorrey Pin Ccamp Interp hES C0 hC0
  refine ⟨delta0, hdelta0, ?_⟩
  intro mC bC model hmodel Rm Sreg It H Ω mΩ P field z r hr Sspace GN GE GF NE NF hJoint
    m M hm hmM hM horder zcell k cellIdx hcell paddedIdx hpaddedIdx hPk AE AF hsymAE hsymAF
    hAE hAF ck B
  have hyps : prop_conc_setup d model H Ω P field z r hr Sspace GN GE GF NE NF C0 m M
      zcell k cellIdx paddedIdx hPk AE AF :=
    ⟨hJoint, ⟨hm, hmM, hM⟩, horder, hcell, hpaddedIdx, hsymAE, hsymAF, hAE, hAF⟩
  obtain ⟨hmeE, hmeF, hpsd, hord⟩ := hthm model hmodel Rm Sreg It H Ω P field z r hr Sspace
    GN GE GF NE NF m M zcell k cellIdx paddedIdx hPk AE AF hyps
  obtain ⟨hprob, hfield, hlaw, hIR, -⟩ := hJoint
  haveI : IsProbabilityMeasure P := hprob
  have hm0 : 0 ≤ m := by
    have : 0 < C0⁻¹ := inv_pos.2 (lt_of_lt_of_le zero_lt_one hC0)
    linarith
  have hrk : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℝ)) := by positivity
  have hlaws := SubdiffusiveProcess.CellSymmetry.cs_lc_one_cell_laws model H hIR zcell hrk hPk
    P field hfield hlaw NE NF AE AF hsymAE hsymAF hAE hAF
  have hcent := SubdiffusiveProcess.CellSymmetry.cs_centering_of_laws (by omega) P
    (fun _ => AE) (fun _ => AF) (fun _ => hsymAE) (fun _ => hsymAF) (fun _ => hmeE)
    (fun _ => hmeF) (hpsd.mono fun ω h _ => h) m M hm0 (hord.mono fun ω h _ => h)
    (fun _ => hlaws)
  exact ⟨hcent.1 0, fun i j => hcent.2 0 i j⟩

end
end Paper
