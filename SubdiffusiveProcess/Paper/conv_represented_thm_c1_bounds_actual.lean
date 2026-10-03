module

public import SubdiffusiveProcess.Paper.conv_represented_thm_c1_hyp_buffered_actual
public import SubdiffusiveProcess.Paper.conv_represented_joint_bounds
public import SubdiffusiveProcess.Paper.lem_cutoffs_damped_extrema_uniform

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped Topology ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- The actual model supplies both the joint representation and every represented-bounds field. -/
theorem conv_represented_thm_c1_bounds_actual
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hInterp : CubeFractionalInterpolationInput d hd)
    (E : in_J d) (Pin : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (alpha eta beta t : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (heta : 0 < eta) (hAeta : 1 + eta < 2 * alpha) (hb : 1 / 2 < beta) (hba : beta < alpha) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H),
        M.delta ≤ δ0 →
      ∀ (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
        (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
        (hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (Z i) (R i) (hR i)))
        (hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ m : ℤ, R i = (3 : ℝ) ^ m)
        (hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ), (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) →
          (∃ m : ℤ, r' = (3 : ℝ) ^ m) → ∃ i, Z i = z' ∧ R i = r')
        (NE NF : ℕ → ℕ), StrictMono NE → StrictMono NF →
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
        ∃ (Ωh : Type) (_ : MeasurableSpace Ωh) (Ph : Measure Ωh) (_ : IsProbabilityMeasure Ph)
          (field : Ωh → BilateralField d) (env : ℕ → Ωh → BilateralField d)
          (GNE GNF : (i : ℕ) → ℕ → Ωh →
            DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
              DomainL2 (centeredCube (Z i) (R i) (hR i)))
          (GE GF : (i : ℕ) → Ωh →
            DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
              DomainL2 (centeredCube (Z i) (R i) (hR i))),
          conv_represented_joint_buffered d hd M H Ωh Ph field env env Z R hR Sspace
            GNE GNF GE GF (fun n => NE (seq n)) (fun n => NF (seq n)) alpha eta ∧
          aux_conv_represented_env_interface_bounds d hd M H Ωh Ph env env Z R hR Sspace GE GF
            (fun n => NE (seq n)) (fun n => NF (seq n)) := by
  obtain ⟨deltaCat, hDeltaCat, hcat⟩ := conv_represented_thm_c1_hyp_buffered_actual
    d hd hInterp E Pin X W Cp Sob alpha eta beta t ht htd ha0 ha1 heta hAeta hb hba
  obtain ⟨deltaExt, hDeltaExt, hext⟩ := lem_cutoffs_damped_extrema_uniform d hd eta heta
  refine ⟨min deltaCat deltaExt, lt_min hDeltaCat hDeltaExt, ?_⟩
  intro M Rm Sreg It H hH hDelta Z R hR Sspace hS hrat hcomp NE NF hNE hNF
  obtain ⟨seq, hseq, Ωh, mΩh, Ph, hPh, field, env, GNE, GNF, GE, GF, hjoint⟩ :=
    hcat M Rm Sreg It H hH (hDelta.trans (min_le_left _ _)) Z R hR Sspace hS hrat hcomp
      NE NF hNE hNF
  haveI : IsProbabilityMeasure Ph := hPh
  refine ⟨seq, hseq, Ωh, mΩh, Ph, hPh, field, env, GNE, GNF, GE, GF, hjoint, ?_⟩
  exact conv_represented_joint_bounds d hd M H Ωh Ph field env env Z R hR Sspace GNE GNF GE GF
    (fun n => NE (seq n)) (fun n => NF (seq n)) alpha eta hInterp
    (fun hIR => hext M H hIR (hDelta.trans (min_le_right _ _))) hjoint

end Paper
