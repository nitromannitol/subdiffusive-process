module

public import Mathlib
public import SubdiffusiveProcess.Paper.conv_represented_thm_c1_family_grids_actual_extra
public import SubdiffusiveProcess.Paper.conv_represented_joint_grids
public import SubdiffusiveProcess.Paper.calib_coordinates
public import SubdiffusiveProcess.Paper.conv_represented_calibration_package
public import SubdiffusiveProcess.Paper.conv_represented_limit_forms_package
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- `conv_represented_thm_c1_family_grids_actual` together with the calibration package on the SAME
probability space and subsequence. -/
theorem conv_represented_thm_c1_family_calibration_actual
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hInterp : CubeFractionalInterpolationInput d hd)
    (E : in_J d) (Pin : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (alpha eta beta t : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (heta : 0 < eta) (hAeta : 1 + eta < 2 * alpha) (hb : 1 / 2 < beta) (hba : beta < alpha)
    :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ δ0 →
      ∀ (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
        (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
        (_hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (Z i) (R i) (hR i)))
        (_hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ m : ℤ, R i = (3 : ℝ) ^ m)
        (_hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ), (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) →
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
          conv_represented_joint_grids d hd M H Ωh Ph field env env Z R hR Sspace
            GNE GNF GE GF (fun n => NE (seq n)) (fun n => NF (seq n)) alpha eta E beta t ∧
          conv_represented_limit_forms_package d hd M H Ωh Ph env Z R hR Sspace GE GF
            (fun n => NE (seq n)) (fun n => NF (seq n)) ∧
          conv_represented_calibration_package d hd M H Ωh Ph env
            (fun n => NE (seq n)) (fun n => NF (seq n)) t alpha := by
  obtain ⟨δa, hδa, hfam⟩ := conv_represented_thm_c1_family_grids_actual_extra d hd hInterp E Pin X W Cp Sob alpha eta
    beta t ht htd ha0 ha1 heta hAeta hb hba
  obtain ⟨δb, hδb, hcoord⟩ := calib_coordinates d hd E Pin X W Cp Sob t alpha ht htd ha0 ha1
  refine ⟨min δa δb, lt_min hδa hδb, ?_⟩
  intro M Rm Sreg It H hH hδ Z R hR Sspace hS hrat hcomp NE NF hNE hNF
  obtain ⟨Y, hY, Zx, hZm, hZt, hdec⟩ := hcoord M Rm H hH (hδ.trans (min_le_right _ _))
  obtain ⟨seq, hseq, Ωh, mΩ, Ph, hPh, field, env, GNE, GNF, GE, GF, hjoint, -, hlim, hconv⟩ :=
    @hfam M Rm Sreg It H hH (hδ.trans (min_le_left _ _)) Z R hR Sspace hS hrat hcomp NE NF hNE hNF Y hY Zx
      (fun y n => ⟨hZm y _, hZm y _⟩)
      (fun y rho hrho => by
        obtain ⟨Mb, hMb⟩ := hZt y rho hrho
        exact ⟨Mb, fun n => ⟨hMb (NE n), hMb (NF n)⟩⟩)
  refine ⟨seq, hseq, Ωh, mΩ, Ph, hPh, field, env, GNE, GNF, GE, GF, hjoint, ?_, ?_⟩
  · filter_upwards [hlim] with omega hom
    obtain ⟨LE, LF, hloc, -⟩ := hom
    exact ⟨LE, LF, hloc⟩
  · obtain ⟨⟨hprob, hfm, hfmap, -, hNE', hNF', hMP, -⟩, -⟩ := hjoint
    exact hdec Ph env (fun n => (hMP n).1) (fun n => NE (seq n)) (fun n => NF (seq n)) hconv

end SubdiffusiveProcess.Paper
