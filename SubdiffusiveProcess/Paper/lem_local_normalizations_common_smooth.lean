module

public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.lem_local_normalizations_lam_compact
public import SubdiffusiveProcess.Paper.lem_local_normalizations_lam_unique
public import SubdiffusiveProcess.Probability.CommonSubsequentialLimit
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic
public import SubdiffusiveProcess.DirichletForm.All

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem lem_local_normalizations_common_smooth
    (d : ℕ) (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Interp : CubeFractionalInterpolationInput d hd)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∀ g : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ g →
      let Lam (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
          (N : ℕ) (omega : BilateralField d) (g : SpatialCoordinates d → ℝ) : ℝ :=
        sInf {e : ℝ | ∃ (u : weakSobolevGraph (centeredCube z r hr))
            (U : SpatialCoordinates d → ℝ),
          ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)) ∧
          ((u.val).1 : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
          (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
            U x = g x) ∧
          e = sobolevCoefficientForm
            (cutoffPositiveCoefficient M H omega N z hr) u.val u.val}
        ∃ Rlim : BilateralField d → ℝ, ∀ ψ : ℕ → ℕ, StrictMono ψ →
            ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                Tendsto (fun n => Lam 0 1 one_pos (ψ (ψ' n)) omega g) atTop
                  (𝓝 (Rlim omega)) := by
  classical
  obtain ⟨δc, hδc, hc⟩ := lem_local_normalizations_lam_compact d hd Jc Pc Xc Sf W D
  obtain ⟨δu, hδu, hu⟩ := lem_local_normalizations_lam_unique d hd Jc Pc Xc Sf W Cp D hES
    Step Interp EM
  refine ⟨min δc δu, lt_min hδc hδu, ?_⟩
  intro M Rm Sreg It H HI hM g hg Lam
  have hMc : M.delta ≤ min 1 δc := hM.trans (min_le_min_left 1 (min_le_left δc δu))
  have hMu : M.delta ≤ min 1 δu := hM.trans (min_le_min_left 1 (min_le_right δc δu))
  exact exists_common_limit_of_compact_of_unique (chaosSampleLaw M).toMeasure
    (fun N omega => Lam 0 1 one_pos N omega g)
    (fun ψ hψ => hc M Rm Sreg It H HI hMc 0 1 one_pos le_rfl g hg ψ hψ)
    (fun φ1 φ2 h1 h2 L1 L2 e1 e2 =>
      (hu M Rm Sreg It H HI hMu).2 g hg φ1 φ2 h1 h2 L1 L2 e1 e2)

end SubdiffusiveProcess.Paper
