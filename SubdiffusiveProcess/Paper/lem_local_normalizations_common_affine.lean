import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.cutoff_good_scale_input
import SubdiffusiveProcess.Paper.lem_local_normalizations_lam_compact
import SubdiffusiveProcess.Paper.lem_local_normalizations_lam_unique
import SubdiffusiveProcess.Probability.CommonSubsequentialLimit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic
import SubdiffusiveProcess.DirichletForm.All

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem lem_local_normalizations_common_affine
    (d : ℕ) (hd : 2 ≤ d)
    (Jc : Paper.in_J d) (Pc : Paper.in_poincare d hd Jc)
    (Xc : Paper.in_extension d hd Jc)
    (Sf : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (W : SubdiffusiveProcess.Lane4.SmallPerturbationInput d)
    (Cp : SubdiffusiveProcess.Lane4.CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Interp : CubeFractionalInterpolationInput d hd)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasEnergyMeasure F)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
        (Sreg : Paper.in_6_16 d M) (It : Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∀ k : ℕ,
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
                Tendsto (fun n => Lam 0 ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three (-(k : ℤ)))
                  (ψ (ψ' n)) omega (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i))
                  atTop (𝓝 (Rlim omega)) := by
  classical
  obtain ⟨δc, hδc, hc⟩ := lem_local_normalizations_lam_compact d hd Jc Pc Xc Sf W D
  obtain ⟨δu, hδu, hu⟩ := lem_local_normalizations_lam_unique d hd Jc Pc Xc Sf W Cp D hES
    Step Interp EM
  refine ⟨min δc δu, lt_min hδc hδu, ?_⟩
  intro M Rm Sreg It H HI hM k Lam
  have hMc : M.delta ≤ min 1 δc := hM.trans (min_le_min_left 1 (min_le_left δc δu))
  have hMu : M.delta ≤ min 1 δu := hM.trans (min_le_min_left 1 (min_le_right δc δu))
  have hr : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos zero_lt_three (-(k : ℤ))
  have hrle : (3 : ℝ) ^ (-(k : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hg : ContDiff ℝ ∞ (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i) :=
    ContDiff.sum fun i _ => contDiff_const.mul (contDiff_apply ℝ ℝ i)
  exact exists_common_limit_of_compact_of_unique (chaosSampleLaw M).toMeasure
    (fun N omega => Lam 0 ((3 : ℝ) ^ (-(k : ℤ))) hr N omega
      (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i))
    (fun ψ hψ => hc M Rm Sreg It H HI hMc 0 ((3 : ℝ) ^ (-(k : ℤ))) hr hrle _ hg ψ hψ)
    (fun φ1 φ2 h1 h2 L1 L2 e1 e2 =>
      (hu M Rm Sreg It H HI hMu).1 k φ1 φ2 h1 h2 L1 L2 e1 e2)

end Paper
