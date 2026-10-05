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
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.lem_local_normalizations_lam_compact
public import SubdiffusiveProcess.Paper.lem_local_normalizations_operator_unique
public import SubdiffusiveProcess.Paper.lnorm_smooth_clusters_of_equal_operators
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

/-- `\label{mfd:thm-c1}` (last paragraph of its proof: "all subsequential limit forms coincide"),
scalar consequence for the finite-cutoff Dirichlet energies `Λ_N` used by `lem_local_normalizations`:
two almost surely convergent cutoff subsequences of `Λ_N` have almost surely equal limits.  It is
stated for the affine datum `x ↦ ∑ᵢ xᵢ` on the cubes `centeredCube 0 3^{-k}` and for every smooth
datum on the unit cube, at one small-disorder threshold chosen before the model.

- `Lam` is the actual variational energy of `lem_local_normalizations_common_*`
  (`aux_lem_local_normalizations_lam_compact_Lam`), unfolded there to the same `sInf`.
- Standing inputs are those of `lem_local_normalizations_common_*` (Interp and the good-scale
  input are carried because `thm_c1`'s represented bounds contain them).
- Proof: `lem_local_normalizations_operator_unique` (two cutoff subsequences have a common
  refinement along which the padded killed inverses converge to one limit; `thm_c1`) and the scalar
  transfer `lnorm_smooth_clusters_of_equal_operators` (equal padded operator limits give equal
  smooth scalar boundary-response limits).  Both inputs are proved (`lem_local_normalizations_operator_unique` from `s9_actual_uniqueness`). -/
theorem lem_local_normalizations_lam_unique
    (d : ℕ) (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
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
        (∀ k : ℕ, ∀ (φ1 φ2 : ℕ → ℕ), StrictMono φ1 → StrictMono φ2 →
          ∀ (L1 L2 : BilateralField d → ℝ),
            (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              Tendsto (fun n => aux_lem_local_normalizations_lam_compact_Lam M H 0
                ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three (-(k : ℤ))) (φ1 n) omega
                (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i))
                atTop (𝓝 (L1 omega))) →
            (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              Tendsto (fun n => aux_lem_local_normalizations_lam_compact_Lam M H 0
                ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three (-(k : ℤ))) (φ2 n) omega
                (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i))
                atTop (𝓝 (L2 omega))) →
            L1 =ᵐ[(chaosSampleLaw M).toMeasure] L2) ∧
        (∀ g : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ g →
          ∀ (φ1 φ2 : ℕ → ℕ), StrictMono φ1 → StrictMono φ2 →
          ∀ (L1 L2 : BilateralField d → ℝ),
            (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              Tendsto (fun n => aux_lem_local_normalizations_lam_compact_Lam M H 0 1 one_pos
                (φ1 n) omega g) atTop (𝓝 (L1 omega))) →
            (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              Tendsto (fun n => aux_lem_local_normalizations_lam_compact_Lam M H 0 1 one_pos
                (φ2 n) omega g) atTop (𝓝 (L2 omega))) →
            L1 =ᵐ[(chaosSampleLaw M).toMeasure] L2) := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨δo, hδo, hou⟩ := lem_local_normalizations_operator_unique d hd Jc Pc Xc Sf W Cp D hES
    Step Interp EM
  obtain ⟨δs, hδs, hsc⟩ := lnorm_smooth_clusters_of_equal_operators d hd Jc Pc Xc W Cp Sf Interp
  refine ⟨min δo δs, lt_min hδo hδs, ?_⟩
  intro M Rm Sreg It H HI hM
  have hMo : M.delta ≤ min 1 δo := hM.trans (min_le_min_left 1 (min_le_left δo δs))
  have hMs : M.delta ≤ δs := hM.trans ((min_le_right _ _).trans (min_le_right _ _))
  have key : ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 → (∃ m : ℤ, 3 * r = (3 : ℝ) ^ m) →
      ∀ (g : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ g →
      ∀ (φ1 φ2 : ℕ → ℕ), StrictMono φ1 → StrictMono φ2 →
      ∀ (L1 L2 : BilateralField d → ℝ),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          Tendsto (fun n => aux_lem_local_normalizations_lam_compact_Lam M H 0 r hr (φ1 n) omega g)
            atTop (𝓝 (L1 omega))) →
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          Tendsto (fun n => aux_lem_local_normalizations_lam_compact_Lam M H 0 r hr (φ2 n) omega g)
            atTop (𝓝 (L2 omega))) →
        L1 =ᵐ[(chaosSampleLaw M).toMeasure] L2 := by
    intro r hr hr1 hm g hg φ1 φ2 h1 h2 L1 L2 e1 e2
    have h3r : 0 < 3 * r := mul_pos zero_lt_three hr
    obtain ⟨τ, hτ, G, hG⟩ := hou M Rm Sreg It H HI hMo (fun _ => 3 * r) (fun _ => h3r)
      (fun _ => hm) φ1 φ2 h1 h2
    exact hsc M Rm Sreg It H HI hMs 0 r hr hr1 (φ1 ∘ τ) (φ2 ∘ τ) (G 0) g hg L1 L2
      (by filter_upwards [hG] with omega hω; exact hω 0)
      (by
        filter_upwards [e1, e2] with omega hω1 hω2
        exact ⟨hω1.comp hτ.tendsto_atTop, hω2.comp hτ.tendsto_atTop⟩)
  refine ⟨fun k φ1 φ2 h1 h2 L1 L2 e1 e2 => ?_, fun g hg φ1 φ2 h1 h2 L1 L2 e1 e2 => ?_⟩
  · exact key ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three (-(k : ℤ)))
      (zpow_le_one_of_nonpos₀ (by norm_num) (by omega))
      ⟨1 + -(k : ℤ), by rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]⟩
      (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i)
      (ContDiff.sum fun i _ => contDiff_const.mul (contDiff_apply ℝ ℝ i)) φ1 φ2 h1 h2 L1 L2 e1 e2
  · exact key 1 one_pos le_rfl ⟨1, by norm_num⟩ g hg φ1 φ2 h1 h2 L1 L2 e1 e2

end SubdiffusiveProcess.Paper
