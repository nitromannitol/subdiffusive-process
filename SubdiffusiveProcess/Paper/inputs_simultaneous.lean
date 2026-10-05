module

public import SubdiffusiveProcess.Paper.inputs_J_witness
public import SubdiffusiveProcess.Paper.inputs_poincare_witness
public import SubdiffusiveProcess.Paper.inputs_extension_witness
public import SubdiffusiveProcess.Paper.inputs_Sf_witness
public import SubdiffusiveProcess.Paper.inputs_W_witness
public import SubdiffusiveProcess.Paper.inputs_Cp_witness
public import SubdiffusiveProcess.Paper.inputs_deterministic_witness
public import SubdiffusiveProcess.Paper.inputs_hES_witness
public import SubdiffusiveProcess.Paper.inputs_step_witness
public import SubdiffusiveProcess.Paper.inputs_baseline_witness
public import SubdiffusiveProcess.Paper.inputs_Interp_witness
public import SubdiffusiveProcess.Paper.inputs_BD_witness
public import SubdiffusiveProcess.Paper.inputs_BDQ_witness
public import SubdiffusiveProcess.Paper.inputs_contraction_witness
public import SubdiffusiveProcess.Paper.inputs_lifetime_witness
public import SubdiffusiveProcess.Paper.inputs_EM_witness
public import SubdiffusiveProcess.Paper.inputs_responses_witness
public import SubdiffusiveProcess.Paper.inputs_regularity_witness
public import SubdiffusiveProcess.Paper.inputs_iteration_witness

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Asymptotics
open MarkovProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem inputs_simultaneous (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    (∃ Jc : (_root_.SubdiffusiveProcess.Paper.in_J d),
∃ _Pc : (_root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc),
∃ _Xc : (_root_.SubdiffusiveProcess.Paper.in_extension d hd Jc),
∃ _Sf : (_root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd),
∃ _W : (_root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d),
∃ _Cp : (_root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d),
(@deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) ∧
(_root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality) ∧
(@cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) ∧
(@sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _) ∧
(CubeFractionalInterpolationInput d hd) ∧
(∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm) ∧
(∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm) ∧
(∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u) ∧
(∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
        (∃ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
          (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
          (∀ N, IsMarkovKernel (KN N)) ∧ in_crossing M H PN KN) →
        ∃ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
          (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
          (∀ N, IsMarkovKernel (KN N)) ∧ in_crossing M H PN KN ∧
            aux_cutoff_lifetime_package_LocalInput M H KN) ∧
(∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F) ∧
    (∃ delta0 Cresp : ℝ, 0 < delta0 ∧ 0 < Cresp ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), 0 < M.delta → M.delta ≤ delta0 →
      ∃ (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M),
        Rm.C ≤ Cresp ∧ Nonempty (_root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)))  := by
  classical
  have : NeZero d := ⟨by omega⟩
  let Jc : in_J d := Classical.choice (inputs_J_witness d hd)
  let Pc : in_poincare d hd Jc := Classical.choice (inputs_poincare_witness d hd Jc)
  let Xc : in_extension d hd Jc := Classical.choice (inputs_extension_witness d hd Jc)
  let Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd := Classical.choice (inputs_Sf_witness d hd)
  let W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d := Classical.choice (inputs_W_witness d)
  let Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d := Classical.choice (inputs_Cp_witness d)
  obtain ⟨Cresp, delta0, hCresp, hdelta0, hresponses⟩ :=
    inputs_responses_witness d hd 1 le_rfl
  refine ⟨Jc, Pc, Xc, Sf, W, Cp, inputs_deterministic_witness d hd,
    inputs_hES_witness, inputs_step_witness d hd, inputs_baseline_witness d hd,
    inputs_Interp_witness d hd, inputs_BD_witness d, inputs_BDQ_witness d,
    inputs_contraction_witness d, inputs_lifetime_witness d hd, inputs_EM_witness d,
    delta0, Cresp, hdelta0, hCresp, ?_⟩
  intro M hMpos hMle
  obtain ⟨Rm, hRm, hbank⟩ := hresponses M hMle
  exact ⟨Rm, inputs_regularity_witness d M, hRm,
    ⟨inputs_iteration_witness d hd M Jc⟩⟩

end SubdiffusiveProcess.Paper

