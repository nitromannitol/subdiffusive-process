module

public import SubdiffusiveProcess.Paper.conv_represented_thm_c1_hyp_grids_actual
public import SubdiffusiveProcess.Paper.conv_represented_joint_grids_buffered
public import SubdiffusiveProcess.Paper.conv_represented_thm_c1_bounds_actual
public import SubdiffusiveProcess.Paper.conv_represented_limit_family

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The actual model supplies simultaneous regular strongly local form families, compatible on all nested cubes. -/
theorem conv_represented_thm_c1_family_grids_actual
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hInterp : CubeFractionalInterpolationInput d hd)
    (E : in_J d) (Pin : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (alpha eta beta t : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (heta : 0 < eta) (hAeta : 1 + eta < 2 * alpha) (hb : 1 / 2 < beta) (hba : beta < alpha) :
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
          aux_conv_represented_env_interface_bounds d hd M H Ωh Ph env env Z R hR Sspace GE GF
            (fun n => NE (seq n)) (fun n => NF (seq n)) ∧
          (∀ᵐ omega ∂Ph,
      ∃ (LE : ∀ i, aux_limit_form_package_limit_side d hd (Z i) (R i) (hR i) (Sspace i)
          (GE i omega) (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (NE (seq n)) (Z i) (hR i)))
        (LF : ∀ i, aux_limit_form_package_limit_side d hd (Z i) (R i) (hR i) (Sspace i)
          (GF i omega) (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (NF (seq n)) (Z i) (hR i))),
        (∀ i, _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal (LE i).form.toClosedForm ∧
          _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal (LF i).form.toClosedForm) ∧
        ∀ i j (hji : (centeredCube (Z j) (R j) (hR j) : Set (SpatialCoordinates d)) ⊆
            (centeredCube (Z i) (R i) (hR i) : Set (SpatialCoordinates d))),
          (∃ D : Submodule ℝ (DomainL2 (centeredCube (Z i) (R i) (hR i))),
            _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (LE i).form.toClosedForm
              (centeredCube (Z j) (R j) (hR j) : Set (SpatialCoordinates d)) D ∧
            (∀ w, w ∈ D ↔ ∃ u, u ∈ (LE j).form.domain ∧ zeroExtensionLp hji u = w) ∧
            (∀ u ∈ (LE j).form.domain, zeroExtensionLp hji u ∈ (LE i).form.domain ∧
              (LE i).form.energy (zeroExtensionLp hji u) = (LE j).form.energy u) ∧
            (∀ u ∈ (LE j).form.domain, ∀ v ∈ (LE j).form.domain,
              (LE i).form.form (zeroExtensionLp hji u) (zeroExtensionLp hji v) =
                (LE j).form.form u v)) ∧
          (∃ D : Submodule ℝ (DomainL2 (centeredCube (Z i) (R i) (hR i))),
            _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (LF i).form.toClosedForm
              (centeredCube (Z j) (R j) (hR j) : Set (SpatialCoordinates d)) D ∧
            (∀ w, w ∈ D ↔ ∃ u, u ∈ (LF j).form.domain ∧ zeroExtensionLp hji u = w) ∧
            (∀ u ∈ (LF j).form.domain, zeroExtensionLp hji u ∈ (LF i).form.domain ∧
              (LF i).form.energy (zeroExtensionLp hji u) = (LF j).form.energy u) ∧
            (∀ u ∈ (LF j).form.domain, ∀ v ∈ (LF j).form.domain,
              (LF i).form.form (zeroExtensionLp hji u) (zeroExtensionLp hji v) =
                (LF j).form.form u v))) := by
  obtain ⟨deltaCat, hDeltaCat, hcat⟩ := conv_represented_thm_c1_hyp_grids_actual
    d hd hInterp E Pin X W Cp Sob alpha eta beta t ht htd ha0 ha1 heta hAeta hb hba
  obtain ⟨deltaExt, hDeltaExt, hext⟩ := lem_cutoffs_damped_extrema_uniform d hd eta heta
  refine ⟨min deltaCat deltaExt, lt_min hDeltaCat hDeltaExt, ?_⟩
  intro M Rm Sreg It H hH hDelta Z R hR Sspace hS hrat hcomp NE NF hNE hNF
  obtain ⟨seq, hseq, Ωh, mΩh, Ph, hPh, field, env, GNE, GNF, GE, GF, hjoint⟩ :=
    hcat M Rm Sreg It H hH (hDelta.trans (min_le_left _ _)) Z R hR Sspace hS hrat hcomp
      NE NF hNE hNF
  have : IsProbabilityMeasure Ph := hPh
  have hBuffered := conv_represented_joint_grids_buffered d hd M H Ωh Ph field env env
    Z R hR Sspace GNE GNF GE GF (fun n => NE (seq n)) (fun n => NF (seq n)) alpha eta E beta t hjoint
  have hBounds := conv_represented_joint_bounds d hd M H Ωh Ph field env env Z R hR Sspace
    GNE GNF GE GF (fun n => NE (seq n)) (fun n => NF (seq n)) alpha eta hInterp
    (fun hIR => hext M H hIR (hDelta.trans (min_le_right _ _))) hBuffered
  refine ⟨seq, hseq, Ωh, mΩh, Ph, hPh, field, env, GNE, GNF, GE, GF, hjoint, hBounds, ?_⟩
  exact conv_represented_limit_family d hd M H Ωh Ph field env env Z R hR Sspace GNE GNF GE GF
    (fun n => NE (seq n)) (fun n => NF (seq n)) hjoint.1 hBounds
end SubdiffusiveProcess.Paper
