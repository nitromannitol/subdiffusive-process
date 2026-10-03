module

public import SubdiffusiveProcess.Paper.conv_represented_limit_forms
public import SubdiffusiveProcess.Paper.limit_form_killed_consistency_cutoff

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- Both represented candidates give simultaneous regular strongly local form families,
compatible under killing on every nested pair of determining cubes. -/
theorem conv_represented_limit_family (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d) (envE envF : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (hjoint : aux_conv_represented_env_interface_joint d model H Ω P field envE envF z r hr
      Sspace GNE GNF GE GF NE NF)
    (hBounds : aux_conv_represented_env_interface_bounds d hd model H Ω P envE envF z r hr
      Sspace GE GF NE NF) :
    ∀ᵐ omega ∂P,
      ∃ (LE : ∀ i, aux_limit_form_package_limit_side d hd (z i) (r i) (hr i) (Sspace i)
          (GE i omega) (fun n => Lane4.cutoffPositiveCoefficient model H (envE n omega) (NE n) (z i) (hr i)))
        (LF : ∀ i, aux_limit_form_package_limit_side d hd (z i) (r i) (hr i) (Sspace i)
          (GF i omega) (fun n => Lane4.cutoffPositiveCoefficient model H (envF n omega) (NF n) (z i) (hr i))),
        (∀ i, DirichletForm.IsStronglyLocal (LE i).form.toClosedForm ∧
          DirichletForm.IsStronglyLocal (LF i).form.toClosedForm) ∧
        ∀ i j (hji : (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) ⊆
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))),
          (∃ D : Submodule ℝ (DomainL2 (centeredCube (z i) (r i) (hr i))),
            DirichletForm.IsKilledDomain (LE i).form.toClosedForm
              (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) D ∧
            (∀ w, w ∈ D ↔ ∃ u, u ∈ (LE j).form.domain ∧ zeroExtensionLp hji u = w) ∧
            (∀ u ∈ (LE j).form.domain, zeroExtensionLp hji u ∈ (LE i).form.domain ∧
              (LE i).form.energy (zeroExtensionLp hji u) = (LE j).form.energy u) ∧
            (∀ u ∈ (LE j).form.domain, ∀ v ∈ (LE j).form.domain,
              (LE i).form.form (zeroExtensionLp hji u) (zeroExtensionLp hji v) =
                (LE j).form.form u v)) ∧
          (∃ D : Submodule ℝ (DomainL2 (centeredCube (z i) (r i) (hr i))),
            DirichletForm.IsKilledDomain (LF i).form.toClosedForm
              (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) D ∧
            (∀ w, w ∈ D ↔ ∃ u, u ∈ (LF j).form.domain ∧ zeroExtensionLp hji u = w) ∧
            (∀ u ∈ (LF j).form.domain, zeroExtensionLp hji u ∈ (LF i).form.domain ∧
              (LF i).form.energy (zeroExtensionLp hji u) = (LF j).form.energy u) ∧
            (∀ u ∈ (LF j).form.domain, ∀ v ∈ (LF j).form.domain,
              (LF i).form.form (zeroExtensionLp hji u) (zeroExtensionLp hji v) =
                (LF j).form.form u v)) := by
  classical
  have hForms := conv_represented_limit_forms d hd model H Ω P field envE envF z r hr Sspace
    GNE GNF GE GF NE NF hjoint hBounds
  have hS := hjoint.2.2.2.2.2.2.2.2.1
  filter_upwards [hForms] with omega h
  choose LE hLE using (fun i => (h i).1)
  choose LF hLF using (fun i => (h i).2)
  refine ⟨LE, LF, fun i => ⟨hLE i, hLF i⟩, ?_⟩
  intro i j hji
  constructor
  · exact limit_form_killed_consistency_cutoff d hd (z i) (z j) (r i) (r j) (hr i) (hr j)
      hji (Sspace i) (Sspace j) (hS i) (hS j) model H (fun n => envE n omega) NE
      (GE i omega) (GE j omega) (LE i) (LE j)
  · exact limit_form_killed_consistency_cutoff d hd (z i) (z j) (r i) (r j) (hr i) (hr j)
      hji (Sspace i) (Sspace j) (hS i) (hS j) model H (fun n => envF n omega) NF
      (GF i omega) (GF j omega) (LF i) (LF j)

end Paper
