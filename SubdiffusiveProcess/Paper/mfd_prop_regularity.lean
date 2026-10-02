import SubdiffusiveProcess.Paper.conv_represented_joint_bounds
import SubdiffusiveProcess.Paper.conv_represented_joint_grids_buffered
import SubdiffusiveProcess.Paper.lem_cutoffs_damped_extrema_uniform
import SubdiffusiveProcess.Paper.inputs_Interp_witness
import SubdiffusiveProcess.Paper.inputs_contraction_witness
import SubdiffusiveProcess.Paper.limit_form_package_form
import SubdiffusiveProcess.Regularity.EnergyCoreTransport

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- Construct the killed limit form and its actual cube core, then retain that
same core for every Dirichlet realization of the specified extended energy.
The represented bounds are an internally supplied input to this auxiliary. -/
theorem aux_mfd_prop_regularity_realization
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f = (responseSolution S (a n)
      ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hconv : Tendsto GN atTop (𝓝 G))
    (hbounds : in_represented_bounds_seq d hd z r hr S a G) :
    ∀ E : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      (∀ v : DomainL2 (centeredCube z r hr),
        E.toClosedForm.energy v = limitFormEnergy G v) →
      (∃ C : Set (DomainL2 (centeredCube z r hr)),
        DirichletForm.IsCoreOn E.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) ∧
      DirichletForm.IsRegular E.toClosedForm := by
  obtain ⟨F, _hdom, hF, C, hcore⟩ := limit_form_package_form hd z r hr S hS a
    (fun n T hT u => inputs_contraction_witness d z r hr S hS (a n) T hT u)
    G GN hGN hconv hbounds
  intro E hE
  have hcoreE : DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C :=
    SubdiffusiveProcess.Regularity.isCoreOn_of_energy_eq (fun v => (hE v).trans (hF v).symm) hcore
  refine ⟨⟨C, hcoreE⟩, centeredCube z r hr, (centeredCube z r hr).isOpen, ?_, C, hcoreE⟩
  rw [Measure.restrict_apply (centeredCube z r hr).isOpen.measurableSet.compl]
  simp only [compl_inter_self, measure_empty]

/-- `mfd:prop-regularity`: the killed limit form is regular on the literal cube.
Both core densities hold for every Dirichlet realization of the limit energy,
simultaneously on all catalogue cubes and for both represented candidates.

The standing joint-grid catalogue carries exactly the represented local data.
Its exponent guards include `1/2 < beta < alpha < 1`, `1 + eta < 2 * alpha`
and `d - 1 < t < d`. Outside that admissible range this standing record cannot
hold, as in the paper's subsection. No collar error, finite mesh approximation,
cutoff, core, regularity or represented bounds bundle is a principal premise.
Those fields are supplied inside by the native collar/product and harmonic
mesh constructions. The threshold depends only on the dimension and eta. -/
theorem mfd_prop_regularity
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (alpha eta : ℝ) (heta : 0 < eta) :
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      M.delta ≤ delta0 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (field : Ω → BilateralField d) (envE envF : ℕ → Ω → BilateralField d)
      (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
      (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
      (GNE GNF : (i : ℕ) → ℕ → Ω →
        DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)))
      (GE GF : (i : ℕ) → Ω →
        DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)))
      (NE NF : ℕ → ℕ) (I : Paper.in_J d) (beta t : ℝ),
      conv_represented_joint_grids d hd M H Ω P field envE envF z r hr Sspace
        GNE GNF GE GF NE NF alpha eta I beta t →
      ∀ᵐ omega ∂P, ∀ i : ℕ,
        (∀ E : _root_.DirichletForm
            (volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))),
          (∀ v : DomainL2 (centeredCube (z i) (r i) (hr i)),
            E.toClosedForm.energy v = limitFormEnergy (GE i omega) v) →
          (∃ C : Set (DomainL2 (centeredCube (z i) (r i) (hr i))),
            DirichletForm.IsCoreOn E.toClosedForm
              (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) C) ∧
          DirichletForm.IsRegular E.toClosedForm) ∧
        (∀ E : _root_.DirichletForm
            (volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))),
          (∀ v : DomainL2 (centeredCube (z i) (r i) (hr i)),
            E.toClosedForm.energy v = limitFormEnergy (GF i omega) v) →
          (∃ C : Set (DomainL2 (centeredCube (z i) (r i) (hr i))),
            DirichletForm.IsCoreOn E.toClosedForm
              (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) C) ∧
          DirichletForm.IsRegular E.toClosedForm) := by
  obtain ⟨delta0, hdelta0, hext⟩ := lem_cutoffs_damped_extrema_uniform d hd eta heta
  refine ⟨delta0, hdelta0, ?_⟩
  intro M H hM Ω _ P _ field envE envF z r hr Sspace GNE GNF GE GF NE NF I beta t hjoint
  have hbounds := conv_represented_joint_bounds d hd M H Ω P field envE envF z r hr Sspace
    GNE GNF GE GF NE NF alpha eta (inputs_Interp_witness d hd)
    (fun hIR => hext M H hIR hM)
    (conv_represented_joint_grids_buffered d hd M H Ω P field envE envF z r hr Sspace
      GNE GNF GE GF NE NF alpha eta I beta t hjoint)
  obtain ⟨_, _, _, _, _, _, _, _, hS, hGN, hconv⟩ := hjoint.1
  filter_upwards [hbounds, hGN, hconv] with omega hbounds hGN hconv
  intro i
  constructor
  · exact aux_mfd_prop_regularity_realization d hd (z i) (r i) (hr i) (Sspace i) (hS i)
      (fun n => Lane4.cutoffPositiveCoefficient M H (envE n omega) (NE n) (z i) (hr i))
      (GE i omega) (fun n => GNE i n omega)
      (fun n f => (hGN i n f).1) (hconv i).1 (hbounds i).1
  · exact aux_mfd_prop_regularity_realization d hd (z i) (r i) (hr i) (Sspace i) (hS i)
      (fun n => Lane4.cutoffPositiveCoefficient M H (envF n omega) (NF n) (z i) (hr i))
      (GF i omega) (fun n => GNF i n omega)
      (fun n f => (hGN i n f).2) (hconv i).2 (hbounds i).2

end Paper


