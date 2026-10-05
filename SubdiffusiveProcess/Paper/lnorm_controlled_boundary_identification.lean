module

public import SubdiffusiveProcess.Paper.prop_conc_boundary_glb
public import SubdiffusiveProcess.Paper.prop_conc_boundary_mesh
public import SubdiffusiveProcess.Paper.inputs_classical_e5_locality
public import SubdiffusiveProcess.Paper.inputs_classical_e5_relative_locality
public import SubdiffusiveProcess.Paper.inputs_classical_e5_energy
public import SubdiffusiveProcess.Paper.inputs_contraction_witness
public import SubdiffusiveProcess.Paper.lem_extension_trace_class_transport
public import SubdiffusiveProcess.Geometry.SmoothCollar
public import SubdiffusiveProcess.Sobolev.NativeContinuousBoundaryInfimum

@[expose] public section

/-! Identify a smooth scalar boundary-response limit from its padded operator
limit on any positive cube. Analytic controls and cell bounds remain explicit. -/

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper
noncomputable section

/-- A controlled smooth boundary-response limit equals the local minimum for its padded limiting form. -/
theorem lnorm_controlled_boundary_identification
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (h3r : 0 < 3 * r)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (hS : S.space = killedSobolevGraph (centeredCube z (3 * r) h3r))
    (a : ℕ → SpatialCoordinates d → ℝ) (ha : ∀ n, Continuous (a n))
    (hpos : ∀ n x, 0 < a n x)
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (hAC : ∀ n, (aC n).val =ᵐ[volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] a n)
    (A : aux_prop_conc_controlled_forms_analytic_controls d hd z (3 * r) h3r S aC)
    (GN : ℕ → DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
      DomainL2 (centeredCube z (3 * r) h3r))
    (G : DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
      DomainL2 (centeredCube z (3 * r) h3r))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (aC n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hE : ∀ v, E.energy v = limitFormEnergy G v)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (t alpha : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (hcell : ∀ theta : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ theta →
      ∀ thetaH : H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
      thetaH.toFun = theta →
      aux_prop_conc_mesh_cutoff_family_CellBounds z (3 * r) h3r a t alpha 1 thetaH)
    (aq : ℕ → PositiveCoefficient (centeredCube z r hr))
    (haq : ∀ n, (aq n).val =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] a n)
    (g : SpatialCoordinates d → ℝ) (hg : ContDiff ℝ ∞ g)
    (L : ℝ)
    (hScalar : Tendsto (fun n => sInf (continuousBoundaryEnergies z r hr (aq n) g))
      atTop (𝓝 L)) :
    L = sInf (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r)
      E.toClosedForm Gamma (centeredCube z r hr : Set (SpatialCoordinates d)) g) := by
  have dimensionNonzero : NeZero d := ⟨by omega⟩
  obtain ⟨beta, hbeta, hcomp, hsupp, heq⟩ := exists_smooth_cube_collar z r hr h3r g hg
  let betaH : H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    H1Function.ofContDiff (centeredCube z (3 * r) h3r).isOpen
      (hbeta.of_le (by norm_num)) hcomp
  let betaq : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    H1Function.ofContDiff (centeredCube z r hr).isOpen (hbeta.of_le (by norm_num)) hcomp
  obtain ⟨Mesh⟩ := prop_conc_boundary_mesh hd z (3 * r) h3r S hS a ha hpos aC hAC
    beta hbeta hcomp hsupp betaH rfl 1 t alpha (by linarith only [halpha])
    (hcell beta hbeta betaH rfl)
  have hnative n : cellDirichletInfimum (a n) (centeredCube z r hr : Set (SpatialCoordinates d)) betaq =
      sInf (continuousBoundaryEnergies z r hr (aq n) g) :=
    cellDirichletInfimum_eq_continuousBoundaryInfimum z r hr
      (lem_extension_trace_class_transport hd z r hr) (centeredCube_killedPoincare z hr)
      (aq n) (a n) (haq n) betaq g hbeta.continuous.continuousOn
      (fun x hx => heq x (frontier_subset_closure hx))
  have hell n := aux_lem_cutoffs_pos_bounds (a n) (ha n) (hpos n)
    (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (lane2_isCompact_closure_centeredCube z h3r)
  have hmin := prop_conc_boundary_glb
    (fun z r hr F => ⟨inputs_classical_e5_locality d (centeredCube z r hr) F⟩)
    (fun z r hr F hC hL =>
      (inputs_classical_e5_relative_locality d (centeredCube z r hr) F hC hL).onCore)
    (fun z r hr F => ⟨inputs_classical_e5_energy d (centeredCube z r hr) F⟩)
    (inputs_contraction_witness d)
    z r hr h3r E Gamma _ rfl _ (_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure _ _)
    S hS a aC (fun n => (ha n).continuousOn) hAC hell
    g beta hbeta hcomp hsupp (fun x hx => heq x (frontier_subset_closure hx))
    betaH rfl betaq rfl Mesh.u Mesh.uS Mesh.rep
    (fun k => oddGridCell_subset z h3r (triadicHalf 1) k)
    Mesh.harmonic Mesh.trace
    (fun n k => (Mesh.continuous n).mono (closure_mono (oddGridCell_subset z h3r (triadicHalf 1) k)))
    Mesh.boundary t alpha ht htd halpha halpha1 Mesh.E Mesh.H Mesh.E_nonneg Mesh.H_nonneg
    Mesh.energy Mesh.growth Mesh.holder A GN G hGN hConv hE hcore L
    (hScalar.congr (fun n => (hnative n).symm))
  exact (hmin.1.csInf_eq hmin.2).symm

end
end SubdiffusiveProcess.Paper
