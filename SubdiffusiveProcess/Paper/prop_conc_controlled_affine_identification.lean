module

public import SubdiffusiveProcess.Paper.prop_conc_boundary_glb
public import SubdiffusiveProcess.Paper.prop_conc_boundary_mesh
public import SubdiffusiveProcess.Paper.prop_conc_local_affine_identified_order
public import SubdiffusiveProcess.Paper.inputs_classical_e5_locality
public import SubdiffusiveProcess.Paper.inputs_classical_e5_relative_locality
public import SubdiffusiveProcess.Paper.inputs_classical_e5_energy
public import SubdiffusiveProcess.Paper.inputs_contraction_witness
public import SubdiffusiveProcess.Geometry.SmoothCollar
public import SubdiffusiveProcess.Sobolev.NativeBoundaryResponse

@[expose] public section

/-! Identify the normalized affine matrix by the actual local boundary minimum.
The form lives on the padded cube, but only the energy measure on the observation
cell is minimized. No total padded energy is identified with the affine response. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Controlled operator and affine-response limits realize the specified one-cell identification. -/
theorem prop_conc_controlled_affine_identification
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (h3r : 0 < 3 * r)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (hS : S.space = killedSobolevGraph (centeredCube z (3 * r) h3r))
    (a : ℕ → SpatialCoordinates d → ℝ) (ha : ∀ n, Continuous (a n))
    (hpos : ∀ n x, 0 < a n x)
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (hAC : ∀ n, (aC n).val =ᵐ[volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] a n)
    (Controls : aux_prop_conc_controlled_forms_analytic_controls d hd z (3 * r) h3r S aC)
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
    (hcell : aux_prop_conc_mesh_cutoff_family_AllCellBounds z (3 * r) h3r a t alpha)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖u.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (aq : ℕ → PositiveCoefficient (centeredCube z r hr))
    (haq : ∀ n, (aq n).val =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] a n)
    (Amat : Matrix (Fin d) (Fin d) ℝ)
    (hAffine : ∀ p : Fin d → ℝ,
      Tendsto (fun n => affineDirichletResponse (centeredCube_isBounded z hr) hP (aq n) p /
        (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
        atTop (𝓝 (p ⬝ᵥ Amat.mulVec p))) :
    Nonempty (aux_prop_conc_LocalAffineIdentification (centeredCube z (3 * r) h3r)
      (centeredCube z r hr : Set (SpatialCoordinates d)) G Amat) := by
  have hqQ : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by linarith only [hr]))
  refine ⟨⟨hqQ, E, hE, hcore, Gamma, ?_⟩⟩
  intro p
  obtain ⟨beta, hbeta, hcomp, hsupp, heq⟩ := exists_smooth_cube_collar z r hr h3r
    (fun x => ∑ i, p i * x i) (by
      have hf : (fun x : SpatialCoordinates d => ∑ i, p i * x i) = affineSlope p := by
        funext x
        exact (affineSlope_apply p x).symm
      rw [hf]
      exact (affineSlope p).contDiff)
  let betaH : H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    H1Function.ofContDiff (centeredCube z (3 * r) h3r).isOpen (hbeta.of_le (by norm_num)) hcomp
  let betaq : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    H1Function.ofContDiff (centeredCube z r hr).isOpen (hbeta.of_le (by norm_num)) hcomp
  have hside : 3 * r / (3 : ℝ) ^ (1 : ℕ) ≤ 1 := by
    rw [pow_one, div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    linarith only [hr1]
  obtain ⟨Mesh⟩ := prop_conc_boundary_mesh hd z (3 * r) h3r S hS a ha hpos aC hAC
    beta hbeta hcomp hsupp betaH rfl 1 t alpha (by linarith only [halpha])
    (hcell 1 hside beta hbeta betaH rfl)
  have hnative n : cellDirichletInfimum (a n) (centeredCube z r hr : Set (SpatialCoordinates d)) betaq =
      affineDirichletResponse (centeredCube_isBounded z hr) hP (aq n) p := by
    apply cellDirichletInfimum_eq_affineDirichletResponse
      (centeredCube_isBounded z hr) hP (aq n) (a n) (haq n) betaq p
    filter_upwards [ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx
    exact heq x (subset_closure hx)
  have hvol : (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≠ 0 :=
    (centeredCube_volume_pos z hr).ne'
  have hScalar : Tendsto (fun n => cellDirichletInfimum (a n)
      (centeredCube z r hr : Set (SpatialCoordinates d)) betaq) atTop
      (𝓝 ((volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal *
        (p ⬝ᵥ Amat.mulVec p))) := by
    simpa only [hnative, div_mul_cancel₀ _ hvol, mul_comm] using
      (hAffine p).mul_const (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal
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
    (fun x => ∑ i, p i * x i) beta hbeta hcomp hsupp
    (fun x hx => heq x (frontier_subset_closure hx)) betaH rfl betaq rfl Mesh.u Mesh.uS Mesh.rep
    (fun k => oddGridCell_subset z h3r (triadicHalf 1) k)
    Mesh.harmonic Mesh.trace
    (fun n k => (Mesh.continuous n).mono (closure_mono (oddGridCell_subset z h3r (triadicHalf 1) k)))
    Mesh.boundary t alpha ht htd halpha halpha1 Mesh.E Mesh.H Mesh.E_nonneg Mesh.H_nonneg
    Mesh.energy Mesh.growth Mesh.holder Controls GN G hGN hConv hE hcore _ hScalar
  exact hmin.1

end
end SubdiffusiveProcess.Paper
