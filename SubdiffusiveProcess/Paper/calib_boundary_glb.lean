import SubdiffusiveProcess.Paper.prop_conc_weighted_identification_affine
import SubdiffusiveProcess.Paper.calib_h0_large_cell_bounds

/-! Boundary-minimum identification for a coefficient sequence on the padded cube of ANY size.  This is
`aux_prop_conc_weighted_identification_affine_controlled` (prop_conc) with the harmonic-cell input supplied at mesh
level `J = 1` by `calib_h0_large_cell_bounds` instead of the small-cell `AllCellBounds` (no restriction `r ≤ 1`). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff BigOperators
namespace Paper
noncomputable section

/-- Controlled operator limit and one affine-response limit realize the boundary minimum at that slope. -/
theorem calib_boundary_glb
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (h3r : 0 < 3 * r)
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
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hE : ∀ v, E.energy v = limitFormEnergy G v)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (t alpha : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (hcell : calib_h0_large_cell_bounds z (3 * r) h3r a t alpha)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖u.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (aq : ℕ → PositiveCoefficient (centeredCube z r hr))
    (haq : ∀ n, (aq n).val =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] a n)
    (p : Fin d → ℝ) (L : ℝ)
    (hAffine : Tendsto (fun n => affineDirichletResponse (centeredCube_isBounded z hr) hP (aq n) p /
        (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
        atTop (𝓝 L)) :
    IsGLB (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r) E.toClosedForm Gamma
      (centeredCube z r hr : Set (SpatialCoordinates d)) (fun x => ∑ i, p i * x i))
      ((volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal * L) ∧
    (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r) E.toClosedForm Gamma
      (centeredCube z r hr : Set (SpatialCoordinates d)) (fun x => ∑ i, p i * x i)).Nonempty := by
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
  obtain ⟨Mesh⟩ := prop_conc_boundary_mesh hd z (3 * r) h3r S hS a ha hpos aC hAC
    beta hbeta hcomp hsupp betaH rfl 1 t alpha (by linarith only [halpha])
    (hcell beta hbeta betaH rfl)
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
      (𝓝 ((volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal * L)) := by
    simpa only [hnative, div_mul_cancel₀ _ hvol, mul_comm] using
      hAffine.mul_const (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal
  have hell n := aux_lem_cutoffs_pos_bounds (a n) (ha n) (hpos n)
    (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (lane2_isCompact_closure_centeredCube z h3r)
  have hmin := prop_conc_boundary_glb
    (fun z r hr F => ⟨inputs_classical_e5_locality d (centeredCube z r hr) F⟩)
    (fun z r hr F hC hL =>
      (inputs_classical_e5_relative_locality d (centeredCube z r hr) F hC hL).onCore)
    (fun z r hr F => ⟨inputs_classical_e5_energy d (centeredCube z r hr) F⟩)
    (inputs_contraction_witness d)
    z r hr h3r E Gamma _ rfl _ (DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure _ _)
    S hS a aC (fun n => (ha n).continuousOn) hAC hell
    (fun x => ∑ i, p i * x i) beta hbeta hcomp hsupp
    (fun x hx => heq x (frontier_subset_closure hx)) betaH rfl betaq rfl Mesh.u Mesh.uS Mesh.rep
    (fun k => oddGridCell_subset z h3r (triadicHalf 1) k)
    Mesh.harmonic Mesh.trace
    (fun n k => (Mesh.continuous n).mono (closure_mono (oddGridCell_subset z h3r (triadicHalf 1) k)))
    Mesh.boundary t alpha ht htd halpha halpha1 Mesh.E Mesh.H Mesh.E_nonneg Mesh.H_nonneg
    Mesh.energy Mesh.growth Mesh.holder Controls GN G hGN hConv hE hcore _ hScalar
  exact hmin


end
end Paper
