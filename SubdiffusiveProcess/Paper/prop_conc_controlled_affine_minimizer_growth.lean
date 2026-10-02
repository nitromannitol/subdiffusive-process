import SubdiffusiveProcess.Paper.prop_conc_controlled_affine_identification
import SubdiffusiveProcess.Paper.prop_conc_boundary_minimizer_growth
import SubdiffusiveProcess.Paper.prop_conc_center_mesh_measure
import SubdiffusiveProcess.Paper.prop_conc_affine_cutoff_growth

/-! Controlled affine limits admit actual local minimizers with their quantitative growth bound.
The energy identity and all measure bounds use only the observation cell. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
namespace Paper
noncomputable section

/-- The actual affine cell minimizer inherits any eventual growth bound of its cutoff energy measures. -/
theorem prop_conc_controlled_affine_minimizer_growth
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
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hE : ∀ v, E.energy v = limitFormEnergy G v)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (t alpha : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (hcell : aux_prop_conc_mesh_cutoff_family_AllCellBounds z (3 * r) h3r a t alpha)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖u.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (aq : ℕ → PositiveCoefficient (centeredCube z r hr))
    (haq : ∀ n, (aq n).val =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] a n)
    (p : Fin d → ℝ) (L Bg tg : ℝ)
    (hResponse : Tendsto (fun n => affineDirichletResponse (centeredCube_isBounded z hr) hP
      (aq n) p) atTop (𝓝 L))
    (hgrowth : ∀ x ∈ centeredCube z r hr, ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      ∀ᶠ n in atTop,
        aux_prop_conc_affine_cutoff_growth_measure (centeredCube_isBounded z hr) hP (aq n) p
          (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
            ENNReal.ofReal (Bg * rho ^ tg)) :
    ∃ (U : DomainL2 (centeredCube z (3 * r) h3r)) (Uc : SpatialCoordinates d → ℝ),
      U ∈ E.toClosedForm.domain ∧
      ContinuousOn Uc (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (U : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Uc ∧
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), Uc x = ∑ i, p i * x i) ∧
      Gamma.measure U (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0 ∧
      (∀ phi ∈ E.toClosedForm.killedCoreClosure (centeredCube z r hr : Set (SpatialCoordinates d)),
        E.form U phi = 0) ∧
      (Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal = L ∧
      (∀ V ∈ E.toClosedForm.domain, ∀ Vc : SpatialCoordinates d → ℝ,
        ContinuousOn Vc (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
        (V : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Vc →
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), Vc x = ∑ i, p i * x i) →
        (Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
          (Gamma.measure V (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) ∧
      ∀ x ∈ centeredCube z r hr, ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
        Gamma.measure U (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
          ENNReal.ofReal (Bg * rho ^ tg) := by
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
  have hScalar : Tendsto (fun n => cellDirichletInfimum (a n)
      (centeredCube z r hr : Set (SpatialCoordinates d)) betaq) atTop (𝓝 L) := by
    simpa only [hnative] using hResponse
  have hmeshgrowth : ∀ x ∈ centeredCube z r hr, ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      ∀ᶠ n in atTop,
        ((volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((aC n).val y *
            ∑ i : Fin d, ((Mesh.uS n).val.2 i y) ^ 2)))
          (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
            ENNReal.ofReal (Bg * rho ^ tg) := by
    intro x hx rho hrho hrho1
    filter_upwards [hgrowth x hx rho hrho hrho1] with n hn
    have he := prop_conc_center_mesh_measure z r hr h3r S a aC hAC beta betaH rfl t alpha
      Mesh hP aq haq p (fun y hy => heq y (subset_closure hy)) n
    have he' := congrArg (fun mu : Measure (SpatialCoordinates d) =>
      mu (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))) he
    dsimp only at he'
    rw [Measure.restrict_apply (Metric.isOpen_ball.measurableSet.inter
      (centeredCube z r hr).isOpen.measurableSet), Set.inter_assoc, Set.inter_self] at he'
    rw [he']
    simpa only [aux_prop_conc_affine_cutoff_growth_measure, sobolevGradient, Finset.mul_sum] using hn
  have hell n := aux_lem_cutoffs_pos_bounds (a n) (ha n) (hpos n)
    (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (lane2_isCompact_closure_centeredCube z h3r)
  have hmin := prop_conc_boundary_minimizer_growth
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
    Mesh.energy Mesh.growth Mesh.holder Controls GN G hGN hConv hE hcore L hScalar Bg tg hmeshgrowth
  exact hmin

end
end Paper
