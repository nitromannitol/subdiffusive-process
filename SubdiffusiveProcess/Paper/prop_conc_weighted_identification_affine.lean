module

public import SubdiffusiveProcess.Paper.prop_conc_form_gamma
public import SubdiffusiveProcess.Paper.prop_conc_actual_controls
public import SubdiffusiveProcess.Paper.prop_conc_controlled_affine_identification
public import SubdiffusiveProcess.Paper.prop_conc_actual_affine_identification

@[expose] public section

/-! Slope-by-slope form of the actual one-cell affine identification.  The existing identification
theorem demands convergence of the affine responses at every slope; for a resampled configuration the
limits are available only at finitely many slopes.  The proofs below are those of
`prop_conc_controlled_affine_identification` and `prop_conc_actual_affine_identification`, run for one
slope and one supplied limit value at a time, with the same operator limit, form and energy measure
common to all slopes. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff BigOperators
namespace Paper
noncomputable section

/-- Controlled operator limit and one affine-response limit realize the boundary minimum at that slope. -/
theorem aux_prop_conc_weighted_identification_affine_controlled
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
    (p : Fin d → ℝ) (L : ℝ)
    (hAffine : Tendsto (fun n => affineDirichletResponse (centeredCube_isBounded z hr) hP (aq n) p /
        (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
        atTop (𝓝 L)) :
    IsGLB (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r) E.toClosedForm Gamma
      (centeredCube z r hr : Set (SpatialCoordinates d)) (fun x => ∑ i, p i * x i))
      ((volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal * L) := by
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
  exact hmin.1

/-- Each actual padded-cube operator limit, with the responses converging at any chosen slopes, identifies
the boundary minima at those slopes; the form and energy measure are common to all slopes. -/
theorem prop_conc_weighted_identification_affine
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (_hr1 : r ≤ 1)
        (h3r : 0 < 3 * r)
        (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖u.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (N : ℕ → ℕ),
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (S : ResponseSpace (centeredCube z (3 * r) h3r)),
      S.space = killedSobolevGraph (centeredCube z (3 * r) h3r) →
      ∀ (GN : ℕ → DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
          DomainL2 (centeredCube z (3 * r) h3r))
        (G : DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
          DomainL2 (centeredCube z (3 * r) h3r)),
      (∀ n f, GN n f =
        (responseSolution S (cutoffPositiveCoefficient M H om (N n) z h3r)
          ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) →
      Tendsto GN atTop (𝓝 G) →
      ∃ E : _root_.DirichletForm
          (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))),
        (∀ v, E.energy v = limitFormEnergy G v) ∧
        (∃ C, DirichletForm.IsCoreOn E.toClosedForm
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C) ∧
        ∃ Gamma : DirichletForm.EnergyMeasure E.toClosedForm,
          ∀ (p : Fin d → ℝ) (L : ℝ),
            Tendsto (fun n => affineDirichletResponse (centeredCube_isBounded z hr) hP
              (cutoffPositiveCoefficient M H om (N n) z hr) p /
              (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
              atTop (𝓝 L) →
            IsGLB (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r) E.toClosedForm
              Gamma (centeredCube z r hr : Set (SpatialCoordinates d))
              (fun x => ∑ i, p i * x i))
              ((volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal * L) := by
  obtain ⟨deltaF, hdeltaF, hF⟩ := prop_conc_form_gamma d hd I Pin X W Cp Sob Interp
  obtain ⟨deltaC, hdeltaC, hC⟩ := prop_conc_actual_controls d hd I Pin X W Cp Sob Interp
    ((d : ℝ) - 1 / 2) (3 / 4) (by linarith only []) (by linarith only [])
    (by norm_num) (by norm_num)
  refine ⟨min deltaF deltaC, lt_min hdeltaF hdeltaC, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr hr1 h3r hP N
  haveI dimensionNonzero : NeZero d := ⟨by omega⟩
  let hPQ := centeredCube_killedPoincare z h3r
  filter_upwards [hF M Rm Sreg It H hIR (hdelta.trans (min_le_left _ _)) z (3 * r) h3r hPQ N,
    hC M Rm Sreg It H hIR (hdelta.trans (min_le_right _ _)) z (3 * r) h3r
      (killedResponseSpace hPQ) rfl N] with om hform hcontrols
  intro S hS GN G hGN hG
  have hSeq := aux_prop_conc_actual_affine_identification_response_space S hS hPQ
  subst S
  obtain ⟨E, hE, _hNC, hcore, _hreg, _hloc, Gamma⟩ := hform GN G hGN hG
  obtain ⟨Gamma⟩ := Gamma
  obtain ⟨seq, hseq, ⟨Controls⟩, hcell⟩ := hcontrols
  refine ⟨E, hE, hcore, Gamma, ?_⟩
  intro p L hL
  exact aux_prop_conc_weighted_identification_affine_controlled hd z r hr hr1 h3r
    (killedResponseSpace hPQ) rfl
    (fun n => cutoffCoefficient M H om (N (seq n)))
    (fun n => cutoffCoefficient_continuous M H om (N (seq n)))
    (fun n x => cutoffCoefficient_pos M H om (N (seq n)) x)
    (fun n => cutoffPositiveCoefficient M H om (N (seq n)) z h3r)
    (fun n => (cutoffPositiveCoefficient_representative M H om (N (seq n)) z h3r).2.2.2)
    Controls (fun n => GN (seq n)) G (fun n => hGN (seq n)) (hG.comp hseq.tendsto_atTop)
    E hE hcore Gamma ((d : ℝ) - 1 / 2) (3 / 4)
    (by linarith only []) (by linarith only []) (by norm_num) (by norm_num) hcell hP
    (fun n => cutoffPositiveCoefficient M H om (N (seq n)) z hr)
    (fun n => (cutoffPositiveCoefficient_representative M H om (N (seq n)) z hr).2.2.2)
    p L (hL.comp hseq.tendsto_atTop)

end
end Paper
