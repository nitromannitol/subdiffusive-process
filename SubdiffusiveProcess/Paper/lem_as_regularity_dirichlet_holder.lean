module

public import SubdiffusiveProcess.Paper.lem_as_regularity_dirichlet_mesh
public import SubdiffusiveProcess.Paper.inputs_classical_grid_campanato
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Analysis.HolderWindowOscillation
public import SubdiffusiveProcess.Analysis.GridOscillationAbsorption
public import SubdiffusiveProcess.Probability.SubgeometricEnvelope

@[expose] public section

/-! Resolved Dirichlet windows and the stronger microscopic exponent yield a common Holder constant.
No coefficient-extrema bound uniform in the cutoff is used. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set Metric SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Dirichlet Holder increments have one constant uniform over cutoff, source and solution. -/
theorem lem_as_regularity_dirichlet_holder
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sf : SobolevFoundationalInput d hd)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (alpha : ℝ) (hal : 0 < alpha) (hal1 : alpha < 1) :
    ∃ delta0 : ℝ,0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
      (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d,ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,∃ K : ℝ,0 < K ∧
    ∀ N : ℕ,
    ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),0 ≤ Kf →
      AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
      (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),|F y| ≤ Kf) →
    ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),ContDiff ℝ 2 phi →
      c2Norm (closedCube (fun _ : Fin d => (1/2:ℝ)) 1 one_pos : Set (SpatialCoordinates d)) phi ≤ Cphi →
    ∀ b u : weakSobolevGraph (unitNeumannCube d),
      ((b : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] phi →
      SolvesDirichlet (cutoffPositiveCoefficient M H omega N (fun _ => (1/2:ℝ)) one_pos) F b u →
    ∀ U : SpatialCoordinates d → ℝ,Continuous U →
      ((u : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U →
      ∀ x ∈ (closedCube (fun _ : Fin d => (1/2:ℝ)) 1 one_pos : Set (SpatialCoordinates d)),
      ∀ y ∈ (closedCube (fun _ : Fin d => (1/2:ℝ)) 1 one_pos : Set (SpatialCoordinates d)),
        |U x-U y| ≤ K*(Kf+Cphi)*(Real.sqrt (∑ i : Fin d,(x i-y i)^2))^alpha := by
  let beta := (alpha+1)/2
  have hab : alpha < beta := by dsimp only [beta]; linarith only [hal1]
  have hb : 0 < beta := hal.trans hab
  have hb1 : beta < 1 := by dsimp only [beta]; linarith only [hal1]
  let t := (d:ℝ)-1/2
  have ht1 : (d:ℝ)-1 < t := by dsimp only [t]; linarith
  have ht2 : t < d := by dsimp only [t]; linarith
  obtain ⟨dm,hdm,hmesh⟩ := lem_as_regularity_dirichlet_mesh d hd E Pc Xc W Cp Sf D Step Dbase Interp alpha hal hal1
  obtain ⟨dg,hdg,hgrowth⟩ := prop_growth d hd E Pc Xc W Cp Sf t beta 1 (fun _ => 1)
    ht1 ht2 hb hb1 (fun _ => le_rfl)
  obtain ⟨Cc,hCc,hcamp⟩ := inputs_classical_grid_campanato d (by omega) alpha hal hal1
  refine ⟨min dm dg,lt_min hdm hdg,?_⟩
  intro M Rm Sreg It H hIR hdelta
  obtain ⟨Kg,Cg,hKg,hCg,hKg1,hgrowth⟩ := hgrowth M Rm Sreg It H hIR (hdelta.trans (min_le_right _ _))
    (fun _ => (1/2:ℝ)) 1 one_pos le_rfl
  have henv := ae_subgeometric_envelope_of_memLp_one (chaosSampleLaw M).toMeasure Kg (Cg 0)
    (by simpa only [ENNReal.ofReal_one] using hKg 0)
    (by simpa only [ENNReal.ofReal_one] using hCg 0) (beta-alpha) (sub_pos.mpr hab)
  filter_upwards [hmesh M Rm Sreg It H hIR (hdelta.trans (min_le_left _ _)),henv,hKg1,hgrowth]
    with omega hm he hKg0 hg
  obtain ⟨Km,hKm,hm⟩ := hm
  obtain ⟨B,hB,he⟩ := he
  let Dg := (d:ℝ)*(9/2)
  have hDg : 0 < Dg := by
    have hdp : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    exact mul_pos hdp (by norm_num)
  let Kmic := Dg^beta*B
  have hKmic : 0 < Kmic := mul_pos (Real.rpow_pos_of_pos hDg _) hB
  refine ⟨Cc*(Km+Kmic),mul_pos hCc (add_pos hKm hKmic),?_⟩
  intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb0 hsol U hU hrep x hx y hy
  have hCphi0 : 0 ≤ Cphi := (aux_prop_growth_holder_assembly_c2Norm_nonneg _ _).trans hCphi
  have hdata : 0 ≤ Kf+Cphi := add_nonneg hKf hCphi0
  obtain ⟨Ug,hUg,hUgAE,hUgH,hUgN⟩ := (hg N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb0 hsol).2
  have hUgmem : MemLp Ug 2 (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) :=
    (Lp.memLp ((u : SobolevData (unitNeumannCube d)).1)).ae_eq hUgAE
  have hgrid : ∀ k : ℕ,∀ a ∈ gridIndices d 1 (k+1),
      gridPoint (k+1) a ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
      let W0 := ball (gridPoint (k+1) a) ((9/2:ℝ)*(3:ℝ)^(-(k:ℤ))) ∩
        (unitNeumannCube d : Set (SpatialCoordinates d))
      normalizedL2On W0 (fun z => U z-averageOn W0 U) ≤
        ((Km+Kmic)*(Kf+Cphi))*(3:ℝ)^(-(alpha*k)) := by
    intro k a ha hw W0
    by_cases hk : k ≤ N
    · have hh := hm N k hk a ha hw F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb0 hsol U hU hrep
      refine hh.trans ?_
      gcongr
      linarith only [hKmic]
    · have hh := holder_ball_window_oscillation_le (by omega : 1 ≤ d) beta (Kg N omega*(Kf+Cphi))
        hb (mul_nonneg (zero_le_one.trans (hKg0 N)) hdata) Ug hUgmem
        (fun x hx y hy => cAlphaNorm_pair_le beta _ hb _ Ug hUgH hUgN x y hx hy) (gridPoint (k+1) a) hw
        ((9/2:ℝ)*(3:ℝ)^(-(k:ℤ))) (by positivity)
      dsimp only at hh
      have hosc := Section6BoundedMultiplier.normalizedL2On_sub_average_eq_of_ae_eq
        (ae_restrict_of_ae_restrict_of_subset (show W0 ⊆ (unitNeumannCube d : Set (SpatialCoordinates d)) from inter_subset_right)
          (hUgAE.symm.trans hrep))
      rw [hosc] at hh
      have hgeom : (d:ℝ)*((9/2:ℝ)*(3:ℝ)^(-(k:ℤ))) = Dg*(3:ℝ)^(-(k:ℤ)) := by dsimp only [Dg]; ring
      rw [hgeom] at hh
      have hs := grid_oscillation_absorb (Kg N omega) B Dg alpha beta N k hB.le hDg.le hab.le (by omega) (he N)
      have hm := mul_le_mul_of_nonneg_right hs hdata
      calc _ ≤ Kmic*(Kf+Cphi)*(3:ℝ)^(-(alpha*k)) := by dsimp only [Kmic]; nlinarith only [hh,hm]
           _ ≤ ((Km+Kmic)*(Kf+Cphi))*(3:ℝ)^(-(alpha*k)) := by gcongr; linarith only [hKm]
  have hh := hcamp U hU ((Km+Kmic)*(Kf+Cphi)) (by positivity) hgrid x hx y hy
  simpa only [← mul_assoc] using hh

end SubdiffusiveProcess.Paper
