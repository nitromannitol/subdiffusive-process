module

public import SubdiffusiveProcess.Paper.goodext_represented_controls_with_bank
public import SubdiffusiveProcess.Paper.calib_h0_large_cell_bounds_of_growth
public import SubdiffusiveProcess.Paper.lnorm_controlled_boundary_identification
public import SubdiffusiveProcess.Paper.prop_conc_form_gamma
public import SubdiffusiveProcess.Paper.mfd_prop_as_forms
public import SubdiffusiveProcess.Paper.prop_as_dirichlet
public import SubdiffusiveProcess.Regularity.EnergyCoreTransport
public import SubdiffusiveProcess.Compactness.OperatorConvergence

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open _root_.SubdiffusiveProcess.EllipticRegularity _root_.SubdiffusiveProcess.Paper
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace SubdiffusiveProcess.AuditExports

/-- A common subsequence carries the actual analytic controls and the level-one
cell bounds on every positive cube. Large cells use the proved all-cube growth
conversion; the mesh stays at level one. -/
theorem actual_controls_level_one
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd)
    (t alpha : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
        (S : ResponseSpace (centeredCube z R hR))
        (_hS : S.space = killedSobolevGraph (centeredCube z R hR)) (N : ℕ → ℕ),
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
        Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd z R hR S
          (fun n => cutoffPositiveCoefficient M H om (N (seq n)) z hR)) ∧
        calib_h0_large_cell_bounds z R hR
          (fun n => cutoffCoefficient M H om (N (seq n))) t alpha := by
  classical
  have dimensionNonzero : NeZero d := ⟨by omega⟩
  obtain ⟨deltaSmall, hdeltaSmall, hsmall⟩ :=
    prop_growth d hd I Pin X W Cp Sob t alpha 1 (fun _ => 1)
      ht htd ha ha1 (fun _ => le_rfl)
  obtain ⟨deltaLarge, hdeltaLarge, hlarge⟩ :=
    prop_growth_large_root d hd I Pin X W Cp Sob t alpha 1 (fun _ => 1)
      ht htd ha ha1 (fun _ => le_rfl)
  obtain ⟨deltaControls, hdeltaControls, hcontrols⟩ :=
    goodext_represented_controls_with_bank d hd I Pin X W Cp Sob Interp
      t alpha ht htd ha ha1
  refine ⟨min (min deltaSmall deltaLarge) deltaControls,
    lt_min (lt_min hdeltaSmall hdeltaLarge) hdeltaControls, ?_⟩
  intro M Rm Sreg It H hIR hdelta z R hR S hS N
  let Idx := OddGridIndex d (triadicHalf 1)
  let cz : Idx → SpatialCoordinates d := fun k => oddGridCenter z R (triadicHalf 1) k
  let cr : ℝ := R / (2 * (triadicHalf 1 : ℝ) + 1)
  have hcr : 0 < cr := div_pos hR (by positivity)
  have hdeltaSmall' : M.delta ≤ deltaSmall :=
    hdelta.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hdeltaLarge' : M.delta ≤ deltaLarge :=
    hdelta.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hcell (k : Idx) := if hside : cr ≤ 1 then
      hsmall M Rm Sreg It H hIR hdeltaSmall' (cz k) cr hcr hside
    else hlarge M Rm Sreg It H hIR hdeltaLarge' (cz k) cr hcr (lt_of_not_ge hside)
  choose Kcell Ccell hmemCell hnormCell _hgeCell hgrowthCell using hcell
  have hmem : ∀ k n, MemLp (fun om => Kcell k (N n) om) 1
      (chaosSampleLaw M).toMeasure := by
    intro k n
    simpa only [ENNReal.ofReal_one] using hmemCell k 0 (N n)
  have hnorm : ∀ k n, eLpNorm (fun om => Kcell k (N n) om) 1
      (chaosSampleLaw M).toMeasure ≤ (Ccell k 0).toNNReal := by
    intro k n
    simpa only [ENNReal.ofReal_one, ENNReal.coe_toNNReal] using! hnormCell k 0 (N n)
  have hgood := hcontrols M Rm Sreg It H hIR (hdelta.trans (min_le_right _ _))
    z R hR S hS N (BilateralField d) (chaosSampleLaw M).toMeasure
    (fun _ om => om) (fun _ => measurable_id) (fun _ => Measure.map_id)
    Idx (fun k n om => Kcell k (N n) om) (fun k => (Ccell k 0).toNNReal) hmem hnorm
  filter_upwards [hgood, ae_all_iff.mpr hgrowthCell] with om hgoodOm hgrowthOm
  obtain ⟨seq, hseq, hA, _hsmallCells, hbank⟩ := hgoodOm
  refine ⟨seq, hseq, hA, ?_⟩
  have ht0 : 0 ≤ t := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [hdR, ht]
  apply calib_h0_large_cell_bounds_of_growth hd z R hR
    (fun n => cutoffCoefficient M H om (N (seq n))) t alpha ht0 ha
  intro k
  obtain ⟨B, _hB, hBound⟩ := hbank k
  refine ⟨(fun n => cutoffPositiveCoefficient M H om (N (seq n)) (cz k) hcr),
    (fun n => Kcell k (N (seq n)) om), B, ?_, ?_, ?_⟩
  · intro n
    exact (cutoffPositiveCoefficient_representative M H om (N (seq n)) (cz k) hcr).2.2.2
  · intro n
    exact (le_abs_self _).trans (hBound n)
  · intro n
    exact hgrowthOm k (N (seq n))

/-- Every existing smooth scalar limit is the local boundary minimum of its actual padded operator limit. -/
theorem actual_boundary_identity_all_cubes
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (N : ℕ → ℕ),
      let h3r : 0 < 3 * r := mul_pos zero_lt_three hr
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ G : DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
        DomainL2 (centeredCube z (3 * r) h3r),
      Tendsto (fun n => volumeResponseOperator
        (killedResponseSpace (centeredCube_killedPoincare z h3r))
        (cutoffPositiveCoefficient M H om (N n) z h3r)) atTop (𝓝 G) →
      ∀ (E : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
        (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm),
      (∀ v, E.energy v = limitFormEnergy G v) →
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C) →
      ∀ g : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ g → ∀ L : ℝ,
      Tendsto (fun n => sInf (continuousBoundaryEnergies z r hr
        (cutoffPositiveCoefficient M H om (N n) z hr) g)) atTop (𝓝 L) →
      L = sInf (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r)
        E.toClosedForm Gamma (centeredCube z r hr : Set (SpatialCoordinates d)) g) := by
  obtain ⟨delta0, hdelta0, h⟩ := actual_controls_level_one
    d hd I Pin X W Cp Sob Interp ((d : ℝ) - 1 / 2) (3 / 4)
    (by linarith only []) (by linarith only []) (by norm_num) (by norm_num)
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr N
  let h3r : 0 < 3 * r := mul_pos zero_lt_three hr
  let S := killedResponseSpace (centeredCube_killedPoincare z h3r)
  have hcontrols := h M Rm Sreg It H hIR hdelta z (3 * r) h3r S rfl N

  filter_upwards [hcontrols] with om hom
  intro G hConv E Gamma hE hcore g hg L hScalar
  obtain ⟨seq, hseq, ⟨A⟩, hcell⟩ := hom
  exact lnorm_controlled_boundary_identification hd z r hr h3r S rfl
    (fun n => cutoffCoefficient M H om (N (seq n)))
    (fun n => cutoffCoefficient_continuous M H om (N (seq n)))
    (fun n x => cutoffCoefficient_pos M H om (N (seq n)) x)
    (fun n => cutoffPositiveCoefficient M H om (N (seq n)) z h3r)
    (fun n => (cutoffPositiveCoefficient_representative M H om (N (seq n)) z h3r).2.2.2)
    A (fun n => volumeResponseOperator S (cutoffPositiveCoefficient M H om (N (seq n)) z h3r))
    G (fun n f => volumeResponseOperator_apply _ _ f) (hConv.comp hseq.tendsto_atTop)
    E hE hcore Gamma ((d : ℝ) - 1 / 2) (3 / 4)
    (by linarith only []) (by linarith only []) (by norm_num) (by norm_num)
    hcell (fun n => cutoffPositiveCoefficient M H om (N (seq n)) z hr)
    (fun n => (cutoffPositiveCoefficient_representative M H om (N (seq n)) z hr).2.2.2)
    g hg L (hScalar.comp hseq.tendsto_atTop)


/-- The cube-specific core belongs to every realization of the actual Green
energy, including the form already selected by the forms theorem. Its open
state space is the padded cube itself. -/
theorem actual_padded_cube_core
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (N : ℕ → ℕ),
      let h3r : 0 < 3 * r := mul_pos zero_lt_three hr
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ G : DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
        DomainL2 (centeredCube z (3 * r) h3r),
      Tendsto (fun n => volumeResponseOperator
        (killedResponseSpace (centeredCube_killedPoincare z h3r))
        (cutoffPositiveCoefficient M H om (N n) z h3r)) atTop (𝓝 G) →
      ∀ E : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))),
      (∀ v, E.energy v = limitFormEnergy G v) →
      ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C := by
  obtain ⟨delta0, hdelta0, hforms⟩ := prop_conc_form_gamma d hd I Pin X W Cp Sob Interp
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr N
  let h3r : 0 < 3 * r := mul_pos zero_lt_three hr
  filter_upwards [hforms M Rm Sreg It H hIR hdelta z (3 * r) h3r
    (centeredCube_killedPoincare z h3r) N] with om hform
  intro G hConv E hE
  obtain ⟨F, hF, _hNC, ⟨C, hcore⟩, _hreg, _hloc, _hGamma⟩ :=
    hform _ G (fun n f => volumeResponseOperator_apply _ _ f) hConv
  exact ⟨C, SubdiffusiveProcess.Regularity.isCoreOn_of_energy_eq
    (fun v => (hE v).trans (hF v).symm) hcore⟩

/-- Upgrade the actual strong inverse limit using the uniform fractional
coercivity supplied by limiting_local_energy. This uses the same compactness
and interpolation suppliers as the forms assembly, on an arbitrary center. -/
theorem actual_inverse_norm_of_strong
    {d : ℕ} (hd : 2 ≤ d) (Sob : SobolevFoundationalInput d hd)
    (Interp : CubeFractionalInterpolationInput d hd)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (G : DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR))
    (hStrong : ∀ f : DomainL2 (centeredCube z R hR),
      Tendsto (fun n => (responseSolution
        (killedResponseSpace (aux_mfd_prop_as_forms_poincare hd z R hR))
        (cutoffPositiveCoefficient M H om n z hR)
        ((sobolevVolumeLoad f).comp
          (killedResponseSpace (aux_mfd_prop_as_forms_poincare hd z R hR)).space.subtypeL)).val.1)
        atTop (𝓝 (G f)))
    (K : ℝ) (hK : 0 < K)
    (hCoer : ∀ (n : ℕ) (v : killedSobolevGraph (centeredCube z R hR)),
      cubeFractionalSqNorm hd z R hR threeQuarterOrder v.val.1 ≤
        K * sobolevCoefficientForm (cutoffPositiveCoefficient M H om n z hR) v.val v.val) :
    Tendsto (fun n => volumeResponseOperator
      (killedResponseSpace (aux_mfd_prop_as_forms_poincare hd z R hR))
      (cutoffPositiveCoefficient M H om n z hR)) atTop (𝓝 G) := by
  let S := killedResponseSpace (aux_mfd_prop_as_forms_poincare hd z R hR)
  let a := fun n => cutoffPositiveCoefficient M H om n z hR
  let GN := fun n => volumeResponseOperator S (a n)
  have hCoercive := aux_prop_as_forms_hCoercive hd Sob z R hR
    (aux_mfd_prop_as_forms_poincare hd z R hR) a K hCoer
  have hCompact := prop_killed_inverse_collective_compactness d hd z R hR S a GN
    (fun n f => volumeResponseOperator_apply _ _ f) Interp
    (volume.real (centeredCube z R hR : Set (SpatialCoordinates d)) * K)
    (mul_pos (centeredCube_volume_pos z hR) hK) hCoercive
  refine tendsto_operatorNorm_of_collectively_compact_symmetric ?_ hCompact ?_
  · intro n x y
    rw [volumeResponseOperator_apply, volumeResponseOperator_apply, real_inner_comm]
    exact volumeResponse_pairing_symm S (a n) y x
  · intro f
    simpa only [GN, volumeResponseOperator_apply] using hStrong f

/-- S14 with a prescribed characterized infrared field. On every countable
family of positive triadic cubes, the actual smooth response limit is the
boundary minimum for the same padded Green limit and its actual form and
energy measure. All foundational and realization suppliers are constructed. -/
theorem boundary_response_identity_of_infrared
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_hIR : InfraredCharacterization M H),
      ∀ (I : Type) [Countable I]
        (z : I → SpatialCoordinates d) (r : I → ℝ) (hr : ∀ i, 0 < r i)
        (_htriadic : ∀ i, ∃ j : ℤ, r i = (3 : ℝ) ^ j)
        (phi : I → SpatialCoordinates d → ℝ) (_hphi : ∀ i, ContDiff ℝ ∞ (phi i)),
      let h3r : ∀ i, 0 < 3 * r i := fun i => mul_pos zero_lt_three (hr i)
      ∃ (G : (i : I) → BilateralField d →
          DomainL2 (centeredCube (z i) (3 * r i) (h3r i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (3 * r i) (h3r i)))
        (L : I → BilateralField d → ℝ),
        (∀ i, Measurable (G i)) ∧ (∀ i, Measurable (L i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ i,
          Tendsto (fun n => volumeResponseOperator
            (killedResponseSpace (aux_mfd_prop_as_forms_poincare hd (z i) (3 * r i) (h3r i)))
            (cutoffPositiveCoefficient M H om n (z i) (h3r i))) atTop (𝓝 (G i om)) ∧
          (∀ G' : DomainL2 (centeredCube (z i) (3 * r i) (h3r i)) →L[ℝ]
              DomainL2 (centeredCube (z i) (3 * r i) (h3r i)),
            Tendsto (fun n => volumeResponseOperator
              (killedResponseSpace (aux_mfd_prop_as_forms_poincare hd (z i) (3 * r i) (h3r i)))
              (cutoffPositiveCoefficient M H om n (z i) (h3r i))) atTop (𝓝 G') →
            G' = G i om) ∧
          ∃ (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict
              (centeredCube (z i) (3 * r i) (h3r i) : Set (SpatialCoordinates d))))
            (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm),
            (∀ v, E.energy v = limitFormEnergy (G i om) v) ∧
            (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
              (centeredCube (z i) (3 * r i) (h3r i) : Set (SpatialCoordinates d)) C) ∧
            _root_.SubdiffusiveProcess.DirichletForm.IsRegular E.toClosedForm ∧
            _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal E.toClosedForm ∧
            0 ≤ L i om ∧
            Tendsto (fun n => sInf (continuousBoundaryEnergies (z i) (r i) (hr i)
              (cutoffPositiveCoefficient M H om n (z i) (hr i)) (phi i)))
              atTop (𝓝 (L i om)) ∧
            L i om = sInf (aux_thm_prop_boundary_energy_set
              (centeredCube (z i) (3 * r i) (h3r i)) E.toClosedForm Gamma
              (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) (phi i)) := by
  classical
  have dimensionNonzero : NeZero d := ⟨by omega⟩
  obtain ⟨Jc, Pc, Xc, Sob, W, Cp, D, hES, Step, Dbase, Interp, BD, BDQ,
    hcontract, _hlife, EM, deltaResponses, _Cresp, hdeltaResponses, _hCresp, hResponses⟩ :=
    inputs_simultaneous d hd
  obtain ⟨deltaLimit, hdeltaLimit, hLimit⟩ :=
    limiting_local_energy d hd Jc Pc Xc Sob W Cp D hES Step Dbase Interp BD BDQ hcontract
  obtain ⟨deltaCut, hdeltaCut, hCut⟩ :=
    aux_cor_as_resolvent_hcut_supply hd Jc Pc Xc W Cp D Sob Step Dbase Interp
  obtain ⟨deltaUnif, hdeltaUnif, hUnif⟩ :=
    aux_cor_as_resolvent_hunif_supply hd Jc Pc Xc W Cp D Sob Step Dbase Interp
  obtain ⟨deltaCore, hdeltaCore, hCore⟩ :=
    actual_padded_cube_core d hd Jc Pc Xc W Cp Sob Interp
  obtain ⟨deltaIdentity, hdeltaIdentity, hIdentity⟩ :=
    actual_boundary_identity_all_cubes d hd Jc Pc Xc W Cp Sob Interp
  obtain ⟨deltaDirichlet, _Cgeom, hdeltaDirichlet, _hCgeom, hDirichlet⟩ :=
    prop_as_dirichlet d hd Jc Pc Xc Sob W Cp D hES Step Dbase Interp
      (3 / 4) (by norm_num) (by norm_num)
  refine ⟨min 1 (min deltaResponses (min deltaLimit (min deltaCut (min deltaUnif
    (min deltaCore (min deltaIdentity deltaDirichlet)))))),
    lt_min one_pos (lt_min hdeltaResponses (lt_min hdeltaLimit (lt_min hdeltaCut
      (lt_min hdeltaUnif (lt_min hdeltaCore (lt_min hdeltaIdentity hdeltaDirichlet)))))), ?_⟩
  intro M hdelta H hIR I _ z r hr htriadic phi hphi h3r
  obtain ⟨hdeltaOne, hdeltaRest⟩ := le_min_iff.mp hdelta
  obtain ⟨hdeltaResponses', hdeltaRest⟩ := le_min_iff.mp hdeltaRest
  obtain ⟨hdeltaLimit', hdeltaRest⟩ := le_min_iff.mp hdeltaRest
  obtain ⟨hdeltaCut', hdeltaRest⟩ := le_min_iff.mp hdeltaRest
  obtain ⟨hdeltaUnif', hdeltaRest⟩ := le_min_iff.mp hdeltaRest
  obtain ⟨hdeltaCore', hdeltaRest⟩ := le_min_iff.mp hdeltaRest
  obtain ⟨hdeltaIdentity', hdeltaDirichlet'⟩ := le_min_iff.mp hdeltaRest
  obtain ⟨Rm, Sreg, _hRm, ⟨It⟩⟩ :=
    hResponses M M.shellPrefix.delta_pos hdeltaResponses'
  have HCUT := hCut M Rm Sreg It H hIR hdeltaCut'
  have HUNIF := hUnif M Rm Sreg It H hIR hdeltaUnif'
  have hPaddedTriadic : ∀ i, ∃ j : ℤ, 3 * r i = (3 : ℝ) ^ j := by
    intro i
    obtain ⟨j, hj⟩ := htriadic i
    refine ⟨j + 1, ?_⟩
    rw [hj, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    ring
  have hGex := fun i : I => hLimit M Rm Sreg It H hIR
    (le_min hdeltaOne hdeltaLimit') HCUT HUNIF (z i) (3 * r i) (h3r i)
    (hPaddedTriadic i) (aux_mfd_prop_as_forms_poincare hd (z i) (3 * r i) (h3r i))
  choose G hGmeas hGae _hGrepresented _hGjoint using hGex
  obtain ⟨_RL, _hRL, hBridge, L, hLmeas, _hLEq, _hLmeasure, hLnonneg, _hTail, hLconv⟩ :=
    hDirichlet M Rm Sreg It H hIR (le_min hdeltaOne hdeltaDirichlet')
      I z r hr htriadic phi hphi
  have hCoreAll := ae_all_iff.mpr fun i : I =>
    hCore M Rm Sreg It H hIR hdeltaCore' (z i) (r i) (hr i) id
  have hIdentityAll := ae_all_iff.mpr fun i : I =>
    hIdentity M Rm Sreg It H hIR hdeltaIdentity' (z i) (r i) (hr i) id
  refine ⟨G, L, hGmeas, hLmeas, ?_⟩
  filter_upwards [ae_all_iff.mpr hGae, hCoreAll, hIdentityAll,
    hBridge, hLnonneg, hLconv] with om hGom hCoreOm hIdentityOm hBridgeOm hNonneg hConv
  intro i
  obtain ⟨hStrong, _hLower, _hRecovery, ⟨K, hK, hCoer, _hDomain⟩,
    ⟨E, hE, hRegular, hLocal⟩, _hUniqueEnergy⟩ := hGom i
  have hNorm := actual_inverse_norm_of_strong hd Sob Interp (z i) (3 * r i) (h3r i)
    M H om (G i om) hStrong K hK hCoer
  have hcore := hCoreOm i (G i om) hNorm E hE
  obtain ⟨Gamma⟩ := (EM (z i) (3 * r i) (h3r i) E).exists_energyMeasure hRegular hLocal
  have hScalar : Tendsto (fun n => sInf (continuousBoundaryEnergies (z i) (r i) (hr i)
      (cutoffPositiveCoefficient M H om n (z i) (hr i)) (phi i))) atTop (𝓝 (L i om)) :=
    (hConv i).congr (fun n => hBridgeOm i n)
  exact ⟨hNorm, fun _ hNorm' => tendsto_nhds_unique hNorm' hNorm,
    E, Gamma, hE, hcore, hRegular, hLocal, hNonneg i, hScalar,
    hIdentityOm i (G i om) hNorm E Gamma hE hcore (phi i) (hphi i) (L i om) hScalar⟩

/-- S14 for the actual model, with its characterized infrared field supplied
inside the proof. There is one event for the entire countable family, and the
operator limit, smooth scalar limit, form, padded-cube core and energy measure
are all conclusions on that event. -/
theorem boundary_response_identity
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
      ∃ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_hIR : InfraredCharacterization M H),
      ∀ (I : Type) [Countable I]
        (z : I → SpatialCoordinates d) (r : I → ℝ) (hr : ∀ i, 0 < r i)
        (_htriadic : ∀ i, ∃ j : ℤ, r i = (3 : ℝ) ^ j)
        (phi : I → SpatialCoordinates d → ℝ) (_hphi : ∀ i, ContDiff ℝ ∞ (phi i)),
      let h3r : ∀ i, 0 < 3 * r i := fun i => mul_pos zero_lt_three (hr i)
      ∃ (G : (i : I) → BilateralField d →
          DomainL2 (centeredCube (z i) (3 * r i) (h3r i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (3 * r i) (h3r i)))
        (L : I → BilateralField d → ℝ),
        (∀ i, Measurable (G i)) ∧ (∀ i, Measurable (L i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ i,
          Tendsto (fun n => volumeResponseOperator
            (killedResponseSpace (aux_mfd_prop_as_forms_poincare hd (z i) (3 * r i) (h3r i)))
            (cutoffPositiveCoefficient M H om n (z i) (h3r i))) atTop (𝓝 (G i om)) ∧
          (∀ G' : DomainL2 (centeredCube (z i) (3 * r i) (h3r i)) →L[ℝ]
              DomainL2 (centeredCube (z i) (3 * r i) (h3r i)),
            Tendsto (fun n => volumeResponseOperator
              (killedResponseSpace (aux_mfd_prop_as_forms_poincare hd (z i) (3 * r i) (h3r i)))
              (cutoffPositiveCoefficient M H om n (z i) (h3r i))) atTop (𝓝 G') →
            G' = G i om) ∧
          ∃ (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict
              (centeredCube (z i) (3 * r i) (h3r i) : Set (SpatialCoordinates d))))
            (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm),
            (∀ v, E.energy v = limitFormEnergy (G i om) v) ∧
            (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
              (centeredCube (z i) (3 * r i) (h3r i) : Set (SpatialCoordinates d)) C) ∧
            _root_.SubdiffusiveProcess.DirichletForm.IsRegular E.toClosedForm ∧
            _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal E.toClosedForm ∧
            0 ≤ L i om ∧
            Tendsto (fun n => sInf (continuousBoundaryEnergies (z i) (r i) (hr i)
              (cutoffPositiveCoefficient M H om n (z i) (hr i)) (phi i)))
              atTop (𝓝 (L i om)) ∧
            L i om = sInf (aux_thm_prop_boundary_energy_set
              (centeredCube (z i) (3 * r i) (h3r i)) E.toClosedForm Gamma
              (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) (phi i)) := by
  obtain ⟨delta0, hdelta0, hmain⟩ := boundary_response_identity_of_infrared d hd
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hdelta
  obtain ⟨H, hIR⟩ := SubdiffusiveProcess.exists_infraredCharacterization hd M
  exact ⟨H, hIR, hmain M hdelta H hIR⟩

end SubdiffusiveProcess.AuditExports
