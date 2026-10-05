module

public import SubdiffusiveProcess.Paper.affine_source_cells_root_represented
public import SubdiffusiveProcess.Paper.affine_source_cells_mass_represented
public import SubdiffusiveProcess.Paper.conv_represented_limit_forms
public import SubdiffusiveProcess.Paper.gcat_finite_scores

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Apply the represented affine theorem and convert its conclusion to mass cells.
The limiting side, rational grids, mass-cell coverage and plane-nullity are supplied internally.
The original-space array and reference limits remain the outputs of the common extraction. -/
theorem affine_source_cells_root_mass
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (D : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d) (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (beta : ℝ) (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1) :
    ∀ (alpha gamma zeta s sigma cell : ℝ)
    (_hba : beta < alpha) (_halpha : alpha < 1)
    (_hgamma : 0 < gamma) (_hgamma1 : gamma < 1) (_hzeta : 0 < zeta)
    (_hneg : affineExponent (d : ℝ) alpha beta gamma zeta < 0)
    (_hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (_hsSmall : s ≤ (1 / 32 : ℝ))
    (_hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (_hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (_hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (cbuf k0 : ℕ),
    ∃ H0 : ℕ, ∀ H1 : ℕ, H0 ≤ H1 →
      (0 < H1 ∧ (1 : ℝ) < (3 : ℝ) ^ H1 ∧ Nat.floor (gamma * (H1 : ℝ)) + 6 < H1) ∧
      ∃ epshom : ℝ, ∃ (_hepshom : 0 < epshom),
      ∃ Cbound eps0 lam0 delta0 : ℝ,
        (1 : ℝ) ≤ Cbound ∧ 0 < eps0 ∧ 0 < lam0 ∧ 0 < delta0 ∧
        ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ))
          (_hMH : InfraredCharacterization M H)
          (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
          (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M)
          (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg)
          (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (field : Ω → BilateralField d)
          (_hfieldMeas : Measurable field)
          (_hfieldLaw : Measure.map field P = (chaosSampleLaw M).toMeasure)
          (env : ℕ → Ω → BilateralField d) (_hEnvMeas : ∀ n, Measurable (env n))
          (_hEnvLaw : ∀ n, Measure.map (env n) P = (chaosSampleLaw M).toMeasure)
          (_hEnvConv : ∀ᵐ omega ∂P, Tendsto (fun n => env n omega) atTop (𝓝 (field omega))),
          M.delta ≤ delta0 →
          ∀ (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
            (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
            (NE psi phi : ℕ → ℕ) (_hpsi : StrictMono psi) (_hphi : phi = fun n => NE (psi n))
            (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
            (responseE : ℕ → Ω → ℝ) (eventE : Set Ω) (root : ℕ)
            (Dcat : ∀ i, Submodule ℚ (DomainL2 (centeredCube (z i) (r i) (hr i))))
            [_hDcat : ∀ i, Countable (Dcat i)]
            (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
            (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
            (traceH1 : ∀ i, ℕ → Homogenization.H1Function
              (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
            (usrcE : ∀ i, Dcat i → ℕ → Ω → (Sspace i).space)
            (srcRepE : ∀ i, Dcat i → ℕ → Ω → SpatialCoordinates d → ℝ)
            (ucellE : ∀ i, ℕ → ℕ → Ω → Homogenization.H1Function
              (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
            (Cext etaCat t : ℝ)
            (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
            (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
            (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
            (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ)
            (_hRepE : conv_represented_estimates d hd M H Ω P NE env
              ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
              usrcE srcRepE ucellE Cext beta alpha etaCat t {1} I
              ℕ (fun i n omega => catalogResponse i (NE n) (env n omega)) responseE
              (fun i n omega => catalogConstant i (NE n) (env n omega)) eventE
              coercivityKey extensionKey lambdaKey
              sourceResponseKey sourceGrowthKey sourceHolderKey
              cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey)
            (_hgrid : ∀ (j : ℕ) (o : SpatialCoordinates d), (∀ i : Fin d, ∃ q : ℚ, o i = (q : ℝ)) →
              ∃ g : ℕ, gridRoot g = j ∧ origin g = o)
            (jQ : ℕ)
            (GE : Ω → DomainL2 (centeredCube (z jQ) (r jQ) (hr jQ)) →L[ℝ]
              DomainL2 (centeredCube (z jQ) (r jQ) (hr jQ)))
            (_hGE : ∀ᵐ omega ∂P,
              Tendsto (fun n => volumeResponseOperator (Sspace jQ)
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (NE n) (z jQ) (hr jQ)))
                atTop (𝓝 (GE omega)))
            (_hBounds : ∀ᵐ omega ∂P, in_represented_bounds_seq d hd
              (z jQ) (r jQ) (hr jQ) (Sspace jQ)
              (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (NE n) (z jQ) (hr jQ))
              (GE omega))
            (g : aux_thm_prop_selection_geometry d)
            (_hgH1 : g.H1 = H1) (_hggamma : g.gamma = gamma) (_hgzeta : g.zeta = zeta)
            (_hwidth : 81 ≤ g.width)
            (eRef : ℕ → ℝ)
            (_heRefPos : ∀ k : ℕ, 0 < eRef k)
            (_heRefLim : ∀ k : ℕ,
              Tendsto (fun n : ℕ =>
                (let kappa : ℕ → ℝ := fun J =>
                   Real.exp (((J : ℝ) + 1) *
                     _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                     SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
                 kappa (((phi n : ℤ) - (k : ℤ)).toNat) / kappa (phi n)))
                atTop (𝓝 (eRef k)))
            (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
            (_hEta : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              ∀ (N i : ℕ) (y : Fin d → ℝ),
                eta N omega i y =
                  omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)))
            (F Praw Rraw Draw : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ENNReal)
            (Z : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ℝ)
            (rawGood : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → Prop)
            (eps : ℝ) (_heps : eps ∈ Set.Ioo (0 : ℝ) 1) (_hepsSmall : eps ≤ eps0)
            (_hPrimitive : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              ∀ N : ℕ,
                primitive_scores d M s eps (eta N omega)
                  (fun m y => F N m y omega)
                  (fun m y => Praw N m y omega)
                  (fun m y => Rraw N m y omega)
                  (fun m y => Draw N m y omega)
                  (fun m y => Z N m y omega)
                  (fun m y => rawGood N m y omega)))
            (lambdaCut lambdaLim lambdaDet cdet : ℝ)
            (_hThresholds :
              0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
              lambdaLim < lambdaDet ∧ lambdaDet < 1)
            (_hcdet : 0 < cdet) (_hcdetSmall : cdet ≤ Cbound⁻¹)
            (_hlamSmall : lambdaDet ≤ lam0)
            (ZLim DLim : (ℕ × ℕ) → ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
              ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
            (loLim hiLim : (ℕ × ℕ) → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
            (AELim : (ℕ × ℕ) → (Fin 3 × (Fin d → Fin 3)) → BilateralField d →
              Matrix (Fin d) (Fin d) ℝ)
            (errLim ratioLim : (ℕ × ℕ) → Unit → BilateralField d → ℝ)
            (_hArrMeas : ∀ c : (ℕ × ℕ),
              (∀ U D code, Measurable (ZLim c U D code) ∧ Measurable (DLim c U D code)) ∧
              (∀ U, Measurable (loLim c U) ∧ Measurable (hiLim c U) ∧
                ∀ i j, Measurable (fun omega => AELim c U omega i j)) ∧
              Measurable (errLim c ()) ∧ Measurable (ratioLim c ()))
            (_hArr : aux_affine_source_cells_env_arrays I M H s sigma
              (Nat.floor (gamma * (H1 : ℝ)) + 4) cbuf Z Draw phi (fun c : ℕ × ℕ => H1 * c.2) (fun c => z c.1)
              ZLim DLim loLim hiLim AELim errLim ratioLim)
            (Good : ℕ → SpatialCoordinates d → Set Ω)
    (_hGood : ∀ n zc, aux_thm_prop_cell_available z r zc (aux_thm_prop_mass_side g.H1 n) →
      ∀ om ∈ Good n zc, field om ∈ gcat_good k0 lambdaLim cell epshom cdet
        (ZLim ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (DLim ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (loLim ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (hiLim ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (errLim ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (ratioLim ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))),
    ∀ᵐ omega ∂P,
      ∀ (E' : _root_.SubdiffusiveProcess.DirichletForm
          (volume.restrict (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))))
        (Gam' : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E'.toClosedForm),
      (∀ u, E'.toClosedForm.energy u = limitFormEnergy (GE omega) u) →
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E'.toClosedForm
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) C) →
      ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z jQ) (r jQ) (hr jQ)),
      ∀ _hu : GE omega f ∈ E'.toClosedForm.domain, ∀ c : ℝ, 0 < c →
      ∃ baseMesh : ℝ, 0 < baseMesh ∧
        ∀ (n : ℕ), 1 ≤ n → aux_thm_prop_mass_side g.H1 n ≤ baseMesh →
        ∀ (sigma : Fin d → Fin g.Mm) (k : Fin d → ℤ),
        omega ∈ Good n (aux_thm_prop_mass_center g.H1 g.Mm sigma n k) →
        aux_thm_prop_mass_padded g.H1 g.Mm g.width g.gamma sigma n k →
        closure (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k) ⊆
          (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) →
        let mu := Gam'.measure (GE omega f) + ENNReal.ofReal c •
          volume.restrict (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))
        (mu (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k)).toReal ≤
          ((3 : ℝ) ^ g.H1) ^ ((d : ℝ) + g.zeta) *
            (mu (aux_thm_prop_mass_cell g.H1 g.Mm sigma n k)).toReal →
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))) ∧
          (⇑(GE omega f) =ᵐ[volume.restrict
            (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))] U) ∧
          aux_thm_prop_affine_error (centeredCube (z jQ) (r jQ) (hr jQ))
            E'.toClosedForm Gam' (GE omega f) U c
            (centeredCube (aux_thm_prop_mass_center g.H1 g.Mm sigma n k)
              (aux_thm_prop_mass_side g.H1 n) (aux_thm_prop_grid_side_pos g.H1 n) :
                Set (SpatialCoordinates d)) := by
  intro alpha gamma zeta s sigma cell hba halpha hgamma hgamma1 hzeta hneg hs hsSmall
    hsigma_eq hsigma hcell cbuf k0
  obtain ⟨H0, hH0⟩ := affine_source_cells_root_represented d hd I _X _Sob _Step _MeyersMorrey Pin D Cp
    beta hbeta hbeta1 alpha gamma zeta (3 / 2048) s sigma cell hba halpha hgamma hgamma1 hzeta (by norm_num) hneg hs
    hsSmall hsigma_eq hsigma hcell cbuf k0
  refine ⟨H0, fun H1 hH1 => ?_⟩
  obtain ⟨hfacts, epshom, hepshom, Cbound, eps0, lam0, delta0, hC, he0, hl0, hd0, hM⟩ := hH0 H1 hH1
  refine ⟨hfacts, epshom, hepshom, Cbound, eps0, lam0, delta0, hC, he0, hl0, hd0, ?_⟩
  intro M H hMH Rm Sreg _It Ω _ P _ field hfieldMeas hfieldLaw env hEnvMeas hEnvLaw hEnvConv hdelta z r hr Sspace NE psi phi hpsi hphi
    catalogResponse catalogConstant responseE eventE root Dcat _ fcat trace traceH1 usrcE srcRepE ucellE
    Cext etaCat t coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey origin gridRoot gridKey hRepE hgrid jQ GE hGE hBounds g hgH1 hggamma hgzeta hwidth
    eRef heRefPos heRefLim eta hEta F Praw Rraw Draw Z rawGood eps heps
    hepsSmall hPrimitive lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall
    ZLim DLim loLim hiLim AELim errLim ratioLim hArrMeas hArr Good hGood
  classical
  have hFiniteScoreGuard : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              ∀ (c : (ℕ × ℕ)) (N : ℕ) (U : Fin 3 × (Fin d → Fin 3)) (D : ℕ)
                (code : (Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))),
                gcat_rootLevel (Nat.floor (gamma * (H1 : ℝ)) + 4) (H1 * c.2) U + (D : ℤ) ≤ (N : ℤ) →
                ∀ j ∈ Finset.Icc (gcat_rootLevel (Nat.floor (gamma * (H1 : ℝ)) + 4) (H1 * c.2) U -
                    (cbuf : ℤ))
                  (gcat_rootLevel (Nat.floor (gamma * (H1 : ℝ)) + 4) (H1 * c.2) U + (D : ℤ)),
                  Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • gcat_obsCentre (Nat.floor (gamma * (H1 : ℝ)) + 4)
                      (H1 * c.2) (z c.1) U D code) omega ≠ ⊤) := by
    filter_upwards [gcat_finite_scores d M s eps hs.1 eta hEta F Praw Rraw Draw Z rawGood
      hPrimitive (ℕ × ℕ) (fun c => H1 * c.2) (fun c => z c.1)
      (Nat.floor (gamma * (H1 : ℝ)) + 4)] with omega h c N U D code _hdeep j _hj
    exact h c N U D code j
  have hS : (Sspace jQ).space = killedSobolevGraph (centeredCube (z jQ) (r jQ) (hr jQ)) := by
    have h := hRepE
    rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, _⟩
    exact hs jQ
  have hside : ∀ᵐ omega ∂P,
      ∃ (Ef : _root_.SubdiffusiveProcess.DirichletForm
          (volume.restrict (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))))
        (Gam : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Ef.toClosedForm),
        (∀ u, Ef.toClosedForm.energy u = limitFormEnergy (GE omega) u) ∧
        ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn Ef.toClosedForm
          (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) C := by
    filter_upwards [hBounds, hGE] with omega hB hG
    obtain ⟨L, _hlocal⟩ := aux_conv_represented_limit_forms_side d hd
      (z jQ) (r jQ) (hr jQ) (Sspace jQ) hS _ (GE omega)
      (fun n => volumeResponseOperator (Sspace jQ)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (NE n) (z jQ) (hr jQ)))
      (fun n f => volumeResponseOperator_apply _ _ _) hG hB
    exact ⟨L.form, L.gamma, L.energy_eq, L.core⟩
  have hGEsub : ∀ᵐ omega ∂P,
      Tendsto (fun n => volumeResponseOperator (Sspace jQ)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env (psi n) omega) (phi n) (z jQ) (hr jQ)))
        atTop (𝓝 (GE omega)) := by
    subst phi
    exact hGE.mono fun omega h => h.comp hpsi.tendsto_atTop
  obtain ⟨Grid, origin', gridChoice, hgc, hConcl⟩ :=
    hM M H hMH Rm Sreg _It Ω P field hfieldMeas hfieldLaw env hEnvMeas hEnvLaw hEnvConv
      hdelta z r hr Sspace NE psi phi hpsi hphi catalogResponse catalogConstant responseE
      eventE root Dcat fcat trace traceH1 usrcE srcRepE ucellE Cext etaCat t
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey origin gridRoot gridKey hRepE hgrid jQ GE
      hGEsub hside eRef heRefPos heRefLim g.Mm (ℕ × ℕ) (fun c => H1 * c.2) (fun c => z c.1)
      eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
      lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hFiniteScoreGuard
      ZLim DLim loLim hiLim AELim errLim ratioLim hArrMeas hArr
  have hConcl' : aux_affine_source_cells_env_Concl (z jQ) (r jQ) (hr jQ) P field GE g.gamma
      g.zeta (3 / 2048) g.H1 k0 lambdaLim cell epshom cdet Grid origin'
      (Fintype.card (Fin d → Fin g.Mm)) gridChoice
      (fun c : ℕ × ℕ => g.H1 * c.2) (fun c => z c.1) ZLim DLim loLim hiLim errLim ratioLim := by
    simpa only [hgH1, hggamma, hgzeta] using hConcl
  exact affine_source_cells_mass_represented d hd M H Ω P NE env root z r hr Sspace Dcat
    fcat (fun _ => ℕ) trace traceH1 usrcE srcRepE ucellE Cext beta alpha etaCat t {1} I ℕ
    (fun i n omega => catalogResponse i (NE n) (env n omega)) responseE
    (fun i n omega => catalogConstant i (NE n) (env n omega)) eventE
    coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey hRepE field jQ
    (fun n omega => volumeResponseOperator (Sspace jQ)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (NE n) (z jQ) (hr jQ)))
    GE (Eventually.of_forall fun omega n f => volumeResponseOperator_apply _ _ _)
    hGE hBounds g Good k0 lambdaLim cell epshom cdet hwidth Grid origin' gridChoice hgc
    ZLim DLim loLim hiLim errLim ratioLim hConcl' hGood

end SubdiffusiveProcess.Paper
