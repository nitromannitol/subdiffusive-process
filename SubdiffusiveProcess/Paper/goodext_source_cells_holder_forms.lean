module

public import SubdiffusiveProcess.Paper.goodext_source_cells_holder_counted
public import SubdiffusiveProcess.Paper.conv_represented_limit_forms
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

/-- Actual represented bounds construct regular limit forms and energy measures
for both candidates. Their same extracted arrays supply extension estimates and
bad-chain counts. No form, energy-recovery or local-extension supplier is assumed. -/
theorem goodext_source_cells_holder_forms
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (D : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (Dbase : _root_.SubdiffusiveProcess.Paper.sum_errors_baseline_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp)
    (alpha beta s sigma cell epshom : ℝ)
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hbetaLtAlpha : beta < alpha)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ))
    (hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (hepshom : 0 < epshom)
    (etaGrid : ℝ) (hetaGrid : 0 < etaGrid)
    (H1 : ℕ) (hH1 : 0 < H1)
    (moment : ℝ) (hmoment : 1 ≤ moment)
    (theta bstar : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) (hbstar : 0 < bstar)
    :
    ∃ Cbound eps0 lam0 : ℝ,
      1 ≤ Cbound ∧ 0 < eps0 ∧ 0 < lam0 ∧
      ∀ (cbuf k0 gH : ℕ) (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1), eps ≤ eps0 →
      ∀ (hk0 : 1 ≤ k0)
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (hcdet : 0 < cdet) (hcdetSmall : cdet ≤ Cbound⁻¹)
        (hlamSmall : lambdaDet ≤ lam0),
      ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M) (hRm : Rm.C ≤ Cresp)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hMH : InfraredCharacterization M H)
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d)
        (hfield_meas : Measurable field)
        (hfield_law : Measure.map field P = (chaosSampleLaw M).toMeasure)
        (env : Fin 2 → ℕ → Ω → BilateralField d)
        (henv_meas : ∀ (a : Fin 2) (n : ℕ), Measurable (env a n))
        (henv_law : ∀ (a : Fin 2) (n : ℕ),
          Measure.map (env a n) P = (chaosSampleLaw M).toMeasure)
        (hEnvConv : ∀ᵐ omega ∂P, ∀ a : Fin 2,
          Tendsto (fun n => env a n omega) atTop (𝓝 (field omega)))
        (Cells : Type) [Countable Cells] (first : Cells)
        (k : Cells → ℕ) (z : Cells → SpatialCoordinates d)
        (hgH : ∀ b, gH ≤ k b)
        (phi : Fin 2 → ℕ → ℕ) (hphi : ∀ a, StrictMono (phi a))
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (hEta : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (hPrimitive : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega)))
        (hdisorder : M.delta ≤ delta0)
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (RootIndex : Type) [Countable RootIndex] [DecidableEq RootIndex]
        (root0 : RootIndex)
        (zCat : RootIndex → SpatialCoordinates d) (rCat : RootIndex → ℝ)
        (hrCat : ∀ j, 0 < rCat j)
        (SCat : ∀ j, ResponseSpace (centeredCube (zCat j) (rCat j) (hrCat j)))
        (DCat : ∀ j, Submodule ℚ (DomainL2 (centeredCube (zCat j) (rCat j) (hrCat j))))
        [hDCat : ∀ j, Countable (DCat j)]
        (fCat : ∀ j, (DCat j) → SpatialCoordinates d → ℝ)
        (TCat : RootIndex → Type) [hTCat : ∀ j, Countable (TCat j)]
        (thetaCat : ∀ j, TCat j → SpatialCoordinates d → ℝ)
        (thetaH1Cat : ∀ j, TCat j →
          Homogenization.H1Function
            (centeredCube (zCat j) (rCat j) (hrCat j) : Set (SpatialCoordinates d)))
        (usrc : Fin 2 → ∀ j, (DCat j) → ℕ → Ω → (SCat j).space)
        (srcRep : Fin 2 → ∀ j, (DCat j) → ℕ → Ω → SpatialCoordinates d → ℝ)
        (ucell : Fin 2 → ∀ j, TCat j → ℕ → Ω →
          Homogenization.H1Function
            (centeredCube (zCat j) (rCat j) (hrCat j) : Set (SpatialCoordinates d)))
        (Cext : ℝ) (etaCat : ℝ) (t : ℝ) (orders : Finset ℝ)
        (hetaCatGrid : etaCat ≤ etaGrid)
        (Index : Type) [Countable Index]
        (resp : Fin 2 → Index → ℕ → Ω → ℝ) (respLim : Fin 2 → Index → Ω → ℝ)
        (constants : Fin 2 → Index → ℕ → Ω → ℝ) (Gcat : Set Ω)
        (coercivityKey extensionKey lambdaKey : RootIndex → Index)
        (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (DCat j) → Index)
        (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, TCat j → Index)
        (Grid : Type) [Countable Grid]
        (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → RootIndex)
        (gridKey : Grid → Index)
        (hRootCatalogue : zCat root0 = Qcentre ∧ rCat root0 = Qside)
        (hRepEstimates : ∀ a : Fin 2,
          conv_represented_estimates d hd M H Ω P (phi a) (env a) RootIndex root0
            zCat rCat hrCat SCat DCat fCat TCat thetaCat thetaH1Cat
            (usrc a) (srcRep a) (ucell a) Cext beta alpha etaCat t orders I
            Index (resp a) (respLim a) (constants a) Gcat
            coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey
            sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey
            Grid origin gridRoot gridKey)
        (hRootsQ : ∀ (b : Cells) (U : Fin 3 × (Fin d → Fin 3)),
          closure (centeredCube (gcat_rootCentre gH (k b) (z b) U) (gcat_rootSide gH (k b) U)
            (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
        (S : ResponseSpace (centeredCube Qcentre Qside hQside))
        (hS : S.space = killedSobolevGraph (centeredCube Qcentre Qside hQside))
        (GN : ℕ → BilateralField d →
          DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
            DomainL2 (centeredCube Qcentre Qside hQside))
        (hGN : ∀ N omega f, GN N omega f =
          (responseSolution S
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
            ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
        (G : Fin 2 → Ω →
          DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
            DomainL2 (centeredCube Qcentre Qside hQside))
        (hGE : ∀ (a : Fin 2),
          ∀ᵐ omega ∂P,
            Tendsto (fun n => GN (phi a n) (env a n omega)) atTop (𝓝 (G a omega)))
        (hBounds : ∀ a : Fin 2, ∀ᵐ omega ∂P,
          in_represented_bounds_seq d hd Qcentre Qside hQside S
            (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env a n omega)
              (phi a n) Qcentre hQside) (G a omega)),
      ∃ (Form : Fin 2 → Ω → _root_.SubdiffusiveProcess.DirichletForm
          (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
        (Gamma : ∀ (a : Fin 2) omega, _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (Form a omega).toClosedForm),
      (∀ a omega, ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (Form a omega).toClosedForm
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) C) ∧
      (∀ᵐ omega ∂P, ∀ a u, (Form a omega).energy u = limitFormEnergy (G a omega) u) ∧
      ∃ psi : ℕ → ℕ, StrictMono psi ∧
        ∃ eRef : Fin 2 → ℕ → ℝ,
      (∀ (a : Fin 2) (j : ℕ), 0 < eRef a j) ∧
      ( ∀ (a : Fin 2) (j : ℕ),
          let kappa : ℕ → ℝ := fun J =>
            Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
          Tendsto (fun n : ℕ => kappa (phi a (psi n) - j) / kappa (phi a (psi n))) atTop
            (𝓝 (eRef a j))) ∧
      ∃ (ZL DL : Fin 2 → Cells → ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
        (loL hiL : Fin 2 → Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
        (AEL : Fin 2 → Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (errL ratL : Fin 2 → Cells → Unit → BilateralField d → ℝ),
      ( ∀ (a : Fin 2) (b : Cells),
          (∀ U D code, Measurable (ZL a b U D code) ∧ Measurable (DL a b U D code)) ∧
          (∀ U, Measurable (loL a b U) ∧ Measurable (hiL a b U) ∧
            ∀ i j, Measurable (fun omega => AEL a b U omega i j)) ∧
          Measurable (errL a b ()) ∧ Measurable (ratL a b ())) ∧
      ( ∀ (a : Fin 2) (b : Cells), aux_affine_source_cells_env_cellArrays I M H s sigma gH cbuf Z Draw (fun n => phi a (psi n))
          (k b) (z b) (ZL a b) (DL a b) (loL a b) (hiL a b) (AEL a b) (errL a b) (ratL a b)) ∧
      (∀ (active : List (Fin d → Fin (3 ^ H1)) → Prop)
        (index : List (Fin d → Fin (3 ^ H1)) → Cells),
        (∀ w, active w → k (index w) = H1 * w.length) →
        let Good := fun w => {omega | active w → ∀ a : Fin 2, omega ∈
          gcat_good k0 lambdaLim cell epshom cdet (ZL a (index w)) (DL a (index w))
            (loL a (index w)) (hiL a (index w)) (errL a (index w)) (ratL a (index w))}
        ∃ B : BilateralField d → ℝ, Measurable B ∧ (∀ omega, 0 ≤ B omega) ∧
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            ∀ (J : ℕ) (pi : Fin J → (Fin d → Fin (3 ^ H1))), 1 ≤ J →
              (Set.ncard {i : Fin J | omega ∉ Good ((List.ofFn pi).take (i.val + 1))} : ℝ) ≤
                theta * (J : ℝ) + B omega) ∧
      (let Q := centeredCube Qcentre Qside hQside
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let Good : Cells → Fin 2 → Set Ω := fun b a => field ⁻¹' gcat_good k0 lambdaLim cell epshom cdet
        (ZL a b) (DL a b) (loL a b) (hiL a b) (errL a b) (ratL a b)
      let sRef : Cells → Fin 2 → Ω → ℝ := fun b a omega => eRef a (k b) *
        Real.exp (H (field omega) (z b) + ∑ j ∈ Finset.range (k b), (field omega) (-(j : ℤ)) (z b))
      let L : ℝ := (3 : ℝ) ^ H1
      ∀ᵐ omega ∂P, ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
        ∀ (fL2 : DomainL2 Q), ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (Q : Set (SpatialCoordinates d))] f) →
        let u := G 0 omega fL2
        let fsup := sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|}
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
          ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
          (∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), U x = 0) ∧
          _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (Q : Set (SpatialCoordinates d))) U ∧
          (∀ b : Cells, omega ∈ Good b 0 ∧ omega ∈ Good b 1 →
            ∀ (zP : SpatialCoordinates d) (idx : OddGridIndex d (subdivisionHalfWidth H1)),
            let r : ℝ := (3 : ℝ) ^ (-(k b : ℤ))
            z b = oddGridCenter zP (L * r) (subdivisionHalfWidth H1) idx →
            Metric.closedBall (z b) (3 * r / 2) ⊆ Metric.ball zP (L * r / 2) →
            Metric.ball zP (L * r / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
            let response := (Gamma 1 omega).continuousTraceValues
              (closure (Q : Set (SpatialCoordinates d))) (Metric.ball (z b) (r / 2)) U
            ∃ cq : ℝ,
              _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
                (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
                (fun x => U (z b + r • x) - cq) ∧
              _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
                (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
                (fun x => U (z b + r • x) - cq) ≤
                  Ctotal * r ^ ((2 - (d : ℝ)) / 2) * (sRef b 0 omega) ^ (-(1 : ℝ) / 2) *
                    Real.sqrt (((Gamma 0 omega).measure u) (Metric.ball zP (L * r / 2))).toReal +
                  Ctotal * r ^ (2 : ℝ) * (sRef b 0 omega)⁻¹ * fsup ∧
            response.Nonempty ∧ IsGLB response (sInf response) ∧
            sInf response ≤ Ctotal * (eRef 1 (k b) / eRef 0 (k b)) *
              ((((Gamma 0 omega).measure u) (Metric.ball zP (L * r / 2))).toReal +
                (sRef b 0 omega)⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2)) ∧
          (∃ K : ℝ, 0 ≤ K ∧ ∀ (z' : SpatialCoordinates d) (r' : ℝ), 0 < r' →
            Metric.ball z' (r' / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
            let response := (Gamma 1 omega).continuousTraceValues
              (closure (Q : Set (SpatialCoordinates d))) (Metric.ball z' (r' / 2)) U
            response.Nonempty ∧ IsGLB response (sInf response) ∧
            sInf response ≤ K * r' ^ ((d : ℝ) - 2 + 2 * alpha - etaGrid))) := by
  obtain ⟨Cbound, eps0, lam0, hC, he0, hl0, hCounted⟩ :=
    goodext_source_cells_holder_counted d hd I _X _Sob _Step Pin _MeyersMorrey D Cp Dbase Cresp hCresp
      alpha beta s sigma cell epshom halpha hbeta hbetaLtAlpha hs hsSmall hsigma_eq
      hsigma hcell hepshom etaGrid hetaGrid H1 hH1 moment hmoment theta bstar htheta0 htheta1 hbstar
  refine ⟨Cbound, eps0, lam0, hC, he0, hl0, ?_⟩
  intro cbuf k0 gH eps heps hepsSmall hk0 lambdaCut lambdaLim lambdaDet cdet
    hThresholds hcdet hcdetSmall hlamSmall
  obtain ⟨delta0, hd0, hApply⟩ := hCounted cbuf k0 gH eps heps hepsSmall hk0
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall
  refine ⟨delta0, hd0, ?_⟩
  intro M Rm hRm Sreg It H hMH Ω _ P _ field hfield_meas hfield_law env henv_meas
    henv_law hEnvConv Cells _ first k z hgH phi hphi eta hEta F Praw Rraw Draw Z rawGood
    hPrimitive hdisorder
    Qcentre Qside hQside RootIndex _ _ root0 zCat rCat hrCat SCat DCat _ fCat TCat _ thetaCat
    thetaH1Cat usrc srcRep ucell Cext etaCat t orders hetaCatGrid Index _ resp respLim constants
    Gcat coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid _ origin gridRoot gridKey hRootCatalogue
    hRepEstimates hRootsQ S hS GN hGN G hGE hBounds
  classical
  have hside : ∀ a : Fin 2, ∀ᵐ omega ∂P,
      aux_affine_source_cells_env_side (centeredCube Qcentre Qside hQside) (G a omega) := by
    intro a
    filter_upwards [hBounds a, hGE a] with omega hB hG
    obtain ⟨L, _hlocal⟩ := aux_conv_represented_limit_forms_side d hd
      Qcentre Qside hQside S hS _ (G a omega)
      (fun n => GN (phi a n) (env a n omega))
      (fun n f => hGN (phi a n) (env a n omega) f) hG hB
    exact ⟨L.form, L.gamma, L.energy_eq, L.core⟩
  choose Gsel hSel hSelEq using fun a => aux_affine_source_cells_env_select P
    (centeredCube Qcentre Qside hQside) (G a) (hside a)
  choose Form Gamma hEnergy hCore using hSel
  have hGEsel : ∀ a : Fin 2, ∀ᵐ omega ∂P,
      Tendsto (fun n => GN (phi a n) (env a n omega)) atTop (𝓝 (Gsel a omega)) := by
    intro a
    filter_upwards [hGE a, hSelEq a] with omega hg heq
    rw [heq]
    exact hg
  have hBsel : ∀ a : Fin 2, ∀ᵐ omega ∂P,
      in_represented_bounds_seq d hd Qcentre Qside hQside S
        (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env a n omega)
          (phi a n) Qcentre hQside) (Gsel a omega) := by
    intro a
    filter_upwards [hBounds a, hSelEq a] with omega hb heq
    rw [heq]
    exact hb
  have hSelAll := ae_all_iff.mpr hSelEq
  have hEnergyActual : ∀ᵐ omega ∂P, ∀ a u,
      (Form a omega).energy u = limitFormEnergy (G a omega) u := by
    filter_upwards [hSelAll] with omega heq a u
    exact (hEnergy a omega u).trans (congrArg (fun G => limitFormEnergy G u) (heq a))
  obtain ⟨psi, hpsi, eRef, heRef, heRefLim, ZL, DL, loL, hiL, AEL, errL, ratL,
    hMeas, hArr, hChain, hExt⟩ :=
    hApply M Rm hRm Sreg It H hMH Ω P field hfield_meas hfield_law env henv_meas
      henv_law hEnvConv Cells first k z hgH phi hphi eta hEta F Praw Rraw Draw Z rawGood
      hPrimitive hdisorder Qcentre Qside hQside RootIndex root0
      zCat rCat hrCat SCat DCat fCat TCat thetaCat thetaH1Cat usrc srcRep ucell Cext etaCat t
      orders hetaCatGrid Index resp respLim constants Gcat coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey
      Grid origin gridRoot gridKey hRootCatalogue hRepEstimates hRootsQ S hS GN hGN Gsel hGEsel
      Form hEnergy Gamma hBsel (fun a => Eventually.of_forall (hCore a))
  refine ⟨Form, Gamma, hCore, hEnergyActual, psi, hpsi, eRef, heRef, heRefLim,
    ZL, DL, loL, hiL, AEL, errL, ratL, hMeas, hArr, hChain, ?_⟩
  filter_upwards [hExt, hSelAll] with omega hext heq
  simpa only [heq 0] using hext

end SubdiffusiveProcess.Paper
