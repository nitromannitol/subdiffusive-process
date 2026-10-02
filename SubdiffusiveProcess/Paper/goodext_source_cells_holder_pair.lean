import SubdiffusiveProcess.Paper.goodext_source_cells_holder_represented
import SubdiffusiveProcess.Paper.gcat_prefix_reference_pair
import SubdiffusiveProcess.Paper.represented_bounds_subseq
open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- Both represented candidates use the same actual extraction of reference
coefficients and every measurable good-cell array. The extracted data are retained,
and one source representative satisfies all their good-extension estimates. -/
theorem goodext_source_cells_holder_pair
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : Lane4.SobolevFoundationalInput d hd)
    (_Step : Paper.cutoff_good_scale_input d)
    (Pin : Paper.in_poincare d hd I)
    (_MeyersMorrey : Lane4.SmallPerturbationInput d)
    (D : Paper.lane4_deterministic_good_scale_input d)
    (Cp : Lane4.CampanatoInput d)
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
    :
    ∃ Cbound eps0 lam0 : ℝ,
      1 ≤ Cbound ∧ 0 < eps0 ∧ 0 < lam0 ∧
      ∀ (cbuf k0 gH : ℕ) (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1), eps ≤ eps0 →
      ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Rm : Paper.in_responses d M) (hRm : Rm.C ≤ Cresp)
        (Sreg : Paper.in_6_16 d M) (It : Paper.in_iteration d M I Sreg)
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
        (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
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
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (hcdet : 0 < cdet) (hcdetSmall : cdet ≤ Cbound⁻¹)
        (hlamSmall : lambdaDet ≤ lam0)
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
            (Lane4.cutoffPositiveCoefficient M H omega N Qcentre hQside)
            ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
        (G : Fin 2 → Ω →
          DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
            DomainL2 (centeredCube Qcentre Qside hQside))
        (hGE : ∀ (a : Fin 2),
          ∀ᵐ omega ∂P,
            Tendsto (fun n => GN (phi a n) (env a n omega)) atTop (𝓝 (G a omega)))
        (Form : Fin 2 → Ω → _root_.DirichletForm
          (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
        (hE : ∀ (a : Fin 2) omega u,
          (Form a omega).energy u = limitFormEnergy (G a omega) u)
        (Gamma : ∀ (a : Fin 2) omega,
          DirichletForm.EnergyMeasure (Form a omega).toClosedForm)
        (hBounds : ∀ a : Fin 2, ∀ᵐ omega ∂P,
          in_represented_bounds_seq d hd Qcentre Qside hQside S
            (fun n => Lane4.cutoffPositiveCoefficient M H (env a n omega)
              (phi a n) Qcentre hQside) (G a omega))
        (hcore : ∀ a : Fin 2, ∀ᵐ omega ∂P,
          ∃ C, DirichletForm.IsCoreOn (Form a omega).toClosedForm
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) C),
      ∃ psi : ℕ → ℕ, StrictMono psi ∧
        ∃ eRef : Fin 2 → ℕ → ℝ,
      (∀ (a : Fin 2) (j : ℕ), 0 < eRef a j) ∧
      ( ∀ (a : Fin 2) (j : ℕ),
          let kappa : ℕ → ℝ := fun J =>
            Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
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
          Lane4.IsHolderOn alpha (closure (Q : Set (SpatialCoordinates d))) U ∧
          (∀ b : Cells, omega ∈ Good b 0 ∧ omega ∈ Good b 1 →
            ∀ (zP : SpatialCoordinates d) (idx : OddGridIndex d (subdivisionHalfWidth H1)),
            let r : ℝ := (3 : ℝ) ^ (-(k b : ℤ))
            z b = oddGridCenter zP (L * r) (subdivisionHalfWidth H1) idx →
            Metric.closedBall (z b) (3 * r / 2) ⊆ Metric.ball zP (L * r / 2) →
            Metric.ball zP (L * r / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
            let response := (Gamma 1 omega).continuousTraceValues
              (closure (Q : Set (SpatialCoordinates d))) (Metric.ball (z b) (r / 2)) U
            ∃ cq : ℝ,
              Lane4.IsHolderOn alpha
                (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
                (fun x => U (z b + r • x) - cq) ∧
              Lane4.cAlphaNorm alpha
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
  obtain ⟨Cbound, eps0, lam0, deltaExt, hC, he0, hl0, hdExt, hApply⟩ :=
    goodext_source_cells_holder_represented d hd I _X _Sob _Step Pin _MeyersMorrey D Cp
      alpha beta s sigma cell epshom halpha hbeta hbetaLtAlpha hs hsSmall hsigma_eq
      hsigma hcell hepshom etaGrid hetaGrid H1 hH1 moment hmoment
  refine ⟨Cbound, eps0, lam0, hC, he0, hl0, ?_⟩
  intro cbuf k0 gH eps heps hepsSmall
  obtain ⟨deltaPrefix, hdPrefix, hPrefix⟩ := gcat_prefix_reference_pair d hd I Pin _X
    _MeyersMorrey _Sob D Cresp hCresp s sigma eps hs hsigma heps gH cbuf
  refine ⟨min deltaExt deltaPrefix, lt_min hdExt hdPrefix, ?_⟩
  intro M Rm hRm Sreg It H hMH Ω _ P _ field hfield_meas hfield_law env henv_meas
    henv_law hEnvConv Cells _ first k z hgH phi hphi eta hEta F Praw Rraw Draw Z rawGood
    hPrimitive lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet
    hcdetSmall hlamSmall hdisorder
    Qcentre Qside hQside RootIndex _ _ root0 zCat rCat hrCat SCat DCat _ fCat TCat _ thetaCat
    thetaH1Cat usrc srcRep ucell Cext etaCat t orders hetaCatGrid Index _ resp respLim constants
    Gcat coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid _ origin gridRoot gridKey hRootCatalogue
    hRepEstimates hRootsQ S hS GN hGN G hGE Form hE Gamma hBounds hcore
  obtain ⟨psi, hpsi, eRef, heRef, heRefLim, ZL, DL, loL, hiL, AEL, errL, ratL, hArr⟩ :=
    hPrefix M (hdisorder.trans (min_le_right _ _)) Rm hRm Sreg It H hMH
      eta hEta F Praw Rraw Draw Z rawGood hPrimitive Cells k z phi hphi
  have hRef : ∀ (a : Fin 2) (j : ℕ),
      let kappa : ℕ → ℝ := fun J =>
        Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
      Tendsto (fun n => kappa (phi a (psi n) - j) / kappa (phi a (psi n))) atTop (𝓝 (eRef a j)) := by
    intro a j
    simpa only [Int.toNat_sub, Int.toNat_natCast] using heRefLim a j
  have hMeas : ∀ (a : Fin 2) (b : Cells),
      (∀ U D code, Measurable (ZL a b U D code) ∧ Measurable (DL a b U D code)) ∧
      (∀ U, Measurable (loL a b U) ∧ Measurable (hiL a b U) ∧
        ∀ i j, Measurable (fun omega => AEL a b U omega i j)) ∧
      Measurable (errL a b ()) ∧ Measurable (ratL a b ()) := fun a b =>
    ⟨(hArr a b).1, (hArr a b).2.1, (hArr a b).2.2.1, (hArr a b).2.2.2.1⟩
  refine ⟨psi, hpsi, eRef, heRef, hRef, ZL, DL, loL, hiL, AEL, errL, ratL,
    hMeas, (fun a b => (hArr a b).2.2.2.2), ?_⟩
  have hRepSub := fun a : Fin 2 => conv_represented_estimates_subseq d hd M H Ω P
    (phi a) (env a) RootIndex root0 zCat rCat hrCat SCat DCat fCat TCat thetaCat thetaH1Cat
    (usrc a) (srcRep a) (ucell a) Cext beta alpha etaCat t orders I Index
    (resp a) (respLim a) (constants a) Gcat coercivityKey extensionKey lambdaKey
    sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
    cellHolderKey Grid origin gridRoot gridKey (hRepEstimates a) psi hpsi
  exact hApply cbuf k0 M Rm Sreg It H hMH Ω P field hfield_meas hfield_law
    (fun a n => env a (psi n)) (fun a n => henv_meas a (psi n))
    (fun a n => henv_law a (psi n))
    (hEnvConv.mono fun omega h a => (h a).comp hpsi.tendsto_atTop)
    Cells first k z gH hgH (fun a n => phi a (psi n)) (fun a => (hphi a).comp hpsi)
    eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall
    (hdisorder.trans (min_le_left _ _)) eRef heRef hRef
    ZL DL loL hiL AEL errL ratL hMeas (fun a b => (hArr a b).2.2.2.2)
    Qcentre Qside hQside RootIndex root0 zCat rCat hrCat SCat DCat fCat TCat thetaCat thetaH1Cat
    (fun a j f n => usrc a j f (psi n)) (fun a j f n => srcRep a j f (psi n))
    (fun a j t n => ucell a j t (psi n)) Cext etaCat t orders hetaCatGrid Index
    (fun a i n => resp a i (psi n)) respLim (fun a i n => constants a i (psi n)) Gcat
    coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hRootCatalogue
    hRepSub hRootsQ S hS GN hGN G
    (fun a => (hGE a).mono fun omega h => h.comp hpsi.tendsto_atTop)
    Form hE Gamma
    (fun a => (hBounds a).mono fun omega h => represented_bounds_subseq d hd
      Qcentre Qside hQside S _ (G a omega) h psi hpsi.tendsto_atTop) hcore

end Paper
