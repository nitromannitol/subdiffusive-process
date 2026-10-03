module

public import SubdiffusiveProcess.Paper.goodext_source_cell
public import SubdiffusiveProcess.Paper.goodext_common_response
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- One source representative retains the normalized local Holder estimates on
every good cell, together with the trace-response and crude bounds. This stronger
consumer preserves the estimates needed for finite harmonic-energy costs. -/
theorem goodext_source_cells_holder
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
    ∃ Cbound eps0 lam0 delta0 : ℝ,
      1 ≤ Cbound ∧ 0 < eps0 ∧ 0 < lam0 ∧ 0 < delta0 ∧
      ∀ (cbuf k0 : ℕ)
        (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Rm : Paper.in_responses d M)
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
        (gH : ℕ) (hgH : ∀ b, gH ≤ k b)
        (phi : Fin 2 → ℕ → ℕ) (hphi : ∀ a, StrictMono (phi a))
        (hIRConv : ∀ᵐ omega ∂P, ∀ (a : Fin 2) (b : Cells),
          Tendsto (fun n => H (env a n omega) (z b)) atTop (𝓝 (H (field omega) (z b))))
        (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        (hEta : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (hepsSmall : eps ≤ eps0)
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
        (eRef : Fin 2 → ℕ → ℝ)
        (heRef_pos : ∀ (a : Fin 2) (j : ℕ), 0 < eRef a j)
        (heRef_lim : ∀ (a : Fin 2) (j : ℕ),
          let kappa : ℕ → ℝ := fun J =>
            Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
          Tendsto (fun n : ℕ => kappa (phi a n - j) / kappa (phi a n)) atTop
            (𝓝 (eRef a j)))
        (ZL DL : Fin 2 → Cells → ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
        (loL hiL : Fin 2 → Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
        (AEL : Fin 2 → Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (errL ratL : Fin 2 → Cells → Unit → BilateralField d → ℝ)
        (hmeas : ∀ (a : Fin 2) (b : Cells),
          (∀ U D code, Measurable (ZL a b U D code) ∧ Measurable (DL a b U D code)) ∧
          (∀ U, Measurable (loL a b U) ∧ Measurable (hiL a b U) ∧
            ∀ i j, Measurable (fun omega => AEL a b U omega i j)) ∧
          Measurable (errL a b ()) ∧ Measurable (ratL a b ()))
        (harr : ∀ (a : Fin 2) (b : Cells), aux_affine_source_cells_env_cellArrays I M H s sigma gH cbuf Z Draw (phi a)
          (k b) (z b) (ZL a b) (DL a b) (loL a b) (hiL a b) (AEL a b) (errL a b) (ratL a b))
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
        (Form : Fin 2 → Ω → DirichletForm.ClosedForm
          (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
        (hE : ∀ (a : Fin 2) omega u,
          (Form a omega).energy u = limitFormEnergy (G a omega) u)
        (Gamma : ∀ (a : Fin 2) omega,
          DirichletForm.EnergyMeasure (Form a omega))
        (hGammaRecovery : ∀ a : Fin 2, ∀ᵐ omega ∂P,
          ∀ f : DomainL2 (centeredCube Qcentre Qside hQside),
          ∀ test : SpatialCoordinates d → ℝ,
            Continuous test → HasCompactSupport test →
            Tendsto (fun n =>
              let coeff := Lane4.cutoffPositiveCoefficient M H
                (env a n omega) (phi a n) Qcentre hQside
              let un := responseSolution S coeff
                ((sobolevVolumeLoad f).comp S.space.subtypeL)
              ∫ x in (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
                test x * coeff.val x *
                  ∑ i : Fin d, ((sobolevGradient un.val i) x) ^ 2)
              atTop (𝓝 (∫ x, test x ∂((Gamma a omega).measure (G a omega f))))),
      let Q := centeredCube Qcentre Qside hQside
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
            sInf response ≤ K * r' ^ ((d : ℝ) - 2 + 2 * alpha - etaGrid)) := by
  obtain ⟨Cbound, eps0, lam0, delta0, hC, he0, hl0, hd0, hApply⟩ :=
    goodext_source_cell d hd I _X _Sob _Step Pin _MeyersMorrey D Cp alpha beta s sigma cell epshom
      halpha hbeta hbetaLtAlpha hs hsSmall hsigma_eq hsigma hcell hepshom etaGrid hetaGrid
      H1 hH1 moment hmoment
  refine ⟨Cbound, eps0, lam0, delta0, hC, he0, hl0, hd0, ?_⟩
  intro cbuf k0 M Rm Sreg It H hMH Ω _ P _ field hfield_meas hfield_law env henv_meas
    henv_law hEnvConv Cells _ first k z gH hgH phi hphi hIRConv eta hEta F Praw Rraw Draw Z rawGood
    eps heps hepsSmall hPrimitive lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet
    hcdetSmall hlamSmall hdisorder eRef heRef_pos heRef_lim ZL DL loL hiL AEL errL ratL hmeas harr
    Qcentre Qside hQside RootIndex _ _ root0 zCat rCat hrCat SCat DCat _ fCat TCat _ thetaCat
    thetaH1Cat usrc srcRep ucell Cext etaCat t orders hetaCatGrid Index _ resp respLim constants
    Gcat coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid _ origin gridRoot gridKey hRootCatalogue
    hRepEstimates hRootsQ S hS GN hGN G hGE Form hE Gamma hGammaRecovery
  have hLocal := fun b : Cells => hApply cbuf k0 M Rm Sreg It H hMH Ω P field hfield_meas hfield_law
    env henv_meas henv_law hEnvConv (k b) (z b) gH (hgH b) phi hphi
    (hIRConv.mono fun omega h a => h a b) eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder eRef heRef_pos
    heRef_lim (fun a => ZL a b) (fun a => DL a b) (fun a => loL a b) (fun a => hiL a b)
    (fun a => AEL a b) (fun a => errL a b) (fun a => ratL a b) (fun a => hmeas a b) (fun a => harr a b)
    Qcentre Qside hQside RootIndex root0 zCat rCat hrCat SCat DCat fCat TCat thetaCat thetaH1Cat
    usrc srcRep ucell Cext etaCat t orders hetaCatGrid Index resp respLim constants Gcat
    coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hRootCatalogue
    hRepEstimates (hRootsQ b) S hS GN hGN G hGE Form hE Gamma hGammaRecovery
  have hAll := ae_all_iff.mpr hLocal
  filter_upwards [hAll] with omega hloc
  intro f hf fL2 hfr
  obtain ⟨U, hUc, hUr, hUb, hUh, _hFirst, hCrude⟩ := hloc first f hf fL2 hfr
  refine ⟨U, hUc, hUr, hUb, hUh, ?_, hCrude⟩
  intro b hgood zP idx
  dsimp only
  intro hz hpad hparent
  obtain ⟨V, hVc, hVr, _hVb, _hVh, hCell, _hVCrude⟩ := hloc b f hf fL2 hfr
  obtain ⟨cq, hcq, hnorm, hnonempty, hglb, hbound⟩ := hCell hgood zP idx hz hpad hparent
  have hq : Metric.ball (z b) ((3 : ℝ) ^ (-(k b : ℤ)) / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) :=
    (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by
        have hr := zpow_pos (by norm_num : (0 : ℝ) < 3) (-(k b : ℤ))
        linarith :
        (3 : ℝ) ^ (-(k b : ℤ)) / 2 ≤ 3 * (3 : ℝ) ^ (-(k b : ℤ)) / 2))).trans (hpad.trans hparent)
  have heq := goodext_common_response d (centeredCube Qcentre Qside hQside) (Form 1 omega)
    (Gamma 1 omega) (G 0 omega fL2) V U hVc hUc hVr hUr _ hq
  change ((Gamma 1 omega).continuousTraceValues _ _ V).Nonempty at hnonempty
  change IsGLB ((Gamma 1 omega).continuousTraceValues _ _ V)
    (sInf ((Gamma 1 omega).continuousTraceValues _ _ V)) at hglb
  change sInf ((Gamma 1 omega).continuousTraceValues _ _ V) ≤ _ at hbound
  rw [heq] at hnonempty hglb hbound
  have hEq : EqOn V U (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) :=
    eqOn_closure_of_ae_eq_restrict (centeredCube Qcentre Qside hQside).isOpen hVc hUc (hVr.symm.trans hUr)
  have hPull : EqOn
      (fun x => V (z b + ((3 : ℝ) ^ (-(k b : ℤ))) • x) - cq)
      (fun x => U (z b + ((3 : ℝ) ^ (-(k b : ℤ))) • x) - cq)
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
    intro x hx
    apply congrArg (fun v : ℝ => v - cq)
    apply hEq
    apply closure_mono hq
    have hr : 0 < (3 : ℝ) ^ (-(k b : ℤ)) := zpow_pos (by norm_num) _
    rw [closure_ball (z b) (half_pos hr).ne']
    have hx' : ‖x‖ ≤ 1 / 2 := by
      change dist x (0 : SpatialCoordinates d) ≤ 1 / 2 at hx
      simpa only [dist_zero_right] using hx
    change dist (z b + ((3 : ℝ) ^ (-(k b : ℤ))) • x) (z b) ≤ _
    rw [dist_eq_norm, show z b + ((3 : ℝ) ^ (-(k b : ℤ))) • x - z b =
        ((3 : ℝ) ^ (-(k b : ℤ))) • x by abel,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    linarith only [mul_le_mul_of_nonneg_left hx' hr.le]
  have hNormEq := cAlphaNorm_congr (alpha := alpha) hPull
  refine ⟨cq, (isHolderOn_congr hPull).mp hcq, ?_, hnonempty, hglb, hbound⟩
  exact hNormEq ▸ hnorm

end Paper
