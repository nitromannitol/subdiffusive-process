module

public import SubdiffusiveProcess.Paper.lem_goodext
public import SubdiffusiveProcess.Paper.affine_source_cells_env
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

/-- Apply good extension to the concrete good-cell arrays of both represented
candidates. Finite-score guards, normalization limits and same-law transport
are supplied internally; the represented catalogue and recovery data are retained. -/
theorem goodext_source_cell
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
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
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
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
        (k : ℕ) (z : SpatialCoordinates d)
        (gH : ℕ) (hgH : gH ≤ k)
        (phi : Fin 2 → ℕ → ℕ) (hphi : ∀ a, StrictMono (phi a))
        (hIRConv : ∀ᵐ omega ∂P, ∀ a : Fin 2,
          Tendsto (fun n => H (env a n omega) z) atTop (𝓝 (H (field omega) z)))
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
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
            Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
          Tendsto (fun n : ℕ => kappa (phi a n - j) / kappa (phi a n)) atTop
            (𝓝 (eRef a j)))
        (ZL DL : Fin 2 → ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
        (loL hiL : Fin 2 → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
        (AEL : Fin 2 → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (errL ratL : Fin 2 → Unit → BilateralField d → ℝ)
        (hmeas : ∀ a : Fin 2,
          (∀ U D code, Measurable (ZL a U D code) ∧ Measurable (DL a U D code)) ∧
          (∀ U, Measurable (loL a U) ∧ Measurable (hiL a U) ∧
            ∀ i j, Measurable (fun omega => AEL a U omega i j)) ∧
          Measurable (errL a ()) ∧ Measurable (ratL a ()))
        (harr : ∀ a : Fin 2, aux_affine_source_cells_env_cellArrays I M H s sigma gH cbuf Z Draw (phi a)
          k z (ZL a) (DL a) (loL a) (hiL a) (AEL a) (errL a) (ratL a))
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
        (hRootsQ : ∀ U : Fin 3 × (Fin d → Fin 3),
          closure (centeredCube (gcat_rootCentre gH k z U) (gcat_rootSide gH k U)
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
        (Form : Fin 2 → Ω → _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
          (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
        (hE : ∀ (a : Fin 2) omega u,
          (Form a omega).energy u = limitFormEnergy (G a omega) u)
        (Gamma : ∀ (a : Fin 2) omega,
          _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (Form a omega))
        (hGammaRecovery : ∀ a : Fin 2, ∀ᵐ omega ∂P,
          ∀ f : DomainL2 (centeredCube Qcentre Qside hQside),
          ∀ test : SpatialCoordinates d → ℝ,
            Continuous test → HasCompactSupport test →
            Tendsto (fun n =>
              let coeff := _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H
                (env a n omega) (phi a n) Qcentre hQside
              let un := responseSolution S coeff
                ((sobolevVolumeLoad f).comp S.space.subtypeL)
              ∫ x in (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
                test x * coeff.val x *
                  ∑ i : Fin d, ((sobolevGradient un.val i) x) ^ 2)
              atTop (𝓝 (∫ x, test x ∂((Gamma a omega).measure (G a omega f))))),
      let Q := centeredCube Qcentre Qside hQside
      let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
      let _q : Set (SpatialCoordinates d) := Metric.ball z (r / 2)
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let Good : Fin 2 → Set Ω := fun a => field ⁻¹' gcat_good k0 lambdaLim cell epshom cdet
        (ZL a) (DL a) (loL a) (hiL a) (errL a) (ratL a)
      let sRef : Fin 2 → Ω → ℝ := fun a omega => eRef a k *
        Real.exp (H (field omega) z + ∑ j ∈ Finset.range k, (field omega) (-(j : ℤ)) z)
      let L : ℝ := (3 : ℝ) ^ H1
      let unitClosed : Set (SpatialCoordinates d) :=
        closedCube (0 : SpatialCoordinates d) 1 one_pos
      ∀ᵐ omega ∂P,
        let responseSet : ℝ → SpatialCoordinates d → (SpatialCoordinates d → ℝ) → Set ℝ :=
          fun r' z' b =>
            {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
              v ∈ (Form 1 omega).domain ∧
              ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
              ((v : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) ∧
              (∀ x ∈ frontier (Metric.ball z' (r' / 2)), V x = b x) ∧
              e = ((Gamma 1 omega).measure v
                (Metric.ball z' (r' / 2))).toReal}
        let responseF : ℝ → SpatialCoordinates d → (SpatialCoordinates d → ℝ) → ℝ :=
          fun r' z' b => sInf (responseSet r' z' b)
        (∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
          ∀ (fL2 : DomainL2 Q),
            ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (Q : Set (SpatialCoordinates d))] f) →
          let u := G 0 omega fL2
          let fsup := sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|}
          ∃ U : SpatialCoordinates d → ℝ,
            ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
            ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (Q : Set (SpatialCoordinates d))] U) ∧
            (∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), U x = 0) ∧
            _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (Q : Set (SpatialCoordinates d))) U ∧
            ((omega ∈ Good 0 ∧ omega ∈ Good 1) →
              ∀ (zP : SpatialCoordinates d)
                (idx : OddGridIndex d (subdivisionHalfWidth H1)),
                z = oddGridCenter zP (L * r) (subdivisionHalfWidth H1) idx →
                Metric.closedBall z (3 * r / 2) ⊆ Metric.ball zP (L * r / 2) →
                Metric.ball zP (L * r / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
                let parentCell : Set (SpatialCoordinates d) := Metric.ball zP (L * r / 2)
                let nuP : ℝ := ((Gamma 0 omega).measure u parentCell).toReal
                ∃ cq : ℝ,
                  _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha unitClosed (fun x => U (z + r • x) - cq) ∧
                  _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha unitClosed (fun x => U (z + r • x) - cq) ≤
                    Ctotal * r ^ ((2 - (d : ℝ)) / 2) * (sRef 0 omega) ^ (-(1 : ℝ) / 2) *
                      Real.sqrt nuP +
                      Ctotal * r ^ (2 : ℝ) * (sRef 0 omega)⁻¹ * fsup ∧
                  (responseSet r z U).Nonempty ∧
                  IsGLB (responseSet r z U) (responseF r z U) ∧
                  responseF r z U ≤ Ctotal * (eRef 1 k / eRef 0 k) *
                    (nuP + (sRef 0 omega)⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2)) ∧
            (∃ K : ℝ, 0 ≤ K ∧
              ∀ (z' : SpatialCoordinates d) (r' : ℝ), 0 < r' →
                Metric.ball z' (r' / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
                  (responseSet r' z' U).Nonempty ∧
                  IsGLB (responseSet r' z' U) (responseF r' z' U) ∧
                  responseF r' z' U ≤ K * r' ^ ((d : ℝ) - 2 + 2 * alpha - etaGrid)))
  := by
  obtain ⟨Cbound, eps0, lam0, delta0, hC, he0, hl0, hd0, hApply⟩ :=
    lem_goodext d hd I _X _Sob _Step Pin _MeyersMorrey D Cp alpha beta s sigma cell epshom
      halpha hbeta hbetaLtAlpha hs hsSmall hsigma_eq hsigma hcell hepshom etaGrid hetaGrid
      H1 hH1 moment hmoment
  refine ⟨Cbound, eps0, lam0, delta0, hC, he0, hl0, hd0, ?_⟩
  intro cbuf k0 M Rm Sreg It H hMH Ω _ P _ field hfield_meas hfield_law env henv_meas
    henv_law hEnvConv k z gH hgH phi hphi hIRConv eta hEta F Praw Rraw Draw Z rawGood
    eps heps hepsSmall hPrimitive lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet
    hcdetSmall hlamSmall hdisorder eRef heRef_pos heRef_lim ZL DL loL hiL AEL errL ratL hmeas harr
    Qcentre Qside hQside RootIndex _ _ root0 zCat rCat hrCat SCat DCat _ fCat TCat _ thetaCat
    thetaH1Cat usrc srcRep ucell Cext etaCat t orders hetaCatGrid Index _ resp respLim constants
    Gcat coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid _ origin gridRoot gridKey hRootCatalogue
    hRepEstimates hRootsQ S hS GN hGN G hGE Form hE Gamma hGammaRecovery
  have htransfer (a : Fin 2) {X : ℕ → BilateralField d → ℝ} {V : BilateralField d → ℝ}
      (hV : Measurable V) (hXV : TendstoInMeasure (chaosSampleLaw M).toMeasure X atTop V) :
      TendstoInMeasure P (fun n omega => X n (env a n omega)) atTop (fun omega => V (field omega)) :=
    represented_same_law_in_measure (fun n => ⟨henv_meas a n, henv_law a n⟩)
      ⟨hfield_meas, hfield_law⟩ (hEnvConv.mono fun omega h => h a) hV.aestronglyMeasurable hXV
  have hZ := fun a U D code => htransfer a ((hmeas a).1 U D code).1 ((harr a).1 U D code)
  have hD := fun a U D code => htransfer a ((hmeas a).1 U D code).2 ((harr a).2.1 U D code)
  have hlo := fun a U => htransfer a ((hmeas a).2.1 U).1 ((harr a).2.2.1 U)
  have hhi := fun a U => htransfer a ((hmeas a).2.1 U).2.1 ((harr a).2.2.2.1 U)
  have hA := fun a U i j => htransfer a (((hmeas a).2.1 U).2.2 i j) ((harr a).2.2.2.2.1 U i j)
  have herr := fun a => htransfer a (hmeas a).2.2.1 (harr a).2.2.2.2.2.1
  have hrat := fun a => htransfer a (hmeas a).2.2.2 (harr a).2.2.2.2.2.2
  have hFinite := gcat_finite_scores d M s eps hs.1 eta hEta F Praw Rraw Draw Z rawGood hPrimitive
    Unit (fun _ => k) (fun _ => z) gH
  have hcen := aux_affine_source_cells_env_chosen_centre gH k z (fun i => Fin.elim0 i)
  have hlev : gcat_rootLevel gH k ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)) +
      ((0 : ℕ) : ℤ) = (k : ℤ) - (gH : ℤ) := by
    rw [aux_affine_source_cells_env_chosen_level, Nat.cast_zero, add_zero]
  have hRefLim (a : Fin 2) (j : ℕ) :
      Tendsto (fun n : ℕ =>
        (let kappa : ℕ → ℝ := fun J => Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
         kappa (((phi a n : ℤ) - (j : ℤ)).toNat) / kappa (phi a n))) atTop (𝓝 (eRef a j)) := by
    simpa using heRef_lim a j
  let sr : Fin 2 → Ω → ℝ := fun a omega => eRef a k *
    Real.exp (H (field omega) z + ∑ j ∈ Finset.range k, (field omega) (-(j : ℤ)) z)
  let sc : Fin 2 → Unit → Ω → ℝ := fun a _ omega => eRef a (k - gH) *
    Real.exp (H (field omega) z + ∑ j ∈ Finset.range (k - gH), (field omega) (-(j : ℤ)) z)
  have hsRef : ∀ a : Fin 2, ∀ᵐ omega ∂P, 0 < sr a omega ∧
      Tendsto (fun n => gcat_sN M H (phi a n) (k : ℤ) z (env a n omega)) atTop (𝓝 (sr a omega)) := by
    intro a
    filter_upwards [hEnvConv, hIRConv] with omega he hi
    exact ⟨mul_pos (heRef_pos a k) (Real.exp_pos _),
      aux_affine_source_cells_env_sN_tendsto M H (phi a) (hphi a) (eRef a) (hRefLim a)
        k z (fun n => env a n omega) (field omega) (he a) (hi a)⟩
  have hsCmp : ∀ a : Fin 2, ∀ᵐ omega ∂P, ∀ c : Unit, 0 < sc a c omega ∧
      Tendsto (fun n => gcat_sN M H (phi a n)
        (gcat_rootLevel gH k ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)) + ((0 : ℕ) : ℤ))
        (descendantCenter 1 (gcat_rootCentre gH k z ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)))
          (gcat_rootSide gH k ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3))) 0 (fun i => Fin.elim0 i))
        (env a n omega)) atTop (𝓝 (sc a c omega)) := by
    intro a
    filter_upwards [hEnvConv, hIRConv] with omega he hi
    intro c
    refine ⟨mul_pos (heRef_pos a _) (Real.exp_pos _), ?_⟩
    have h := aux_affine_source_cells_env_sN_tendsto M H (phi a) (hphi a) (eRef a) (hRefLim a)
      (k - gH) z (fun n => env a n omega) (field omega) (he a) (hi a)
    simpa only [sc, hcen, hlev, Nat.cast_sub hgH] using h
  have hres := hApply cbuf k0 M Rm Sreg It H hMH Ω P field hfield_meas hfield_law env
    henv_meas henv_law hEnvConv k z ((3 : ℝ) ^ (-(k : ℤ))) rfl z rfl
    (Fin 3) (Fin d → Fin 3) Unit (0 : Fin 3) (fun _ => (1 : Fin 3))
    ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3)) rfl
    (gcat_factor gH) rfl (1 : Fin 3) rfl gcat_shift
    aux_affine_source_cells_env_shift_one
    (gcat_rootLevel gH k) (fun e t => rfl)
    (gcat_rootSide gH k) (fun U => rfl)
    (gcat_rootCentre gH k z) (fun e t => rfl)
    (fun U => zpow_pos (by norm_num) _)
    (aux_affine_source_cells_env_gridCover gH k z)
    (fun _ => ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3))) (fun _ => 0)
    (fun _ i => Fin.elim0 i)
    (fun c => descendantCenter 1
      (gcat_rootCentre gH k z ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)))
      (gcat_rootSide gH k ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3))) 0 (fun i => Fin.elim0 i))
    (fun c => rfl)
    (fun _ => gcat_rootLevel gH k ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)) + ((0 : ℕ) : ℤ))
    (fun c => rfl)
    (fun _ => (3 : ℝ) ^ (-(gcat_rootLevel gH k ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)) + ((0 : ℕ) : ℤ))))
    (fun c => rfl) (fun _ => zpow_pos (by norm_num) _) ()
    (gcat_obsCentre gH k z) (fun U D code => rfl)
    eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive lambdaCut lambdaLim
    lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
    (fun N U D code omega => gcat_prefix gH cbuf k z Z N U D code omega)
    (fun N U D code omega => gcat_prefix gH cbuf k z
      (fun N m w om => (Draw N m w om).toReal) N U D code omega)
    (fun N U D code omega => rfl) (fun N U D code omega => rfl) (by
      filter_upwards [hFinite] with omega hfin
      intro N U D code _hl j _hj
      exact hfin () N U D code j)
    (gcat_sN M H) (fun N l w omega => rfl)
    (fun N U omega => I.lam (gcat_rootCentre gH k z U)
      (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
        (gcat_rootCentre gH k z U) (zpow_pos (by norm_num) _))
      (gcat_rootCentre gH k z U)
      (gcat_rootSide gH k U) sigma 2 /
      gcat_sN M H N (gcat_rootLevel gH k U)
        (gcat_rootCentre gH k z U) omega)
    (fun N U omega => I.Lam (gcat_rootCentre gH k z U)
      (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
        (gcat_rootCentre gH k z U) (zpow_pos (by norm_num) _))
      (gcat_rootCentre gH k z U)
      (gcat_rootSide gH k U) sigma 2 /
      gcat_sN M H N (gcat_rootLevel gH k U)
        (gcat_rootCentre gH k z U) omega)
    (fun N U omega => rfl) (fun N U omega => rfl)
    (fun N U omega =>
      ((gcat_sN M H N (gcat_rootLevel gH k U)
        (gcat_rootCentre gH k z U) omega)⁻¹ •
        Homogenization.Book.Ch02.sigmaCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          ((I.chart (gcat_rootCentre gH k z U)
            (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
              (gcat_rootCentre gH k z U)
              (zpow_pos (by norm_num) _))
            (gcat_rootCentre gH k z U)
            (gcat_rootSide gH k U)).coeffOn
            (Homogenization.originCube d 0))))
    (fun N U omega => rfl)
    (fun N c omega => I.err z ((3 : ℝ) ^ (-((k : ℤ) - (gH : ℤ))))
      (zpow_pos (by norm_num) _)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z (zpow_pos (by norm_num) _))
      z ((3 : ℝ) ^ (-((k : ℤ) - (gH : ℤ))))
      (gcat_sN M H N ((k : ℤ) - (gH : ℤ)) z omega) s 2)
    (fun N c omega => gcat_sN M H N (k : ℤ) z omega /
      gcat_sN M H N ((k : ℤ) - (gH : ℤ)) z omega)
    (by
      intro N c omega
      have ha : gcat_sN M H N (gcat_rootLevel gH k
          ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)) + ((0 : ℕ) : ℤ)) (descendantCenter 1
          (gcat_rootCentre gH k z ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)))
          (gcat_rootSide gH k ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3))) 0
          (fun i => Fin.elim0 i)) omega =
          gcat_sN M H N ((k : ℤ) - (gH : ℤ)) z omega := by
        rw [hlev, hcen]
      rw [ha]
      exact aux_affine_source_cells_env_err_congr I M H N omega _ _ _ _ _ _ _ s
        hcen.symm (by rw [hlev]))
    (by
      intro N c omega
      rw [hlev, hcen])
    phi hphi
    (fun a U D code omega => ZL a U D code (field omega))
    (fun a U D code omega => DL a U D code (field omega))
    (fun a U omega => loL a U (field omega)) (fun a U omega => hiL a U (field omega))
    (fun a U omega => AEL a U (field omega))
    (fun a c omega => errL a c (field omega)) (fun a c omega => ratL a c (field omega))
    hZ hD hlo hhi hA (fun a c => herr a) (fun a c => hrat a)
    Qcentre Qside hQside RootIndex root0 zCat rCat hrCat SCat DCat fCat TCat thetaCat thetaH1Cat
    usrc srcRep ucell Cext etaCat t orders hetaCatGrid Index resp respLim constants Gcat
    coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hRootCatalogue
    hRepEstimates hRootsQ S hS GN hGN G hGE Form hE Gamma hGammaRecovery sr sc hsRef hsCmp
    eRef heRef_pos heRef_lim (fun a => Filter.Eventually.of_forall fun omega => rfl)
  exact hres

end SubdiffusiveProcess.Paper
