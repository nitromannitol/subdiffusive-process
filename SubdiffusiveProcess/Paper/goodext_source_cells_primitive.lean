import SubdiffusiveProcess.Paper.goodext_source_cells_holder_forms
import SubdiffusiveProcess.Paper.lfsgs_primitive_scores_exists
import SubdiffusiveProcess.Paper.uniform_response_input
open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- Choose every score margin, the uniform response witness and actual primitive
scores before applying the counted local Holder/form construction. The same actual
arrays and references are returned for later harmonic energy and stopping use. -/
theorem goodext_source_cells_primitive
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
    (Dbase : Paper.sum_errors_baseline_input d)
    (alpha beta etaGrid : ℝ)
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) (hbetaLtAlpha : beta < alpha)
    (hetaGrid : 0 < etaGrid) (H1 : ℕ) (hH1 : 0 < H1)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    ∃ Cbound eps lambdaLim cdet delta0 : ℝ,
      1 ≤ Cbound ∧ eps ∈ Set.Ioo (0 : ℝ) 1 ∧ lambdaLim ∈ Set.Ioo (0 : ℝ) 1 ∧
      0 < cdet ∧ 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
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
        (hgH : ∀ b, 1 ≤ k b)
        (phi : Fin 2 → ℕ → ℕ) (hphi : ∀ a, StrictMono (phi a))
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
          closure (centeredCube (gcat_rootCentre 1 (k b) (z b) U) (gcat_rootSide 1 (k b) U)
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
        (hBounds : ∀ a : Fin 2, ∀ᵐ omega ∂P,
          in_represented_bounds_seq d hd Qcentre Qside hQside S
            (fun n => Lane4.cutoffPositiveCoefficient M H (env a n omega)
              (phi a n) Qcentre hQside) (G a omega)),
      ∃ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (N i : ℕ) (y : Vec d),
          eta N omega i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)) ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
          primitive_scores d M (1 / 64) eps (eta N omega)
            (fun m y => F N m y omega) (fun m y => Praw N m y omega)
            (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
            (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) ∧
      ∃ (Form : Fin 2 → Ω → _root_.DirichletForm
          (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
        (Gamma : ∀ (a : Fin 2) omega, DirichletForm.EnergyMeasure (Form a omega).toClosedForm),
      (∀ a omega, ∃ C, DirichletForm.IsCoreOn (Form a omega).toClosedForm
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) C) ∧
      (∀ᵐ omega ∂P, ∀ a u, (Form a omega).energy u = limitFormEnergy (G a omega) u) ∧
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
      ( ∀ (a : Fin 2) (b : Cells), aux_affine_source_cells_env_cellArrays I M H (1 / 64 : ℝ) ((beta - 1 / 2) / 4) 1 0 Z Draw (fun n => phi a (psi n))
          (k b) (z b) (ZL a b) (DL a b) (loL a b) (hiL a b) (AEL a b) (errL a b) (ratL a b)) ∧
      (∀ (active : List (Fin d → Fin (3 ^ H1)) → Prop)
        (index : List (Fin d → Fin (3 ^ H1)) → Cells),
        (∀ w, active w → k (index w) = H1 * w.length) →
        let Good := fun w => {omega | active w → ∀ a : Fin 2, omega ∈
          gcat_good 1 lambdaLim (1 / 4 : ℝ) (1 / 4 : ℝ) cdet (ZL a (index w)) (DL a (index w))
            (loL a (index w)) (hiL a (index w)) (errL a (index w)) (ratL a (index w))}
        ∃ B : BilateralField d → ℝ, Measurable B ∧ (∀ omega, 0 ≤ B omega) ∧
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            ∀ (J : ℕ) (pi : Fin J → (Fin d → Fin (3 ^ H1))), 1 ≤ J →
              (Set.ncard {i : Fin J | omega ∉ Good ((List.ofFn pi).take (i.val + 1))} : ℝ) ≤
                theta * (J : ℝ) + B omega) ∧
      (let Q := centeredCube Qcentre Qside hQside
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * (((1 : ℕ) : ℝ) + ((0 : ℕ) : ℝ)))
      let Good : Cells → Fin 2 → Set Ω := fun b a => field ⁻¹' gcat_good 1 lambdaLim (1 / 4 : ℝ) (1 / 4 : ℝ) cdet
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
  obtain ⟨Cresp, hCresp, hUniform⟩ := aux_thm_prop_uniform_response_input d hd
  have hsigma : (beta - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor <;> linarith [hbeta.1, hbeta.2]
  obtain ⟨Cbound, eps0, lam0, hC, he0, hl0, hApply⟩ :=
    goodext_source_cells_holder_forms d hd I _X _Sob _Step Pin _MeyersMorrey D Cp Dbase
      Cresp hCresp alpha beta (1 / 64) ((beta - 1 / 2) / 4) (1 / 4) (1 / 4)
      halpha hbeta hbetaLtAlpha (by norm_num) (by norm_num) rfl hsigma (by norm_num)
      (by norm_num) etaGrid hetaGrid H1 hH1 1 le_rfl theta 1 htheta0 htheta1 (by norm_num)
  let eps := min (1 / 2 : ℝ) (eps0 / 2)
  have heps : eps ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_min (by norm_num) (by positivity), (min_le_left _ _).trans_lt (by norm_num)⟩
  have hepsSmall : eps ≤ eps0 := (min_le_right _ _).trans (by linarith)
  let lambdaDet := min (1 / 2 : ℝ) (lam0 / 2)
  let lambdaLim := lambdaDet / 2
  let lambdaCut := lambdaLim / 2
  have hld : 0 < lambdaDet := lt_min (by norm_num) (by positivity)
  have hld1 : lambdaDet < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hThresholds : 0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
      lambdaLim < lambdaDet ∧ lambdaDet < 1 := by
    dsimp only [lambdaCut, lambdaLim]
    constructor; · positivity
    constructor; · linarith
    exact ⟨by linarith, hld1⟩
  have hll : lambdaLim ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp only [lambdaLim]; constructor <;> linarith
  have hlam : lambdaDet ≤ lam0 := (min_le_right _ _).trans (by linarith)
  let cdet := Cbound⁻¹ / 2
  have hC0 : 0 < Cbound := zero_lt_one.trans_le hC
  have hcdet : 0 < cdet := by positivity
  have hcSmall : cdet ≤ Cbound⁻¹ := by
    have : 0 < Cbound⁻¹ := inv_pos.mpr hC0
    dsimp only [cdet]; linarith
  obtain ⟨delta0, hd0, hModel⟩ := hApply 0 1 1 eps heps hepsSmall le_rfl
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcSmall hlam
  refine ⟨Cbound, eps, lambdaLim, cdet, delta0, hC, heps, hll, hcdet, hd0, ?_⟩
  intro M Rm Sreg It H hMH Ω _ P _ field hfield_meas hfield_law env henv_meas
    henv_law hEnvConv Cells _ first k z hgH phi hphi hdisorder
    Qcentre Qside hQside RootIndex _ _ root0 zCat rCat hrCat SCat DCat _ fCat TCat _ thetaCat
    thetaH1Cat usrc srcRep ucell Cext etaCat t orders hetaCatGrid Index _ resp respLim constants
    Gcat coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid _ origin gridRoot gridKey hRootCatalogue
    hRepEstimates hRootsQ S hS GN hGN G hGE hBounds
  obtain ⟨Rgood, hRgood, _hPhysical⟩ := hUniform M Rm
  obtain ⟨eta, F, Praw, Rraw, Draw, Z, rawGood, hEta, hPrimitive⟩ :=
    aux_lfsgs_hRegWitness_of_arbitrary_Rm_primitive_scores_exists M (1 / 64) eps
      (by norm_num) heps
  refine ⟨eta, F, Praw, Rraw, Draw, Z, rawGood, hEta, hPrimitive, ?_⟩
  exact hModel M Rgood hRgood.le Sreg It H hMH Ω P field hfield_meas hfield_law env henv_meas
    henv_law hEnvConv Cells first k z hgH phi hphi eta hEta F Praw Rraw Draw Z rawGood
    hPrimitive hdisorder Qcentre Qside hQside RootIndex root0 zCat rCat hrCat SCat DCat
    fCat TCat thetaCat thetaH1Cat usrc srcRep ucell Cext etaCat t orders hetaCatGrid Index
    resp respLim constants Gcat coercivityKey extensionKey lambdaKey sourceResponseKey
    sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin
    gridRoot gridKey hRootCatalogue hRepEstimates hRootsQ S hS GN hGN G hGE hBounds
end Paper
