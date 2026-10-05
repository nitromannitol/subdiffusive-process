module

public import SubdiffusiveProcess.Paper.gcat_prefix_limits
public import SubdiffusiveProcess.Paper.gcat_band_witness
public import SubdiffusiveProcess.Paper.inputs_simultaneous
public import SubdiffusiveProcess.Paper.lem_as_regularity_primitive_witness
public import SubdiffusiveProcess.Probability.InfraredCharacterizationExistence

@[expose] public section

open SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Paper SubdiffusiveProcess.EllipticRegularity MeasureTheory Filter Set Topology
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.AuditExports

/-- Measurability and convergence in probability of the actual catalogue arrays.
This definition contains no moment, band, tail or witness-cover assumption. -/
def is_limiting_good_cell_catalogue
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Model.GMCModel d) (I : in_J d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (s sigma : ℝ) (gH cbuf k : ℕ) (z : SpatialCoordinates d) (phi : ℕ → ℕ)
    (Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (ZLim DLim : aux_gcat_band_witness_Roots d → ∀ D : ℕ,
      aux_gcat_band_witness_Code d D → BilateralField d → ℝ)
    (loLim hiLim : aux_gcat_band_witness_Roots d → BilateralField d → ℝ)
    (AELim : aux_gcat_band_witness_Roots d → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
    (errLim ratioLim : Unit → BilateralField d → ℝ) : Prop :=
        (∀ U D code, Measurable (ZLim U D code) ∧ Measurable (DLim U D code)) ∧
        (∀ U, Measurable (loLim U) ∧ Measurable (hiLim U) ∧
          ∀ i j, Measurable (fun omega => AELim U omega i j)) ∧
        Measurable (errLim ()) ∧ Measurable (ratioLim ()) ∧
        (∀ U D code, TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega => gcat_prefix gH cbuf k z Z (phi n) U D code omega) atTop
          (ZLim U D code)) ∧
        (∀ U D code, TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega => gcat_prefix gH cbuf k z (fun N m w om => (Draw N m w om).toReal)
            (phi n) U D code omega) atTop (DLim U D code)) ∧
        (∀ U, TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega =>
            I.lam (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi n) (gcat_rootCentre gH k z U)
                (zpow_pos (by norm_num) _))
              (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) sigma 2 /
            gcat_sN M H (phi n) (gcat_rootLevel gH k U) (gcat_rootCentre gH k z U) omega)
          atTop (loLim U)) ∧
        (∀ U, TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega =>
            I.Lam (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi n) (gcat_rootCentre gH k z U)
                (zpow_pos (by norm_num) _))
              (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) sigma 2 /
            gcat_sN M H (phi n) (gcat_rootLevel gH k U) (gcat_rootCentre gH k z U) omega)
          atTop (hiLim U)) ∧
        (∀ U (i j : Fin d), TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega =>
            ((gcat_sN M H (phi n) (gcat_rootLevel gH k U) (gcat_rootCentre gH k z U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((I.chart (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi n) (gcat_rootCentre gH k z U)
                    (zpow_pos (by norm_num) _))
                  (gcat_rootCentre gH k z U) (gcat_rootSide gH k U)).coeffOn
                  (Homogenization.originCube d 0))) i j)
          atTop (fun omega => AELim U omega i j)) ∧
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega =>
            I.err z ((3 : ℝ) ^ (-((k : ℤ) - (gH : ℤ)))) (zpow_pos (by norm_num) _)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi n) z (zpow_pos (by norm_num) _))
              z ((3 : ℝ) ^ (-((k : ℤ) - (gH : ℤ))))
              (gcat_sN M H (phi n) ((k : ℤ) - (gH : ℤ)) z omega) s 2)
          atTop (errLim ()) ∧
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega => gcat_sN M H (phi n) (k : ℤ) z omega /
            gcat_sN M H (phi n) ((k : ℤ) - (gH : ℤ)) z omega)
          atTop (ratioLim ())

/-- Paper `mfd:lem-witness` for the actual limiting catalogue, with `lambdaLim` used in
`gcat_good`. The primitive arrays and all convergence, moment, band and prefix suppliers are
constructed inside the proof. One disorder threshold works for a countable cell catalogue,
and the cover holds outside one null set shared by its cells. -/
theorem limiting_good_cell_witness
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (s sigma eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (gH cbuf k0 : ℕ) (hk0 : 1 ≤ k0)
    (lambdaLim cell epshom cdet : ℝ) (hlam : 0 < lambdaLim)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1) (hepshom : 0 < epshom) (hcdet : 0 < cdet)
    (A : ℝ) :
    let I : in_J d := Classical.choice (inputs_J_witness d hd)
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
      ∃ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H ∧
      let eta := Classical.choose (SubdiffusiveProcess.FiniteStopping.ps_eta_exists M)
      let Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal :=
        fun N m y omega => primitiveErrorScore M s (eta N omega) m y
      let Z : ℕ → ℕ → Vec d → BilateralField d → ℝ :=
        fun N m y omega => primitiveBadScore M s eps (eta N omega) m y
      ∀ (Cells : Type) [Countable Cells] (cellLevel : Cells → ℕ)
        (cellCentre : Cells → SpatialCoordinates d) (phi0 : ℕ → ℕ), StrictMono phi0 →
      ∃ psi : ℕ → ℕ, StrictMono psi ∧
      ∃ (ZLim DLim : Cells → aux_gcat_band_witness_Roots d → ∀ D : ℕ,
          aux_gcat_band_witness_Code d D → BilateralField d → ℝ)
        (loLim hiLim : Cells → aux_gcat_band_witness_Roots d → BilateralField d → ℝ)
        (AELim : Cells → aux_gcat_band_witness_Roots d →
          BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (errLim ratioLim : Cells → Unit → BilateralField d → ℝ),
        (∀ c : Cells, is_limiting_good_cell_catalogue d M I H s sigma gH cbuf
          (cellLevel c) (cellCentre c) (fun n => phi0 (psi n)) Draw Z
          (ZLim c) (DLim c) (loLim c) (hiLim c) (AELim c) (errLim c) (ratioLim c)) ∧
        ∃ W : Cells → ℕ+ → Set (BilateralField d),
          (∀ c (h : ℕ+), MeasurableSet[aux_gcat_band_condexp_Bsig d
            ((cellLevel c : ℤ) - (h : ℤ)) ((cellLevel c : ℤ) + 2 * (h : ℤ))] (W c h)) ∧
          (∀ c h, (chaosSampleLaw M).toMeasure (W c h) ≤
            ENNReal.ofReal (Real.exp (-(A * (h : ℝ))))) ∧
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ c : Cells,
            omega ∉ gcat_good k0 lambdaLim cell epshom cdet
              (ZLim c) (DLim c) (loLim c) (hiLim c) (errLim c) (ratioLim c) →
            omega ∈ ⋃ h : ℕ+, W c h) := by
  classical
  intro I
  let Pc : in_poincare d hd I := Classical.choice (inputs_poincare_witness d hd I)
  let Xc : in_extension d hd I := Classical.choice (inputs_extension_witness d hd I)
  let Sf : SobolevFoundationalInput d hd := Classical.choice (inputs_Sf_witness d hd)
  let W : SmallPerturbationInput d := Classical.choice (inputs_W_witness d)
  obtain ⟨Cresp, deltaR, hCresp, hdeltaR, hresponses⟩ :=
    inputs_responses_witness d hd 1 le_rfl
  obtain ⟨deltaL, hdeltaL, hlimits⟩ := gcat_prefix_limits d hd I Pc Xc W Sf
    (inputs_deterministic_witness d hd) Cresp hCresp s sigma eps hs hsigma heps gH cbuf
  have hA : 0 < max A 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨deltaW, hdeltaW, hwitness⟩ := gcat_band_witness d hd I Pc Xc W Sf
    (inputs_deterministic_witness d hd) Cresp hCresp (inputs_baseline_witness d hd)
    s sigma eps hs hsigma heps gH cbuf k0 hk0 lambdaLim cell epshom cdet
    hlam hcell hepshom hcdet (max A 1) hA
  refine ⟨min deltaR (min deltaL deltaW), lt_min hdeltaR (lt_min hdeltaL hdeltaW), ?_⟩
  intro M hdelta
  obtain ⟨Rm, hRm, _⟩ := hresponses M (hdelta.trans (min_le_left _ _))
  let Sreg : in_6_16 d M := inputs_regularity_witness d M
  let It : in_iteration d M I Sreg := inputs_iteration_witness d hd M I
  obtain ⟨H, hH⟩ := SubdiffusiveProcess.exists_infraredCharacterization hd M
  refine ⟨H, hH, ?_⟩
  intro eta Draw Z Cells _ cellLevel cellCentre phi0 hphi0
  have heta := Classical.choose_spec (SubdiffusiveProcess.FiniteStopping.ps_eta_exists M)
  let F : ℕ → ℕ → Vec d → BilateralField d → ENNReal :=
    fun N m y omega => primitiveFieldScore s (eta N omega) m y
  let Praw : ℕ → ℕ → Vec d → BilateralField d → ENNReal :=
    fun N m y omega => primitiveProductScore s (eta N omega) m y
  let Rraw : ℕ → ℕ → Vec d → BilateralField d → ENNReal :=
    fun N m y omega => primitiveResponseScore M s (eta N omega) m y
  let rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop :=
    fun N m y omega => primitiveGoodEvent M s eps (eta N omega) m y
  have hprim : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega) :=
    Filter.Eventually.of_forall (fun omega N =>
      aux_lem_as_regularity_primitive_witness_exact M s eps hs heps (eta N omega))
  obtain ⟨psi, hpsi, ZLim, DLim, loLim, hiLim, AELim, errLim, ratioLim, hlim⟩ :=
    hlimits M (hdelta.trans ((min_le_right _ _).trans (min_le_left _ _)))
      Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim
      Cells cellLevel cellCentre phi0 hphi0
  refine ⟨psi, hpsi, ZLim, DLim, loLim, hiLim, AELim, errLim, ratioLim, hlim, ?_⟩
  have hex : ∀ c : Cells, ∃ Wc : ℕ+ → Set (BilateralField d),
      (∀ h : ℕ+, MeasurableSet[aux_gcat_band_condexp_Bsig d
        ((cellLevel c : ℤ) - (h : ℤ)) ((cellLevel c : ℤ) + 2 * (h : ℤ))] (Wc h)) ∧
      (∀ h, (chaosSampleLaw M).toMeasure (Wc h) ≤
        ENNReal.ofReal (Real.exp (-(A * (h : ℝ))))) ∧
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        omega ∉ gcat_good k0 lambdaLim cell epshom cdet
          (ZLim c) (DLim c) (loLim c) (hiLim c) (errLim c) (ratioLim c) →
        omega ∈ ⋃ h : ℕ+, Wc h) := by
    intro c
    obtain ⟨_, _, _, _, hZ, hD, hlo, hhi, _, herr, hratio⟩ := hlim c
    obtain ⟨Wc, hWm, hWp, hWa⟩ :=
      hwitness M (hdelta.trans ((min_le_right _ _).trans (min_le_right _ _)))
        Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim
        (cellLevel c) (cellCentre c) (fun n => phi0 (psi n)) (hphi0.comp hpsi)
        (ZLim c) (DLim c) (loLim c) (hiLim c) (errLim c) (ratioLim c)
        hZ hD hlo hhi herr hratio
    refine ⟨Wc, hWm, fun h => (hWp h).trans ?_, hWa⟩
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (le_max_left A 1) (show 0 ≤ (h : ℝ) by positivity)
    linarith
  choose Wc hWm hWp hWa using hex
  exact ⟨Wc, hWm, hWp, ae_all_iff.mpr hWa⟩

/-- Paper `mfd:lem-witness` for the limiting arrays defining `G_E(q)`, taken as given: for any
strictly increasing sequence of cutoffs along which the arrays are the limits in measure of the
finite-cutoff quantities of the catalogue, and any infrared characterization `H`, the failure of
`gcat_good` with `λ = lambdaLim` is covered by the events `W c h`, outside one null set shared by
the cells. The disorder threshold precedes the model, `H`, the catalogue and the arrays. -/
theorem limiting_good_cell_witness_of_limits
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (s sigma eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (gH cbuf k0 : ℕ) (hk0 : 1 ≤ k0)
    (lambdaLim cell epshom cdet : ℝ) (hlam : 0 < lambdaLim)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1) (hepshom : 0 < epshom) (hcdet : 0 < cdet)
    (A : ℝ) :
    let I : in_J d := Classical.choice (inputs_J_witness d hd)
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
      ∀ H : BilateralField d → C(SpatialCoordinates d, ℝ), InfraredCharacterization M H →
      let eta := Classical.choose (SubdiffusiveProcess.FiniteStopping.ps_eta_exists M)
      let Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal :=
        fun N m y omega => primitiveErrorScore M s (eta N omega) m y
      let Z : ℕ → ℕ → Vec d → BilateralField d → ℝ :=
        fun N m y omega => primitiveBadScore M s eps (eta N omega) m y
      ∀ (Cells : Type) [Countable Cells] (cellLevel : Cells → ℕ)
        (cellCentre : Cells → SpatialCoordinates d) (phi : ℕ → ℕ), StrictMono phi →
      ∀ (ZLim DLim : Cells → aux_gcat_band_witness_Roots d → ∀ D : ℕ,
          aux_gcat_band_witness_Code d D → BilateralField d → ℝ)
        (loLim hiLim : Cells → aux_gcat_band_witness_Roots d → BilateralField d → ℝ)
        (AELim : Cells → aux_gcat_band_witness_Roots d →
          BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (errLim ratioLim : Cells → Unit → BilateralField d → ℝ),
        (∀ c : Cells, is_limiting_good_cell_catalogue d M I H s sigma gH cbuf
          (cellLevel c) (cellCentre c) phi Draw Z
          (ZLim c) (DLim c) (loLim c) (hiLim c) (AELim c) (errLim c) (ratioLim c)) →
        ∃ W : Cells → ℕ+ → Set (BilateralField d),
          (∀ c (h : ℕ+), MeasurableSet[aux_gcat_band_condexp_Bsig d
            ((cellLevel c : ℤ) - (h : ℤ)) ((cellLevel c : ℤ) + 2 * (h : ℤ))] (W c h)) ∧
          (∀ c h, (chaosSampleLaw M).toMeasure (W c h) ≤
            ENNReal.ofReal (Real.exp (-(A * (h : ℝ))))) ∧
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ c : Cells,
            omega ∉ gcat_good k0 lambdaLim cell epshom cdet
              (ZLim c) (DLim c) (loLim c) (hiLim c) (errLim c) (ratioLim c) →
            omega ∈ ⋃ h : ℕ+, W c h) := by
  classical
  intro I
  let Pc : in_poincare d hd I := Classical.choice (inputs_poincare_witness d hd I)
  let Xc : in_extension d hd I := Classical.choice (inputs_extension_witness d hd I)
  let Sf : SobolevFoundationalInput d hd := Classical.choice (inputs_Sf_witness d hd)
  let W : SmallPerturbationInput d := Classical.choice (inputs_W_witness d)
  obtain ⟨Cresp, deltaR, hCresp, hdeltaR, hresponses⟩ :=
    inputs_responses_witness d hd 1 le_rfl
  have hA : 0 < max A 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨deltaW, hdeltaW, hwitness⟩ := gcat_band_witness d hd I Pc Xc W Sf
    (inputs_deterministic_witness d hd) Cresp hCresp (inputs_baseline_witness d hd)
    s sigma eps hs hsigma heps gH cbuf k0 hk0 lambdaLim cell epshom cdet
    hlam hcell hepshom hcdet (max A 1) hA
  refine ⟨min deltaR deltaW, lt_min hdeltaR hdeltaW, ?_⟩
  intro M hdelta H hH eta Draw Z Cells _ cellLevel cellCentre phi hphi
    ZLim DLim loLim hiLim AELim errLim ratioLim hlim
  obtain ⟨Rm, hRm, _⟩ := hresponses M (hdelta.trans (min_le_left _ _))
  let Sreg : in_6_16 d M := inputs_regularity_witness d M
  let It : in_iteration d M I Sreg := inputs_iteration_witness d hd M I
  have heta := Classical.choose_spec (SubdiffusiveProcess.FiniteStopping.ps_eta_exists M)
  let F : ℕ → ℕ → Vec d → BilateralField d → ENNReal :=
    fun N m y omega => primitiveFieldScore s (eta N omega) m y
  let Praw : ℕ → ℕ → Vec d → BilateralField d → ENNReal :=
    fun N m y omega => primitiveProductScore s (eta N omega) m y
  let Rraw : ℕ → ℕ → Vec d → BilateralField d → ENNReal :=
    fun N m y omega => primitiveResponseScore M s (eta N omega) m y
  let rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop :=
    fun N m y omega => primitiveGoodEvent M s eps (eta N omega) m y
  have hprim : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega) :=
    Filter.Eventually.of_forall (fun omega N =>
      aux_lem_as_regularity_primitive_witness_exact M s eps hs heps (eta N omega))
  have hex : ∀ c : Cells, ∃ Wc : ℕ+ → Set (BilateralField d),
      (∀ h : ℕ+, MeasurableSet[aux_gcat_band_condexp_Bsig d
        ((cellLevel c : ℤ) - (h : ℤ)) ((cellLevel c : ℤ) + 2 * (h : ℤ))] (Wc h)) ∧
      (∀ h, (chaosSampleLaw M).toMeasure (Wc h) ≤
        ENNReal.ofReal (Real.exp (-(A * (h : ℝ))))) ∧
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        omega ∉ gcat_good k0 lambdaLim cell epshom cdet
          (ZLim c) (DLim c) (loLim c) (hiLim c) (errLim c) (ratioLim c) →
        omega ∈ ⋃ h : ℕ+, Wc h) := by
    intro c
    obtain ⟨_, _, _, _, hZ, hD, hlo, hhi, _, herr, hratio⟩ := hlim c
    obtain ⟨Wc, hWm, hWp, hWa⟩ :=
      hwitness M (hdelta.trans (min_le_right _ _))
        Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim
        (cellLevel c) (cellCentre c) phi hphi
        (ZLim c) (DLim c) (loLim c) (hiLim c) (errLim c) (ratioLim c)
        hZ hD hlo hhi herr hratio
    refine ⟨Wc, hWm, fun h => (hWp h).trans ?_, hWa⟩
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (le_max_left A 1) (show 0 ≤ (h : ℝ) by positivity)
    linarith
  choose Wc hWm hWp hWa using hex
  exact ⟨Wc, hWm, hWp, ae_all_iff.mpr hWa⟩

end SubdiffusiveProcess.AuditExports
