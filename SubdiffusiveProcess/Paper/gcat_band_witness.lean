module

public import SubdiffusiveProcess.Paper.gcat_band_witness_prefix
public import SubdiffusiveProcess.Paper.gcat_band_witness_tests

@[expose] public section

open MeasureTheory Filter Set SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators Topology NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_gcat_band_witness_union_rate (A : ℝ) (h : ℕ+) :
    ENNReal.ofReal (Real.exp (-((A + 1) * ((h : ℕ) : ℝ)))) +
      ENNReal.ofReal (Real.exp (-((A + 1) * ((h : ℕ) : ℝ)))) ≤
      ENNReal.ofReal (Real.exp (-(A * ((h : ℕ) : ℝ)))) := by
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have hh : (1 : ℝ) ≤ ((h : ℕ) : ℝ) := by exact_mod_cast h.pos
  have hexp : Real.exp (-((A + 1) * ((h : ℕ) : ℝ))) =
      Real.exp (-(A * ((h : ℕ) : ℝ))) * Real.exp (-((h : ℕ) : ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : Real.exp (-((h : ℕ) : ℝ)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-1) < 1 / 2 := by
    rw [Real.exp_neg]
    have := Real.exp_one_gt_d9
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have h3 := Real.exp_pos (-(A * ((h : ℕ) : ℝ)))
  rw [hexp]
  nlinarith

/-- The complete interval-witness cover of the failure of `gcat_good` for one catalogue cell: `deltaW` is
chosen before the model, the cell, the arrays and the subsequence. -/
theorem gcat_band_witness
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Pc : Paper.in_poincare d hd I) (Xc : Paper.in_extension d hd I)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (Dd : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (Dbase : Paper.sum_errors_baseline_input d)
    (s sigma eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (heps : eps ∈ Set.Ioo (0 : ℝ) 1) (gH cbuf k0 : ℕ) (hk0 : 1 ≤ k0)
    (lambdaLim cell epshom cdet : ℝ) (hlam : 0 < lambdaLim)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1) (hepshom : 0 < epshom) (hcdet : 0 < cdet)
    (A : ℝ) (hA : 0 < A) :
    ∃ deltaW : ℝ, 0 < deltaW ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ deltaW →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
            omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
      ∀ (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
          primitive_scores d M s eps (eta N omega)
            (fun m y => F N m y omega) (fun m y => Praw N m y omega)
            (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
            (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
      ∀ (k : ℕ) (z : SpatialCoordinates d) (phi : ℕ → ℕ), StrictMono phi →
      ∀ (ZLim DLim : aux_gcat_band_witness_Roots d → ∀ D : ℕ, aux_gcat_band_witness_Code d D →
          BilateralField d → ℝ)
        (loLim hiLim : aux_gcat_band_witness_Roots d → BilateralField d → ℝ)
        (errLim ratioLim : Unit → BilateralField d → ℝ),
        (∀ (U : aux_gcat_band_witness_Roots d) (D : ℕ) (code : aux_gcat_band_witness_Code d D),
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun n omega => gcat_prefix gH cbuf k z Z (phi n) U D code omega) atTop (ZLim U D code)) →
        (∀ (U : aux_gcat_band_witness_Roots d) (D : ℕ) (code : aux_gcat_band_witness_Code d D),
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun n omega => gcat_prefix gH cbuf k z (fun N m w om => (Draw N m w om).toReal) (phi n)
              U D code omega) atTop (DLim U D code)) →
        (∀ U : aux_gcat_band_witness_Roots d, TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega =>
            I.lam (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
              (Lane4.cutoffPositiveCoefficient M H omega (phi n) (gcat_rootCentre gH k z U)
                (zpow_pos (by norm_num) _))
              (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) sigma 2 /
            gcat_sN M H (phi n) (gcat_rootLevel gH k U) (gcat_rootCentre gH k z U) omega)
          atTop (loLim U)) →
        (∀ U : aux_gcat_band_witness_Roots d, TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega =>
            I.Lam (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
              (Lane4.cutoffPositiveCoefficient M H omega (phi n) (gcat_rootCentre gH k z U)
                (zpow_pos (by norm_num) _))
              (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) sigma 2 /
            gcat_sN M H (phi n) (gcat_rootLevel gH k U) (gcat_rootCentre gH k z U) omega)
          atTop (hiLim U)) →
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega =>
            I.err z ((3 : ℝ) ^ (-((k : ℤ) - (gH : ℤ)))) (zpow_pos (by norm_num) _)
              (Lane4.cutoffPositiveCoefficient M H omega (phi n) z (zpow_pos (by norm_num) _))
              z ((3 : ℝ) ^ (-((k : ℤ) - (gH : ℤ))))
              (gcat_sN M H (phi n) ((k : ℤ) - (gH : ℤ)) z omega) s 2)
          atTop (errLim ()) →
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega => gcat_sN M H (phi n) (k : ℤ) z omega /
            gcat_sN M H (phi n) ((k : ℤ) - (gH : ℤ)) z omega)
          atTop (ratioLim ()) →
        ∃ Wc : ℕ+ → Set (BilateralField d),
          (∀ h : ℕ+, MeasurableSet[aux_gcat_band_condexp_Bsig d ((k : ℤ) - (h : ℤ))
            ((k : ℤ) + 2 * (h : ℤ))] (Wc h)) ∧
          (∀ h : ℕ+, (chaosSampleLaw M).toMeasure (Wc h) ≤
            ENNReal.ofReal (Real.exp (-(A * ((h : ℕ) : ℝ))))) ∧
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            omega ∉ gcat_good k0 lambdaLim cell epshom cdet ZLim DLim loLim hiLim errLim ratioLim →
            omega ∈ ⋃ h : ℕ+, Wc h := by
  obtain ⟨δp, hδp, hpre⟩ := gcat_band_witness_prefix d hd I Pc Xc W Sf Dd Cresp hCresp Dbase s sigma eps
    hs hsigma heps gH cbuf k0 hk0 lambdaLim hlam (A + 1) (by linarith)
  obtain ⟨δt, hδt, htest⟩ := gcat_band_witness_tests d hd I Pc Xc W Sf Dd Cresp hCresp Dbase s sigma eps
    hs hsigma heps gH cell epshom cdet hcell hepshom hcdet (A + 1) (by linarith)
  refine ⟨min δp δt, lt_min hδp hδt, ?_⟩
  intro M hMd Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim k z phi hphi ZLim DLim loLim
    hiLim errLim ratioLim hZ hD hlo hhi herr hrat
  obtain ⟨Wp, hWpm, hWpp, hWpa⟩ := hpre M (hMd.trans (min_le_left _ _)) Rm hRm Sreg It H hH eta heta F
    Praw Rraw Draw Z rawGood hprim k z phi hphi ZLim DLim hZ hD
  obtain ⟨Wt, hWtm, hWtp, hWta⟩ := htest M (hMd.trans (min_le_right _ _)) Rm hRm Sreg It H hH eta heta F
    Praw Rraw Draw Z rawGood hprim k z phi hphi loLim hiLim errLim ratioLim hlo hhi herr hrat
  refine ⟨fun h => Wp h ∪ Wt h, fun h => (hWpm h).union (hWtm h), fun h => ?_, ?_⟩
  · refine (measure_union_le _ _).trans ?_
    exact (add_le_add (hWpp h) (hWtp h)).trans (aux_gcat_band_witness_union_rate A h)
  · filter_upwards [hWpa, hWta] with ω hp ht hnot
    by_cases hpre' : ∀ (U : aux_gcat_band_witness_Roots d) (D : ℕ), k0 ≤ D →
        ∀ code : aux_gcat_band_witness_Code d D,
          ZLim U D code ω < lambdaLim * (D : ℝ) ∧ DLim U D code ω < lambdaLim * (D : ℝ)
    · have hT : ¬ ((∀ U : aux_gcat_band_witness_Roots d, cell ≤ loLim U ω ∧ hiLim U ω ≤ cell⁻¹) ∧
          errLim () ω ≤ epshom * cdet ∧ ∀ c : Unit, ratioLim c ω ∈ Set.Ioo (1 / 2 : ℝ) 2) :=
        fun h => hnot ⟨hpre', h⟩
      obtain ⟨h, hh⟩ := Set.mem_iUnion.mp (ht hT)
      exact Set.mem_iUnion.mpr ⟨h, Or.inr hh⟩
    · obtain ⟨h, hh⟩ := Set.mem_iUnion.mp (hp hpre')
      exact Set.mem_iUnion.mpr ⟨h, Or.inl hh⟩

end Paper
