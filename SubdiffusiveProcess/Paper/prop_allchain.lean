module

public import SubdiffusiveProcess.Section10.AllChainCounting
public import SubdiffusiveProcess.Paper.gcat_band_witness
public import SubdiffusiveProcess.Paper.gcat_good_measurable
public import SubdiffusiveProcess.Paper.affine_source_cells_env

@[expose] public section

open Filter MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_prop_allchain_band
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (lo hi : ℤ) :
    (MeasurableSpace.comap
          (fun omega : BilateralField d =>
            fun j : Set.Icc lo hi => omega (-(j : ℤ)))
          (inferInstance : MeasurableSpace
            ((j : Set.Icc lo hi) → C(SpatialCoordinates d, ℝ)))) =
      ⨆ j : ℤ, ⨆ (_ : j ∈ Finset.Icc lo hi),
        MeasurableSpace.comap
          (fun omega : BilateralField d => omega (-j))
          (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)) := by
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, iSup_subtype]
  simp only [Finset.mem_Icc, Set.mem_Icc]
  rfl

/-- Actual failed-cell events from the same concrete gcat catalogue used by
`aux_affine_source_cells_env_cellArrays`, `goodext_source_cell`, and the affine
consumers. The band supplier is produced internally before the disorder threshold.
All three chain and tail conclusions are retained. -/
theorem prop_allchain
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
    (H1 : ℕ) (hH1 : 0 < H1) (theta bstar : ℝ)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) (hbstar : 0 < bstar) :
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
      ∀ (Cells : Type) [Countable Cells] (cellLevel : Cells → ℕ)
        (cellCentre : Cells → SpatialCoordinates d)
        (phi : ℕ → ℕ), StrictMono phi →
      ∀ (ZLim DLim : Cells → ∀ (U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
        (loLim hiLim : Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
        (AELim : Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (errLim ratioLim : Cells → Unit → BilateralField d → ℝ),
      (∀ c : Cells,
        (∀ U D code, Measurable (ZLim c U D code) ∧ Measurable (DLim c U D code)) ∧
        (∀ U, Measurable (loLim c U) ∧ Measurable (hiLim c U)) ∧
        Measurable (errLim c ()) ∧ Measurable (ratioLim c ())) →
      aux_affine_source_cells_env_arrays I M H s sigma gH cbuf Z Draw phi cellLevel cellCentre
        ZLim DLim loLim hiLim AELim errLim ratioLim →
      ∀ (active : List (Fin d → Fin (3 ^ H1)) → Prop)
        (index : List (Fin d → Fin (3 ^ H1)) → Cells),
      (∀ w, active w → cellLevel (index w) = H1 * w.length) →
      let bad := fun w => {omega | active w ∧ omega ∉
        gcat_good k0 lambdaLim cell epshom cdet (ZLim (index w)) (DLim (index w))
          (loLim (index w)) (hiLim (index w)) (errLim (index w)) (ratioLim (index w))}
      let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
      let badCount : (J : ℕ) → (Fin J → (Fin d → Fin (3 ^ H1))) → BilateralField d → ℕ :=
        fun J pi omega =>
          Set.ncard {i : Fin J | omega ∈ bad ((List.ofFn pi).take (i.val + 1))}
      (∀ (J : ℕ), 1 ≤ J →
        P {omega | ∃ pi : Fin J → (Fin d → Fin (3 ^ H1)),
            theta * (J : ℝ) ≤ (badCount J pi omega : ℝ)} ≤
          ENNReal.ofReal (Real.exp (-(bstar * (J : ℝ))))) ∧
      ∃ B : BilateralField d → ℝ, Measurable B ∧ (∀ omega, 0 ≤ B omega) ∧
        (∀ᵐ omega ∂P,
          ∀ (J : ℕ) (pi : Fin J → (Fin d → Fin (3 ^ H1))), 1 ≤ J →
            (badCount J pi omega : ℝ) ≤ theta * (J : ℝ) + B omega) ∧
        (∀ t : ℝ, 0 ≤ t →
          P {omega | t < B omega} ≤
            ENNReal.ofReal ((1 - Real.exp (-bstar))⁻¹ *
              Real.exp (-(bstar * t / (1 - theta))))) := by
  obtain ⟨A, hA, hchain⟩ := SubdiffusiveProcess.Section10.all_chain_estimate_of_band_witnesses d hd H1 hH1 theta bstar htheta0 htheta1 hbstar
  obtain ⟨deltaW, hdeltaW, hwit⟩ := gcat_band_witness d hd I Pc Xc W Sf Dd Cresp hCresp
    Dbase s sigma eps hs hsigma heps gH cbuf k0 hk0 lambdaLim cell epshom cdet hlam hcell
    hepshom hcdet A hA
  refine ⟨deltaW, hdeltaW, ?_⟩
  intro M hdelta Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim
    Cells _ cellLevel cellCentre phi hphi ZLim DLim loLim hiLim AELim errLim ratioLim
    hMeas hArr active index hLevel bad
  have hGood : ∀ c, MeasurableSet
      (gcat_good k0 lambdaLim cell epshom cdet (ZLim c) (DLim c) (loLim c) (hiLim c)
        (errLim c) (ratioLim c)) := by
    intro c
    exact gcat_good_measurable k0 lambdaLim cell epshom cdet _ _ _ _ _ _
      (fun U D code => ((hMeas c).1 U D code).1) (fun U D code => ((hMeas c).1 U D code).2)
      (fun U => ((hMeas c).2.1 U).1) (fun U => ((hMeas c).2.1 U).2) (hMeas c).2.2.1
      (fun a => by cases a; exact (hMeas c).2.2.2)
  have hm : ∀ w, MeasurableSet (bad w) := by
    intro w
    by_cases h : active w
    · simpa only [bad, h, true_and] using! (hGood (index w)).compl
    · simp only [bad, h, false_and, Set.setOf_false, MeasurableSet.empty]
  obtain ⟨htail, B, hBm, hB0, hBae, hBtail⟩ := hchain M bad hm (by
    intro w _hlen
    by_cases ha : active w
    · obtain ⟨hZ, hD, hlo, hhi, _hA, herr, hrat⟩ := hArr (index w)
      rw [hLevel w ha] at hZ hD hlo hhi herr hrat
      obtain ⟨Wc, hband, hprob, hcover⟩ := hwit M hdelta Rm hRm Sreg It H hH eta heta F Praw
        Rraw Draw Z rawGood hprim (H1 * w.length) (cellCentre (index w)) phi hphi
        (ZLim (index w)) (DLim (index w)) (loLim (index w)) (hiLim (index w))
        (errLim (index w)) (ratioLim (index w)) hZ hD hlo hhi herr hrat
      refine ⟨Wc, hband, hprob, ?_⟩
      filter_upwards [hcover] with omega hω hb
      exact hω hb.2
    · refine ⟨fun _ => ∅, fun _ => MeasurableSpace.measurableSet_empty _, ?_, ?_⟩
      · intro i
        simp only [measure_empty]
        exact bot_le
      · exact Filter.Eventually.of_forall fun omega hb => False.elim (ha hb.1))
  exact ⟨htail, B, hBm, hB0, hBae, hBtail⟩


end Paper
