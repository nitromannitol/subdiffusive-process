import SubdiffusiveProcess.Paper.gcat_array_chain
open Filter MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- The literal intersection of both candidates' good-cell tests has a simultaneous
chain-count bound, using their actual coordinate limits on the common field. -/
theorem gcat_array_pair_chain
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
        (phi : Fin 2 → ℕ → ℕ), (∀ a, StrictMono (phi a)) →
      ∀ (ZLim DLim : Fin 2 → Cells → ∀ (U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
        (loLim hiLim : Fin 2 → Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
        (AELim : Fin 2 → Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (errLim ratioLim : Fin 2 → Cells → Unit → BilateralField d → ℝ),
      (∀ (a : Fin 2) (c : Cells),
        (∀ U D code, Measurable (ZLim a c U D code) ∧ Measurable (DLim a c U D code)) ∧
        (∀ U, Measurable (loLim a c U) ∧ Measurable (hiLim a c U)) ∧
        Measurable (errLim a c ()) ∧ Measurable (ratioLim a c ())) →
      (∀ a, aux_affine_source_cells_env_arrays I M H s sigma gH cbuf Z Draw (phi a) cellLevel cellCentre
        (ZLim a) (DLim a) (loLim a) (hiLim a) (AELim a) (errLim a) (ratioLim a)) →
      ∀ (active : List (Fin d → Fin (3 ^ H1)) → Prop)
        (index : List (Fin d → Fin (3 ^ H1)) → Cells),
      (∀ w, active w → cellLevel (index w) = H1 * w.length) →
      let Good := fun w => {omega | active w → ∀ a : Fin 2, omega ∈
        gcat_good k0 lambdaLim cell epshom cdet (ZLim a (index w)) (DLim a (index w))
          (loLim a (index w)) (hiLim a (index w)) (errLim a (index w)) (ratioLim a (index w))}
      ∃ B : BilateralField d → ℝ, Measurable B ∧ (∀ omega, 0 ≤ B omega) ∧
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (J : ℕ) (pi : Fin J → (Fin d → Fin (3 ^ H1))), 1 ≤ J →
            (Set.ncard {i : Fin J | omega ∉ Good ((List.ofFn pi).take (i.val + 1))} : ℝ) ≤
              theta * (J : ℝ) + B omega := by
  obtain ⟨deltaW, hdeltaW, hside⟩ := gcat_array_chain d hd I Pc Xc W Sf Dd Cresp hCresp
    Dbase s sigma eps hs hsigma heps gH cbuf k0 hk0 lambdaLim cell epshom cdet hlam hcell
    hepshom hcdet H1 hH1 (theta / 2) bstar (by positivity) (by linarith) hbstar
  refine ⟨deltaW, hdeltaW, ?_⟩
  intro M hdelta Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim
    Cells _ cellLevel cellCentre phi hphi ZLim DLim loLim hiLim AELim errLim ratioLim
    hMeas hArr active index hLevel Good
  classical
  let bad (a : Fin 2) (w : List (Fin d → Fin (3 ^ H1))) := {omega | active w ∧ omega ∉
    gcat_good k0 lambdaLim cell epshom cdet (ZLim a (index w)) (DLim a (index w))
      (loLim a (index w)) (hiLim a (index w)) (errLim a (index w)) (ratioLim a (index w))}
  have side (a : Fin 2) := hside M hdelta Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z
    rawGood hprim Cells cellLevel cellCentre (phi a) (hphi a) (ZLim a) (DLim a) (loLim a)
    (hiLim a) (AELim a) (errLim a) (ratioLim a) (hMeas a) (hArr a) active index hLevel
  obtain ⟨B0, hm0, hn0, he0⟩ := side 0
  obtain ⟨B1, hm1, hn1, he1⟩ := side 1
  refine ⟨fun omega => B0 omega + B1 omega, hm0.add hm1,
    fun omega => add_nonneg (hn0 omega) (hn1 omega), ?_⟩
  filter_upwards [he0, he1] with omega h0 h1 J pi hJ
  have heq : {i : Fin J | omega ∉ Good ((List.ofFn pi).take (i.val + 1))} =
      {i : Fin J | omega ∈ bad 0 ((List.ofFn pi).take (i.val + 1))} ∪
      {i : Fin J | omega ∈ bad 1 ((List.ofFn pi).take (i.val + 1))} := by
    ext i
    simp only [Good, bad, Set.mem_setOf_eq, Set.mem_union, Fin.forall_fin_two]
    tauto
  rw [heq]
  have hcard : (Set.ncard ({i : Fin J | omega ∈ bad 0 ((List.ofFn pi).take (i.val + 1))} ∪
      {i : Fin J | omega ∈ bad 1 ((List.ofFn pi).take (i.val + 1))}) : ℝ) ≤
      (Set.ncard {i : Fin J | omega ∈ bad 0 ((List.ofFn pi).take (i.val + 1))} : ℝ) +
      (Set.ncard {i : Fin J | omega ∈ bad 1 ((List.ofFn pi).take (i.val + 1))} : ℝ) := by
    exact_mod_cast Set.ncard_union_le _ _
  have h0' := h0 J pi hJ
  have h1' := h1 J pi hJ
  change (Set.ncard {i : Fin J | omega ∈ bad 0 ((List.ofFn pi).take (i.val + 1))} : ℝ) ≤
    theta / 2 * J + B0 omega at h0'
  change (Set.ncard {i : Fin J | omega ∈ bad 1 ((List.ofFn pi).take (i.val + 1))} : ℝ) ≤
    theta / 2 * J + B1 omega at h1'
  linarith only [hcard, h0', h1']

end Paper
