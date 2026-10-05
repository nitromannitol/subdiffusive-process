module

public import SubdiffusiveProcess.Paper.gcat_array_pair_chain
public import SubdiffusiveProcess.Paper.thm_prop_base
public import SubdiffusiveProcess.Paper.gcat_mass_grid_prefix
@[expose] public section

open Filter MeasureTheory Set SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper
/-- The actual shared affine-good event satisfies the bad-chain count on each shifted grid root,
pulled back by the original field law to the representation space. -/
theorem gcat_mass_grid_chain
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Dd : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (Dbase : _root_.SubdiffusiveProcess.Paper.sum_errors_baseline_input d)
    (s sigma eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (heps : eps ∈ Set.Ioo (0 : ℝ) 1) (gH cbuf k0 : ℕ) (hk0 : 1 ≤ k0)
    (lambdaLim cell epshom cdet : ℝ) (hlam : 0 < lambdaLim)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1) (hepshom : 0 < epshom) (hcdet : 0 < cdet)
    (H1 : ℕ) (hH1 : 0 < H1) (theta bstar : ℝ)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) (hbstar : 0 < bstar) :
    ∃ deltaW : ℝ, 0 < deltaW ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ deltaW →
      ∀ (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d),
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
      ∀ (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
        (phi : Fin 2 → ℕ → ℕ), (∀ a, StrictMono (phi a)) →
      ∀ (ZLim DLim : Fin 2 → (ℕ × ℕ) → ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
        (loLim hiLim : Fin 2 → (ℕ × ℕ) → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
        (AELim : Fin 2 → (ℕ × ℕ) → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (errLim ratioLim : Fin 2 → (ℕ × ℕ) → Unit → BilateralField d → ℝ),
      (∀ (a : Fin 2) (c : (ℕ × ℕ)),
        (∀ U D code, Measurable (ZLim a c U D code) ∧ Measurable (DLim a c U D code)) ∧
        (∀ U, Measurable (loLim a c U) ∧ Measurable (hiLim a c U)) ∧
        Measurable (errLim a c ()) ∧ Measurable (ratioLim a c ())) →
      (∀ a, aux_affine_source_cells_env_arrays I M H s sigma gH cbuf Z Draw (phi a) (fun c : ℕ × ℕ => H1 * c.2) (fun c => z c.1)
        (ZLim a) (DLim a) (loLim a) (hiLim a) (AELim a) (errLim a) (ratioLim a)) →
      let Good : ℕ → SpatialCoordinates d → Set (BilateralField d) := fun n zc =>
        {omega | aux_thm_prop_cell_available z r zc (aux_thm_prop_mass_side H1 n) →
        ∀ a : Fin 2, omega ∈ gcat_good k0 lambdaLim cell epshom cdet
          (ZLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side H1 n)).1, n))
          (DLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side H1 n)).1, n))
          (loLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side H1 n)).1, n))
          (hiLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side H1 n)).1, n))
          (errLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side H1 n)).1, n))
          (ratioLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side H1 n)).1, n))}
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d), Measurable field →
        Measure.map field P = (chaosSampleLaw M).toMeasure →
      ∀ z0 : SpatialCoordinates d,
      ∃ B : Ω → ℝ, Measurable B ∧ (∀ omega, 0 ≤ B omega) ∧
        ∀ᵐ omega ∂P, ∀ (J : ℕ) (pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1)),
          (Nat.card {j : Fin J // field omega ∉ Good (j.val + 1)
            (descendantCenter (subdivisionHalfWidth H1) z0 1 (j.val + 1)
              (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩))} : ℝ) ≤
            theta * (J : ℝ) + B omega := by
  obtain ⟨deltaW, hdeltaW, hpair⟩ := gcat_array_pair_chain d hd I Pc Xc W Sf Dd Cresp hCresp
    Dbase s sigma eps hs hsigma heps gH cbuf k0 hk0 lambdaLim cell epshom cdet hlam hcell
    hepshom hcdet H1 hH1 theta bstar htheta0 htheta1 hbstar
  refine ⟨deltaW, hdeltaW, ?_⟩
  intro M hdelta Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim
    z r phi hphi ZLim DLim loLim hiLim AELim errLim ratioLim hMeas hArr Good
    Ω _ P field hfield hlaw z0
  classical
  have hpair' := hpair M hdelta Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood
    hprim (ℕ × ℕ) (fun c => H1 * c.2) (fun c => z c.1) phi hphi ZLim DLim loLim hiLim
    AELim errLim ratioLim hMeas hArr
  rw [← two_mul_subdivisionHalfWidth_add_one H1] at hpair'
  let ctr (w : List (OddGridIndex d (subdivisionHalfWidth H1))) :=
    descendantCenter (subdivisionHalfWidth H1) z0 1 w.length w.get
  let active (w : List (OddGridIndex d (subdivisionHalfWidth H1))) :=
    aux_thm_prop_cell_available z r (ctr w) (aux_thm_prop_mass_side H1 w.length)
  let index (w : List (OddGridIndex d (subdivisionHalfWidth H1))) : ℕ × ℕ :=
    ((aux_thm_prop_cell_index z r (ctr w) (aux_thm_prop_mass_side H1 w.length)).1, w.length)
  obtain ⟨B, hBm, hB0, hBae⟩ := hpair' active index (fun _ _ => rfl)
  have hBae' : ∀ᵐ omega ∂P,
      ∀ (J : ℕ) (pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1)), 1 ≤ J →
        (Set.ncard {i : Fin J | field omega ∉
          Good ((List.ofFn pi).take (i.val + 1)).length
            (ctr ((List.ofFn pi).take (i.val + 1)))} : ℝ) ≤
          theta * J + B (field omega) := by
    rw [← hlaw] at hBae
    exact ae_of_ae_map hfield.aemeasurable hBae
  refine ⟨B ∘ field, hBm.comp hfield, fun omega => hB0 (field omega), ?_⟩
  filter_upwards [hBae'] with omega hom J pi
  by_cases hJ : 1 ≤ J
  · have h := hom J pi hJ
    have heq (i : Fin J) :
        Good ((List.ofFn pi).take (i.val + 1)).length
          (ctr ((List.ofFn pi).take (i.val + 1))) =
        Good (i.val + 1) (descendantCenter (subdivisionHalfWidth H1) z0 1 (i.val + 1)
          (fun t : Fin (i.val + 1) => pi ⟨t.val, by omega⟩)) :=
      aux_gcat_mass_grid_chain_prefix
        (fun n w => Good n (descendantCenter (subdivisionHalfWidth H1) z0 1 n w))
        J (i.val + 1) (by omega) pi
    simpa only [heq, Nat.card_coe_set_eq, Function.comp_apply] using! h
  · have hJ0 : J = 0 := by omega
    subst J
    simpa only [Nat.card_of_isEmpty, Nat.cast_zero, mul_zero, zero_add,
      Function.comp_apply] using! hB0 (field omega)

end SubdiffusiveProcess.Paper
