module

public import SubdiffusiveProcess.EllipticRegularity.GoodCellCatalogue
public import SubdiffusiveProcess.Paper.lem_prefix_limit

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal BigOperators Topology

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ}

/-! ## Root catalogue equivalence: `Fin T ≃ (Fin 3 × (Fin d → Fin 3)) ⊕ Unit` -/

/-- Number of catalogue root entries: `3 * 3^d` roots plus the comparison cube. -/
def aux_gcat_prefix_limits_T (d : ℕ) : ℕ :=
  Fintype.card ((Fin 3 × (Fin d → Fin 3)) ⊕ Unit)

/-- The catalogue equivalence between root labels and `Fin T`. -/
def aux_gcat_prefix_limits_equiv (d : ℕ) :
    (Fin 3 × (Fin d → Fin 3)) ⊕ Unit ≃ Fin (aux_gcat_prefix_limits_T d) :=
  Fintype.equivFin _

/-- The `T`-array offsets `lem_prefix_limit` needs: root `(e,t)` sits `factor gH e` levels
above the cell, the comparison cube sits `gH` levels above. -/
def aux_gcat_prefix_limits_offset (d gH : ℕ) : Fin (aux_gcat_prefix_limits_T d) → ℤ :=
  fun i => Sum.elim (fun et => -(gcat_factor gH et.1 : ℤ)) (fun _ => -(gH : ℤ))
    ((aux_gcat_prefix_limits_equiv d).symm i)

/-- The `T`-array shifts `lem_prefix_limit` needs: root `(e,t)` shifts by `3^(factor gH e)`
times the label shift, the comparison cube does not shift. -/
def aux_gcat_prefix_limits_shift (d gH : ℕ) :
    Fin (aux_gcat_prefix_limits_T d) → SpatialCoordinates d :=
  fun i => Sum.elim (fun et => (3 : ℝ) ^ (gcat_factor gH et.1) • gcat_shift et.2) (fun _ => 0)
    ((aux_gcat_prefix_limits_equiv d).symm i)

lemma aux_gcat_prefix_limits_offset_root (d gH : ℕ) (U : Fin 3 × (Fin d → Fin 3)) :
    aux_gcat_prefix_limits_offset d gH ((aux_gcat_prefix_limits_equiv d) (Sum.inl U)) =
      -(gcat_factor gH U.1 : ℤ) := by
  simp only [aux_gcat_prefix_limits_offset, Equiv.symm_apply_apply, Sum.elim_inl]

lemma aux_gcat_prefix_limits_shift_root (d gH : ℕ) (U : Fin 3 × (Fin d → Fin 3)) :
    aux_gcat_prefix_limits_shift d gH ((aux_gcat_prefix_limits_equiv d) (Sum.inl U)) =
      (3 : ℝ) ^ (gcat_factor gH U.1) • gcat_shift U.2 := by
  simp only [aux_gcat_prefix_limits_shift, Equiv.symm_apply_apply, Sum.elim_inl]

lemma aux_gcat_prefix_limits_offset_cmp (d gH : ℕ) :
    aux_gcat_prefix_limits_offset d gH ((aux_gcat_prefix_limits_equiv d) (Sum.inr ())) =
      -(gH : ℤ) := by
  simp only [aux_gcat_prefix_limits_offset, Equiv.symm_apply_apply, Sum.elim_inr]

lemma aux_gcat_prefix_limits_shift_cmp (d gH : ℕ) :
    aux_gcat_prefix_limits_shift d gH ((aux_gcat_prefix_limits_equiv d) (Sum.inr ())) =
      (0 : SpatialCoordinates d) := by
  simp only [aux_gcat_prefix_limits_shift, Equiv.symm_apply_apply, Sum.elim_inr]

/-! ## Matching the shifted root data with the catalogue root data at `n = k` -/

lemma aux_gcat_prefix_limits_root_level_eq (gH k : ℕ) (U : Fin 3 × (Fin d → Fin 3)) :
    (k : ℤ) + aux_gcat_prefix_limits_offset d gH ((aux_gcat_prefix_limits_equiv d) (Sum.inl U)) =
      gcat_rootLevel gH k U := by
  rw [aux_gcat_prefix_limits_offset_root, gcat_rootLevel]; ring

lemma aux_gcat_prefix_limits_root_side_eq (gH k : ℕ) (U : Fin 3 × (Fin d → Fin 3)) :
    (3 : ℝ) ^ (-((k : ℤ) + aux_gcat_prefix_limits_offset d gH
      ((aux_gcat_prefix_limits_equiv d) (Sum.inl U)))) = gcat_rootSide gH k U := by
  rw [aux_gcat_prefix_limits_root_level_eq, gcat_rootSide]

lemma aux_gcat_prefix_limits_root_centre_eq (gH k : ℕ) (z : SpatialCoordinates d)
    (U : Fin 3 × (Fin d → Fin 3)) :
    z + (3 : ℝ) ^ (-(k : ℤ)) •
        aux_gcat_prefix_limits_shift d gH ((aux_gcat_prefix_limits_equiv d) (Sum.inl U)) =
      gcat_rootCentre gH k z U := by
  rw [aux_gcat_prefix_limits_shift_root, gcat_rootCentre, ← aux_gcat_prefix_limits_root_side_eq,
    aux_gcat_prefix_limits_root_level_eq, smul_smul]
  congr 2
  rw [← zpow_natCast (3 : ℝ) (gcat_factor gH U.1), ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  congr 1
  rw [gcat_rootLevel]
  ring

lemma aux_gcat_prefix_limits_cmp_level_eq (gH k : ℕ) :
    (k : ℤ) + aux_gcat_prefix_limits_offset d gH ((aux_gcat_prefix_limits_equiv d) (Sum.inr ())) =
      (k : ℤ) - (gH : ℤ) := by
  rw [aux_gcat_prefix_limits_offset_cmp]; ring

lemma aux_gcat_prefix_limits_cmp_centre_eq (gH k : ℕ) (z : SpatialCoordinates d) :
    z + (3 : ℝ) ^ (-(k : ℤ)) •
        aux_gcat_prefix_limits_shift d gH ((aux_gcat_prefix_limits_equiv d) (Sum.inr ())) = z := by
  rw [aux_gcat_prefix_limits_shift_cmp, smul_zero, add_zero]

/-- `gcat_sN` unfolded to its raw `kappa`/`retained` formula, once the level is in range
(matches `lem_prefix_limit`'s local `reference` verbatim: both are the same construction). -/
lemma aux_gcat_prefix_limits_gcat_sN_unfold [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (l : ℤ) (w : SpatialCoordinates d) (omega : BilateralField d) (hle : l ≤ (N : ℤ)) :
    gcat_sN M H N l w omega =
      (fun J : ℕ => Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M J) ((N : ℤ) - l).toNat /
      (fun J : ℕ => Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M J) N *
      Real.exp (H omega w +
        (fun (ell : ℤ) (v : SpatialCoordinates d) (beta : BilateralField d) =>
          if 0 ≤ ell then ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
           else -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v) l w omega) := by
  simp only [gcat_sN, ite_eq_left hle]

/-! ## Generic measure-in-measure transfer: Lp convergence plus eventual equality to a limit. -/

lemma aux_gcat_prefix_limits_transfer {M : _root_.SubdiffusiveProcess.Model.GMCModel d}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {f : ℕ → BilateralField d → ℝ} {g : BilateralField d → ℝ} {p : ℝ≥0∞} (hp : p ≠ 0)
    (hLp : Tendsto (fun n => eLpNorm (f n - g) p (chaosSampleLaw M).toMeasure) atTop (𝓝 0))
    (_hf : ∀ n, AEStronglyMeasurable (f n) (chaosSampleLaw M).toMeasure)
    (hg : AEStronglyMeasurable g (chaosSampleLaw M).toMeasure)
    (f' : ℕ → BilateralField d → ℝ) (hEq : ∀ᶠ n in (atTop : Filter ℕ), f n = f' n) :
    ∃ g' : BilateralField d → ℝ, Measurable g' ∧
      TendstoInMeasure (chaosSampleLaw M).toMeasure f' atTop g' := by
  refine ⟨hg.mk g, hg.measurable_mk, ?_⟩
  have hbase : TendstoInMeasure (chaosSampleLaw M).toMeasure f atTop g :=
    tendstoInMeasure_of_tendsto_eLpNorm hp hLp
  have hEq' : ∀ᶠ n in (atTop : Filter ℕ), f n =ᵐ[(chaosSampleLaw M).toMeasure] f' n :=
    hEq.mono (fun n h => by rw [h])
  exact TendstoInMeasure.congr' hEq' hg.ae_eq_mk hbase

lemma aux_gcat_prefix_limits_eventually_ge (phi0 psi : ℕ → ℕ) (hphi0 : StrictMono phi0)
    (hpsi : StrictMono psi) (Nthr : ℕ) :
    ∀ᶠ n in (atTop : Filter ℕ), Nthr ≤ phi0 (psi n) := by
  have h1 : Tendsto (fun n => phi0 (psi n)) atTop atTop :=
    hphi0.tendsto_atTop.comp hpsi.tendsto_atTop
  exact (tendsto_atTop.mp h1) Nthr

/-! ## The joint countable position index for `lem_prefix_limit`'s subsequence extraction -/

/-- Either a cell (for the direct root/comparison tests, used at `j = 0`) or a cell together
with a prefix-sum descriptor `(U, D, code)` (for the `Z`/`D.toReal` finite prefixes). -/
abbrev aux_gcat_prefix_limits_Pos (d : ℕ) (Cells : Type) : Type :=
  Cells ⊕ (Cells × (Fin 3 × (Fin d → Fin 3)) ×
    Σ D : ℕ, (Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3)))

instance aux_gcat_prefix_limits_Pos_countable (d : ℕ) (Cells : Type) [Countable Cells] :
    Countable (aux_gcat_prefix_limits_Pos d Cells) := by
  infer_instance

/-- `level pos`: the cell's own level for a direct position, `0` for a prefix position
(so `level pos + j = j` ranges exactly over the prefix window). -/
def aux_gcat_prefix_limits_level (d : ℕ) {Cells : Type} (cellLevel : Cells → ℕ) :
    aux_gcat_prefix_limits_Pos d Cells → ℤ :=
  fun p => match p with
    | Sum.inl c => (cellLevel c : ℤ)
    | Sum.inr _ => 0

/-- `centre pos`: the cell's own centre for a direct position, the observation centre
`gcat_obsCentre` for a prefix position. -/
def aux_gcat_prefix_limits_centre (d gH : ℕ) {Cells : Type} (cellLevel : Cells → ℕ)
    (cellCentre : Cells → SpatialCoordinates d) :
    aux_gcat_prefix_limits_Pos d Cells → SpatialCoordinates d :=
  fun p => match p with
    | Sum.inl c => cellCentre c
    | Sum.inr (c, U, ⟨D, code⟩) => gcat_obsCentre gH (cellLevel c) (cellCentre c) U D code

/-- A2: along a subsequence of any given cutoff sequence, every finite array of the concrete
good-cell catalogue converges in measure, for every cell of a countable family at once. -/
theorem gcat_prefix_limits
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Dd : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp)
    (s sigma eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (heps : eps ∈ Set.Ioo (0 : ℝ) 1) (gH cbuf : ℕ) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
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
      ∀ (Cells : Type) [Countable Cells] (cellLevel : Cells → ℕ)
        (cellCentre : Cells → SpatialCoordinates d) (phi0 : ℕ → ℕ), StrictMono phi0 →
      ∃ psi : ℕ → ℕ, StrictMono psi ∧
      ∃ (ZLim DLim : Cells → ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
            ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
        (loLim hiLim : Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
        (AELim : Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (errLim ratioLim : Cells → Unit → BilateralField d → ℝ),
      ∀ c : Cells,
        let k := cellLevel c
        let z := cellCentre c
        let phi : ℕ → ℕ := fun n => phi0 (psi n)
        (∀ U D code, Measurable (ZLim c U D code) ∧ Measurable (DLim c U D code)) ∧
        (∀ U, Measurable (loLim c U) ∧ Measurable (hiLim c U) ∧
          ∀ i j, Measurable (fun omega => AELim c U omega i j)) ∧
        Measurable (errLim c ()) ∧ Measurable (ratioLim c ()) ∧
        (∀ U D code, TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega => gcat_prefix gH cbuf k z Z (phi n) U D code omega) atTop
          (ZLim c U D code)) ∧
        (∀ U D code, TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega => gcat_prefix gH cbuf k z (fun N m w om => (Draw N m w om).toReal)
            (phi n) U D code omega) atTop (DLim c U D code)) ∧
        (∀ U, TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega =>
            I.lam (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi n) (gcat_rootCentre gH k z U)
                (zpow_pos (by norm_num) _))
              (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) sigma 2 /
            gcat_sN M H (phi n) (gcat_rootLevel gH k U) (gcat_rootCentre gH k z U) omega)
          atTop (loLim c U)) ∧
        (∀ U, TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega =>
            I.Lam (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi n) (gcat_rootCentre gH k z U)
                (zpow_pos (by norm_num) _))
              (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) sigma 2 /
            gcat_sN M H (phi n) (gcat_rootLevel gH k U) (gcat_rootCentre gH k z U) omega)
          atTop (hiLim c U)) ∧
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
          atTop (fun omega => AELim c U omega i j)) ∧
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega =>
            I.err z ((3 : ℝ) ^ (-((k : ℤ) - (gH : ℤ)))) (zpow_pos (by norm_num) _)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi n) z (zpow_pos (by norm_num) _))
              z ((3 : ℝ) ^ (-((k : ℤ) - (gH : ℤ))))
              (gcat_sN M H (phi n) ((k : ℤ) - (gH : ℤ)) z omega) s 2)
          atTop (errLim c ()) ∧
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega => gcat_sN M H (phi n) (k : ℤ) z omega /
            gcat_sN M H (phi n) ((k : ℤ) - (gH : ℤ)) z omega)
          atTop (ratioLim c ()) := by
  obtain ⟨q, delta0, K, hq1, hq2, hq3, hdelta0, hK, hM⟩ :=
    _root_.SubdiffusiveProcess.Paper.lem_prefix_limit d hd I Pc Xc W Sf Dd Cresp hCresp s sigma eps hs hsigma heps
      (aux_gcat_prefix_limits_T d) (aux_gcat_prefix_limits_offset d gH)
      (aux_gcat_prefix_limits_shift d gH) ({1} : Finset ℝ)
      (fun p hp => le_of_eq (Finset.mem_singleton.mp hp).symm)
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hMdelta Rm hRmC Sreg _It H hH eta heta F Praw Rraw Draw Z rawGood hprim
  have hInner := hM M hMdelta Rm hRmC Sreg _It H hH eta heta F Praw Rraw Draw Z rawGood hprim
    (fun n => zpow_pos (by norm_num : (0 : ℝ) < 3) (-n))
  obtain ⟨hRefPos, h12q, hPosAll⟩ := hInner
  intro Cells _ cellLevel cellCentre phi0 hphi0
  obtain ⟨psi, hpsi, Vlim, hVlimMeas, hVlimMoment, hvalueMoment, hLpConv, hPrefix⟩ :=
    hPosAll (aux_gcat_prefix_limits_Pos d Cells) (aux_gcat_prefix_limits_level d cellLevel)
      (aux_gcat_prefix_limits_centre d gH cellLevel cellCentre) phi0 hphi0
  refine ⟨psi, hpsi, ?_⟩
  have hZfamily : ∀ (c : Cells) (U : Fin 3 × (Fin d → Fin 3)) (D : ℕ)
      (code : (Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))),
      ∃ Lim : BilateralField d → ℝ, Measurable Lim ∧
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega =>
            gcat_prefix gH cbuf (cellLevel c) (cellCentre c) Z (phi0 (psi n)) U D code omega)
          atTop Lim := by
    intro c U D code
    set pos : aux_gcat_prefix_limits_Pos d Cells := Sum.inr (c, U, ⟨D, code⟩) with hposdef
    obtain ⟨hAESMlim, hMomentTendsto, -⟩ :=
      hPrefix pos (gcat_rootLevel gH (cellLevel c) U) D cbuf (Sum.inl (4 : Fin 5))
    obtain ⟨-, hTendsto⟩ := hMomentTendsto 1 (Finset.mem_insert_self _ _)
    refine aux_gcat_prefix_limits_transfer (by norm_num) hTendsto ?_ hAESMlim _ ?_
    · intro n
      have hsum := Finset.aestronglyMeasurable_sum
        (Finset.Icc (gcat_rootLevel gH (cellLevel c) U - (cbuf : ℤ))
          (gcat_rootLevel gH (cellLevel c) U + (D : ℤ)))
        (fun jj _ => MemLp.aestronglyMeasurable
          (hvalueMoment 1 (Finset.mem_insert_self _ _) (phi0 (psi n)) pos jj (Sum.inl 4)).1)
      rwa [Finset.sum_fn] at hsum
    filter_upwards [aux_gcat_prefix_limits_eventually_ge phi0 psi hphi0 hpsi
      (gcat_rootLevel gH (cellLevel c) U + (D : ℤ)).toNat] with n hn
    have hNge : gcat_rootLevel gH (cellLevel c) U + (D : ℤ) ≤ (phi0 (psi n) : ℤ) :=
      le_trans (Int.self_le_toNat _) (by exact_mod_cast hn)
    funext omega
    simp only [hposdef, aux_gcat_prefix_limits_level, aux_gcat_prefix_limits_centre, zero_add]
    rw [gcat_prefix, ite_eq_left hNge]
    apply Finset.sum_congr rfl
    intro jj hjj
    have hjjle : jj ≤ (phi0 (psi n) : ℤ) := by
      have h2 := (Finset.mem_Icc.mp hjj).2
      omega
    show (if jj ≤ (phi0 (psi n) : ℤ) then
        Z (phi0 (psi n)) (((phi0 (psi n) : ℤ) - jj).toNat)
          ((3 : ℝ) ^ (phi0 (psi n)) •
            gcat_obsCentre gH (cellLevel c) (cellCentre c) U D code) omega
      else 0) =
      (if (0 : ℤ) ≤ (phi0 (psi n) : ℤ) - jj then
        Z (phi0 (psi n)) (((phi0 (psi n) : ℤ) - jj).toNat)
          ((3 : ℝ) ^ (phi0 (psi n)) •
            gcat_obsCentre gH (cellLevel c) (cellCentre c) U D code) omega
      else 0)
    rw [ite_eq_left hjjle, ite_eq_left (by omega : (0 : ℤ) ≤ (phi0 (psi n) : ℤ) - jj)]
  choose ZLim hZmeas hZtendsto using hZfamily
  have hDfamily : ∀ (c : Cells) (U : Fin 3 × (Fin d → Fin 3)) (D : ℕ)
      (code : (Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))),
      ∃ Lim : BilateralField d → ℝ, Measurable Lim ∧
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega =>
            gcat_prefix gH cbuf (cellLevel c) (cellCentre c)
              (fun N m w om => (Draw N m w om).toReal) (phi0 (psi n)) U D code omega)
          atTop Lim := by
    intro c U D code
    set pos : aux_gcat_prefix_limits_Pos d Cells := Sum.inr (c, U, ⟨D, code⟩) with hposdef
    obtain ⟨hAESMlim, hMomentTendsto, -⟩ :=
      hPrefix pos (gcat_rootLevel gH (cellLevel c) U) D cbuf (Sum.inl (3 : Fin 5))
    obtain ⟨-, hTendsto⟩ := hMomentTendsto 1 (Finset.mem_insert_self _ _)
    refine aux_gcat_prefix_limits_transfer (by norm_num) hTendsto ?_ hAESMlim _ ?_
    · intro n
      have hsum := Finset.aestronglyMeasurable_sum
        (Finset.Icc (gcat_rootLevel gH (cellLevel c) U - (cbuf : ℤ))
          (gcat_rootLevel gH (cellLevel c) U + (D : ℤ)))
        (fun jj _ => MemLp.aestronglyMeasurable
          (hvalueMoment 1 (Finset.mem_insert_self _ _) (phi0 (psi n)) pos jj (Sum.inl 3)).1)
      rwa [Finset.sum_fn] at hsum
    filter_upwards [aux_gcat_prefix_limits_eventually_ge phi0 psi hphi0 hpsi
      (gcat_rootLevel gH (cellLevel c) U + (D : ℤ)).toNat] with n hn
    have hNge : gcat_rootLevel gH (cellLevel c) U + (D : ℤ) ≤ (phi0 (psi n) : ℤ) :=
      le_trans (Int.self_le_toNat _) (by exact_mod_cast hn)
    funext omega
    simp only [hposdef, aux_gcat_prefix_limits_level, aux_gcat_prefix_limits_centre, zero_add]
    rw [gcat_prefix, ite_eq_left hNge]
    apply Finset.sum_congr rfl
    intro jj hjj
    have hjjle : jj ≤ (phi0 (psi n) : ℤ) := by
      have h2 := (Finset.mem_Icc.mp hjj).2
      omega
    show (if jj ≤ (phi0 (psi n) : ℤ) then
        (Draw (phi0 (psi n)) (((phi0 (psi n) : ℤ) - jj).toNat)
          ((3 : ℝ) ^ (phi0 (psi n)) •
            gcat_obsCentre gH (cellLevel c) (cellCentre c) U D code) omega).toReal
      else 0) =
      (if (0 : ℤ) ≤ (phi0 (psi n) : ℤ) - jj then
        (Draw (phi0 (psi n)) (((phi0 (psi n) : ℤ) - jj).toNat)
          ((3 : ℝ) ^ (phi0 (psi n)) •
            gcat_obsCentre gH (cellLevel c) (cellCentre c) U D code) omega).toReal
      else 0)
    rw [ite_eq_left hjjle, ite_eq_left (by omega : (0 : ℤ) ≤ (phi0 (psi n) : ℤ) - jj)]
  choose DLim hDmeas hDtendsto using hDfamily
  have hLoFamily : ∀ (c : Cells) (U : Fin 3 × (Fin d → Fin 3)),
      ∃ Lim : BilateralField d → ℝ, Measurable Lim ∧
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega =>
            I.lam (gcat_rootCentre gH (cellLevel c) (cellCentre c) U)
              (gcat_rootSide gH (cellLevel c) U) (zpow_pos (by norm_num) _)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi0 (psi n))
                (gcat_rootCentre gH (cellLevel c) (cellCentre c) U) (zpow_pos (by norm_num) _))
              (gcat_rootCentre gH (cellLevel c) (cellCentre c) U)
              (gcat_rootSide gH (cellLevel c) U) sigma 2 /
            gcat_sN M H (phi0 (psi n)) (gcat_rootLevel gH (cellLevel c) U)
              (gcat_rootCentre gH (cellLevel c) (cellCentre c) U) omega)
          atTop Lim := by
    intro c U
    set pos : aux_gcat_prefix_limits_Pos d Cells := Sum.inl c with hposdef
    set iT : Fin (aux_gcat_prefix_limits_T d) := (aux_gcat_prefix_limits_equiv d) (Sum.inl U)
      with hiTdef
    refine aux_gcat_prefix_limits_transfer (by norm_num)
      (hLpConv 1 (Finset.mem_insert_self _ _) pos 0 (Sum.inr (iT, Sum.inl 0)))
      (fun n => MemLp.aestronglyMeasurable
        (hvalueMoment 1 (Finset.mem_insert_self _ _) (phi0 (psi n)) pos 0
          (Sum.inr (iT, Sum.inl 0))).1)
      (hVlimMeas pos 0 (Sum.inr (iT, Sum.inl 0))) _ ?_
    have hlevel : (cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT =
        gcat_rootLevel gH (cellLevel c) U := by
      simp only [hiTdef]; exact aux_gcat_prefix_limits_root_level_eq gH (cellLevel c) U
    have hcentre : cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) •
        aux_gcat_prefix_limits_shift d gH iT = gcat_rootCentre gH (cellLevel c) (cellCentre c) U := by
      simp only [hiTdef]; exact aux_gcat_prefix_limits_root_centre_eq gH (cellLevel c) (cellCentre c) U
    filter_upwards [aux_gcat_prefix_limits_eventually_ge phi0 psi hphi0 hpsi
      (max (cellLevel c) (gcat_rootLevel gH (cellLevel c) U).toNat)] with n hn
    have hk_le : (cellLevel c : ℤ) ≤ (phi0 (psi n) : ℤ) := by
      have h1 := le_trans (le_max_left (cellLevel c) (gcat_rootLevel gH (cellLevel c) U).toNat) hn
      exact_mod_cast h1
    have hm_le : gcat_rootLevel gH (cellLevel c) U ≤ (phi0 (psi n) : ℤ) := by
      have h1 := le_trans (le_max_right (cellLevel c) (gcat_rootLevel gH (cellLevel c) U).toNat) hn
      calc gcat_rootLevel gH (cellLevel c) U
          ≤ ((gcat_rootLevel gH (cellLevel c) U).toNat : ℤ) := Int.self_le_toNat _
        _ ≤ (phi0 (psi n) : ℤ) := by exact_mod_cast h1
    funext omega
    show (if (cellLevel c : ℤ) ≤ (phi0 (psi n) : ℤ) ∧
        (cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT ≤ (phi0 (psi n) : ℤ) then
        I.lam (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) • aux_gcat_prefix_limits_shift d gH iT)
          ((3 : ℝ) ^ (-((cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT)))
          (zpow_pos (by norm_num) _)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi0 (psi n))
            (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) • aux_gcat_prefix_limits_shift d gH iT)
            (zpow_pos (by norm_num) _))
          (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) • aux_gcat_prefix_limits_shift d gH iT)
          ((3 : ℝ) ^ (-((cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT))) sigma 2 /
        ((fun J : ℕ => Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M J)
            (((phi0 (psi n) : ℤ) - ((cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT)).toNat) /
          (fun J : ℕ => Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M J) (phi0 (psi n)) *
          Real.exp (H omega
              (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) • aux_gcat_prefix_limits_shift d gH iT) +
            (fun (ell : ℤ) (v : SpatialCoordinates d) (beta : BilateralField d) =>
              if 0 ≤ ell then ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
               else -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v)
              ((cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT)
              (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) • aux_gcat_prefix_limits_shift d gH iT)
              omega))
      else 0) =
      I.lam (gcat_rootCentre gH (cellLevel c) (cellCentre c) U)
        (gcat_rootSide gH (cellLevel c) U) (zpow_pos (by norm_num) _)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi0 (psi n))
          (gcat_rootCentre gH (cellLevel c) (cellCentre c) U) (zpow_pos (by norm_num) _))
        (gcat_rootCentre gH (cellLevel c) (cellCentre c) U)
        (gcat_rootSide gH (cellLevel c) U) sigma 2 /
      gcat_sN M H (phi0 (psi n)) (gcat_rootLevel gH (cellLevel c) U)
        (gcat_rootCentre gH (cellLevel c) (cellCentre c) U) omega
    have hm_le' : (cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT ≤ (phi0 (psi n) : ℤ) := by
      rw [hlevel]; exact hm_le
    rw [ite_eq_left ⟨hk_le, hm_le'⟩, hlevel, hcentre,
      aux_gcat_prefix_limits_gcat_sN_unfold M H (phi0 (psi n)) (gcat_rootLevel gH (cellLevel c) U)
        (gcat_rootCentre gH (cellLevel c) (cellCentre c) U) omega hm_le]
    simp only [gcat_rootSide]
  choose loLim hLoMeas hLoTendsto using hLoFamily
  have hHiFamily : ∀ (c : Cells) (U : Fin 3 × (Fin d → Fin 3)),
      ∃ Lim : BilateralField d → ℝ, Measurable Lim ∧
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega =>
            I.Lam (gcat_rootCentre gH (cellLevel c) (cellCentre c) U)
              (gcat_rootSide gH (cellLevel c) U) (zpow_pos (by norm_num) _)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi0 (psi n))
                (gcat_rootCentre gH (cellLevel c) (cellCentre c) U) (zpow_pos (by norm_num) _))
              (gcat_rootCentre gH (cellLevel c) (cellCentre c) U)
              (gcat_rootSide gH (cellLevel c) U) sigma 2 /
            gcat_sN M H (phi0 (psi n)) (gcat_rootLevel gH (cellLevel c) U)
              (gcat_rootCentre gH (cellLevel c) (cellCentre c) U) omega)
          atTop Lim := by
    intro c U
    set pos : aux_gcat_prefix_limits_Pos d Cells := Sum.inl c with hposdef
    set iT : Fin (aux_gcat_prefix_limits_T d) := (aux_gcat_prefix_limits_equiv d) (Sum.inl U)
      with hiTdef
    refine aux_gcat_prefix_limits_transfer (by norm_num)
      (hLpConv 1 (Finset.mem_insert_self _ _) pos 0 (Sum.inr (iT, Sum.inl 1)))
      (fun n => MemLp.aestronglyMeasurable
        (hvalueMoment 1 (Finset.mem_insert_self _ _) (phi0 (psi n)) pos 0
          (Sum.inr (iT, Sum.inl 1))).1)
      (hVlimMeas pos 0 (Sum.inr (iT, Sum.inl 1))) _ ?_
    have hlevel : (cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT =
        gcat_rootLevel gH (cellLevel c) U := by
      simp only [hiTdef]; exact aux_gcat_prefix_limits_root_level_eq gH (cellLevel c) U
    have hcentre : cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) •
        aux_gcat_prefix_limits_shift d gH iT = gcat_rootCentre gH (cellLevel c) (cellCentre c) U := by
      simp only [hiTdef]; exact aux_gcat_prefix_limits_root_centre_eq gH (cellLevel c) (cellCentre c) U
    filter_upwards [aux_gcat_prefix_limits_eventually_ge phi0 psi hphi0 hpsi
      (max (cellLevel c) (gcat_rootLevel gH (cellLevel c) U).toNat)] with n hn
    have hk_le : (cellLevel c : ℤ) ≤ (phi0 (psi n) : ℤ) := by
      have h1 := le_trans (le_max_left (cellLevel c) (gcat_rootLevel gH (cellLevel c) U).toNat) hn
      exact_mod_cast h1
    have hm_le : gcat_rootLevel gH (cellLevel c) U ≤ (phi0 (psi n) : ℤ) := by
      have h1 := le_trans (le_max_right (cellLevel c) (gcat_rootLevel gH (cellLevel c) U).toNat) hn
      calc gcat_rootLevel gH (cellLevel c) U
          ≤ ((gcat_rootLevel gH (cellLevel c) U).toNat : ℤ) := Int.self_le_toNat _
        _ ≤ (phi0 (psi n) : ℤ) := by exact_mod_cast h1
    funext omega
    show (if (cellLevel c : ℤ) ≤ (phi0 (psi n) : ℤ) ∧
        (cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT ≤ (phi0 (psi n) : ℤ) then
        I.Lam (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) • aux_gcat_prefix_limits_shift d gH iT)
          ((3 : ℝ) ^ (-((cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT)))
          (zpow_pos (by norm_num) _)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi0 (psi n))
            (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) • aux_gcat_prefix_limits_shift d gH iT)
            (zpow_pos (by norm_num) _))
          (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) • aux_gcat_prefix_limits_shift d gH iT)
          ((3 : ℝ) ^ (-((cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT))) sigma 2 /
        ((fun J : ℕ => Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M J)
            (((phi0 (psi n) : ℤ) - ((cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT)).toNat) /
          (fun J : ℕ => Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M J) (phi0 (psi n)) *
          Real.exp (H omega
              (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) • aux_gcat_prefix_limits_shift d gH iT) +
            (fun (ell : ℤ) (v : SpatialCoordinates d) (beta : BilateralField d) =>
              if 0 ≤ ell then ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
               else -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v)
              ((cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT)
              (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) • aux_gcat_prefix_limits_shift d gH iT)
              omega))
      else 0) =
      I.Lam (gcat_rootCentre gH (cellLevel c) (cellCentre c) U)
        (gcat_rootSide gH (cellLevel c) U) (zpow_pos (by norm_num) _)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi0 (psi n))
          (gcat_rootCentre gH (cellLevel c) (cellCentre c) U) (zpow_pos (by norm_num) _))
        (gcat_rootCentre gH (cellLevel c) (cellCentre c) U)
        (gcat_rootSide gH (cellLevel c) U) sigma 2 /
      gcat_sN M H (phi0 (psi n)) (gcat_rootLevel gH (cellLevel c) U)
        (gcat_rootCentre gH (cellLevel c) (cellCentre c) U) omega
    have hm_le' : (cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT ≤ (phi0 (psi n) : ℤ) := by
      rw [hlevel]; exact hm_le
    rw [ite_eq_left ⟨hk_le, hm_le'⟩, hlevel, hcentre,
      aux_gcat_prefix_limits_gcat_sN_unfold M H (phi0 (psi n)) (gcat_rootLevel gH (cellLevel c) U)
        (gcat_rootCentre gH (cellLevel c) (cellCentre c) U) omega hm_le]
    simp only [gcat_rootSide]
  choose hiLim hHiMeas hHiTendsto using hHiFamily
  have hErrFamily : ∀ (c : Cells),
      ∃ Lim : BilateralField d → ℝ, Measurable Lim ∧
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega =>
            I.err (cellCentre c) ((3 : ℝ) ^ (-((cellLevel c : ℤ) - (gH : ℤ))))
              (zpow_pos (by norm_num) _)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi0 (psi n)) (cellCentre c)
                (zpow_pos (by norm_num) _))
              (cellCentre c) ((3 : ℝ) ^ (-((cellLevel c : ℤ) - (gH : ℤ))))
              (gcat_sN M H (phi0 (psi n)) ((cellLevel c : ℤ) - (gH : ℤ)) (cellCentre c) omega)
              s 2)
          atTop Lim := by
    intro c
    set pos : aux_gcat_prefix_limits_Pos d Cells := Sum.inl c with hposdef
    set iC : Fin (aux_gcat_prefix_limits_T d) := (aux_gcat_prefix_limits_equiv d) (Sum.inr ())
      with hiCdef
    refine aux_gcat_prefix_limits_transfer (by norm_num)
      (hLpConv 1 (Finset.mem_insert_self _ _) pos 0
        (Sum.inr (iC, Sum.inr (Sum.inr (0 : Fin 2)))))
      (fun n => MemLp.aestronglyMeasurable
        (hvalueMoment 1 (Finset.mem_insert_self _ _) (phi0 (psi n)) pos 0
          (Sum.inr (iC, Sum.inr (Sum.inr (0 : Fin 2))))).1)
      (hVlimMeas pos 0 (Sum.inr (iC, Sum.inr (Sum.inr (0 : Fin 2))))) _ ?_
    have hlevel : (cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iC =
        (cellLevel c : ℤ) - (gH : ℤ) := by
      simp only [hiCdef]; exact aux_gcat_prefix_limits_cmp_level_eq gH (cellLevel c)
    have hcentre : cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) •
        aux_gcat_prefix_limits_shift d gH iC = cellCentre c := by
      simp only [hiCdef]; exact aux_gcat_prefix_limits_cmp_centre_eq gH (cellLevel c) (cellCentre c)
    filter_upwards [aux_gcat_prefix_limits_eventually_ge phi0 psi hphi0 hpsi
      (max (cellLevel c) ((cellLevel c : ℤ) - (gH : ℤ)).toNat)] with n hn
    have hk_le : (cellLevel c : ℤ) ≤ (phi0 (psi n) : ℤ) := by
      have h1 := le_trans (le_max_left (cellLevel c) ((cellLevel c : ℤ) - (gH : ℤ)).toNat) hn
      exact_mod_cast h1
    have hm_le : (cellLevel c : ℤ) - (gH : ℤ) ≤ (phi0 (psi n) : ℤ) := by
      have h1 := le_trans (le_max_right (cellLevel c) ((cellLevel c : ℤ) - (gH : ℤ)).toNat) hn
      calc (cellLevel c : ℤ) - (gH : ℤ)
          ≤ (((cellLevel c : ℤ) - (gH : ℤ)).toNat : ℤ) := Int.self_le_toNat _
        _ ≤ (phi0 (psi n) : ℤ) := by exact_mod_cast h1
    funext omega
    show (if (cellLevel c : ℤ) ≤ (phi0 (psi n) : ℤ) ∧
        (cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iC ≤ (phi0 (psi n) : ℤ) then
        I.err (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) • aux_gcat_prefix_limits_shift d gH iC)
          ((3 : ℝ) ^ (-((cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iC)))
          (zpow_pos (by norm_num) _)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi0 (psi n))
            (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) • aux_gcat_prefix_limits_shift d gH iC)
            (zpow_pos (by norm_num) _))
          (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) • aux_gcat_prefix_limits_shift d gH iC)
          ((3 : ℝ) ^ (-((cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iC)))
          ((fun J : ℕ => Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M J)
              (((phi0 (psi n) : ℤ) -
                ((cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iC)).toNat) /
            (fun J : ℕ => Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M J) (phi0 (psi n)) *
            Real.exp (H omega
                (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) •
                  aux_gcat_prefix_limits_shift d gH iC) +
              (fun (ell : ℤ) (v : SpatialCoordinates d) (beta : BilateralField d) =>
                if 0 ≤ ell then ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                 else -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v)
                ((cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iC)
                (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) •
                  aux_gcat_prefix_limits_shift d gH iC) omega))
          s 2
      else 0) =
      I.err (cellCentre c) ((3 : ℝ) ^ (-((cellLevel c : ℤ) - (gH : ℤ)))) (zpow_pos (by norm_num) _)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi0 (psi n)) (cellCentre c)
          (zpow_pos (by norm_num) _))
        (cellCentre c) ((3 : ℝ) ^ (-((cellLevel c : ℤ) - (gH : ℤ))))
        (gcat_sN M H (phi0 (psi n)) ((cellLevel c : ℤ) - (gH : ℤ)) (cellCentre c) omega) s 2
    have hm_le' : (cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iC ≤ (phi0 (psi n) : ℤ) := by
      rw [hlevel]; exact hm_le
    rw [ite_eq_left ⟨hk_le, hm_le'⟩, hlevel, hcentre,
      aux_gcat_prefix_limits_gcat_sN_unfold M H (phi0 (psi n)) ((cellLevel c : ℤ) - (gH : ℤ))
        (cellCentre c) omega hm_le]
  have hAEFamily : ∀ (c : Cells) (U : Fin 3 × (Fin d → Fin 3)) (i j : Fin d),
      ∃ Lim : BilateralField d → ℝ, Measurable Lim ∧
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega =>
            ((gcat_sN M H (phi0 (psi n)) (gcat_rootLevel gH (cellLevel c) U)
                (gcat_rootCentre gH (cellLevel c) (cellCentre c) U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((I.chart (gcat_rootCentre gH (cellLevel c) (cellCentre c) U)
                  (gcat_rootSide gH (cellLevel c) U) (zpow_pos (by norm_num) _)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi0 (psi n))
                    (gcat_rootCentre gH (cellLevel c) (cellCentre c) U) (zpow_pos (by norm_num) _))
                  (gcat_rootCentre gH (cellLevel c) (cellCentre c) U)
                  (gcat_rootSide gH (cellLevel c) U)).coeffOn
                  (Homogenization.originCube d 0))) i j)
          atTop Lim := by
    intro c U i j
    set pos : aux_gcat_prefix_limits_Pos d Cells := Sum.inl c with hposdef
    set iT : Fin (aux_gcat_prefix_limits_T d) := (aux_gcat_prefix_limits_equiv d) (Sum.inl U)
      with hiTdef
    refine aux_gcat_prefix_limits_transfer (by norm_num)
      (hLpConv 1 (Finset.mem_insert_self _ _) pos 0
        (Sum.inr (iT, Sum.inr (Sum.inl (true, (i, j))))))
      (fun n => MemLp.aestronglyMeasurable
        (hvalueMoment 1 (Finset.mem_insert_self _ _) (phi0 (psi n)) pos 0
          (Sum.inr (iT, Sum.inr (Sum.inl (true, (i, j)))))).1)
      (hVlimMeas pos 0 (Sum.inr (iT, Sum.inr (Sum.inl (true, (i, j)))))) _ ?_
    have hlevel : (cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT =
        gcat_rootLevel gH (cellLevel c) U := by
      simp only [hiTdef]; exact aux_gcat_prefix_limits_root_level_eq gH (cellLevel c) U
    have hcentre : cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) •
        aux_gcat_prefix_limits_shift d gH iT = gcat_rootCentre gH (cellLevel c) (cellCentre c) U := by
      simp only [hiTdef]; exact aux_gcat_prefix_limits_root_centre_eq gH (cellLevel c) (cellCentre c) U
    filter_upwards [aux_gcat_prefix_limits_eventually_ge phi0 psi hphi0 hpsi
      (max (cellLevel c) (gcat_rootLevel gH (cellLevel c) U).toNat)] with n hn
    have hk_le : (cellLevel c : ℤ) ≤ (phi0 (psi n) : ℤ) := by
      have h1 := le_trans (le_max_left (cellLevel c) (gcat_rootLevel gH (cellLevel c) U).toNat) hn
      exact_mod_cast h1
    have hm_le : gcat_rootLevel gH (cellLevel c) U ≤ (phi0 (psi n) : ℤ) := by
      have h1 := le_trans (le_max_right (cellLevel c) (gcat_rootLevel gH (cellLevel c) U).toNat) hn
      calc gcat_rootLevel gH (cellLevel c) U
          ≤ ((gcat_rootLevel gH (cellLevel c) U).toNat : ℤ) := Int.self_le_toNat _
        _ ≤ (phi0 (psi n) : ℤ) := by exact_mod_cast h1
    funext omega
    show (if (cellLevel c : ℤ) ≤ (phi0 (psi n) : ℤ) ∧
        (cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT ≤ (phi0 (psi n) : ℤ) then
        Homogenization.Book.Ch02.sigmaCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          ((I.chart
            (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) • aux_gcat_prefix_limits_shift d gH iT)
            ((3 : ℝ) ^ (-((cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT)))
            (zpow_pos (by norm_num) _)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi0 (psi n))
              (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) • aux_gcat_prefix_limits_shift d gH iT)
              (zpow_pos (by norm_num) _))
            (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) • aux_gcat_prefix_limits_shift d gH iT)
            ((3 : ℝ) ^ (-((cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT)))).coeffOn
            (Homogenization.originCube d 0)) i j /
        ((fun J : ℕ => Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M J)
            (((phi0 (psi n) : ℤ) - ((cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT)).toNat) /
          (fun J : ℕ => Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M J) (phi0 (psi n)) *
          Real.exp (H omega
              (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) • aux_gcat_prefix_limits_shift d gH iT) +
            (fun (ell : ℤ) (v : SpatialCoordinates d) (beta : BilateralField d) =>
              if 0 ≤ ell then ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
               else -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v)
              ((cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT)
              (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) • aux_gcat_prefix_limits_shift d gH iT)
              omega))
      else 0) =
      ((gcat_sN M H (phi0 (psi n)) (gcat_rootLevel gH (cellLevel c) U)
          (gcat_rootCentre gH (cellLevel c) (cellCentre c) U) omega)⁻¹ •
        Homogenization.Book.Ch02.sigmaCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          ((I.chart (gcat_rootCentre gH (cellLevel c) (cellCentre c) U)
            (gcat_rootSide gH (cellLevel c) U) (zpow_pos (by norm_num) _)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi0 (psi n))
              (gcat_rootCentre gH (cellLevel c) (cellCentre c) U) (zpow_pos (by norm_num) _))
            (gcat_rootCentre gH (cellLevel c) (cellCentre c) U)
            (gcat_rootSide gH (cellLevel c) U)).coeffOn
            (Homogenization.originCube d 0))) i j
    have hm_le' : (cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iT ≤ (phi0 (psi n) : ℤ) := by
      rw [hlevel]; exact hm_le
    rw [ite_eq_left ⟨hk_le, hm_le'⟩, hlevel, hcentre,
      aux_gcat_prefix_limits_gcat_sN_unfold M H (phi0 (psi n)) (gcat_rootLevel gH (cellLevel c) U)
        (gcat_rootCentre gH (cellLevel c) (cellCentre c) U) omega hm_le]
    erw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
    simp only [gcat_rootSide]
  choose AELim hAEMeas hAETendsto using hAEFamily
  choose errLim hErrMeas hErrTendsto using hErrFamily
  have hRatioFamily : ∀ (c : Cells),
      ∃ Lim : BilateralField d → ℝ, Measurable Lim ∧
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun n omega => gcat_sN M H (phi0 (psi n)) (cellLevel c : ℤ) (cellCentre c) omega /
            gcat_sN M H (phi0 (psi n)) ((cellLevel c : ℤ) - (gH : ℤ)) (cellCentre c) omega)
          atTop Lim := by
    intro c
    set pos : aux_gcat_prefix_limits_Pos d Cells := Sum.inl c with hposdef
    set iC : Fin (aux_gcat_prefix_limits_T d) := (aux_gcat_prefix_limits_equiv d) (Sum.inr ())
      with hiCdef
    refine aux_gcat_prefix_limits_transfer (by norm_num)
      (hLpConv 1 (Finset.mem_insert_self _ _) pos 0
        (Sum.inr (iC, Sum.inr (Sum.inr (1 : Fin 2)))))
      (fun n => MemLp.aestronglyMeasurable
        (hvalueMoment 1 (Finset.mem_insert_self _ _) (phi0 (psi n)) pos 0
          (Sum.inr (iC, Sum.inr (Sum.inr (1 : Fin 2))))).1)
      (hVlimMeas pos 0 (Sum.inr (iC, Sum.inr (Sum.inr (1 : Fin 2))))) _ ?_
    have hlevel : (cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iC =
        (cellLevel c : ℤ) - (gH : ℤ) := by
      simp only [hiCdef]; exact aux_gcat_prefix_limits_cmp_level_eq gH (cellLevel c)
    have hcentre : cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) •
        aux_gcat_prefix_limits_shift d gH iC = cellCentre c := by
      simp only [hiCdef]; exact aux_gcat_prefix_limits_cmp_centre_eq gH (cellLevel c) (cellCentre c)
    filter_upwards [aux_gcat_prefix_limits_eventually_ge phi0 psi hphi0 hpsi
      (max (cellLevel c) ((cellLevel c : ℤ) - (gH : ℤ)).toNat)] with n hn
    have hk_le : (cellLevel c : ℤ) ≤ (phi0 (psi n) : ℤ) := by
      have h1 := le_trans (le_max_left (cellLevel c) ((cellLevel c : ℤ) - (gH : ℤ)).toNat) hn
      exact_mod_cast h1
    have hm_le : (cellLevel c : ℤ) - (gH : ℤ) ≤ (phi0 (psi n) : ℤ) := by
      have h1 := le_trans (le_max_right (cellLevel c) ((cellLevel c : ℤ) - (gH : ℤ)).toNat) hn
      calc (cellLevel c : ℤ) - (gH : ℤ)
          ≤ (((cellLevel c : ℤ) - (gH : ℤ)).toNat : ℤ) := Int.self_le_toNat _
        _ ≤ (phi0 (psi n) : ℤ) := by exact_mod_cast h1
    funext omega
    show (if (cellLevel c : ℤ) ≤ (phi0 (psi n) : ℤ) ∧
        (cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iC ≤ (phi0 (psi n) : ℤ) then
        ((fun J : ℕ => Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M J)
            (((phi0 (psi n) : ℤ) - (cellLevel c : ℤ)).toNat) /
          (fun J : ℕ => Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M J) (phi0 (psi n)) *
          Real.exp (H omega (cellCentre c) +
            (fun (ell : ℤ) (v : SpatialCoordinates d) (beta : BilateralField d) =>
              if 0 ≤ ell then ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
               else -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v)
              (cellLevel c : ℤ) (cellCentre c) omega)) /
        ((fun J : ℕ => Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M J)
            (((phi0 (psi n) : ℤ) -
              ((cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iC)).toNat) /
          (fun J : ℕ => Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M J) (phi0 (psi n)) *
          Real.exp (H omega
              (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) •
                aux_gcat_prefix_limits_shift d gH iC) +
            (fun (ell : ℤ) (v : SpatialCoordinates d) (beta : BilateralField d) =>
              if 0 ≤ ell then ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
               else -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v)
              ((cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iC)
              (cellCentre c + (3 : ℝ) ^ (-(cellLevel c : ℤ)) •
                aux_gcat_prefix_limits_shift d gH iC) omega))
      else 0) =
      gcat_sN M H (phi0 (psi n)) (cellLevel c : ℤ) (cellCentre c) omega /
      gcat_sN M H (phi0 (psi n)) ((cellLevel c : ℤ) - (gH : ℤ)) (cellCentre c) omega
    have hm_le' : (cellLevel c : ℤ) + aux_gcat_prefix_limits_offset d gH iC ≤ (phi0 (psi n) : ℤ) := by
      rw [hlevel]; exact hm_le
    rw [ite_eq_left ⟨hk_le, hm_le'⟩, hlevel, hcentre,
      aux_gcat_prefix_limits_gcat_sN_unfold M H (phi0 (psi n)) (cellLevel c : ℤ) (cellCentre c)
        omega hk_le,
      aux_gcat_prefix_limits_gcat_sN_unfold M H (phi0 (psi n)) ((cellLevel c : ℤ) - (gH : ℤ))
        (cellCentre c) omega hm_le]
  choose ratioLim hRatioMeas hRatioTendsto using hRatioFamily
  refine ⟨ZLim, DLim, loLim, hiLim, fun c U omega i j => AELim c U i j omega,
    fun c (_ : Unit) => errLim c, fun c (_ : Unit) => ratioLim c, ?_⟩
  intro c
  refine ⟨fun U D code => ⟨hZmeas c U D code, hDmeas c U D code⟩,
    fun U => ⟨hLoMeas c U, hHiMeas c U, fun i j => hAEMeas c U i j⟩,
    hErrMeas c, hRatioMeas c,
    fun U D code => hZtendsto c U D code, fun U D code => hDtendsto c U D code,
    fun U => hLoTendsto c U, fun U => hHiTendsto c U, fun U i j => hAETendsto c U i j,
    hErrTendsto c, hRatioTendsto c⟩

end SubdiffusiveProcess.Paper
end
