module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.in_deterministic_good_scale_transfer
public import SubdiffusiveProcess.Paper.in_deterministic_budget_transfer
public import Homogenization.Book.Ch02.Matrices
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-!
# Actual-coefficient bad-index and error budget

The bad-index count, actual-error sum, subcriticality, and absorption depth
for the fixed-cutoff deterministic implication.
-/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable






def aux_in_deterministic_budget_assembly_transfer_at
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (s Cg delta1 : ℝ) : Prop :=
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta1 →
      ∀ (eps : ℝ), eps ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)) →
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega)) →
      ∀ (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ),
        (∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d) (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1) →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (j : ℤ) (w : SpatialCoordinates d), j ≤ (N : ℤ) →
          Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega ≠ ⊤ →
          Z N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega < 1 →
          I.err w ((3 : ℝ) ^ (-j)) (by positivity)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
              w ((3 : ℝ) ^ (-j)) (sN N j w omega) s 2 ≤
            Cg * (M.delta ^ 2 + eps ^ 8 +
              (Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega).toReal)



theorem aux_in_deterministic_budget_assembly_transfer
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ)) :
    ∃ Cg delta1 : ℝ, 0 < Cg ∧ 0 < delta1 ∧
      aux_in_deterministic_budget_assembly_transfer_at d I s Cg delta1 :=
  in_deterministic_good_scale_transfer d I s hs hsSmall

/-! ## Card and error-sum conjuncts through the closed budget child -/

/-- Short-depth branch `D < k0`: the good sum is empty. -/
lemma aux_in_deterministic_budget_assembly_card_short (a : ℤ) (cbuf k0 D : ℕ) (hD : D < k0)
    (lam : ℝ) (hlam : 0 ≤ lam) (p : ℤ → Prop) [DecidablePred p] :
    (((Finset.Icc (a - (cbuf : ℤ)) (a + (D : ℤ))).filter p).card : ℝ) ≤
      (k0 : ℝ) + (cbuf : ℝ) + lam * (D : ℝ) := by
  have hcard : ((Finset.Icc (a - (cbuf : ℤ)) (a + (D : ℤ))).filter p).card ≤ D + cbuf + 1 := by
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Int.card_Icc]
    omega
  have h1 : (((Finset.Icc (a - (cbuf : ℤ)) (a + (D : ℤ))).filter p).card : ℝ) ≤
      (D : ℝ) + (cbuf : ℝ) + 1 := by exact_mod_cast hcard
  have h2 : (D : ℝ) + 1 ≤ (k0 : ℝ) := by exact_mod_cast hD
  have h3 : 0 ≤ lam * (D : ℝ) := mul_nonneg hlam (Nat.cast_nonneg D)
  linarith



theorem aux_in_deterministic_budget_assembly_budget
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (s : ℝ) (Cg Cbound : ℝ) (hCg0 : 0 ≤ Cg) (hCg : Cg ≤ Cbound)
    (cbuf k0 : ℕ)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Enl Shift : Type)
    (rootLevel : Enl × Shift → ℤ)
    (observationCentre : ∀ (_U : Enl × Shift) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) → SpatialCoordinates d)
    (Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (eps : ℝ) (heps : 0 ≤ eps)
    (lambdaCut lambdaDet : ℝ) (hlamCut : 0 < lambdaCut) (hlam : lambdaCut < lambdaDet)
    (prefixZ : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) → BilateralField d → ℝ)
    (prefixD : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) → BilateralField d → ℝ)
    (hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
      (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
      (omega : BilateralField d),
      prefixZ N U D code omega =
        if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
          ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
            (rootLevel U + (D : ℤ)),
            if 0 ≤ (N : ℤ) - j then
              Z N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega
            else 0
        else 0)
    (hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
      (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
      (omega : BilateralField d),
      prefixD N U D code omega =
        if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
          ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
            (rootLevel U + (D : ℤ)),
            if 0 ≤ (N : ℤ) - j then
              (Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
            else 0
        else 0)
    (hFiniteScoreGuard : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
        (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
        rootLevel U + (D : ℤ) ≤ (N : ℤ) →
        ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
          (rootLevel U + (D : ℤ)),
          Draw N ((N : ℤ) - j).toNat
            (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤)
    (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
    (hZnonneg : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N m : ℕ) (y : Vec d), 0 ≤ Z N m y omega)
    (hTransfer : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (j : ℤ) (w : SpatialCoordinates d), j ≤ (N : ℤ) →
          Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega ≠ ⊤ →
          Z N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega < 1 →
          I.err w ((3 : ℝ) ^ (-j)) (by positivity)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
            w ((3 : ℝ) ^ (-j)) (sN N j w omega) s 2 ≤
          Cg * (M.delta ^ 2 + eps ^ 8 +
            (Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega).toReal))
    (N : ℕ) (U0 : Enl × Shift) (hU0 : rootLevel U0 ≤ (N : ℤ))
    (P : ℕ → Prop) (hP0 : P 0) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      (∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D → P D →
          rootLevel U + (D : ℤ) ≤ (N : ℤ) →
          ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
            prefixZ N U D code omega < lambdaCut * (D : ℝ) ∧
            prefixD N U D code omega < lambdaCut * (D : ℝ)) →
      (∀ (Uroot : Enl × Shift) (D : ℕ), P D →
        rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
        ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
          ((Finset.filter
            (fun j : ℤ => j < rootLevel Uroot + (k0 : ℤ) ∨
              1 ≤ Z N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega)
            (Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
              (rootLevel Uroot + (D : ℤ)))).card : ℝ) ≤
            (k0 : ℝ) + (cbuf : ℝ) + lambdaDet * (D : ℝ)) ∧
      (∀ (Uroot : Enl × Shift) (D : ℕ), P D →
        rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
        ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
          (∑ j ∈ Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
            (rootLevel Uroot + (D : ℤ)),
            if rootLevel Uroot + (k0 : ℤ) ≤ j ∧
                Z N ((N : ℤ) - j).toNat
                  (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega < 1 then
              let w := observationCentre Uroot D code
              let rj := (3 : ℝ) ^ (-j)
              I.err w rj (by positivity)
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
                w rj (sN N j w omega) s 2
            else 0) ≤
              Cbound * (M.delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) +
                Cbound * ((k0 : ℝ) + (cbuf : ℝ))) := by
  have hCb0 : 0 ≤ Cbound := hCg0.trans hCg
  have hlamDet0 : 0 < lambdaDet := hlamCut.trans hlam
  filter_upwards [hTransfer, hZnonneg, hFiniteScoreGuard] with omega hT hZ0 hFG
  intro hev
  -- `k0 = 0`: the event is empty (the depth-zero prefix is a nonnegative sum `< 0`).
  rcases Nat.eq_zero_or_pos k0 with hk0 | hk0pos
  · exfalso
    subst hk0
    have hU0' : rootLevel U0 + ((0 : ℕ) : ℤ) ≤ (N : ℤ) := by simpa using hU0
    have h := (hev U0 0 le_rfl hP0 hU0' (Sum.inr U0)).1
    have hnn : 0 ≤ prefixZ N U0 0 (Sum.inr U0) omega := by
      rw [hPrefixZ, ite_eq_left hU0']
      apply Finset.sum_nonneg
      intro j _
      split_ifs
      · exact hZ0 _ _ _
      · exact le_rfl
    rw [Nat.cast_zero, mul_zero] at h
    linarith
  -- `k0 ≥ 1`
  have hbudget : ∀ (Uroot : Enl × Shift) (D : ℕ), k0 ≤ D → P D →
      rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
      ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift), _ :=
    fun Uroot D hD hPD hN code =>
      in_deterministic_budget_transfer d I Cbound M.delta eps lambdaDet hCb0
        M.shellPrefix.delta_pos.le heps k0 cbuf D N hk0pos M H Enl Shift Uroot omega
        rootLevel observationCentre code Z Draw (prefixZ N Uroot D code omega)
        (prefixD N Uroot D code omega) sN s hN
        (by rw [hPrefixZ, ite_eq_left hN]) (by rw [hPrefixD, ite_eq_left hN])
        (lt_of_lt_of_le (hev Uroot D hD hPD hN code).1
          (mul_le_mul_of_nonneg_right hlam.le (Nat.cast_nonneg D)))
        (lt_of_lt_of_le (hev Uroot D hD hPD hN code).2
          (mul_le_mul_of_nonneg_right hlam.le (Nat.cast_nonneg D)))
        (fun j => hZ0 _ _ _)
        (fun j hj1 hj2 hj3 hZlt =>
          (hT N j (observationCentre Uroot D code) (by omega)
            (hFG N Uroot D code hN j (Finset.mem_Icc.2 ⟨by omega, hj2⟩)) hZlt).trans
            (mul_le_mul_of_nonneg_right hCg (by positivity)))
  refine ⟨fun Uroot D hPD hN code => ?_, fun Uroot D hPD hN code => ?_⟩
  · rcases le_or_gt k0 D with hD | hD
    · exact (hbudget Uroot D hD hPD hN code).1
    · exact aux_in_deterministic_budget_assembly_card_short _ cbuf k0 D hD lambdaDet hlamDet0.le _
  · rcases le_or_gt k0 D with hD | hD
    · exact (hbudget Uroot D hD hPD hN code).2
    · have hzero : (∑ j ∈ Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
            (rootLevel Uroot + (D : ℤ)),
            if rootLevel Uroot + (k0 : ℤ) ≤ j ∧
                Z N ((N : ℤ) - j).toNat
                  (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega < 1 then
              let w := observationCentre Uroot D code
              let rj := (3 : ℝ) ^ (-j)
              I.err w rj (by positivity)
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
                w rj (sN N j w omega) s 2
            else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hj2 := (Finset.mem_Icc.1 hj).2
        rw [ite_eq_right]
        rintro ⟨hj1, _⟩
        omega
      rw [hzero]
      have h1 : 0 ≤ M.delta ^ 2 + eps ^ 8 + lambdaDet := by positivity
      positivity

/-! ## Subcriticality, absorption depth and the parameter order -/

/-- The fixed allowance is absorbed beyond an explicit depth. -/
lemma aux_in_deterministic_budget_assembly_absorb (alpha Cbound t : ℝ) (k0 cbuf : ℕ)
    (hsub : Cbound * t < 1 - alpha) :
    ∃ D0 : ℕ, k0 ≤ D0 ∧ ∀ D : ℕ, D0 ≤ D →
      (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ))) * (3 : ℝ) ^ (Cbound * t * (D : ℝ)) ≤
        (3 : ℝ) ^ ((1 - alpha) * (D : ℝ)) := by
  have hg : 0 < (1 - alpha) - Cbound * t := by linarith
  refine ⟨max k0 ⌈Cbound * ((k0 : ℝ) + (cbuf : ℝ)) / ((1 - alpha) - Cbound * t)⌉₊,
    le_max_left _ _, ?_⟩
  intro D hD
  have h1 : Cbound * ((k0 : ℝ) + (cbuf : ℝ)) / ((1 - alpha) - Cbound * t) ≤ (D : ℝ) := by
    refine (Nat.le_ceil _).trans ?_
    exact_mod_cast (le_max_right _ _).trans hD
  have h2 : Cbound * ((k0 : ℝ) + (cbuf : ℝ)) ≤ ((1 - alpha) - Cbound * t) * (D : ℝ) := by
    rwa [div_le_iff₀ hg, mul_comm (D : ℝ)] at h1
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  linarith

/-- The parameters `eps0`, `lam0`, `delta0` exist after `Cbound` (and below any caps). -/
lemma aux_in_deterministic_budget_assembly_params (alpha Cbound delta1 : ℝ) (halpha : alpha < 1)
    (hC : 0 < Cbound) (hd1 : 0 < delta1) :
    ∃ eps0 lam0 delta0 : ℝ, 0 < eps0 ∧ 0 < lam0 ∧ 0 < delta0 ∧ delta0 ≤ delta1 ∧
      Cbound * (lam0 + delta0 ^ 2 + eps0 ^ 8) < 1 - alpha := by
  set t : ℝ := (1 - alpha) / (4 * Cbound) with ht
  have ht0 : 0 < t := div_pos (by linarith) (by positivity)
  have hCt : Cbound * t = (1 - alpha) / 4 := by
    rw [ht]; field_simp
  refine ⟨min 1 t, t, min delta1 (min 1 t), lt_min one_pos ht0, ht0,
    lt_min hd1 (lt_min one_pos ht0), min_le_left _ _, ?_⟩
  have he0 : 0 ≤ min 1 t := (lt_min one_pos ht0).le
  have he1 : min 1 t ≤ 1 := min_le_left _ _
  have het : min 1 t ≤ t := min_le_right _ _
  have hd0 : 0 ≤ min delta1 (min 1 t) := (lt_min hd1 (lt_min one_pos ht0)).le
  have hdm : min delta1 (min 1 t) ≤ min 1 t := min_le_right _ _
  have h8 : (min 1 t) ^ 8 ≤ t :=
    (pow_le_of_le_one he0 he1 (by norm_num)).trans het
  have h2 : (min delta1 (min 1 t)) ^ 2 ≤ t :=
    (pow_le_of_le_one hd0 (hdm.trans he1) (by norm_num)).trans (hdm.trans het)
  have hsum : t + (min delta1 (min 1 t)) ^ 2 + (min 1 t) ^ 8 ≤ 3 * t := by linarith
  calc Cbound * (t + (min delta1 (min 1 t)) ^ 2 + (min 1 t) ^ 8) ≤ Cbound * (3 * t) :=
        mul_le_mul_of_nonneg_left hsum hC.le
    _ = 3 * ((1 - alpha) / 4) := by rw [← hCt]; ring
    _ < 1 - alpha := by linarith




/-- **Budget block of the full fixed-cutoff conclusion, with the fixed-cutoff binders.**
Constants `Cblock`, `delta1` depend on `d`, `I`, `s` only; for every later choice
`Cbound ≥ Cblock`, `delta0 ≤ delta1` and subcritical `(eps0, lam0, delta0)`, the
card, error-sum, subcriticality and absorption conjuncts of the second conjunct of
`SubdiffusiveProcess.Paper.in_deterministic` hold on one full-measure event per cutoff.  No
`hGoodScaleError`-type premise is present. -/
theorem in_deterministic_budget_assembly
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (alpha beta s sigma cell epshom : ℝ)
    (_halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (_hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ))
    (_hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (_hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (_hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (_hepshom : 0 < epshom) :
    ∃ Cblock delta1 : ℝ, 1 ≤ Cblock ∧ 0 < delta1 ∧
    ∀ Cbound eps0 lam0 delta0 : ℝ, Cblock ≤ Cbound → 0 < eps0 → 0 < lam0 →
      0 < delta0 → delta0 ≤ delta1 →
      Cbound * (lam0 + delta0 ^ 2 + eps0 ^ 8) < 1 - alpha →
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hMH : InfraredCharacterization M H)
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ) (hqpos : 0 < qside)
        (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (hqcenter : qcenter = z)
        (Enl Shift Cmp : Type)
        [Fintype Enl] [Fintype Shift] [Fintype Cmp]
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (hfactor : factor selfE = 0)
        (padE : Enl) (hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (hGridCover : ∀ (x : SpatialCoordinates d),
          x ∈ Metric.closedBall z (qside / 2) →
          ∀ rho : ℝ, 0 < rho → rho ≤ qside →
            ∃ (U : Enl × Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
              Metric.ball x (rho / 2) ⊆
                Metric.ball (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                  (descendantSide 1 D (rootSide U) / 2) ∧
              descendantSide 1 D (rootSide U) ≤ 9 * rho)
        (parent : Cmp → Enl × Shift)
        (depth : Cmp → ℕ)
        (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
        (cmpCentre : Cmp → SpatialCoordinates d)
        (hcmpCentre : ∀ (c : Cmp),
          cmpCentre c =
            descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
              (depth c) (word c))
        (cmpLevel : Cmp → ℤ)
        (hcmpLevel : ∀ (c : Cmp),
          cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
        (cmpSide : Cmp → ℝ)
        (hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
        (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
        (chosen : Cmp)
        (observationCentre : ∀ (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            SpatialCoordinates d)
        (hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ))
                (((3 : ℝ) ^ (-(N : ℤ))) • y))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (hepsSmall : eps ≤ eps0)
        (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega))
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (hcdet : 0 < cdet) (hcdetSmall : cdet ≤ Cbound⁻¹)
        (hlamSmall : lambdaDet ≤ lam0)
        (hdisorder : M.delta ≤ delta0)
        (prefixZ : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixZ N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega
                else 0
            else 0)
        (hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (hFiniteScoreGuard : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤)
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ,
      ∀ (N : ℕ), k ≤ N → (∀ c : Cmp, cmpLevel c ≤ (N : ℤ)) →
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          (          ((∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D →
              rootLevel U + (D : ℤ) ≤ (N : ℤ) →
              ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
                prefixZ N U D code omega < lambdaCut * (D : ℝ) ∧
                prefixD N U D code omega < lambdaCut * (D : ℝ)) ∧
           (∀ U : Enl × Shift,
              cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹) ∧
           errN N chosen omega ≤ epshom * cdet ∧
           (∀ c : Cmp, ratioN N c omega ∈ Set.Icc (1 / 2 : ℝ) 2)) →
          (∀ (Uroot : Enl × Shift) (D : ℕ),
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              ((Finset.filter
                (fun j : ℤ => j < rootLevel Uroot + (k0 : ℤ) ∨
                  1 ≤ Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega)
                (Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                  (rootLevel Uroot + (D : ℤ)))).card : ℝ) ≤
                (k0 : ℝ) + (cbuf : ℝ) + lambdaDet * (D : ℝ)) ∧
          (∀ (Uroot : Enl × Shift) (D : ℕ),
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              (∑ j ∈ Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                (rootLevel Uroot + (D : ℤ)),
                if rootLevel Uroot + (k0 : ℤ) ≤ j ∧
                    Z N ((N : ℤ) - j).toNat
                      (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega < 1 then
                  let w := observationCentre Uroot D code
                  let rj := (3 : ℝ) ^ (-j)
                  I.err w rj (by positivity)
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
                    w rj (sN N j w omega) s 2
                else 0) ≤
                  Cbound * (M.delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) +
                    Cbound * ((k0 : ℝ) + (cbuf : ℝ))) ∧
          Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) < 1 - alpha ∧
          (∃ D0 : ℕ, k0 ≤ D0 ∧ ∀ D : ℕ, D0 ≤ D →
            (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ))) *
              (3 : ℝ) ^ (Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)) ≤
                (3 : ℝ) ^ ((1 - alpha) * (D : ℝ)))) := by
  obtain ⟨Cg, delta1, hCg, hdelta1, hT⟩ :=
    aux_in_deterministic_budget_assembly_transfer d I s hs hsSmall
  refine ⟨max Cg 1, delta1, le_max_right _ _, hdelta1, ?_⟩
  intro Cbound eps0 lam0 delta0 hCb heps0 hlam0 hdelta0 hdd1 hsub
    cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp _ _ _
    selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
    rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
    hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
    hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
    prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
    AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ N hkN _hcmp
  have hCb0 : 0 ≤ Cbound := zero_le_one.trans ((le_max_right _ _).trans hCb)
  have hT' := hT M H hMH (hdisorder.trans hdd1) eps heps eta F Praw Rraw Draw Z
    rawGood hEta hPrimitive sN hsN
  have hZnn : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N m : ℕ) (y : Vec d), 0 ≤ Z N m y omega := by
    filter_upwards [hPrimitive] with omega hP
    intro N m y
    obtain ⟨_, _, _, _, _, _, _, _, _, hZdef, _⟩ := hP N
    exact (hZdef m y).2.1
  have hU0 : rootLevel qRoot ≤ (N : ℤ) := by
    rw [hqRoot, hrootLevel, hfactor]
    push_cast
    omega
  have hB := aux_in_deterministic_budget_assembly_budget d I s Cg Cbound hCg.le
    ((le_max_left _ _).trans hCb) cbuf k0 M H Enl Shift rootLevel observationCentre Draw Z
    eps heps.1.le lambdaCut lambdaDet hThresholds.1 (hThresholds.2.1.trans hThresholds.2.2.1)
    prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hZnn hT' N qRoot hU0
    (fun _ => True) trivial
  have hd0 : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  have hsubc : Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) < 1 - alpha := by
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ hCb0) hsub
    have h1 : M.delta ^ 2 ≤ delta0 ^ 2 := pow_le_pow_left₀ hd0 hdisorder 2
    have h2 : eps ^ 8 ≤ eps0 ^ 8 := pow_le_pow_left₀ heps.1.le hepsSmall 8
    linarith
  filter_upwards [hB] with omega hBw
  intro hev
  obtain ⟨hcard, herr⟩ := hBw (fun U D hD _ hN code => hev.1 U D hD hN code)
  exact ⟨fun U D hN code => hcard U D trivial hN code,
    fun U D hN code => herr U D trivial hN code, hsubc, aux_in_deterministic_budget_assembly_absorb alpha Cbound _ k0 cbuf hsubc⟩

end SubdiffusiveProcess.Paper
