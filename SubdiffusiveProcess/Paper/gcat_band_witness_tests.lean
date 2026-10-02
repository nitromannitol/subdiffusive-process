import SubdiffusiveProcess.Paper.gcat_band_witness_prefix
import SubdiffusiveProcess.Paper.gcat_band_witness_tests_core2
import SubdiffusiveProcess.Paper.gcat_prefix_limits
import SubdiffusiveProcess.Paper.lem_prefix_limit
import SubdiffusiveProcess.Paper.lem_band
import SubdiffusiveProcess.Paper.sum_errors_baseline_input
import SubdiffusiveProcess.Paper.primitive_scores

open MeasureTheory Filter Set SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators Topology NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Coordinate entries of `lem_band`'s test vector. -/
abbrev aux_gcat_band_witness_TestEntry (d : ℕ) := Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Fin 2)

/-- Weighted sum of the moduli of the four catalogue test coordinates (lo/hi ellipticity at every root, error and
reference ratio at the comparison cube). -/
def aux_gcat_band_witness_Phi (d : ℕ) (wl wh we wr : ℝ) :
    (Fin (aux_gcat_prefix_limits_T d) → aux_gcat_band_witness_TestEntry d → ℝ) → ℝ :=
  fun x => (∑ U : aux_gcat_band_witness_Roots d,
      (wl * |x (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 0)| +
        wh * |x (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 1)|)) +
    we * |x (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 0))| +
    wr * |x (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 1))|

/-- Lipschitz constant of `Phi`. -/
def aux_gcat_band_witness_PhiK (d : ℕ) (wl wh we wr : ℝ) : ℝ :=
  (Fintype.card (aux_gcat_band_witness_Roots d) : ℝ) * (wl + wh) + we + wr

theorem aux_gcat_band_witness_Phi_lip (d : ℕ) (wl wh we wr : ℝ)
    (hwl : 0 ≤ wl) (hwh : 0 ≤ wh) (hwe : 0 ≤ we) (hwr : 0 ≤ wr) :
    LipschitzWith ⟨aux_gcat_band_witness_PhiK d wl wh we wr, by
      unfold aux_gcat_band_witness_PhiK; positivity⟩ (aux_gcat_band_witness_Phi d wl wh we wr) := by
  classical
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  have hcoord : ∀ i j, |x i j - y i j| ≤ dist x y := by
    intro i j
    rw [← Real.dist_eq]
    exact (dist_le_pi_dist (x i) (y i) j).trans (dist_le_pi_dist x y i)
  have hnn : 0 ≤ dist x y := dist_nonneg
  rw [Real.dist_eq]
  unfold aux_gcat_band_witness_Phi
  have habs : ∀ a b : ℝ, abs (abs a - abs b) ≤ abs (a - b) := fun a b => abs_abs_sub_abs_le_abs_sub a b
  have hU : ∀ U : aux_gcat_band_witness_Roots d,
      |(wl * |x (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 0)| +
        wh * |x (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 1)|) -
       (wl * |y (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 0)| +
        wh * |y (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 1)|)| ≤ (wl + wh) * dist x y := by
    intro U
    have h0 := (habs (x (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 0))
      (y (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 0))).trans
      (hcoord (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 0))
    have h1 := (habs (x (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 1))
      (y (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 1))).trans
      (hcoord (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 1))
    have e : (wl * |x (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 0)| +
        wh * |x (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 1)|) -
       (wl * |y (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 0)| +
        wh * |y (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 1)|) =
       wl * (|x (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 0)| -
          |y (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 0)|) +
       wh * (|x (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 1)| -
          |y (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 1)|) := by ring
    rw [e]
    calc _ ≤ |wl * (|x (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 0)| -
          |y (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 0)|)| +
        |wh * (|x (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 1)| -
          |y (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 1)|)| := abs_add_le _ _
      _ = wl * |(|x (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 0)| -
          |y (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 0)|)| +
        wh * |(|x (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 1)| -
          |y (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 1)|)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hwl, abs_of_nonneg hwh]
      _ ≤ wl * dist x y + wh * dist x y :=
          add_le_add (mul_le_mul_of_nonneg_left h0 hwl) (mul_le_mul_of_nonneg_left h1 hwh)
      _ = (wl + wh) * dist x y := by ring
  have hsum : |(∑ U : aux_gcat_band_witness_Roots d,
      (wl * |x (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 0)| +
        wh * |x (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 1)|)) -
      (∑ U : aux_gcat_band_witness_Roots d,
      (wl * |y (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 0)| +
        wh * |y (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 1)|))| ≤
      (Fintype.card (aux_gcat_band_witness_Roots d) : ℝ) * ((wl + wh) * dist x y) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _U : aux_gcat_band_witness_Roots d, (wl + wh) * dist x y :=
          Finset.sum_le_sum (fun U _ => hU U)
      _ = _ := by simp
  have he := (habs (x (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 0)))
      (y (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 0)))).trans
      (hcoord (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 0)))
  have hr := (habs (x (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 1)))
      (y (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 1)))).trans
      (hcoord (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 1)))
  set SX := ∑ U : aux_gcat_band_witness_Roots d,
      (wl * |x (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 0)| +
        wh * |x (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 1)|) with hSX
  set SY := ∑ U : aux_gcat_band_witness_Roots d,
      (wl * |y (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 0)| +
        wh * |y (aux_gcat_prefix_limits_equiv d (Sum.inl U)) (Sum.inl 1)|) with hSY
  have h3 : |SX + we * |x (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 0))| +
        wr * |x (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 1))| -
      (SY + we * |y (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 0))| +
        wr * |y (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 1))|)| ≤
      |SX - SY| + we * |(|x (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 0))| -
        |y (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 0))|)| +
      wr * |(|x (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 1))| -
        |y (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 1))|)| := by
    have e : SX + we * |x (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 0))| +
        wr * |x (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 1))| -
      (SY + we * |y (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 0))| +
        wr * |y (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 1))|) =
      (SX - SY) + we * (|x (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 0))| -
        |y (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 0))|) +
      wr * (|x (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 1))| -
        |y (aux_gcat_prefix_limits_equiv d (Sum.inr ())) (Sum.inr (Sum.inr 1))|) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)
    · rw [abs_mul, abs_of_nonneg hwe]
    · rw [abs_mul, abs_of_nonneg hwr]
  refine h3.trans ?_
  have : (aux_gcat_band_witness_PhiK d wl wh we wr) * dist x y =
      (Fintype.card (aux_gcat_band_witness_Roots d) : ℝ) * ((wl + wh) * dist x y) +
        we * dist x y + wr * dist x y := by
    unfold aux_gcat_band_witness_PhiK; ring
  simp only [NNReal.coe_mk]
  rw [this]
  have := mul_le_mul_of_nonneg_left he hwe
  have := mul_le_mul_of_nonneg_left hr hwr
  nlinarith

/-- Value at scale `n` of the four test coordinates, in the form of `lem_prefix_limit`'s `value`
(entries `Sum.inr (i, j)`), for an entry with offset `off` and shift `sh`. Guarded: zero unless both
scales are within the cutoff. -/
def aux_gcat_band_witness_loG {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (sigma : ℝ)
    (N : ℕ) (n : ℤ) (z : SpatialCoordinates d) (off : ℤ) (sh : SpatialCoordinates d)
    (omega : BilateralField d) : ℝ :=
  if n ≤ (N : ℤ) ∧ n + off ≤ (N : ℤ) then
    I.lam (z + ((3 : ℝ) ^ (-n)) • sh) ((3 : ℝ) ^ (-(n + off))) (zpow_pos (by norm_num) _)
      (Lane4.cutoffPositiveCoefficient M H omega N (z + ((3 : ℝ) ^ (-n)) • sh)
        (zpow_pos (by norm_num) _))
      (z + ((3 : ℝ) ^ (-n)) • sh) ((3 : ℝ) ^ (-(n + off))) sigma 2 /
    aux_lem_band_U2_reference M H N (n + off) (z + ((3 : ℝ) ^ (-n)) • sh) omega
  else 0

def aux_gcat_band_witness_hiG {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (sigma : ℝ)
    (N : ℕ) (n : ℤ) (z : SpatialCoordinates d) (off : ℤ) (sh : SpatialCoordinates d)
    (omega : BilateralField d) : ℝ :=
  if n ≤ (N : ℤ) ∧ n + off ≤ (N : ℤ) then
    I.Lam (z + ((3 : ℝ) ^ (-n)) • sh) ((3 : ℝ) ^ (-(n + off))) (zpow_pos (by norm_num) _)
      (Lane4.cutoffPositiveCoefficient M H omega N (z + ((3 : ℝ) ^ (-n)) • sh)
        (zpow_pos (by norm_num) _))
      (z + ((3 : ℝ) ^ (-n)) • sh) ((3 : ℝ) ^ (-(n + off))) sigma 2 /
    aux_lem_band_U2_reference M H N (n + off) (z + ((3 : ℝ) ^ (-n)) • sh) omega
  else 0

def aux_gcat_band_witness_errG {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (s : ℝ)
    (N : ℕ) (n : ℤ) (z : SpatialCoordinates d) (off : ℤ) (sh : SpatialCoordinates d)
    (omega : BilateralField d) : ℝ :=
  if n ≤ (N : ℤ) ∧ n + off ≤ (N : ℤ) then
    I.err (z + ((3 : ℝ) ^ (-n)) • sh) ((3 : ℝ) ^ (-(n + off))) (zpow_pos (by norm_num) _)
      (Lane4.cutoffPositiveCoefficient M H omega N (z + ((3 : ℝ) ^ (-n)) • sh)
        (zpow_pos (by norm_num) _))
      (z + ((3 : ℝ) ^ (-n)) • sh) ((3 : ℝ) ^ (-(n + off)))
      (aux_lem_band_U2_reference M H N (n + off) (z + ((3 : ℝ) ^ (-n)) • sh) omega) s 2
  else 0

def aux_gcat_band_witness_ratioG {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (n : ℤ) (z : SpatialCoordinates d) (off : ℤ) (sh : SpatialCoordinates d)
    (omega : BilateralField d) : ℝ :=
  if n ≤ (N : ℤ) ∧ n + off ≤ (N : ℤ) then
    aux_lem_band_U2_reference M H N n z omega /
      aux_lem_band_U2_reference M H N (n + off) (z + ((3 : ℝ) ^ (-n)) • sh) omega
  else 0


/-- Unit-coefficient value of `lam`. -/
theorem aux_gcat_band_witness_unit_lam (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    I.lam z r hr (aux_gcat_band_witness_unitA d (centeredCube z r hr)) z r sigma 2 = 1 := by
  rw [aux_lem_band_U2_lam_eq I z r hr _ sigma hsigma]
  exact aux_lem_band_U2_isOne_lamF sigma hsigma _
    (aux_lem_band_U2_chart_isOne I z r hr _ (aux_gcat_band_witness_unitA_ae d _))

/-- Unit-coefficient value of `Lam`. -/
theorem aux_gcat_band_witness_unit_Lam (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    I.Lam z r hr (aux_gcat_band_witness_unitA d (centeredCube z r hr)) z r sigma 2 = 1 := by
  rw [aux_lem_band_U2_Lam_eq I z r hr _ sigma hsigma]
  exact aux_lem_band_U2_isOne_LamF sigma hsigma _
    (aux_lem_band_U2_chart_isOne I z r hr _ (aux_gcat_band_witness_unitA_ae d _))

/-- The finite-cutoff test statistic of the cell `(n, z)`: weighted moduli of the deviations of the four
catalogue coordinates from their zero-disorder values. -/
def aux_gcat_band_witness_Tfin {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (gH : ℕ) (wl wh we wr : ℝ) (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (sigma s : ℝ) (N : ℕ) (n : ℤ)
    (z : SpatialCoordinates d) (omega : BilateralField d) : ℝ :=
  (∑ U : aux_gcat_band_witness_Roots d,
    (wl * |aux_gcat_band_witness_loG I M H sigma N n z
        (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
        (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))) omega - 1| +
     wh * |aux_gcat_band_witness_hiG I M H sigma N n z
        (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
        (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))) omega - 1|)) +
  we * |aux_gcat_band_witness_errG I M H s N n z
        (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
        (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))) omega| +
  wr * |aux_gcat_band_witness_ratioG M H N n z
        (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
        (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))) omega - 1|


/-- Band approximants of the finite-cutoff test statistic, from `lem_band` (weights `0`, the test functional `Phi`). -/
theorem aux_gcat_band_witness_bank_T
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Pc : Paper.in_poincare d hd I) (Xc : Paper.in_extension d hd I)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (Dd : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (Dbase : Paper.sum_errors_baseline_input d)
    (s sigma eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (heps : eps ∈ Set.Ioo (0 : ℝ) 1) (gH : ℕ) (wl wh we wr : ℝ)
    (hwl : 0 ≤ wl) (hwh : 0 ≤ wh) (hwe : 0 ≤ we) (hwr : 0 ≤ wr) :
    ∃ a c : ℝ, ∃ width : ℕ, 0 < a ∧ 0 < c ∧ 0 < width ∧
      ∀ p : ℝ, 1 ≤ p → ∃ delta0 Cp : ℝ, 0 < delta0 ∧ 0 < Cp ∧
        ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
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
        ∀ (N : ℕ) (n : ℤ) (z : SpatialCoordinates d), n ≤ (N : ℤ) →
          (∀ i : Fin (aux_gcat_prefix_limits_T d), n + aux_gcat_prefix_limits_offset d gH i ≤ (N : ℤ)) →
          ∀ h : ℕ, 1 ≤ h →
          ∃ Yn : BilateralField d → ℝ,
            AEStronglyMeasurable[aux_gcat_band_witness_lbWindow d n width h] Yn
              (chaosSampleLaw M).toMeasure ∧
            eLpNorm (fun omega => aux_gcat_band_witness_Tfin gH wl wh we wr I M H sigma s N n z omega -
                Yn omega) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal (Cp * M.delta ^ c * (3 : ℝ) ^ (-(a * (h : ℝ)))) := by
  classical
  obtain ⟨CD, deltaD, hCDdD, hbase⟩ := Dbase s eps hs heps
  obtain ⟨a, c, width, ha, hc, hw, hmain⟩ :=
    Paper.lem_band d hd I Pc Xc W Sf Dd Cresp hCresp s sigma eps hs hsigma heps
      (aux_gcat_prefix_limits_T d) (aux_gcat_prefix_limits_offset d gH)
      (aux_gcat_prefix_limits_shift d gH) (fun _ => 0) (fun _ => le_refl 0)
      ⟨aux_gcat_band_witness_PhiK d wl wh we wr, by unfold aux_gcat_band_witness_PhiK; positivity⟩
      (aux_gcat_band_witness_Phi d wl wh we wr)
      (aux_gcat_band_witness_Phi_lip d wl wh we wr hwl hwh hwe hwr)
      (by simp [aux_gcat_band_witness_Phi])
      (fun x => by unfold aux_gcat_band_witness_Phi; positivity) CD (fun p hp => (hCDdD p hp).1)
  refine ⟨a, c, width, ha, hc, hw, fun p hp => ?_⟩
  obtain ⟨q, delta0, Cp, hq2, hq1, hd0, hCp, hM⟩ := hmain p hp
  refine ⟨min delta0 (min 1 (deltaD q)), Cp, lt_min hd0 (lt_min one_pos (hCDdD q hq1).2), hCp, ?_⟩
  intro M hMd Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim N n z hn hoff h hh
  have hM1 : M.delta ≤ delta0 := hMd.trans (min_le_left _ _)
  have hM2 : M.delta ≤ min 1 (deltaD q) := hMd.trans (min_le_right _ _)
  have hDb := hbase q hq1 M hM2 eta heta F Praw Rraw Draw Z rawGood hprim
  let sidePos : ∀ n : ℤ, 0 < (3 : ℝ) ^ (-n) := fun n => zpow_pos (by norm_num) _
  obtain ⟨-, hmain2⟩ := hM M hM1 Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim hDb
    sidePos (fun n z => aux_gcat_band_witness_unitA d _) (fun n z => aux_gcat_band_witness_unitA_ae d _)
  obtain ⟨Xband, hXm, hXe⟩ := hmain2 N n z hn hoff h hh
  refine ⟨Xband, hXm, ?_⟩
  refine le_trans (le_of_eq ?_) hXe
  congr 1
  funext omega
  congr 1
  have hg : ∀ i : Fin (aux_gcat_prefix_limits_T d), n ≤ (N : ℤ) ∧
      n + aux_gcat_prefix_limits_offset d gH i ≤ (N : ℤ) := fun i => ⟨hn, hoff i⟩
  have hulam : ∀ (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      I.lam w r hr (aux_gcat_band_witness_unitA d (centeredCube w r hr)) w r sigma 2 = 1 :=
    fun w r hr => aux_gcat_band_witness_unit_lam d I w r hr sigma hsigma
  have hulam' : ∀ (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      I.Lam w r hr (aux_gcat_band_witness_unitA d (centeredCube w r hr)) w r sigma 2 = 1 :=
    fun w r hr => aux_gcat_band_witness_unit_Lam d I w r hr sigma hsigma
  simp only [zero_mul, zero_add]
  unfold aux_gcat_band_witness_Tfin aux_gcat_band_witness_Phi
  dsimp only
  simp only [Sum.elim_inl, Sum.elim_inr, hulam, hulam', aux_gcat_band_witness_loG,
    aux_gcat_band_witness_hiG, aux_gcat_band_witness_errG, aux_gcat_band_witness_ratioG,
    hn, hoff, and_self, if_true, (by decide : ((1 : Fin 2) = 0) = False),
    (by decide : ((1 : Fin 3) = 0) = False), if_false]
  rfl


/-- Limit bank of the four test coordinates at the cell `(k, z)` from `lem_prefix_limit` (all catalogue entries):
a common subsequence along which the guarded coordinates converge in `L^p`. -/
theorem aux_gcat_band_witness_tests_limit_bank
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Pc : Paper.in_poincare d hd I) (Xc : Paper.in_extension d hd I)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (Dd : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp)
    (s sigma eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (heps : eps ∈ Set.Ioo (0 : ℝ) 1) (p : ℝ) (hp : 1 ≤ p) (gH : ℕ) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
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
      ∃ psi : ℕ → ℕ, StrictMono psi ∧
      ∃ (Vlo Vhi : aux_gcat_band_witness_Roots d → BilateralField d → ℝ)
        (Verr Vrat : BilateralField d → ℝ),
        (∀ U, MemLp (Vlo U) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
        (∀ U, MemLp (Vhi U) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
        MemLp Verr (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
        MemLp Vrat (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
        (∀ N U, MemLp (aux_gcat_band_witness_loG I M H sigma N (k : ℤ) z
          (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
          (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
        (∀ N U, MemLp (aux_gcat_band_witness_hiG I M H sigma N (k : ℤ) z
          (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
          (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
        (∀ N, MemLp (aux_gcat_band_witness_errG I M H s N (k : ℤ) z
          (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
          (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
        (∀ N, MemLp (aux_gcat_band_witness_ratioG M H N (k : ℤ) z
          (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
          (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
        (∀ U, Tendsto (fun kk => eLpNorm (fun ω =>
          aux_gcat_band_witness_loG I M H sigma (phi (psi kk)) (k : ℤ) z
            (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
            (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))) ω -
          Vlo U ω) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) atTop (𝓝 0)) ∧
        (∀ U, Tendsto (fun kk => eLpNorm (fun ω =>
          aux_gcat_band_witness_hiG I M H sigma (phi (psi kk)) (k : ℤ) z
            (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
            (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))) ω -
          Vhi U ω) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) atTop (𝓝 0)) ∧
        Tendsto (fun kk => eLpNorm (fun ω =>
          aux_gcat_band_witness_errG I M H s (phi (psi kk)) (k : ℤ) z
            (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
            (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))) ω -
          Verr ω) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) atTop (𝓝 0) ∧
        Tendsto (fun kk => eLpNorm (fun ω =>
          aux_gcat_band_witness_ratioG M H (phi (psi kk)) (k : ℤ) z
            (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
            (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))) ω -
          Vrat ω) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) atTop (𝓝 0) := by
  classical
  obtain ⟨q, delta0, K, hq1, hq2, hq3, hdelta0, hK, hM⟩ :=
    Paper.lem_prefix_limit d hd I Pc Xc W Sf Dd Cresp hCresp s sigma eps hs hsigma heps
      (aux_gcat_prefix_limits_T d) (aux_gcat_prefix_limits_offset d gH)
      (aux_gcat_prefix_limits_shift d gH) ({p} : Finset ℝ)
      (fun p' hp' => by rw [Finset.mem_singleton.mp hp']; exact hp)
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hMd Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim k z phi hphi
  obtain ⟨hRefPos, h12q, hPosAll⟩ := hM M hMd Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim
    (fun n => zpow_pos (by norm_num : (0 : ℝ) < 3) (-n))
  obtain ⟨psi, hpsi, Vlim, hVm, hVmom, hvalmom, hLpConv, hPrefix⟩ :=
    hPosAll Unit (fun _ => (k : ℤ)) (fun _ => z) phi hphi
  have hmem : p ∈ insert (1 : ℝ) ({p} : Finset ℝ) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self p)
  refine ⟨psi, hpsi,
    fun U => Vlim () 0 (Sum.inr ((aux_gcat_prefix_limits_equiv d) (Sum.inl U), Sum.inl 0)),
    fun U => Vlim () 0 (Sum.inr ((aux_gcat_prefix_limits_equiv d) (Sum.inl U), Sum.inl 1)),
    Vlim () 0 (Sum.inr ((aux_gcat_prefix_limits_equiv d) (Sum.inr ()), Sum.inr (Sum.inr 0))),
    Vlim () 0 (Sum.inr ((aux_gcat_prefix_limits_equiv d) (Sum.inr ()), Sum.inr (Sum.inr 1))),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U; exact (hVmom p hmem () 0 _).1
  · intro U; exact (hVmom p hmem () 0 _).1
  · exact (hVmom p hmem () 0 _).1
  · exact (hVmom p hmem () 0 _).1
  · intro N U; exact (hvalmom p hmem N () 0 (Sum.inr ((aux_gcat_prefix_limits_equiv d) (Sum.inl U), Sum.inl 0))).1
  · intro N U; exact (hvalmom p hmem N () 0 (Sum.inr ((aux_gcat_prefix_limits_equiv d) (Sum.inl U), Sum.inl 1))).1
  · intro N; exact (hvalmom p hmem N () 0 (Sum.inr ((aux_gcat_prefix_limits_equiv d) (Sum.inr ()), Sum.inr (Sum.inr 0)))).1
  · intro N; exact (hvalmom p hmem N () 0 (Sum.inr ((aux_gcat_prefix_limits_equiv d) (Sum.inr ()), Sum.inr (Sum.inr 1)))).1
  · intro U; exact hLpConv p hmem () 0 (Sum.inr ((aux_gcat_prefix_limits_equiv d) (Sum.inl U), Sum.inl 0))
  · intro U; exact hLpConv p hmem () 0 (Sum.inr ((aux_gcat_prefix_limits_equiv d) (Sum.inl U), Sum.inl 1))
  · exact hLpConv p hmem () 0 (Sum.inr ((aux_gcat_prefix_limits_equiv d) (Sum.inr ()), Sum.inr (Sum.inr 0)))
  · exact hLpConv p hmem () 0 (Sum.inr ((aux_gcat_prefix_limits_equiv d) (Sum.inr ()), Sum.inr (Sum.inr 1)))

/-- Smallness of the unit-cell `lam` deviation. -/
theorem aux_gcat_band_witness_small_lam_unit
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Pc : Paper.in_poincare d hd I) (Xc : Paper.in_extension d hd I)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (Dd : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℝ, 1 ≤ p → ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 ≤ C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ K : ℕ,
        eLpNorm (fun omega => aux_lem_band_U2_lamF sigma (aux_lem_band_U2_unitChart I M H omega K) - 1)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C * M.delta ^ c) := by
  obtain ⟨a, c, ha, hc, w', hw', hcore⟩ := aux_lem_band_U2_invlam_core d hd I Pc Xc W Sf Dd Cresp hCresp
    sigma hsigma
  refine ⟨c, hc, fun p hp => ?_⟩
  obtain ⟨δ1, C1, hδ1, hC1, hcore'⟩ := hcore (2 * p) (by linarith)
  obtain ⟨δ2, C2, hδ2, hC2, hmom⟩ := aux_lem_band_U2_lamF_moment d hd I Pc Xc W Sf Dd Cresp hCresp
    sigma hsigma (2 * p) (by linarith)
  refine ⟨min δ1 δ2, C2 * C1, lt_min hδ1 hδ2, by positivity, ?_⟩
  intro M hM Rm hRm Sreg It H hH K
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  obtain ⟨hTm, hTdev, -⟩ := hcore' M (hM.trans (min_le_left _ _)) Rm hRm Sreg It H hH K
  have hB0 := hmom M (hM.trans (min_le_right _ _)) Rm hRm Sreg It H hH K
  have hlampos : ∀ omega, 0 < aux_lem_band_U2_lamF sigma (aux_lem_band_U2_unitChart I M H omega K) := by
    intro omega
    have := I.lam_pos 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1
      sigma 2
    rwa [aux_lem_band_U2_lam_eq I 0 1 one_pos _ sigma hsigma] at this
  have hp0 : (1 : ℝ) ≤ p := hp
  have hG : AEStronglyMeasurable (fun omega =>
      aux_lem_band_U2_lamF sigma (aux_lem_band_U2_unitChart I M H omega K)) (chaosSampleLaw M).toMeasure := by
    have := hTm.aemeasurable.inv
    have h2 : (fun omega => aux_lem_band_U2_lamF sigma (aux_lem_band_U2_unitChart I M H omega K)) =
        fun omega => ((aux_lem_band_U2_lamF sigma (aux_lem_band_U2_unitChart I M H omega K))⁻¹)⁻¹ := by
      funext omega; rw [inv_inv]
    rw [h2]
    exact this.aestronglyMeasurable
  have hD : AEStronglyMeasurable (fun omega =>
      (aux_lem_band_U2_lamF sigma (aux_lem_band_U2_unitChart I M H omega K))⁻¹ - 1)
      (chaosSampleLaw M).toMeasure := hTm.sub aestronglyMeasurable_const
  have hprod := aux_lem_band_U2_holder2 (chaosSampleLaw M).toMeasure p hp0
    (fun omega => -aux_lem_band_U2_lamF sigma (aux_lem_band_U2_unitChart I M H omega K))
    (fun omega => (aux_lem_band_U2_lamF sigma (aux_lem_band_U2_unitChart I M H omega K))⁻¹ - 1)
    hG.neg hD
  have heq : (fun omega => aux_lem_band_U2_lamF sigma (aux_lem_band_U2_unitChart I M H omega K) - 1) =
      fun omega => (-aux_lem_band_U2_lamF sigma (aux_lem_band_U2_unitChart I M H omega K)) *
        ((aux_lem_band_U2_lamF sigma (aux_lem_band_U2_unitChart I M H omega K))⁻¹ - 1) := by
    funext omega
    have hne := (hlampos omega).ne'
    field_simp
    ring
  rw [heq]
  refine hprod.trans ?_
  have h1 : eLpNorm (fun omega =>
      -aux_lem_band_U2_lamF sigma (aux_lem_band_U2_unitChart I M H omega K))
      (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C2 := by
    have hneg : (fun omega => -aux_lem_band_U2_lamF sigma (aux_lem_band_U2_unitChart I M H omega K)) =
        -(fun omega => aux_lem_band_U2_lamF sigma (aux_lem_band_U2_unitChart I M H omega K)) := rfl
    rw [hneg, eLpNorm_neg]; exact hB0
  calc _ ≤ ENNReal.ofReal C2 * ENNReal.ofReal (C1 * M.delta ^ c) := mul_le_mul' h1 hTdev
    _ = ENNReal.ofReal (C2 * (C1 * M.delta ^ c)) := (ENNReal.ofReal_mul hC2).symm
    _ = ENNReal.ofReal (C2 * C1 * M.delta ^ c) := by rw [mul_assoc]


/-- Smallness of the unit-cell `Lam` deviation (the moment output of the aggregation step of `aux_lem_band_U2_Lam`). -/
theorem aux_gcat_band_witness_small_Lam_unit
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Pc : Paper.in_poincare d hd I) (Xc : Paper.in_extension d hd I)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (Dd : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℝ, 1 ≤ p → ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 ≤ C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ K : ℕ,
        eLpNorm (fun omega => aux_lem_band_U2_LamF sigma (aux_lem_band_U2_unitChart I M H omega K) - 1)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C * M.delta ^ c) := by
  obtain ⟨a, c, ha, hc, w', hw', hcell⟩ := aux_lem_band_U2_cell_bNorm d hd I Pc Xc W Sf Dd Cresp hCresp
  refine ⟨c, hc, fun p hp => ?_⟩
  have hs0 : 0 < sigma := hsigma.1
  have hpq : p ≤ max p (2 * (d : ℝ) / sigma) := le_max_left _ _
  have hq1 : 1 ≤ max p (2 * (d : ℝ) / sigma) := hp.trans hpq
  obtain ⟨δ0, C, hδ0, hC, hcell'⟩ := hcell (sigma / 2) (by linarith) _ hq1
  have hCβ := aux_lem_band_U2_Cbeta_pos sigma hs0
  refine ⟨δ0, (1 - (3 : ℝ) ^ (-(2 * sigma / 2)))⁻¹ * C, hδ0, by positivity, ?_⟩
  intro M hM Rm hRm Sreg It H hH K
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδc : 0 ≤ M.delta ^ c := Real.rpow_nonneg hδpos.le c
  have hLampos : ∀ omega, 0 < aux_lem_band_U2_LamF sigma (aux_lem_band_U2_unitChart I M H omega K) := by
    intro omega
    have := I.Lam_pos 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1
      sigma 2
    rwa [aux_lem_band_U2_Lam_eq I 0 1 one_pos _ sigma hsigma] at this
  have hsum : ∀ omega, Summable (fun k => Homogenization.Book.Ch02.geometricWeight sigma 2 k *
      (aux_lem_band_U2_D (d := d) k).sup' (aux_lem_band_U2_D_nonempty k)
        (fun R => Homogenization.Book.Ch02.coarseBMatrixNorm R
          (aux_lem_band_U2_unitChart I M H omega K))) := by
    intro omega
    by_contra hns
    have h0 := tsum_eq_zero_of_not_summable hns
    have h1 := aux_lem_band_U2_LamF_eq (d := d) sigma (aux_lem_band_U2_unitChart I M H omega K)
    rw [h0] at h1
    exact (hLampos omega).ne' h1
  have hsumE : Summable (fun k => Homogenization.Book.Ch02.geometricWeight sigma 2 k *
      (aux_lem_band_U2_D (d := d) k).sup' (aux_lem_band_U2_D_nonempty k) (fun _ => (1 : ℝ))) := by
    simp only [Finset.sup'_const, mul_one]; exact (aux_lem_band_U2_gw_tsum sigma hs0).summable
  have hTE : ∑' k, Homogenization.Book.Ch02.geometricWeight sigma 2 k *
      (aux_lem_band_U2_D (d := d) k).sup' (aux_lem_band_U2_D_nonempty k) (fun _ => (1 : ℝ)) = 1 := by
    simp only [Finset.sup'_const, mul_one]; exact (aux_lem_band_U2_gw_tsum sigma hs0).tsum_eq
  have hfun : (fun omega => aux_lem_band_U2_LamF sigma (aux_lem_band_U2_unitChart I M H omega K) - 1) =
      (fun omega => (∑' k, Homogenization.Book.Ch02.geometricWeight sigma 2 k *
        (aux_lem_band_U2_D (d := d) k).sup' (aux_lem_band_U2_D_nonempty k)
          (fun R => Homogenization.Book.Ch02.coarseBMatrixNorm R
            (aux_lem_band_U2_unitChart I M H omega K))) -
        ∑' k, Homogenization.Book.Ch02.geometricWeight sigma 2 k *
          (aux_lem_band_U2_D (d := d) k).sup' (aux_lem_band_U2_D_nonempty k) (fun _ => (1 : ℝ))) := by
    funext omega
    rw [aux_lem_band_U2_LamF_eq, hTE]
  obtain ⟨-, hmom, -⟩ := aux_lem_band_U2_agg (chaosSampleLaw M).toMeasure
      (aux_lem_band_U2_band d (-((w' * (0 + 1) : ℕ) : ℤ)) ((w' * (0 + 1) : ℕ) : ℤ))
      (aux_lem_band_U2_band_le_ambient _ _) (aux_lem_band_U2_D (d := d)) aux_lem_band_U2_D_nonempty (d : ℝ)
      (Nat.cast_nonneg d) aux_lem_band_U2_D_card (Homogenization.Book.Ch02.geometricWeight sigma 2)
      (2 * sigma) (by linarith) (aux_lem_band_U2_gw_nonneg sigma hs0.le) (aux_lem_band_U2_gw_le sigma hs0.le)
      (fun k R omega => Homogenization.Book.Ch02.coarseBMatrixNorm R
        (aux_lem_band_U2_unitChart I M H omega K)) (fun _ _ => (1 : ℝ))
      (fun k R hR => (hcell' M hM Rm hRm Sreg It H hH K k R hR).1) hsum hsumE
      p (max p (2 * (d : ℝ) / sigma)) (sigma / 2) hp hpq (by linarith)
      (aux_lem_band_U2_q_bound d p sigma hp hs0)
      (C * M.delta ^ c) 0
      (mul_nonneg hC hδc) le_rfl 0
      (fun k R hR => (hcell' M hM Rm hRm Sreg It H hH K k R hR).2.1)
      (fun k hk R hR => absurd hk (Nat.not_lt_zero k))
  rw [hfun]
  refine hmom.trans (le_of_eq ?_)
  congr 1
  ring

/-- `L^p` norm of a square root: `‖√T‖_p ≤ √ε` when `‖T‖_p ≤ ε`. -/
theorem aux_gcat_band_witness_sqrt_norm {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : Ω → ℝ) (hT : AEStronglyMeasurable T P) (hT0 : ∀ o, 0 ≤ T o)
    (p : ℝ) (hp : 1 ≤ p) (ε : ℝ) (hε : 0 ≤ ε)
    (hb : eLpNorm T (ENNReal.ofReal p) P ≤ ENNReal.ofReal ε) :
    eLpNorm (fun o => Real.sqrt (T o)) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Real.sqrt ε) := by
  have hp0 : 0 < p := by linarith
  have hpt : ∀ o, ‖Real.sqrt (T o)‖ ≤ ‖‖T o‖ ^ (1 / 2 : ℝ)‖ := by
    intro o
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), ← Real.sqrt_eq_rpow, abs_of_nonneg (hT0 o)]
  calc eLpNorm (fun o => Real.sqrt (T o)) (ENNReal.ofReal p) P
      ≤ eLpNorm (fun o => ‖T o‖ ^ (1 / 2 : ℝ)) (ENNReal.ofReal p) P := eLpNorm_mono hpt
    _ = eLpNorm T (ENNReal.ofReal p * ENNReal.ofReal (1 / 2)) P ^ (1 / 2 : ℝ) :=
        eLpNorm_norm_rpow _ (by norm_num)
    _ ≤ eLpNorm T (ENNReal.ofReal p) P ^ (1 / 2 : ℝ) := by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        refine eLpNorm_le_eLpNorm_of_exponent_le ?_ hT
        rw [← ENNReal.ofReal_mul hp0.le]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal ε ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hb (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt ε) := by
        rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hε (by norm_num)]

/-- Smallness of the unit-cell `err` (the moment output of the aggregation step of `aux_lem_band_U2_err`). -/
theorem aux_gcat_band_witness_small_err_unit
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Pc : Paper.in_poincare d hd I) (Xc : Paper.in_extension d hd I)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (Dd : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℝ, 1 ≤ p → ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 ≤ C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ K : ℕ,
        eLpNorm (fun omega => aux_lem_band_U2_errF s (aux_lem_band_U2_unitChart I M H omega K) 1)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C * M.delta ^ c) := by
  obtain ⟨a, c, ha, hc, w', hw', hcell⟩ := aux_lem_band_U2_cell_probe d hd I Pc Xc W Sf Dd Cresp hCresp
  have hs0 : 0 < s := hs.1
  refine ⟨c / 2, by positivity, fun p hp => ?_⟩
  have hpq : p ≤ max p (2 * (d : ℝ) / s) := le_max_left _ _
  have hq1 : 1 ≤ max p (2 * (d : ℝ) / s) := hp.trans hpq
  obtain ⟨δ0, C, hδ0, hC, hcell'⟩ := hcell (s / 2) (by linarith) _ hq1
  have hCβ := aux_lem_band_U2_Cbeta_pos s hs0
  refine ⟨δ0, Real.sqrt ((1 - (3 : ℝ) ^ (-(2 * s / 2)))⁻¹ * C), hδ0, Real.sqrt_nonneg _, ?_⟩
  intro M hM Rm hRm Sreg It H hH K
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδc : 0 ≤ M.delta ^ c := Real.rpow_nonneg hδpos.le c
  have hfin : ∀ omega, SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
      (Homogenization.originCube d 0) 0 s Homogenization.Book.Ch02.MultiscaleExponent.infinity 2
      (aux_lem_band_U2_unitChart I M H omega K) 1 < ⊤ := by
    intro omega
    have h := I.err_finite 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos)
      0 1 one_pos subset_rfl s hs 2 (by norm_num) 1 one_pos
    simpa using h
  have hsum : ∀ omega, Summable (fun k => Homogenization.Book.Ch02.geometricWeight s 2 k *
      (aux_lem_band_U2_D (d := d) k).sup' (aux_lem_band_U2_D_nonempty k)
        (fun R => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R
          (aux_lem_band_U2_unitChart I M H omega K) 1).toReal)) :=
    fun omega => (aux_lem_band_U2_errF_eq s hs0 _ (hfin omega)).1
  have hsumE : Summable (fun k => Homogenization.Book.Ch02.geometricWeight s 2 k *
      (aux_lem_band_U2_D (d := d) k).sup' (aux_lem_band_U2_D_nonempty k) (fun _ => (0 : ℝ))) := by
    simp only [Finset.sup'_const, mul_zero]; exact summable_zero
  have hTE : ∑' k, Homogenization.Book.Ch02.geometricWeight s 2 k *
      (aux_lem_band_U2_D (d := d) k).sup' (aux_lem_band_U2_D_nonempty k) (fun _ => (0 : ℝ)) = 0 := by
    simp only [Finset.sup'_const, mul_zero, tsum_zero]
  obtain ⟨hTm, hmom, -⟩ := aux_lem_band_U2_agg (chaosSampleLaw M).toMeasure
      (aux_lem_band_U2_band d (-((w' * (0 + 1) : ℕ) : ℤ)) ((w' * (0 + 1) : ℕ) : ℤ))
      (aux_lem_band_U2_band_le_ambient _ _) (aux_lem_band_U2_D (d := d)) aux_lem_band_U2_D_nonempty (d : ℝ)
      (Nat.cast_nonneg d) aux_lem_band_U2_D_card (Homogenization.Book.Ch02.geometricWeight s 2)
      (2 * s) (by linarith) (aux_lem_band_U2_gw_nonneg s hs0.le) (aux_lem_band_U2_gw_le s hs0.le)
      (fun k R omega => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R
        (aux_lem_band_U2_unitChart I M H omega K) 1).toReal) (fun _ _ => (0 : ℝ))
      (fun k R hR => (hcell' M hM Rm hRm Sreg It H hH K k R hR).1) hsum hsumE
      p (max p (2 * (d : ℝ) / s)) (s / 2) hp hpq (by linarith)
      (aux_lem_band_U2_q_bound d p s hp hs0)
      (C * M.delta ^ c) 0
      (mul_nonneg hC hδc) le_rfl 0
      (fun k R hR => by
        have := (hcell' M hM Rm hRm Sreg It H hH K k R hR).2.1
        simpa only [sub_zero] using this)
      (fun k hk R hR => absurd hk (Nat.not_lt_zero k))
  set T : BilateralField d → ℝ := fun omega => ∑' k, Homogenization.Book.Ch02.geometricWeight s 2 k *
      (aux_lem_band_U2_D (d := d) k).sup' (aux_lem_band_U2_D_nonempty k)
        (fun R => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R
          (aux_lem_band_U2_unitChart I M H omega K) 1).toReal) with hTdef
  have hT0 : ∀ omega, 0 ≤ T omega := by
    intro omega
    refine tsum_nonneg (fun k => mul_nonneg (aux_lem_band_U2_gw_nonneg s hs0.le k) ?_)
    obtain ⟨R, hR⟩ := aux_lem_band_U2_D_nonempty (d := d) k
    exact le_trans ENNReal.toReal_nonneg (Finset.le_sup' (fun R =>
      (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (aux_lem_band_U2_unitChart I M H omega K) 1).toReal) hR)
  have hTb : eLpNorm T (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((1 - (3 : ℝ) ^ (-(2 * s / 2)))⁻¹ * C * M.delta ^ c) := by
    have hfn : T = fun omega => T omega - (∑' k : ℕ, Homogenization.Book.Ch02.geometricWeight s 2 k *
        (aux_lem_band_U2_D (d := d) k).sup' (aux_lem_band_U2_D_nonempty k) (fun _ => (0 : ℝ))) := by
      funext omega; rw [hTE, sub_zero]
    rw [hfn]
    refine hmom.trans (le_of_eq ?_)
    congr 1
    ring
  have hfun : ∀ omega, aux_lem_band_U2_errF s (aux_lem_band_U2_unitChart I M H omega K) 1 = Real.sqrt (T omega) :=
    fun omega => (aux_lem_band_U2_errF_eq s hs0 _ (hfin omega)).2
  simp only [hfun]
  refine (aux_gcat_band_witness_sqrt_norm _ T hTm hT0 p hp _ (by positivity) hTb).trans
    (le_of_eq ?_)
  congr 1
  have h1 : 0 ≤ (1 - (3 : ℝ) ^ (-(2 * s / 2)))⁻¹ * C := by positivity
  have h2 : Real.sqrt (M.delta ^ c) = M.delta ^ (c / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hδpos.le]; ring_nf
  rw [Real.sqrt_mul h1, h2]

/-- `L^p` smallness of the constant `κ`-ratio factor of the reference ratio. -/
theorem aux_gcat_band_witness_kappa_ratio_dev
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M) (off : ℤ)
    (N : ℕ) (n : ℤ) (hnN : n ≤ (N : ℤ)) (hmN : n + off ≤ (N : ℤ)) :
    0 < aux_lem_band_U2_kappa M ((N : ℤ) - n).toNat / aux_lem_band_U2_kappa M ((N : ℤ) - (n + off)).toNat ∧
    aux_lem_band_U2_kappa M ((N : ℤ) - n).toNat / aux_lem_band_U2_kappa M ((N : ℤ) - (n + off)).toNat ≤
      Real.exp (3 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * |(off : ℝ)|) ∧
    |aux_lem_band_U2_kappa M ((N : ℤ) - n).toNat / aux_lem_band_U2_kappa M ((N : ℤ) - (n + off)).toNat - 1| ≤
      3 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * |(off : ℝ)| *
        Real.exp (3 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * |(off : ℝ)|) := by
  have hc : 0 < aux_lem_band_U2_kappa M ((N : ℤ) - n).toNat / aux_lem_band_U2_kappa M ((N : ℤ) - (n + off)).toNat :=
    div_pos (aux_lem_band_U2_kappa_pos M _) (aux_lem_band_U2_kappa_pos M _)
  have hoffabs : |(((n + off : ℤ)) : ℝ) - (n : ℝ)| = |(off : ℝ)| := by
    push_cast; ring_nf
  have hoffabs' : |(n : ℝ) - (((n + off : ℤ)) : ℝ)| = |(off : ℝ)| := by
    rw [abs_sub_comm]; exact hoffabs
  have hu := (aux_lem_band_piece_coords_K7_kappa_ratio_bounded M Rm n (n + off) N hnN hmN).2
  have hi := (aux_lem_band_piece_coords_K7_kappa_ratio_bounded M Rm (n + off) n N hmN hnN).2
  have hu' : aux_lem_band_U2_kappa M ((N : ℤ) - n).toNat / aux_lem_band_U2_kappa M ((N : ℤ) - (n + off)).toNat ≤
      Real.exp (3 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * |(off : ℝ)|) := by
    have h := hu
    simp only [hoffabs] at h
    exact h
  have hi' : (aux_lem_band_U2_kappa M ((N : ℤ) - n).toNat / aux_lem_band_U2_kappa M ((N : ℤ) - (n + off)).toNat)⁻¹ ≤
      Real.exp (3 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * |(off : ℝ)|) := by
    have h := hi
    simp only [hoffabs'] at h
    rw [inv_div]
    exact h
  refine ⟨hc, hu', ?_⟩
  have hlogu := (Real.log_le_iff_le_exp hc).mpr hu'
  have hlogi := (Real.log_le_iff_le_exp (inv_pos.mpr hc)).mpr hi'
  rw [Real.log_inv] at hlogi
  have hlog : |Real.log (aux_lem_band_U2_kappa M ((N : ℤ) - n).toNat /
      aux_lem_band_U2_kappa M ((N : ℤ) - (n + off)).toNat)| ≤
      3 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * |(off : ℝ)| := abs_le.mpr ⟨by linarith, hlogu⟩
  have h1 := aux_lem_band_ref_abs_exp_sub_one (Real.log (aux_lem_band_U2_kappa M ((N : ℤ) - n).toNat /
      aux_lem_band_U2_kappa M ((N : ℤ) - (n + off)).toNat))
  rw [Real.exp_log hc] at h1
  refine h1.trans ?_
  exact mul_le_mul hlog (Real.exp_le_exp.mpr hlog) (Real.exp_pos _).le
    (le_trans (abs_nonneg _) hlog)

/-- Smallness of the reference ratio coordinate `ref(n,z)/ref(n+off, z + 3^{-n} sh) - 1`. -/
theorem aux_gcat_band_witness_small_ratio
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (off : ℤ) (sh : SpatialCoordinates d) :
    ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ 1 →
      ∀ (Rm : Paper.in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (N : ℕ) (n : ℤ) (z : SpatialCoordinates d), n ≤ (N : ℤ) → n + off ≤ (N : ℤ) →
        eLpNorm (fun omega => aux_gcat_band_witness_ratioG M H N n z off sh omega - 1)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C * M.delta) := by
  intro p hp
  have hp0 : 0 < p := by linarith
  obtain ⟨w0, hw0pos, hw0off, hw0growth⟩ := aux_lem_band_piece_coords_K7_tail_w0 off sh
  obtain ⟨B, hB, hSg⟩ := aux_lem_band_K7_full_log_orlicz off sh w0 hw0pos hw0off
    (by simpa using hw0growth 1 le_rfl)
  obtain ⟨Co, hCo, hdiff⟩ := aux_lem_band_orlicz_exp_difference
  let Dp : ℝ → ℝ := fun u => (2 * Real.exp ((4 * p) ^ 2 * u ^ 2 / 4)) ^ (1 / (4 * p))
  let K : ℝ := Co * B * Real.sqrt (2 * p) * Dp 1 * Dp B
  let A0 : ℝ := 3 * (Real.log 2 / 2) * |(off : ℝ)|
  have hK : 0 ≤ K := by dsimp only [K, Dp]; positivity
  have hA0 : 0 ≤ A0 := by dsimp only [A0]; have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  refine ⟨Real.exp A0 * K + A0 * Real.exp A0, by positivity, ?_⟩
  intro M hM Rm H hH N n z hnN hmN
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  let μ := (chaosSampleLaw M).toMeasure
  let w : SpatialCoordinates d := z + ((3 : ℝ) ^ (-n)) • sh
  let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
    fun k y omega => if 0 ≤ k then ∑ j ∈ Finset.Ico (0 : ℤ) k, omega (-j) y
      else -∑ j ∈ Finset.Ico k (0 : ℤ), omega (-j) y
  have hr : retained = fun k y omega => if 0 ≤ k then ∑ j ∈ Finset.Ico (0 : ℤ) k, omega (-j) y
      else -∑ j ∈ Finset.Ico k (0 : ℤ), omega (-j) y := rfl
  let X : BilateralField d → ℝ := fun omega =>
    H omega z + retained n z omega - (H omega w + retained (n + off) w omega)
  have hXm : Measurable X :=
    (((continuous_eval_const z).measurable.comp hH.1).add
      (aux_lem_band_K7_retained_meas retained hr n z)).sub
      (((continuous_eval_const w).measurable.comp hH.1).add
        (aux_lem_band_K7_retained_meas retained hr (n + off) w))
  have hXg : (∫⁻ omega, ENNReal.ofReal (Real.exp ((|-X omega| / (B * M.delta)) ^ 2)) ∂μ) ≤ 2 := by
    simpa only [abs_neg] using hSg M H hH retained hr n z
  have hσ : (0 : ℝ) < 1 := one_pos
  have hτ : 0 < B * M.delta := mul_pos hB hδpos
  have hτA : B * M.delta ≤ B := mul_le_of_le_one_right hB.le hM
  have hS0 : (∫⁻ omega : BilateralField d, ENNReal.ofReal (Real.exp ((|(fun _ : BilateralField d => (0 : ℝ)) omega| / 1) ^ 2)) ∂μ) ≤ 2 := by
    simp
  have hmain := hdiff μ (fun _ => (0 : ℝ)) (fun omega => -X omega) measurable_const hXm.neg
    1 (B * M.delta) 1 B p hσ hτ le_rfl hτA hp hS0 hXg
  have hfun0 : (fun omega => Real.exp ((fun _ : BilateralField d => (0 : ℝ)) omega) -
      Real.exp ((fun _ : BilateralField d => (0 : ℝ)) omega - (fun omega => -X omega) omega)) =
      fun omega => -(Real.exp (X omega) - 1) := by
    funext omega; simp
  have hneg : (fun omega => -(Real.exp (X omega) - 1)) = -(fun omega => Real.exp (X omega) - 1) := rfl
  rw [hfun0, hneg, eLpNorm_neg] at hmain
  have hexpb : eLpNorm (fun omega => Real.exp (X omega) - 1) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (K * M.delta) := by
    refine hmain.trans (le_of_eq ?_)
    congr 1
    dsimp only [K, Dp]
    ring
  -- the constant `κ`-ratio factor
  obtain ⟨hc0, hc1, hc2⟩ := aux_gcat_band_witness_kappa_ratio_dev d M Rm off N n hnN hmN
  set c : ℝ := aux_lem_band_U2_kappa M ((N : ℤ) - n).toNat /
    aux_lem_band_U2_kappa M ((N : ℤ) - (n + off)).toNat with hcdef
  have htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (Real.log 2 / 2) * M.delta ^ 2 :=
    SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M
  have hδ2 : M.delta ^ 2 ≤ M.delta := by nlinarith
  have hδ2' : M.delta ^ 2 ≤ 1 := by nlinarith
  have hexpA : 3 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * |(off : ℝ)| ≤ A0 * M.delta := by
    dsimp only [A0]
    have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have h1 : 3 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * |(off : ℝ)| ≤
        3 * ((Real.log 2 / 2) * M.delta ^ 2) * |(off : ℝ)| := by
      gcongr
    refine h1.trans ?_
    have h2 : 3 * ((Real.log 2 / 2) * M.delta ^ 2) * |(off : ℝ)| =
        (3 * (Real.log 2 / 2) * |(off : ℝ)|) * M.delta ^ 2 := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left hδ2 (by positivity)
  have hexpA0 : 3 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * |(off : ℝ)| ≤ A0 := by
    refine hexpA.trans ?_
    exact mul_le_of_le_one_right hA0 hM
  have hcle : c ≤ Real.exp A0 := hc1.trans (Real.exp_le_exp.mpr hexpA0)
  have hcdev : |c - 1| ≤ A0 * Real.exp A0 * M.delta := by
    refine hc2.trans ?_
    have h3 : 3 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * |(off : ℝ)| *
        Real.exp (3 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * |(off : ℝ)|) ≤ A0 * M.delta * Real.exp A0 :=
      mul_le_mul hexpA (Real.exp_le_exp.mpr hexpA0) (Real.exp_pos _).le (by positivity)
    refine h3.trans (le_of_eq ?_)
    ring
  -- the pointwise identity
  have hident : ∀ omega, aux_gcat_band_witness_ratioG M H N n z off sh omega - 1 =
      c * (Real.exp (X omega) - 1) + (c - 1) := by
    intro omega
    have hg : n ≤ (N : ℤ) ∧ n + off ≤ (N : ℤ) := ⟨hnN, hmN⟩
    have h1 := aux_lem_band_piece_coords_K7_value_ref_ratio_eq M H n (n + off) z w N hnN hmN omega
    unfold aux_gcat_band_witness_ratioG
    rw [if_pos hg]
    have h2 : aux_lem_band_U2_reference M H N n z omega / aux_lem_band_U2_reference M H N (n + off) w omega =
        c * Real.exp (X omega) := h1
    rw [h2]
    ring
  have hfunEq : (fun omega => aux_gcat_band_witness_ratioG M H N n z off sh omega - 1) =
      fun omega => c * (Real.exp (X omega) - 1) + (c - 1) := funext hident
  have hexpm : AEStronglyMeasurable (fun omega => Real.exp (X omega) - 1) μ :=
    (hXm.exp.sub measurable_const).aestronglyMeasurable
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  rw [hfunEq]
  calc eLpNorm (fun omega => c * (Real.exp (X omega) - 1) + (c - 1)) (ENNReal.ofReal p) μ
      ≤ eLpNorm (fun omega => c * (Real.exp (X omega) - 1)) (ENNReal.ofReal p) μ +
        eLpNorm (fun _ : BilateralField d => c - 1) (ENNReal.ofReal p) μ :=
        eLpNorm_add_le (hexpm.const_mul c) aestronglyMeasurable_const hp1
    _ ≤ ENNReal.ofReal (c * (K * M.delta)) + ENNReal.ofReal |c - 1| := by
        refine add_le_add ?_ (le_of_eq ?_)
        · rw [aux_lem_band_U2_eLpNorm_cmul, abs_of_pos hc0, ENNReal.ofReal_mul hc0.le]
          exact mul_le_mul' le_rfl hexpb
        · rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr hp0).ne' (NeZero.ne μ)]
          simp [Real.enorm_eq_ofReal_abs, μ]
    _ ≤ ENNReal.ofReal ((Real.exp A0 * K + A0 * Real.exp A0) * M.delta) := by
        rw [← ENNReal.ofReal_add (by positivity) (abs_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h4 : c * (K * M.delta) ≤ Real.exp A0 * (K * M.delta) :=
          mul_le_mul_of_nonneg_right hcle (by positivity)
        nlinarith [hcdev]

/-- Smallness of the `lo` coordinate `lam/ref - 1` of an arbitrary catalogue entry `(off, sh)`, uniformly in the
cell (transport of the unit-chart smallness by the chart identity and the shift invariance of the law). -/
theorem aux_gcat_band_witness_small_lo
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Pc : Paper.in_poincare d hd I) (Xc : Paper.in_extension d hd I)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (Dd : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℝ, 1 ≤ p → ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 ≤ C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (N : ℕ) (n : ℤ) (z : SpatialCoordinates d) (off : ℤ) (sh : SpatialCoordinates d),
        n ≤ (N : ℤ) → n + off ≤ (N : ℤ) →
        eLpNorm (fun omega => aux_gcat_band_witness_loG I M H sigma N n z off sh omega - 1)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C * M.delta ^ c) := by
  obtain ⟨c, hc, hU⟩ := aux_gcat_band_witness_small_lam_unit d hd I Pc Xc W Sf Dd Cresp hCresp sigma hsigma
  refine ⟨c, hc, fun p hp => ?_⟩
  obtain ⟨delta0, C, hδ0, hC, hU'⟩ := hU p hp
  refine ⟨delta0, C, hδ0, hC, ?_⟩
  intro M hM Rm hRm Sreg It H hH N n z off sh hnN hmN
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(n + off)) := zpow_pos (by norm_num) _
  have hT4 := aux_lem_band_U2_T4_chart_identity I M H hH N (n + off) hmN
    (z + ((3 : ℝ) ^ (-n)) • sh) hpos
  have hae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      aux_gcat_band_witness_loG I M H sigma N n z off sh omega - 1 =
        (fun omega' => aux_lem_band_U2_lamF sigma
          (aux_lem_band_U2_unitChart I M H omega' ((N : ℤ) - (n + off)).toNat) - 1)
          (aux_lem_band_U2_shift (n + off) (z + ((3 : ℝ) ^ (-n)) • sh) omega) := by
    filter_upwards [hT4] with omega homega
    have hpos' := aux_lem_band_U2_reference_pos M H N (n + off) (z + ((3 : ℝ) ^ (-n)) • sh) omega
    have hsc := aux_lem_band_U2_lamF_scaled sigma _ hpos' _ _ homega
    unfold aux_gcat_band_witness_loG
    rw [if_pos ⟨hnN, hmN⟩]
    show I.lam (z + ((3 : ℝ) ^ (-n)) • sh) ((3 : ℝ) ^ (-(n + off))) hpos
        (Lane4.cutoffPositiveCoefficient M H omega N (z + ((3 : ℝ) ^ (-n)) • sh) hpos)
        (z + ((3 : ℝ) ^ (-n)) • sh) ((3 : ℝ) ^ (-(n + off))) sigma 2 /
        aux_lem_band_U2_reference M H N (n + off) (z + ((3 : ℝ) ^ (-n)) • sh) omega - 1 = _
    rw [aux_lem_band_U2_lam_eq I _ _ hpos _ sigma hsigma, hsc, mul_div_cancel_left₀ _ hpos'.ne']
  rw [eLpNorm_congr_ae hae, aux_lem_band_U2_eLpNorm_comp_shift M (n + off)
    (z + ((3 : ℝ) ^ (-n)) • sh) (fun omega' => aux_lem_band_U2_lamF sigma
      (aux_lem_band_U2_unitChart I M H omega' ((N : ℤ) - (n + off)).toNat) - 1)]
  exact hU' M hM Rm hRm Sreg It H hH _

/-- Smallness of the `hi` coordinate `Lam/ref - 1`. -/
theorem aux_gcat_band_witness_small_hi
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Pc : Paper.in_poincare d hd I) (Xc : Paper.in_extension d hd I)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (Dd : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℝ, 1 ≤ p → ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 ≤ C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (N : ℕ) (n : ℤ) (z : SpatialCoordinates d) (off : ℤ) (sh : SpatialCoordinates d),
        n ≤ (N : ℤ) → n + off ≤ (N : ℤ) →
        eLpNorm (fun omega => aux_gcat_band_witness_hiG I M H sigma N n z off sh omega - 1)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C * M.delta ^ c) := by
  obtain ⟨c, hc, hU⟩ := aux_gcat_band_witness_small_Lam_unit d hd I Pc Xc W Sf Dd Cresp hCresp sigma hsigma
  refine ⟨c, hc, fun p hp => ?_⟩
  obtain ⟨delta0, C, hδ0, hC, hU'⟩ := hU p hp
  refine ⟨delta0, C, hδ0, hC, ?_⟩
  intro M hM Rm hRm Sreg It H hH N n z off sh hnN hmN
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(n + off)) := zpow_pos (by norm_num) _
  have hT4 := aux_lem_band_U2_T4_chart_identity I M H hH N (n + off) hmN
    (z + ((3 : ℝ) ^ (-n)) • sh) hpos
  have hae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      aux_gcat_band_witness_hiG I M H sigma N n z off sh omega - 1 =
        (fun omega' => aux_lem_band_U2_LamF sigma
          (aux_lem_band_U2_unitChart I M H omega' ((N : ℤ) - (n + off)).toNat) - 1)
          (aux_lem_band_U2_shift (n + off) (z + ((3 : ℝ) ^ (-n)) • sh) omega) := by
    filter_upwards [hT4] with omega homega
    have hpos' := aux_lem_band_U2_reference_pos M H N (n + off) (z + ((3 : ℝ) ^ (-n)) • sh) omega
    have hsc := aux_lem_band_U2_LamF_scaled sigma _ hpos' _ _ homega
    unfold aux_gcat_band_witness_hiG
    rw [if_pos ⟨hnN, hmN⟩]
    show I.Lam (z + ((3 : ℝ) ^ (-n)) • sh) ((3 : ℝ) ^ (-(n + off))) hpos
        (Lane4.cutoffPositiveCoefficient M H omega N (z + ((3 : ℝ) ^ (-n)) • sh) hpos)
        (z + ((3 : ℝ) ^ (-n)) • sh) ((3 : ℝ) ^ (-(n + off))) sigma 2 /
        aux_lem_band_U2_reference M H N (n + off) (z + ((3 : ℝ) ^ (-n)) • sh) omega - 1 = _
    rw [aux_lem_band_U2_Lam_eq I _ _ hpos _ sigma hsigma, hsc, mul_div_cancel_left₀ _ hpos'.ne']
  rw [eLpNorm_congr_ae hae, aux_lem_band_U2_eLpNorm_comp_shift M (n + off)
    (z + ((3 : ℝ) ^ (-n)) • sh) (fun omega' => aux_lem_band_U2_LamF sigma
      (aux_lem_band_U2_unitChart I M H omega' ((N : ℤ) - (n + off)).toNat) - 1)]
  exact hU' M hM Rm hRm Sreg It H hH _

/-- Smallness of the `err` coordinate. -/
theorem aux_gcat_band_witness_small_err
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Pc : Paper.in_poincare d hd I) (Xc : Paper.in_extension d hd I)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (Dd : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℝ, 1 ≤ p → ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 ≤ C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (N : ℕ) (n : ℤ) (z : SpatialCoordinates d) (off : ℤ) (sh : SpatialCoordinates d),
        n ≤ (N : ℤ) → n + off ≤ (N : ℤ) →
        eLpNorm (fun omega => aux_gcat_band_witness_errG I M H s N n z off sh omega)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C * M.delta ^ c) := by
  obtain ⟨c, hc, hU⟩ := aux_gcat_band_witness_small_err_unit d hd I Pc Xc W Sf Dd Cresp hCresp s hs
  refine ⟨c, hc, fun p hp => ?_⟩
  obtain ⟨delta0, C, hδ0, hC, hU'⟩ := hU p hp
  refine ⟨delta0, C, hδ0, hC, ?_⟩
  intro M hM Rm hRm Sreg It H hH N n z off sh hnN hmN
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(n + off)) := zpow_pos (by norm_num) _
  have hT4 := aux_lem_band_U2_T4_chart_identity I M H hH N (n + off) hmN
    (z + ((3 : ℝ) ^ (-n)) • sh) hpos
  have hae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      aux_gcat_band_witness_errG I M H s N n z off sh omega =
        (fun omega' => aux_lem_band_U2_errF s
          (aux_lem_band_U2_unitChart I M H omega' ((N : ℤ) - (n + off)).toNat) 1)
          (aux_lem_band_U2_shift (n + off) (z + ((3 : ℝ) ^ (-n)) • sh) omega) := by
    filter_upwards [hT4] with omega homega
    have hpos' := aux_lem_band_U2_reference_pos M H N (n + off) (z + ((3 : ℝ) ^ (-n)) • sh) omega
    have hsc := aux_lem_band_U2_errF_scaled s _ hpos' _ _ homega
    unfold aux_gcat_band_witness_errG
    rw [if_pos ⟨hnN, hmN⟩]
    show I.err (z + ((3 : ℝ) ^ (-n)) • sh) ((3 : ℝ) ^ (-(n + off))) hpos
        (Lane4.cutoffPositiveCoefficient M H omega N (z + ((3 : ℝ) ^ (-n)) • sh) hpos)
        (z + ((3 : ℝ) ^ (-n)) • sh) ((3 : ℝ) ^ (-(n + off)))
        (aux_lem_band_U2_reference M H N (n + off) (z + ((3 : ℝ) ^ (-n)) • sh) omega) s 2 = _
    rw [aux_lem_band_U2_err_eq I _ _ hpos _ _ hpos' s hs, hsc]
  rw [eLpNorm_congr_ae hae, aux_lem_band_U2_eLpNorm_comp_shift M (n + off)
    (z + ((3 : ℝ) ^ (-n)) • sh) (fun omega' => aux_lem_band_U2_errF s
      (aux_lem_band_U2_unitChart I M H omega' ((N : ℤ) - (n + off)).toNat) 1)]
  exact hU' M hM Rm hRm Sreg It H hH _

/-- Weighted sum of the moduli of the four coordinate families of the test statistic. -/
def aux_gcat_band_witness_Sum4 {Ω : Type*} {d : ℕ} (wl wh we wr : ℝ)
    (x y : aux_gcat_band_witness_Roots d → Ω → ℝ) (u v : Ω → ℝ) : Ω → ℝ :=
  fun ω => (∑ U : aux_gcat_band_witness_Roots d, (wl * |x U ω| + wh * |y U ω|)) +
    we * |u ω| + wr * |v ω|

theorem aux_gcat_band_witness_eLpNorm_wabs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (q : ENNReal) (w : ℝ) (hw : 0 ≤ w) (f : Ω → ℝ) :
    eLpNorm (fun ω => w * |f ω|) q P = ENNReal.ofReal w * eLpNorm f q P := by
  rw [aux_lem_band_U2_eLpNorm_cmul, abs_of_nonneg hw]
  congr 1
  have : (fun ω => |f ω|) = fun ω => ‖f ω‖ := by funext ω; rw [Real.norm_eq_abs]
  rw [this, eLpNorm_norm]

theorem aux_gcat_band_witness_Sum4_norm_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (p : ℝ) (hp : 1 ≤ p) (wl wh we wr : ℝ) (hwl : 0 ≤ wl) (hwh : 0 ≤ wh) (hwe : 0 ≤ we) (hwr : 0 ≤ wr)
    (x y : aux_gcat_band_witness_Roots d → Ω → ℝ) (u v : Ω → ℝ)
    (hx : ∀ U, AEStronglyMeasurable (x U) P) (hy : ∀ U, AEStronglyMeasurable (y U) P)
    (hu : AEStronglyMeasurable u P) (hv : AEStronglyMeasurable v P) :
    eLpNorm (aux_gcat_band_witness_Sum4 wl wh we wr x y u v) (ENNReal.ofReal p) P ≤
      (∑ U : aux_gcat_band_witness_Roots d,
        (ENNReal.ofReal wl * eLpNorm (x U) (ENNReal.ofReal p) P +
          ENNReal.ofReal wh * eLpNorm (y U) (ENNReal.ofReal p) P)) +
      ENNReal.ofReal we * eLpNorm u (ENNReal.ofReal p) P +
      ENNReal.ofReal wr * eLpNorm v (ENNReal.ofReal p) P := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  have hxm : ∀ U, AEStronglyMeasurable (fun ω => wl * |x U ω|) P :=
    fun U => (hx U).norm.const_mul wl
  have hym : ∀ U, AEStronglyMeasurable (fun ω => wh * |y U ω|) P :=
    fun U => (hy U).norm.const_mul wh
  have hterm : ∀ U : aux_gcat_band_witness_Roots d,
      AEStronglyMeasurable (fun ω => wl * |x U ω| + wh * |y U ω|) P :=
    fun U => (hxm U).add (hym U)
  have hsumm : AEStronglyMeasurable (fun ω => ∑ U : aux_gcat_band_witness_Roots d,
      (wl * |x U ω| + wh * |y U ω|)) P := by
    have := Finset.aestronglyMeasurable_sum Finset.univ (fun U _ => hterm U)
    rwa [Finset.sum_fn] at this
  have e : aux_gcat_band_witness_Sum4 wl wh we wr x y u v =
      (fun ω => ∑ U : aux_gcat_band_witness_Roots d, (wl * |x U ω| + wh * |y U ω|)) +
        (fun ω => we * |u ω|) + (fun ω => wr * |v ω|) := by
    funext ω; simp [aux_gcat_band_witness_Sum4]
  rw [e]
  have hum : AEStronglyMeasurable (fun ω => we * |u ω|) P := hu.norm.const_mul we
  have hvm : AEStronglyMeasurable (fun ω => wr * |v ω|) P := hv.norm.const_mul wr
  refine (eLpNorm_add_le (hsumm.add hum) hvm hp1).trans ?_
  refine add_le_add ((eLpNorm_add_le hsumm hum hp1).trans ?_) (le_of_eq ?_)
  · refine add_le_add ?_ (le_of_eq ?_)
    · have hs : (fun ω => ∑ U : aux_gcat_band_witness_Roots d, (wl * |x U ω| + wh * |y U ω|)) =
          ∑ U : aux_gcat_band_witness_Roots d, (fun ω => wl * |x U ω| + wh * |y U ω|) := by
        funext ω; simp [Finset.sum_apply]
      rw [hs]
      refine (eLpNorm_sum_le (fun U _ => hterm U) hp1).trans (Finset.sum_le_sum (fun U _ => ?_))
      refine (eLpNorm_add_le (hxm U) (hym U) hp1).trans (le_of_eq ?_)
      rw [aux_gcat_band_witness_eLpNorm_wabs P _ wl hwl, aux_gcat_band_witness_eLpNorm_wabs P _ wh hwh]
    · exact aux_gcat_band_witness_eLpNorm_wabs P _ we hwe u
  · exact aux_gcat_band_witness_eLpNorm_wabs P _ wr hwr v

/-- Pointwise: `Sum4` is 1-Lipschitz-like in the coordinate families. -/
theorem aux_gcat_band_witness_Sum4_diff_le {Ω : Type*} {d : ℕ} (wl wh we wr : ℝ)
    (hwl : 0 ≤ wl) (hwh : 0 ≤ wh) (hwe : 0 ≤ we) (hwr : 0 ≤ wr)
    (x y x' y' : aux_gcat_band_witness_Roots d → Ω → ℝ) (u v u' v' : Ω → ℝ) (ω : Ω) :
    |aux_gcat_band_witness_Sum4 wl wh we wr x y u v ω - aux_gcat_band_witness_Sum4 wl wh we wr x' y' u' v' ω| ≤
      aux_gcat_band_witness_Sum4 wl wh we wr (fun U ω => x U ω - x' U ω) (fun U ω => y U ω - y' U ω)
        (fun ω => u ω - u' ω) (fun ω => v ω - v' ω) ω := by
  have habs : ∀ a b : ℝ, |(|a| - |b|)| ≤ |a - b| := fun a b => abs_abs_sub_abs_le_abs_sub a b
  unfold aux_gcat_band_witness_Sum4
  have hU : ∀ U : aux_gcat_band_witness_Roots d,
      |(wl * |x U ω| + wh * |y U ω|) - (wl * |x' U ω| + wh * |y' U ω|)| ≤
        wl * |x U ω - x' U ω| + wh * |y U ω - y' U ω| := by
    intro U
    have e : (wl * |x U ω| + wh * |y U ω|) - (wl * |x' U ω| + wh * |y' U ω|) =
        wl * (|x U ω| - |x' U ω|) + wh * (|y U ω| - |y' U ω|) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hwl]
      exact mul_le_mul_of_nonneg_left (habs _ _) hwl
    · rw [abs_mul, abs_of_nonneg hwh]
      exact mul_le_mul_of_nonneg_left (habs _ _) hwh
  have hsum : |(∑ U : aux_gcat_band_witness_Roots d, (wl * |x U ω| + wh * |y U ω|)) -
      (∑ U : aux_gcat_band_witness_Roots d, (wl * |x' U ω| + wh * |y' U ω|))| ≤
      ∑ U : aux_gcat_band_witness_Roots d, (wl * |x U ω - x' U ω| + wh * |y U ω - y' U ω|) := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun U _ => hU U))
  have hu : abs (we * |u ω| - we * |u' ω|) ≤ we * |u ω - u' ω| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hwe]
    exact mul_le_mul_of_nonneg_left (habs _ _) hwe
  have hv : abs (wr * |v ω| - wr * |v' ω|) ≤ wr * |v ω - v' ω| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hwr]
    exact mul_le_mul_of_nonneg_left (habs _ _) hwr
  set SX := ∑ U : aux_gcat_band_witness_Roots d, (wl * |x U ω| + wh * |y U ω|)
  set SY := ∑ U : aux_gcat_band_witness_Roots d, (wl * |x' U ω| + wh * |y' U ω|)
  have e : SX + we * |u ω| + wr * |v ω| - (SY + we * |u' ω| + wr * |v' ω|) =
      (SX - SY) + (we * |u ω| - we * |u' ω|) + (wr * |v ω| - wr * |v' ω|) := by ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hsum hu)) hv)

theorem aux_gcat_band_witness_Sum4_memLp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (q : ENNReal) (wl wh we wr : ℝ)
    (x y : aux_gcat_band_witness_Roots d → Ω → ℝ) (u v : Ω → ℝ)
    (hx : ∀ U, MemLp (x U) q P) (hy : ∀ U, MemLp (y U) q P) (hu : MemLp u q P) (hv : MemLp v q P) :
    MemLp (aux_gcat_band_witness_Sum4 wl wh we wr x y u v) q P := by
  have hterm : ∀ U : aux_gcat_band_witness_Roots d,
      MemLp (fun ω => wl * |x U ω| + wh * |y U ω|) q P := by
    intro U
    have h1 : MemLp (fun ω => wl * |x U ω|) q P := by
      have := (hx U).norm.const_mul wl
      simpa only [Real.norm_eq_abs] using this
    have h2 : MemLp (fun ω => wh * |y U ω|) q P := by
      have := (hy U).norm.const_mul wh
      simpa only [Real.norm_eq_abs] using this
    exact h1.add h2
  have hs : MemLp (fun ω => ∑ U : aux_gcat_band_witness_Roots d, (wl * |x U ω| + wh * |y U ω|)) q P :=
    memLp_finset_sum Finset.univ (fun U _ => hterm U)
  have h3 : MemLp (fun ω => we * |u ω|) q P := by
    have := hu.norm.const_mul we
    simpa only [Real.norm_eq_abs] using this
  have h4 : MemLp (fun ω => wr * |v ω|) q P := by
    have := hv.norm.const_mul wr
    simpa only [Real.norm_eq_abs] using this
  exact (hs.add h3).add h4

/-- An `L^p` limit inherits an eventual norm bound of the approximants. -/
theorem aux_gcat_band_witness_limit_norm_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {q : ENNReal} (hq : 1 ≤ q) (f : ℕ → Ω → ℝ) (V : Ω → ℝ) (kk : ℕ → ℕ)
    (hf : ∀ n, AEStronglyMeasurable (f n) P) (hV : AEStronglyMeasurable V P)
    (hconv : Tendsto (fun n => eLpNorm (fun ω => f (kk n) ω - V ω) q P) atTop (𝓝 0))
    (B : ENNReal) (hB : ∀ᶠ n in atTop, eLpNorm (f (kk n)) q P ≤ B) :
    eLpNorm V q P ≤ B := by
  have hle : ∀ᶠ n in atTop, eLpNorm V q P ≤ B + eLpNorm (fun ω => f (kk n) ω - V ω) q P := by
    filter_upwards [hB] with n hn
    have h1 : V = (fun ω => f (kk n) ω) - (fun ω => f (kk n) ω - V ω) := by
      funext ω; simp
    calc eLpNorm V q P = eLpNorm ((fun ω => f (kk n) ω) - (fun ω => f (kk n) ω - V ω)) q P := by
          rw [← h1]
      _ ≤ eLpNorm (fun ω => f (kk n) ω) q P + eLpNorm (fun ω => f (kk n) ω - V ω) q P :=
          eLpNorm_sub_le (hf _) ((hf _).sub hV) hq
      _ ≤ B + _ := add_le_add hn le_rfl
  have hlim : Tendsto (fun n => B + eLpNorm (fun ω => f (kk n) ω - V ω) q P) atTop (𝓝 (B + 0)) :=
    tendsto_const_nhds.add hconv
  rw [add_zero] at hlim
  exact ge_of_tendsto hlim hle

theorem aux_gcat_band_witness_offset_nonpos (d gH : ℕ) (i : Fin (aux_gcat_prefix_limits_T d)) :
    aux_gcat_prefix_limits_offset d gH i ≤ 0 := by
  unfold aux_gcat_prefix_limits_offset
  rcases h : (aux_gcat_prefix_limits_equiv d).symm i with et | u
  · simp only [Sum.elim_inl]
    exact neg_nonpos.mpr (Nat.cast_nonneg _)
  · simp only [Sum.elim_inr]
    exact neg_nonpos.mpr (Nat.cast_nonneg _)

theorem aux_gcat_band_witness_lam_congr {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (sigma : ℝ) (N : ℕ) (ω : BilateralField d)
    {c₁ c₂ : SpatialCoordinates d} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) (hc : c₁ = c₂) (hr : r₁ = r₂) :
    I.lam c₁ r₁ h₁ (Lane4.cutoffPositiveCoefficient M H ω N c₁ h₁) c₁ r₁ sigma 2 =
      I.lam c₂ r₂ h₂ (Lane4.cutoffPositiveCoefficient M H ω N c₂ h₂) c₂ r₂ sigma 2 := by
  subst hc; subst hr; rfl

theorem aux_gcat_band_witness_Lam_congr {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (sigma : ℝ) (N : ℕ) (ω : BilateralField d)
    {c₁ c₂ : SpatialCoordinates d} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) (hc : c₁ = c₂) (hr : r₁ = r₂) :
    I.Lam c₁ r₁ h₁ (Lane4.cutoffPositiveCoefficient M H ω N c₁ h₁) c₁ r₁ sigma 2 =
      I.Lam c₂ r₂ h₂ (Lane4.cutoffPositiveCoefficient M H ω N c₂ h₂) c₂ r₂ sigma 2 := by
  subst hc; subst hr; rfl

theorem aux_gcat_band_witness_err_congr {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (s : ℝ) (N : ℕ) (ω : BilateralField d)
    {c₁ c₂ : SpatialCoordinates d} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) (hc : c₁ = c₂) (hr : r₁ = r₂)
    {a₁ a₂ : ℝ} (ha : a₁ = a₂) :
    I.err c₁ r₁ h₁ (Lane4.cutoffPositiveCoefficient M H ω N c₁ h₁) c₁ r₁ a₁ s 2 =
      I.err c₂ r₂ h₂ (Lane4.cutoffPositiveCoefficient M H ω N c₂ h₂) c₂ r₂ a₂ s 2 := by
  subst hc; subst hr; subst ha; rfl

theorem aux_gcat_band_witness_sN_eq_reference {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) {l₁ l₂ : ℤ} {w₁ w₂ : SpatialCoordinates d} (ω : BilateralField d)
    (hl : l₁ = l₂) (hw : w₁ = w₂) (hle : l₂ ≤ (N : ℤ)) :
    gcat_sN M H N l₁ w₁ ω = aux_lem_band_U2_reference M H N l₂ w₂ ω := by
  subst hl; subst hw
  rw [aux_gcat_prefix_limits_gcat_sN_unfold M H N l₁ w₁ ω hle]
  rfl

theorem aux_gcat_band_witness_lo_eq {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (sigma : ℝ) (gH k : ℕ) (z : SpatialCoordinates d)
    (U : aux_gcat_band_witness_Roots d) (N : ℕ) (hN : (k : ℤ) ≤ (N : ℤ)) :
    (fun ω => I.lam (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
        (Lane4.cutoffPositiveCoefficient M H ω N (gcat_rootCentre gH k z U) (zpow_pos (by norm_num) _))
        (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) sigma 2 /
      gcat_sN M H N (gcat_rootLevel gH k U) (gcat_rootCentre gH k z U) ω) =
    aux_gcat_band_witness_loG I M H sigma N (k : ℤ) z
      (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
      (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))) := by
  funext ω
  have hoff := aux_gcat_band_witness_offset_nonpos d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))
  have hg : (k : ℤ) ≤ (N : ℤ) ∧ (k : ℤ) + aux_gcat_prefix_limits_offset d gH
      (aux_gcat_prefix_limits_equiv d (Sum.inl U)) ≤ (N : ℤ) := ⟨hN, by linarith⟩
  have hc := aux_gcat_prefix_limits_root_centre_eq gH k z U
  have hr := aux_gcat_prefix_limits_root_side_eq gH k U
  have hl := aux_gcat_prefix_limits_root_level_eq gH k U
  unfold aux_gcat_band_witness_loG
  rw [if_pos hg]
  have h1 := aux_gcat_band_witness_lam_congr I M H sigma N ω (c₁ := gcat_rootCentre gH k z U)
    (c₂ := z + ((3 : ℝ) ^ (-(k : ℤ))) • aux_gcat_prefix_limits_shift d gH
      (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
    (r₁ := gcat_rootSide gH k U)
    (r₂ := (3 : ℝ) ^ (-((k : ℤ) + aux_gcat_prefix_limits_offset d gH
      (aux_gcat_prefix_limits_equiv d (Sum.inl U)))))
    (zpow_pos (by norm_num) _) (zpow_pos (by norm_num) _) hc.symm hr.symm
  have h2 := aux_gcat_band_witness_sN_eq_reference M H N ω (l₁ := gcat_rootLevel gH k U)
    (l₂ := (k : ℤ) + aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
    (w₁ := gcat_rootCentre gH k z U)
    (w₂ := z + ((3 : ℝ) ^ (-(k : ℤ))) • aux_gcat_prefix_limits_shift d gH
      (aux_gcat_prefix_limits_equiv d (Sum.inl U))) hl.symm hc.symm hg.2
  rw [h1, h2]

theorem aux_gcat_band_witness_hi_eq {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (sigma : ℝ) (gH k : ℕ) (z : SpatialCoordinates d)
    (U : aux_gcat_band_witness_Roots d) (N : ℕ) (hN : (k : ℤ) ≤ (N : ℤ)) :
    (fun ω => I.Lam (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
        (Lane4.cutoffPositiveCoefficient M H ω N (gcat_rootCentre gH k z U) (zpow_pos (by norm_num) _))
        (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) sigma 2 /
      gcat_sN M H N (gcat_rootLevel gH k U) (gcat_rootCentre gH k z U) ω) =
    aux_gcat_band_witness_hiG I M H sigma N (k : ℤ) z
      (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
      (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))) := by
  funext ω
  have hoff := aux_gcat_band_witness_offset_nonpos d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))
  have hg : (k : ℤ) ≤ (N : ℤ) ∧ (k : ℤ) + aux_gcat_prefix_limits_offset d gH
      (aux_gcat_prefix_limits_equiv d (Sum.inl U)) ≤ (N : ℤ) := ⟨hN, by linarith⟩
  have hc := aux_gcat_prefix_limits_root_centre_eq gH k z U
  have hr := aux_gcat_prefix_limits_root_side_eq gH k U
  have hl := aux_gcat_prefix_limits_root_level_eq gH k U
  unfold aux_gcat_band_witness_hiG
  rw [if_pos hg]
  have h1 := aux_gcat_band_witness_Lam_congr I M H sigma N ω (c₁ := gcat_rootCentre gH k z U)
    (c₂ := z + ((3 : ℝ) ^ (-(k : ℤ))) • aux_gcat_prefix_limits_shift d gH
      (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
    (r₁ := gcat_rootSide gH k U)
    (r₂ := (3 : ℝ) ^ (-((k : ℤ) + aux_gcat_prefix_limits_offset d gH
      (aux_gcat_prefix_limits_equiv d (Sum.inl U)))))
    (zpow_pos (by norm_num) _) (zpow_pos (by norm_num) _) hc.symm hr.symm
  have h2 := aux_gcat_band_witness_sN_eq_reference M H N ω (l₁ := gcat_rootLevel gH k U)
    (l₂ := (k : ℤ) + aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
    (w₁ := gcat_rootCentre gH k z U)
    (w₂ := z + ((3 : ℝ) ^ (-(k : ℤ))) • aux_gcat_prefix_limits_shift d gH
      (aux_gcat_prefix_limits_equiv d (Sum.inl U))) hl.symm hc.symm hg.2
  rw [h1, h2]

theorem aux_gcat_band_witness_err_eq {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (s : ℝ) (gH k : ℕ) (z : SpatialCoordinates d)
    (N : ℕ) (hN : (k : ℤ) ≤ (N : ℤ)) :
    (fun ω => I.err z ((3 : ℝ) ^ (-((k : ℤ) - (gH : ℤ)))) (zpow_pos (by norm_num) _)
        (Lane4.cutoffPositiveCoefficient M H ω N z (zpow_pos (by norm_num) _))
        z ((3 : ℝ) ^ (-((k : ℤ) - (gH : ℤ))))
        (gcat_sN M H N ((k : ℤ) - (gH : ℤ)) z ω) s 2) =
    aux_gcat_band_witness_errG I M H s N (k : ℤ) z
      (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
      (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))) := by
  funext ω
  have hoff := aux_gcat_band_witness_offset_nonpos d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))
  have hg : (k : ℤ) ≤ (N : ℤ) ∧ (k : ℤ) + aux_gcat_prefix_limits_offset d gH
      (aux_gcat_prefix_limits_equiv d (Sum.inr ())) ≤ (N : ℤ) := ⟨hN, by linarith⟩
  have hc := aux_gcat_prefix_limits_cmp_centre_eq (d := d) gH k z
  have hl := aux_gcat_prefix_limits_cmp_level_eq (d := d) gH k
  unfold aux_gcat_band_witness_errG
  rw [if_pos hg]
  have h2 := aux_gcat_band_witness_sN_eq_reference M H N ω (l₁ := (k : ℤ) - (gH : ℤ))
    (l₂ := (k : ℤ) + aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
    (w₁ := z)
    (w₂ := z + ((3 : ℝ) ^ (-(k : ℤ))) • aux_gcat_prefix_limits_shift d gH
      (aux_gcat_prefix_limits_equiv d (Sum.inr ()))) hl.symm hc.symm hg.2
  refine aux_gcat_band_witness_err_congr I M H s N ω (zpow_pos (by norm_num) _) (zpow_pos (by norm_num) _)
    hc.symm ?_ h2
  rw [hl]

theorem aux_gcat_band_witness_ratio_eq {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (gH k : ℕ) (z : SpatialCoordinates d)
    (N : ℕ) (hN : (k : ℤ) ≤ (N : ℤ)) :
    (fun ω => gcat_sN M H N (k : ℤ) z ω / gcat_sN M H N ((k : ℤ) - (gH : ℤ)) z ω) =
    aux_gcat_band_witness_ratioG M H N (k : ℤ) z
      (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
      (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))) := by
  funext ω
  have hoff := aux_gcat_band_witness_offset_nonpos d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))
  have hg : (k : ℤ) ≤ (N : ℤ) ∧ (k : ℤ) + aux_gcat_prefix_limits_offset d gH
      (aux_gcat_prefix_limits_equiv d (Sum.inr ())) ≤ (N : ℤ) := ⟨hN, by linarith⟩
  have hc := aux_gcat_prefix_limits_cmp_centre_eq (d := d) gH k z
  have hl := aux_gcat_prefix_limits_cmp_level_eq (d := d) gH k
  unfold aux_gcat_band_witness_ratioG
  rw [if_pos hg]
  have h1 := aux_gcat_band_witness_sN_eq_reference M H N ω (l₁ := (k : ℤ)) (l₂ := (k : ℤ)) (w₁ := z) (w₂ := z)
    rfl rfl hN
  have h2 := aux_gcat_band_witness_sN_eq_reference M H N ω (l₁ := (k : ℤ) - (gH : ℤ))
    (l₂ := (k : ℤ) + aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
    (w₁ := z)
    (w₂ := z + ((3 : ℝ) ^ (-(k : ℤ))) • aux_gcat_prefix_limits_shift d gH
      (aux_gcat_prefix_limits_equiv d (Sum.inr ()))) hl.symm hc.symm hg.2
  rw [h1, h2]

/-- Almost-sure identification of the catalogue test limit arrays with the `L^p` limits of the guarded
coordinates. -/
theorem aux_gcat_band_witness_tests_links
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (sigma s : ℝ) (p : ℝ) (hp : 1 ≤ p)
    (gH k : ℕ) (z : SpatialCoordinates d) (phi psi : ℕ → ℕ) (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (Vlo Vhi : aux_gcat_band_witness_Roots d → BilateralField d → ℝ) (Verr Vrat : BilateralField d → ℝ)
    (hVlo : ∀ U, MemLp (Vlo U) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
    (hVhi : ∀ U, MemLp (Vhi U) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
    (hVerr : MemLp Verr (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
    (hVrat : MemLp Vrat (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
    (hXlo : ∀ N U, MemLp (aux_gcat_band_witness_loG I M H sigma N (k : ℤ) z
      (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
      (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))))
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
    (hXhi : ∀ N U, MemLp (aux_gcat_band_witness_hiG I M H sigma N (k : ℤ) z
      (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
      (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))))
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
    (hXerr : ∀ N, MemLp (aux_gcat_band_witness_errG I M H s N (k : ℤ) z
      (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
      (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))))
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
    (hXrat : ∀ N, MemLp (aux_gcat_band_witness_ratioG M H N (k : ℤ) z
      (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
      (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))))
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
    (hclo : ∀ U, Tendsto (fun kk => eLpNorm (fun ω =>
      aux_gcat_band_witness_loG I M H sigma (phi (psi kk)) (k : ℤ) z
        (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
        (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))) ω -
      Vlo U ω) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) atTop (𝓝 0))
    (hchi : ∀ U, Tendsto (fun kk => eLpNorm (fun ω =>
      aux_gcat_band_witness_hiG I M H sigma (phi (psi kk)) (k : ℤ) z
        (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
        (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))) ω -
      Vhi U ω) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) atTop (𝓝 0))
    (hcerr : Tendsto (fun kk => eLpNorm (fun ω =>
      aux_gcat_band_witness_errG I M H s (phi (psi kk)) (k : ℤ) z
        (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
        (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))) ω -
      Verr ω) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) atTop (𝓝 0))
    (hcrat : Tendsto (fun kk => eLpNorm (fun ω =>
      aux_gcat_band_witness_ratioG M H (phi (psi kk)) (k : ℤ) z
        (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
        (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))) ω -
      Vrat ω) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) atTop (𝓝 0))
    (loLim hiLim : aux_gcat_band_witness_Roots d → BilateralField d → ℝ)
    (errLim ratioLim : Unit → BilateralField d → ℝ)
    (hlo : ∀ U, TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun n omega =>
        I.lam (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
          (Lane4.cutoffPositiveCoefficient M H omega (phi n) (gcat_rootCentre gH k z U)
            (zpow_pos (by norm_num) _))
          (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) sigma 2 /
        gcat_sN M H (phi n) (gcat_rootLevel gH k U) (gcat_rootCentre gH k z U) omega)
      atTop (loLim U))
    (hhi : ∀ U, TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun n omega =>
        I.Lam (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
          (Lane4.cutoffPositiveCoefficient M H omega (phi n) (gcat_rootCentre gH k z U)
            (zpow_pos (by norm_num) _))
          (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) sigma 2 /
        gcat_sN M H (phi n) (gcat_rootLevel gH k U) (gcat_rootCentre gH k z U) omega)
      atTop (hiLim U))
    (herr : TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun n omega =>
        I.err z ((3 : ℝ) ^ (-((k : ℤ) - (gH : ℤ)))) (zpow_pos (by norm_num) _)
          (Lane4.cutoffPositiveCoefficient M H omega (phi n) z (zpow_pos (by norm_num) _))
          z ((3 : ℝ) ^ (-((k : ℤ) - (gH : ℤ))))
          (gcat_sN M H (phi n) ((k : ℤ) - (gH : ℤ)) z omega) s 2)
      atTop (errLim ()))
    (hrat : TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun n omega => gcat_sN M H (phi n) (k : ℤ) z omega /
        gcat_sN M H (phi n) ((k : ℤ) - (gH : ℤ)) z omega)
      atTop (ratioLim ())) :
    (∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∀ U, loLim U ω = Vlo U ω) ∧
    (∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∀ U, hiLim U ω = Vhi U ω) ∧
    (∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, errLim () ω = Verr ω) ∧
    (∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ratioLim () ω = Vrat ω) := by
  classical
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hphiT : Tendsto phi atTop atTop := hphi.tendsto_atTop
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ae_all_iff.mpr (fun U => ?_)
    refine aux_gcat_band_witness_link (chaosSampleLaw M).toMeasure
      (fun N => aux_gcat_band_witness_loG I M H sigma N (k : ℤ) z
        (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
        (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))))
      (fun N ω => I.lam (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
        (Lane4.cutoffPositiveCoefficient M H ω N (gcat_rootCentre gH k z U) (zpow_pos (by norm_num) _))
        (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) sigma 2 /
        gcat_sN M H N (gcat_rootLevel gH k U) (gcat_rootCentre gH k z U) ω)
      (Vlo U) (loLim U) phi psi hpsi hphiT hp0 (fun N => (hXlo N U).aestronglyMeasurable)
      (hVlo U).aestronglyMeasurable (hclo U) (hlo U) ?_
    filter_upwards [eventually_ge_atTop k] with N hN
    exact aux_gcat_band_witness_lo_eq I M H sigma gH k z U N (by exact_mod_cast hN)
  · refine ae_all_iff.mpr (fun U => ?_)
    refine aux_gcat_band_witness_link (chaosSampleLaw M).toMeasure
      (fun N => aux_gcat_band_witness_hiG I M H sigma N (k : ℤ) z
        (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
        (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))))
      (fun N ω => I.Lam (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
        (Lane4.cutoffPositiveCoefficient M H ω N (gcat_rootCentre gH k z U) (zpow_pos (by norm_num) _))
        (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) sigma 2 /
        gcat_sN M H N (gcat_rootLevel gH k U) (gcat_rootCentre gH k z U) ω)
      (Vhi U) (hiLim U) phi psi hpsi hphiT hp0 (fun N => (hXhi N U).aestronglyMeasurable)
      (hVhi U).aestronglyMeasurable (hchi U) (hhi U) ?_
    filter_upwards [eventually_ge_atTop k] with N hN
    exact aux_gcat_band_witness_hi_eq I M H sigma gH k z U N (by exact_mod_cast hN)
  · refine aux_gcat_band_witness_link (chaosSampleLaw M).toMeasure
      (fun N => aux_gcat_band_witness_errG I M H s N (k : ℤ) z
        (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
        (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))))
      (fun N ω => I.err z ((3 : ℝ) ^ (-((k : ℤ) - (gH : ℤ)))) (zpow_pos (by norm_num) _)
        (Lane4.cutoffPositiveCoefficient M H ω N z (zpow_pos (by norm_num) _))
        z ((3 : ℝ) ^ (-((k : ℤ) - (gH : ℤ))))
        (gcat_sN M H N ((k : ℤ) - (gH : ℤ)) z ω) s 2)
      Verr (errLim ()) phi psi hpsi hphiT hp0 (fun N => (hXerr N).aestronglyMeasurable)
      hVerr.aestronglyMeasurable hcerr herr ?_
    filter_upwards [eventually_ge_atTop k] with N hN
    exact aux_gcat_band_witness_err_eq I M H s gH k z N (by exact_mod_cast hN)
  · refine aux_gcat_band_witness_link (chaosSampleLaw M).toMeasure
      (fun N => aux_gcat_band_witness_ratioG M H N (k : ℤ) z
        (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
        (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))))
      (fun N ω => gcat_sN M H N (k : ℤ) z ω / gcat_sN M H N ((k : ℤ) - (gH : ℤ)) z ω)
      Vrat (ratioLim ()) phi psi hpsi hphiT hp0 (fun N => (hXrat N).aestronglyMeasurable)
      hVrat.aestronglyMeasurable hcrat hrat ?_
    filter_upwards [eventually_ge_atTop k] with N hN
    exact aux_gcat_band_witness_ratio_eq M H gH k z N (by exact_mod_cast hN)

/-- Failure of a catalogue test forces the test statistic to be at least `lam`. -/
theorem aux_gcat_band_witness_tests_finish {Ω : Type*} {d : ℕ}
    (cell epshom cdet : ℝ) (hcell : cell ∈ Set.Ioo (0 : ℝ) 1) (hepshom : 0 < epshom) (hcdet : 0 < cdet)
    (loLim hiLim Vlo Vhi : aux_gcat_band_witness_Roots d → Ω → ℝ) (errLim ratioLim : Unit → Ω → ℝ)
    (Verr Vrat : Ω → ℝ) (ω : Ω)
    (hlo : ∀ U, loLim U ω = Vlo U ω) (hhi : ∀ U, hiLim U ω = Vhi U ω)
    (herr : errLim () ω = Verr ω) (hrat : ratioLim () ω = Vrat ω)
    (hfail : ¬ ((∀ U, cell ≤ loLim U ω ∧ hiLim U ω ≤ cell⁻¹) ∧ errLim () ω ≤ epshom * cdet ∧
      ∀ c : Unit, ratioLim c ω ∈ Set.Ioo (1 / 2 : ℝ) 2)) :
    min (1 - cell) (min (cell⁻¹ - 1) (min (epshom * cdet) (1 / 2))) ≤
      aux_gcat_band_witness_Sum4 1 1 1 1 (fun U ω => Vlo U ω - 1) (fun U ω => Vhi U ω - 1) Verr
        (fun ω => Vrat ω - 1) ω := by
  obtain ⟨hc0, hc1⟩ := hcell
  have hcinv : 1 < cell⁻¹ := by
    rw [lt_inv_comm₀ one_pos hc0]; simpa using hc1
  set lam := min (1 - cell) (min (cell⁻¹ - 1) (min (epshom * cdet) (1 / 2))) with hlam
  have hl1 : lam ≤ 1 - cell := min_le_left _ _
  have hl2 : lam ≤ cell⁻¹ - 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hl3 : lam ≤ epshom * cdet := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hl4 : lam ≤ 1 / 2 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  unfold aux_gcat_band_witness_Sum4
  simp only [one_mul]
  have hnonneg : ∀ U : aux_gcat_band_witness_Roots d, 0 ≤ |Vlo U ω - 1| + |Vhi U ω - 1| :=
    fun U => by positivity
  have hsum_ge : ∀ U : aux_gcat_band_witness_Roots d,
      |Vlo U ω - 1| + |Vhi U ω - 1| ≤ ∑ U' : aux_gcat_band_witness_Roots d, (|Vlo U' ω - 1| + |Vhi U' ω - 1|) :=
    fun U => Finset.single_le_sum (f := fun U' => |Vlo U' ω - 1| + |Vhi U' ω - 1|)
      (fun U' _ => hnonneg U') (Finset.mem_univ U)
  have hev : 0 ≤ |Verr ω| := abs_nonneg _
  have hrv : 0 ≤ |Vrat ω - 1| := abs_nonneg _
  have hSnn : 0 ≤ ∑ U' : aux_gcat_band_witness_Roots d, (|Vlo U' ω - 1| + |Vhi U' ω - 1|) :=
    Finset.sum_nonneg (fun U' _ => hnonneg U')
  by_contra hcon
  push_neg at hcon
  apply hfail
  refine ⟨fun U => ?_, ?_, fun c => ?_⟩
  · have h1 := hsum_ge U
    have hlo1 : cell ≤ Vlo U ω := by
      by_contra hlt
      push_neg at hlt
      have : 1 - cell < |Vlo U ω - 1| := by
        rw [abs_sub_comm]; exact lt_of_lt_of_le (by linarith) (le_abs_self _)
      have := abs_nonneg (Vhi U ω - 1)
      linarith
    have hhi1 : Vhi U ω ≤ cell⁻¹ := by
      by_contra hlt
      push_neg at hlt
      have : cell⁻¹ - 1 < |Vhi U ω - 1| := lt_of_lt_of_le (by linarith) (le_abs_self _)
      have := abs_nonneg (Vlo U ω - 1)
      linarith
    rw [hlo U, hhi U]
    exact ⟨hlo1, hhi1⟩
  · rw [herr]
    by_contra hlt
    push_neg at hlt
    have : epshom * cdet < |Verr ω| := lt_of_lt_of_le hlt (le_abs_self _)
    linarith
  · rw [hrat]
    constructor
    · by_contra hlt
      push_neg at hlt
      have : 1 / 2 ≤ |Vrat ω - 1| := by
        rw [abs_sub_comm]; exact le_trans (by linarith) (le_abs_self _)
      linarith
    · by_contra hlt
      push_neg at hlt
      have : 1 ≤ |Vrat ω - 1| := le_trans (by linarith) (le_abs_self _)
      linarith

/-- `Tfin` is the `Sum4` of the guarded coordinates. -/
theorem aux_gcat_band_witness_Tfin_eq_Sum4 {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (gH : ℕ) (wl wh we wr : ℝ) (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (sigma s : ℝ) (N : ℕ) (n : ℤ)
    (z : SpatialCoordinates d) :
    aux_gcat_band_witness_Tfin gH wl wh we wr I M H sigma s N n z =
      aux_gcat_band_witness_Sum4 wl wh we wr
        (fun U ω => aux_gcat_band_witness_loG I M H sigma N n z
          (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
          (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))) ω - 1)
        (fun U ω => aux_gcat_band_witness_hiG I M H sigma N n z
          (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
          (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))) ω - 1)
        (fun ω => aux_gcat_band_witness_errG I M H s N n z
          (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
          (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))) ω)
        (fun ω => aux_gcat_band_witness_ratioG M H N n z
          (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
          (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))  ω - 1) := by
  rfl

/-- `L^p` convergence of the `Sum4` statistics from the convergence of the four coordinate families. -/
theorem aux_gcat_band_witness_Sum4_conv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (p : ℝ) (hp : 1 ≤ p) (wl wh we wr : ℝ) (hwl : 0 ≤ wl) (hwh : 0 ≤ wh) (hwe : 0 ≤ we) (hwr : 0 ≤ wr)
    (xN yN : ℕ → aux_gcat_band_witness_Roots d → Ω → ℝ) (uN vN : ℕ → Ω → ℝ)
    (x y : aux_gcat_band_witness_Roots d → Ω → ℝ) (u v : Ω → ℝ)
    (hxm : ∀ n U, AEStronglyMeasurable (fun ω => xN n U ω - x U ω) P)
    (hym : ∀ n U, AEStronglyMeasurable (fun ω => yN n U ω - y U ω) P)
    (hum : ∀ n, AEStronglyMeasurable (fun ω => uN n ω - u ω) P)
    (hvm : ∀ n, AEStronglyMeasurable (fun ω => vN n ω - v ω) P)
    (hx : ∀ U, Tendsto (fun n => eLpNorm (fun ω => xN n U ω - x U ω) (ENNReal.ofReal p) P) atTop (𝓝 0))
    (hy : ∀ U, Tendsto (fun n => eLpNorm (fun ω => yN n U ω - y U ω) (ENNReal.ofReal p) P) atTop (𝓝 0))
    (hu : Tendsto (fun n => eLpNorm (fun ω => uN n ω - u ω) (ENNReal.ofReal p) P) atTop (𝓝 0))
    (hv : Tendsto (fun n => eLpNorm (fun ω => vN n ω - v ω) (ENNReal.ofReal p) P) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun ω =>
      aux_gcat_band_witness_Sum4 wl wh we wr (xN n) (yN n) (uN n) (vN n) ω -
        aux_gcat_band_witness_Sum4 wl wh we wr x y u v ω) (ENNReal.ofReal p) P) atTop (𝓝 0) := by
  have hbound : ∀ n, eLpNorm (fun ω =>
      aux_gcat_band_witness_Sum4 wl wh we wr (xN n) (yN n) (uN n) (vN n) ω -
        aux_gcat_band_witness_Sum4 wl wh we wr x y u v ω) (ENNReal.ofReal p) P ≤
      (∑ U : aux_gcat_band_witness_Roots d,
        (ENNReal.ofReal wl * eLpNorm (fun ω => xN n U ω - x U ω) (ENNReal.ofReal p) P +
          ENNReal.ofReal wh * eLpNorm (fun ω => yN n U ω - y U ω) (ENNReal.ofReal p) P)) +
      ENNReal.ofReal we * eLpNorm (fun ω => uN n ω - u ω) (ENNReal.ofReal p) P +
      ENNReal.ofReal wr * eLpNorm (fun ω => vN n ω - v ω) (ENNReal.ofReal p) P := by
    intro n
    refine le_trans ?_ (aux_gcat_band_witness_Sum4_norm_le P p hp wl wh we wr hwl hwh hwe hwr
      (fun U ω => xN n U ω - x U ω) (fun U ω => yN n U ω - y U ω) (fun ω => uN n ω - u ω)
      (fun ω => vN n ω - v ω) (hxm n) (hym n) (hum n) (hvm n))
    refine eLpNorm_mono (fun ω => ?_)
    have h1 := aux_gcat_band_witness_Sum4_diff_le wl wh we wr hwl hwh hwe hwr (xN n) (yN n) x y
      (uN n) (vN n) u v ω
    have h2 : 0 ≤ aux_gcat_band_witness_Sum4 wl wh we wr (fun U ω => xN n U ω - x U ω)
        (fun U ω => yN n U ω - y U ω) (fun ω => uN n ω - u ω) (fun ω => vN n ω - v ω) ω := by
      unfold aux_gcat_band_witness_Sum4
      have : 0 ≤ ∑ U : aux_gcat_band_witness_Roots d,
          (wl * |xN n U ω - x U ω| + wh * |yN n U ω - y U ω|) :=
        Finset.sum_nonneg (fun U _ => by positivity)
      positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h2]
    exact h1
  have hlim : Tendsto (fun n =>
      (∑ U : aux_gcat_band_witness_Roots d,
        (ENNReal.ofReal wl * eLpNorm (fun ω => xN n U ω - x U ω) (ENNReal.ofReal p) P +
          ENNReal.ofReal wh * eLpNorm (fun ω => yN n U ω - y U ω) (ENNReal.ofReal p) P)) +
      ENNReal.ofReal we * eLpNorm (fun ω => uN n ω - u ω) (ENNReal.ofReal p) P +
      ENNReal.ofReal wr * eLpNorm (fun ω => vN n ω - v ω) (ENNReal.ofReal p) P) atTop (𝓝 0) := by
    have hfin : Tendsto (fun n => ∑ U : aux_gcat_band_witness_Roots d,
        (ENNReal.ofReal wl * eLpNorm (fun ω => xN n U ω - x U ω) (ENNReal.ofReal p) P +
          ENNReal.ofReal wh * eLpNorm (fun ω => yN n U ω - y U ω) (ENNReal.ofReal p) P)) atTop (𝓝 0) := by
      have := tendsto_finset_sum (Finset.univ : Finset (aux_gcat_band_witness_Roots d))
        (fun U _ => ((ENNReal.Tendsto.const_mul (hx U) (Or.inr (ENNReal.ofReal_ne_top (r := wl)))).add
          (ENNReal.Tendsto.const_mul (hy U) (Or.inr (ENNReal.ofReal_ne_top (r := wh))))))
      simpa using this
    have h3 := ENNReal.Tendsto.const_mul hu (Or.inr (ENNReal.ofReal_ne_top (r := we)))
    have h4 := ENNReal.Tendsto.const_mul hv (Or.inr (ENNReal.ofReal_ne_top (r := wr)))
    have := (hfin.add h3).add h4
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le _) hbound

/-- The norm of the limit statistic, from the norms of the limit coordinates. -/
theorem aux_gcat_band_witness_Sum4_small {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (p : ℝ) (hp : 1 ≤ p) (CL CH CE CR eta : ℝ) (hCL : 0 ≤ CL) (hCH : 0 ≤ CH) (hCE : 0 ≤ CE) (hCR : 0 ≤ CR)
    (heta : 0 ≤ eta)
    (x y : aux_gcat_band_witness_Roots d → Ω → ℝ) (u v : Ω → ℝ)
    (hxm : ∀ U, AEStronglyMeasurable (x U) P) (hym : ∀ U, AEStronglyMeasurable (y U) P)
    (hum : AEStronglyMeasurable u P) (hvm : AEStronglyMeasurable v P)
    (hx : ∀ U, eLpNorm (x U) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (CL * eta))
    (hy : ∀ U, eLpNorm (y U) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (CH * eta))
    (hu : eLpNorm u (ENNReal.ofReal p) P ≤ ENNReal.ofReal (CE * eta))
    (hv : eLpNorm v (ENNReal.ofReal p) P ≤ ENNReal.ofReal (CR * eta)) :
    eLpNorm (aux_gcat_band_witness_Sum4 1 1 1 1 x y u v) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (((Fintype.card (aux_gcat_band_witness_Roots d) : ℝ) * (CL + CH) + CE + CR) * eta) := by
  refine (aux_gcat_band_witness_Sum4_norm_le P p hp 1 1 1 1 zero_le_one zero_le_one zero_le_one zero_le_one
    x y u v hxm hym hum hvm).trans ?_
  simp only [ENNReal.ofReal_one, one_mul]
  have hsum : (∑ U : aux_gcat_band_witness_Roots d, (eLpNorm (x U) (ENNReal.ofReal p) P +
      eLpNorm (y U) (ENNReal.ofReal p) P)) ≤
      ∑ U : aux_gcat_band_witness_Roots d, ENNReal.ofReal ((CL + CH) * eta) := by
    refine Finset.sum_le_sum (fun U _ => ?_)
    calc eLpNorm (x U) (ENNReal.ofReal p) P + eLpNorm (y U) (ENNReal.ofReal p) P
        ≤ ENNReal.ofReal (CL * eta) + ENNReal.ofReal (CH * eta) := add_le_add (hx U) (hy U)
      _ = ENNReal.ofReal ((CL + CH) * eta) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  calc (∑ U : aux_gcat_band_witness_Roots d, (eLpNorm (x U) (ENNReal.ofReal p) P +
        eLpNorm (y U) (ENNReal.ofReal p) P)) + eLpNorm u (ENNReal.ofReal p) P +
        eLpNorm v (ENNReal.ofReal p) P
      ≤ (∑ U : aux_gcat_band_witness_Roots d, ENNReal.ofReal ((CL + CH) * eta)) +
        ENNReal.ofReal (CE * eta) + ENNReal.ofReal (CR * eta) :=
        add_le_add (add_le_add hsum hu) hv
    _ = ENNReal.ofReal (((Fintype.card (aux_gcat_band_witness_Roots d) : ℝ) * (CL + CH) + CE + CR) * eta) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hc : ((Fintype.card (aux_gcat_band_witness_Roots d) : ℕ) : ℝ≥0∞) =
            ENNReal.ofReal (Fintype.card (aux_gcat_band_witness_Roots d) : ℝ) := by
          rw [ENNReal.ofReal_natCast]
        rw [hc, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

theorem aux_gcat_band_witness_shift_conv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (q : ENNReal)
    (g : ℕ → Ω → ℝ) (V : Ω → ℝ) (c : ℝ)
    (h : Tendsto (fun n => eLpNorm (fun ω => g n ω - V ω) q P) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun ω => (g n ω - c) - (V ω - c)) q P) atTop (𝓝 0) := by
  simpa only [sub_sub_sub_cancel_right] using h

/-- Interval-witness cover of the failure of the four test conditions of a catalogue cell. -/
theorem gcat_band_witness_tests
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Pc : Paper.in_poincare d hd I) (Xc : Paper.in_extension d hd I)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (Dd : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (Dbase : Paper.sum_errors_baseline_input d)
    (s sigma eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (heps : eps ∈ Set.Ioo (0 : ℝ) 1) (gH : ℕ) (cell epshom cdet : ℝ)
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
      ∀ (loLim hiLim : aux_gcat_band_witness_Roots d → BilateralField d → ℝ)
        (errLim ratioLim : Unit → BilateralField d → ℝ),
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
            (¬ ((∀ U : aux_gcat_band_witness_Roots d, cell ≤ loLim U omega ∧ hiLim U omega ≤ cell⁻¹) ∧
              errLim () omega ≤ epshom * cdet ∧
              ∀ c : Unit, ratioLim c omega ∈ Set.Ioo (1 / 2 : ℝ) 2)) →
            omega ∈ ⋃ h : ℕ+, Wc h := by
  classical
  -- (1) constants
  obtain ⟨aT, cT, wT, haT, hcT, hwT, hbankT⟩ :=
    aux_gcat_band_witness_bank_T d hd I Pc Xc W Sf Dd Cresp hCresp Dbase s sigma eps hs hsigma heps gH
      1 1 1 1 zero_le_one zero_le_one zero_le_one zero_le_one
  obtain ⟨cL, hcL, hloS⟩ := aux_gcat_band_witness_small_lo d hd I Pc Xc W Sf Dd Cresp hCresp sigma hsigma
  obtain ⟨cH, hcH, hhiS⟩ := aux_gcat_band_witness_small_hi d hd I Pc Xc W Sf Dd Cresp hCresp sigma hsigma
  obtain ⟨cE, hcE, herrS⟩ := aux_gcat_band_witness_small_err d hd I Pc Xc W Sf Dd Cresp hCresp s hs
  obtain ⟨c, hcDef⟩ : ∃ c : ℝ, c = min (min cT cL) (min (min cH cE) 1) := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hcDef]; exact lt_min (lt_min hcT hcL) (lt_min (lt_min hcH hcE) one_pos)
  have hcT' : c ≤ cT := by rw [hcDef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hcL' : c ≤ cL := by rw [hcDef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hcH' : c ≤ cH := by
    rw [hcDef]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hcE' : c ≤ cE := by
    rw [hcDef]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hc1 : c ≤ 1 := by rw [hcDef]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨p, hpDef⟩ : ∃ p : ℝ, p = max 2 (A * (wT : ℝ) / (aT * Real.log 3) + 1) := ⟨_, rfl⟩
  have hp2 : 2 ≤ p := by rw [hpDef]; exact le_max_left _ _
  have hp1 : (1 : ℝ) ≤ p := by linarith only [hp2]
  have hdecay : A * (wT : ℝ) < aT * p * Real.log 3 := by
    have h0 : A * (wT : ℝ) / (aT * Real.log 3) + 1 ≤ p := by rw [hpDef]; exact le_max_right _ _
    have h1 : A * (wT : ℝ) / (aT * Real.log 3) < p := by linarith only [h0]
    have h2 := (div_lt_iff₀ (mul_pos haT hlog3)).mp h1
    calc A * (wT : ℝ) < p * (aT * Real.log 3) := h2
      _ = aT * p * Real.log 3 := by ring
  obtain ⟨δT, CpT, hδT, hCpT, hbank⟩ := hbankT p hp1
  obtain ⟨δL, CL, hδL, hCL, hloSm⟩ := hloS p hp1
  obtain ⟨δH, CH, hδH, hCH, hhiSm⟩ := hhiS p hp1
  obtain ⟨δE, CE, hδE, hCE, herrSm⟩ := herrS p hp1
  obtain ⟨CR, hCR, hratSm⟩ := aux_gcat_band_witness_small_ratio d
    (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
    (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))) p hp1
  obtain ⟨δLim, hδLim, hLimBank⟩ := aux_gcat_band_witness_tests_limit_bank d hd I Pc Xc W Sf Dd Cresp
    hCresp s sigma eps hs hsigma heps p hp1 gH
  obtain ⟨Ctest, hCtestDef⟩ : ∃ Ctest : ℝ,
      Ctest = (Fintype.card (aux_gcat_band_witness_Roots d) : ℝ) * (CL + CH) + CE + CR := ⟨_, rfl⟩
  have hCtest : 0 ≤ Ctest := by rw [hCtestDef]; positivity
  obtain ⟨Cp, hCpDef⟩ : ∃ Cp : ℝ, Cp = 2 * CpT + Ctest + 1 := ⟨_, rfl⟩
  have hCp : 0 < Cp := by rw [hCpDef]; linarith only [hCpT, hCtest]
  obtain ⟨lam, hlamDef⟩ : ∃ lam : ℝ,
      lam = min (1 - cell) (min (cell⁻¹ - 1) (min (epshom * cdet) (1 / 2))) := ⟨_, rfl⟩
  have hlam : 0 < lam := by
    obtain ⟨hc0, hc1'⟩ := hcell
    have hcinv : 1 < cell⁻¹ := by rw [lt_inv_comm₀ one_pos hc0]; simpa using hc1'
    rw [hlamDef]
    exact lt_min (by linarith) (lt_min (by linarith) (lt_min (mul_pos hepshom hcdet) (by norm_num)))
  obtain ⟨eta0, heta0, hcore2⟩ := gcat_band_witness_tests_core2 d wT 1 hwT A aT lam Cp p haT hlam hCp
    hp2 hdecay
  refine ⟨min (min (min δT δL) (min δH δE)) (min (min δLim 1) (eta0 ^ (1 / c))), ?_, ?_⟩
  · refine lt_min (lt_min (lt_min hδT hδL) (lt_min hδH hδE)) (lt_min (lt_min hδLim one_pos) ?_)
    exact Real.rpow_pos_of_pos heta0 _
  intro M hMd Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim k z phi hphi loLim hiLim
    errLim ratioLim hlo' hhi' herr' hrat'
  -- (2) the model
  have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
  obtain ⟨hMa, hMb⟩ := le_min_iff.mp hMd
  obtain ⟨hMa1, hMa2⟩ := le_min_iff.mp hMa
  obtain ⟨hMT, hML⟩ := le_min_iff.mp hMa1
  obtain ⟨hMH, hME⟩ := le_min_iff.mp hMa2
  obtain ⟨hMb1, hMeta⟩ := le_min_iff.mp hMb
  obtain ⟨hMLim, hM1⟩ := le_min_iff.mp hMb1
  have hη : 0 < M.delta ^ c := Real.rpow_pos_of_pos hdpos c
  have hle : M.delta ^ c ≤ eta0 := by
    calc M.delta ^ c ≤ (eta0 ^ (1 / c)) ^ c := Real.rpow_le_rpow hdpos.le hMeta hc.le
      _ = eta0 := by
        rw [← Real.rpow_mul heta0.le, one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
  have hδpow : ∀ c' : ℝ, c ≤ c' → M.delta ^ c' ≤ M.delta ^ c :=
    fun c' hcc => Real.rpow_le_rpow_of_exponent_ge hdpos hM1 hcc
  obtain ⟨psi, hpsi, Vlo, Vhi, Verr, Vrat, hVlo, hVhi, hVerr, hVrat, hXlo, hXhi, hXerr, hXrat,
    hclo, hchi, hcerr, hcrat⟩ :=
    hLimBank M hMLim Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim k z phi hphi
  have hphipsi : Tendsto (fun kk => phi (psi kk)) atTop atTop :=
    hphi.tendsto_atTop.comp hpsi.tendsto_atTop
  have hev : ∀ᶠ kk in atTop, k ≤ phi (psi kk) := tendsto_atTop.mp hphipsi k
  have hevZ : ∀ᶠ kk in atTop, (k : ℤ) ≤ ((phi (psi kk) : ℕ) : ℤ) := hev.mono (fun kk hk => by exact_mod_cast hk)
  have hoffle : ∀ (j : Fin (aux_gcat_prefix_limits_T d)) (N : ℕ), (k : ℤ) ≤ (N : ℤ) →
      (k : ℤ) + aux_gcat_prefix_limits_offset d gH j ≤ (N : ℤ) := by
    intro j N hN
    have := aux_gcat_band_witness_offset_nonpos d gH j
    linarith only [hN, this]
  -- (3) norms of the limit coordinates
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp1
  have hVloB : ∀ U : aux_gcat_band_witness_Roots d,
      eLpNorm (fun ω => Vlo U ω - 1) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (CL * M.delta ^ c) := by
    intro U
    refine aux_gcat_band_witness_limit_norm_le (chaosSampleLaw M).toMeasure hq1
      (fun N ω => aux_gcat_band_witness_loG I M H sigma N (k : ℤ) z
        (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
        (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))) ω - 1)
      (fun ω => Vlo U ω - 1) (fun kk => phi (psi kk))
      (fun N => ((hXlo N U).sub (memLp_const 1)).aestronglyMeasurable)
      ((hVlo U).sub (memLp_const 1)).aestronglyMeasurable
      (aux_gcat_band_witness_shift_conv _ _ _ _ 1 (hclo U)) _ ?_
    filter_upwards [hevZ] with kk hkk
    have := hloSm M hML Rm hRm Sreg It H hH (phi (psi kk)) (k : ℤ) z
      (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
      (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))) hkk
      (hoffle _ _ hkk)
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (hδpow cL hcL') hCL
  have hVhiB : ∀ U : aux_gcat_band_witness_Roots d,
      eLpNorm (fun ω => Vhi U ω - 1) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (CH * M.delta ^ c) := by
    intro U
    refine aux_gcat_band_witness_limit_norm_le (chaosSampleLaw M).toMeasure hq1
      (fun N ω => aux_gcat_band_witness_hiG I M H sigma N (k : ℤ) z
        (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
        (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))) ω - 1)
      (fun ω => Vhi U ω - 1) (fun kk => phi (psi kk))
      (fun N => ((hXhi N U).sub (memLp_const 1)).aestronglyMeasurable)
      ((hVhi U).sub (memLp_const 1)).aestronglyMeasurable
      (aux_gcat_band_witness_shift_conv _ _ _ _ 1 (hchi U)) _ ?_
    filter_upwards [hevZ] with kk hkk
    have := hhiSm M hMH Rm hRm Sreg It H hH (phi (psi kk)) (k : ℤ) z
      (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
      (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))) hkk
      (hoffle _ _ hkk)
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (hδpow cH hcH') hCH
  have hVerrB : eLpNorm Verr (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (CE * M.delta ^ c) := by
    refine aux_gcat_band_witness_limit_norm_le (chaosSampleLaw M).toMeasure hq1
      (fun N ω => aux_gcat_band_witness_errG I M H s N (k : ℤ) z
        (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
        (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))) ω)
      Verr (fun kk => phi (psi kk)) (fun N => (hXerr N).aestronglyMeasurable)
      hVerr.aestronglyMeasurable hcerr _ ?_
    filter_upwards [hevZ] with kk hkk
    have := herrSm M hME Rm hRm Sreg It H hH (phi (psi kk)) (k : ℤ) z
      (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
      (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))) hkk
      (hoffle _ _ hkk)
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (hδpow cE hcE') hCE
  have hVratB : eLpNorm (fun ω => Vrat ω - 1) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (CR * M.delta ^ c) := by
    refine aux_gcat_band_witness_limit_norm_le (chaosSampleLaw M).toMeasure hq1
      (fun N ω => aux_gcat_band_witness_ratioG M H N (k : ℤ) z
        (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
        (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))) ω - 1)
      (fun ω => Vrat ω - 1) (fun kk => phi (psi kk))
      (fun N => ((hXrat N).sub (memLp_const 1)).aestronglyMeasurable)
      (hVrat.sub (memLp_const 1)).aestronglyMeasurable
      (aux_gcat_band_witness_shift_conv _ _ _ _ 1 hcrat) _ ?_
    filter_upwards [hevZ] with kk hkk
    have := hratSm M hM1 Rm H hH (phi (psi kk)) (k : ℤ) z hkk
      (hoffle _ _ hkk)
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : M.delta ≤ M.delta ^ c := by
      have := hδpow 1 hc1
      rwa [Real.rpow_one] at this
    exact mul_le_mul_of_nonneg_left h1 hCR
  -- (4) the statistics
  have hxm : ∀ U : aux_gcat_band_witness_Roots d,
      MemLp (fun ω => Vlo U ω - 1) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure :=
    fun U => (hVlo U).sub (memLp_const 1)
  have hym : ∀ U : aux_gcat_band_witness_Roots d,
      MemLp (fun ω => Vhi U ω - 1) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure :=
    fun U => (hVhi U).sub (memLp_const 1)
  have hvm : MemLp (fun ω => Vrat ω - 1) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure :=
    hVrat.sub (memLp_const 1)
  have hTtnorm : eLpNorm (aux_gcat_band_witness_Sum4 1 1 1 1 (fun U ω => Vlo U ω - 1)
      (fun U ω => Vhi U ω - 1) Verr (fun ω => Vrat ω - 1)) (ENNReal.ofReal p)
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cp * M.delta ^ c) := by
    refine (aux_gcat_band_witness_Sum4_small (chaosSampleLaw M).toMeasure p hp1 CL CH CE CR
      (M.delta ^ c) hCL hCH hCE hCR hη.le _ _ _ _
      (fun U => (hxm U).aestronglyMeasurable) (fun U => (hym U).aestronglyMeasurable)
      hVerr.aestronglyMeasurable hvm.aestronglyMeasurable hVloB hVhiB hVerrB hVratB).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← hCtestDef]
    exact mul_le_mul_of_nonneg_right (by rw [hCpDef]; linarith only [hCpT]) hη.le
  have hTfin : ∀ kk, aux_gcat_band_witness_Tfin gH 1 1 1 1 I M H sigma s (phi (psi kk)) (k : ℤ) z =
      aux_gcat_band_witness_Sum4 1 1 1 1
        (fun U ω => aux_gcat_band_witness_loG I M H sigma (phi (psi kk)) (k : ℤ) z
          (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
          (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))) ω - 1)
        (fun U ω => aux_gcat_band_witness_hiG I M H sigma (phi (psi kk)) (k : ℤ) z
          (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
          (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))) ω - 1)
        (fun ω => aux_gcat_band_witness_errG I M H s (phi (psi kk)) (k : ℤ) z
          (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
          (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))) ω)
        (fun ω => aux_gcat_band_witness_ratioG M H (phi (psi kk)) (k : ℤ) z
          (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
          (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))) ω - 1) :=
    fun kk => aux_gcat_band_witness_Tfin_eq_Sum4 gH 1 1 1 1 I M H sigma s (phi (psi kk)) (k : ℤ) z
  have hTtmem : MemLp (aux_gcat_band_witness_Sum4 1 1 1 1 (fun U ω => Vlo U ω - 1)
      (fun U ω => Vhi U ω - 1) Verr (fun ω => Vrat ω - 1)) (ENNReal.ofReal p)
      (chaosSampleLaw M).toMeasure :=
    aux_gcat_band_witness_Sum4_memLp _ _ 1 1 1 1 _ _ _ _ hxm hym hVerr hvm
  have hTnmem : ∀ kk, MemLp (aux_gcat_band_witness_Tfin gH 1 1 1 1 I M H sigma s (phi (psi kk))
      (k : ℤ) z) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure := by
    intro kk
    rw [hTfin kk]
    exact aux_gcat_band_witness_Sum4_memLp _ _ 1 1 1 1 _ _ _ _
      (fun U => (hXlo (phi (psi kk)) U).sub (memLp_const 1))
      (fun U => (hXhi (phi (psi kk)) U).sub (memLp_const 1)) (hXerr (phi (psi kk)))
      ((hXrat (phi (psi kk))).sub (memLp_const 1))
  have hTconv : Tendsto (fun kk => eLpNorm (fun ω =>
      aux_gcat_band_witness_Tfin gH 1 1 1 1 I M H sigma s (phi (psi kk)) (k : ℤ) z ω -
        aux_gcat_band_witness_Sum4 1 1 1 1 (fun U ω => Vlo U ω - 1) (fun U ω => Vhi U ω - 1) Verr
          (fun ω => Vrat ω - 1) ω) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) atTop (𝓝 0) := by
    have := aux_gcat_band_witness_Sum4_conv (chaosSampleLaw M).toMeasure p hp1 1 1 1 1
      zero_le_one zero_le_one zero_le_one zero_le_one
      (fun kk U ω => aux_gcat_band_witness_loG I M H sigma (phi (psi kk)) (k : ℤ) z
          (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
          (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))) ω - 1)
      (fun kk U ω => aux_gcat_band_witness_hiG I M H sigma (phi (psi kk)) (k : ℤ) z
          (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U)))
          (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inl U))) ω - 1)
      (fun kk ω => aux_gcat_band_witness_errG I M H s (phi (psi kk)) (k : ℤ) z
          (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
          (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))) ω)
      (fun kk ω => aux_gcat_band_witness_ratioG M H (phi (psi kk)) (k : ℤ) z
          (aux_gcat_prefix_limits_offset d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ())))
          (aux_gcat_prefix_limits_shift d gH (aux_gcat_prefix_limits_equiv d (Sum.inr ()))) ω - 1)
      (fun U ω => Vlo U ω - 1) (fun U ω => Vhi U ω - 1) Verr (fun ω => Vrat ω - 1)
      (fun kk U => (((hXlo (phi (psi kk)) U).sub (memLp_const 1)).sub (hxm U)).aestronglyMeasurable)
      (fun kk U => (((hXhi (phi (psi kk)) U).sub (memLp_const 1)).sub (hym U)).aestronglyMeasurable)
      (fun kk => ((hXerr (phi (psi kk))).sub hVerr).aestronglyMeasurable)
      (fun kk => (((hXrat (phi (psi kk))).sub (memLp_const 1)).sub hvm).aestronglyMeasurable)
      (fun U => aux_gcat_band_witness_shift_conv _ _ _ _ 1 (hclo U))
      (fun U => aux_gcat_band_witness_shift_conv _ _ _ _ 1 (hchi U))
      hcerr (aux_gcat_band_witness_shift_conv _ _ _ _ 1 hcrat)
    simpa only [hTfin] using this
  have hTband : ∀ hb : ℕ, 1 ≤ hb → ∀ᶠ kk in atTop, ∃ Yn : BilateralField d → ℝ,
      AEStronglyMeasurable[aux_gcat_band_condexp_Bsig d ((k : ℤ) - ((wT * (hb + 1) : ℕ) : ℤ))
        ((k : ℤ) + ((wT * (hb + 1) : ℕ) : ℤ))] Yn (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => aux_gcat_band_witness_Tfin gH 1 1 1 1 I M H sigma s (phi (psi kk)) (k : ℤ) z om -
        Yn om) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cp * M.delta ^ c / 2 * (3 : ℝ) ^ (-(aT * (hb : ℝ)))) := by
    intro hb hhb
    filter_upwards [hevZ] with kk hkk
    obtain ⟨Yn, hYm, hYb⟩ := hbank M hMT Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim
      (phi (psi kk)) (k : ℤ) z hkk (fun j => hoffle j _ hkk) hb hhb
    refine ⟨Yn, ?_, hYb.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    · rw [aux_gcat_band_witness_lbWindow_eq] at hYm
      exact hYm
    · have h1 : CpT * M.delta ^ cT ≤ CpT * M.delta ^ c :=
        mul_le_mul_of_nonneg_left (hδpow cT hcT') hCpT.le
      have h2 : CpT * M.delta ^ c ≤ Cp * M.delta ^ c / 2 := by
        have : Cp * M.delta ^ c / 2 - CpT * M.delta ^ c = (Ctest + 1) * M.delta ^ c / 2 := by
          rw [hCpDef]; ring
        have h3 : 0 ≤ (Ctest + 1) * M.delta ^ c / 2 := by positivity
        linarith only [this, h3]
      exact mul_le_mul_of_nonneg_right (h1.trans h2) (Real.rpow_nonneg (by norm_num) _)
  -- (5) the cover
  obtain ⟨Sigma, hSigmeas, hSigP, Wt, hWmeas, hWprob, hWcov⟩ :=
    hcore2 (M.delta ^ c) hη hle M (k : ℤ)
      (fun _ => aux_gcat_band_witness_Sum4 1 1 1 1 (fun U ω => Vlo U ω - 1)
        (fun U ω => Vhi U ω - 1) Verr (fun ω => Vrat ω - 1))
      (fun _ kk => aux_gcat_band_witness_Tfin gH 1 1 1 1 I M H sigma s (phi (psi kk)) (k : ℤ) z)
      (fun _ => hTtmem) (fun _ kk => hTnmem kk) (fun _ => hTtnorm) (fun _ => hTconv)
      (fun _ hb hhb => hTband hb hhb)
  -- (6) links and conclusion
  obtain ⟨l1, l2, l3, l4⟩ := aux_gcat_band_witness_tests_links d I M H sigma s p hp1 gH k z phi psi hphi
    hpsi Vlo Vhi Verr Vrat hVlo hVhi hVerr hVrat hXlo hXhi hXerr hXrat hclo hchi hcerr hcrat loLim hiLim
    errLim ratioLim hlo' hhi' herr' hrat'
  refine ⟨Wt, hWmeas, hWprob, ?_⟩
  have hSig : ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ω ∈ Sigma := by
    have h0 : (chaosSampleLaw M).toMeasure Sigmaᶜ = 0 := by
      rw [prob_compl_eq_zero_iff hSigmeas]; exact hSigP
    exact measure_eq_zero_iff_ae_notMem.mp h0 |>.mono (fun ω h => by simpa using h)
  filter_upwards [hSig, l1, l2, l3, l4] with ω hωS h1 h2 h3 h4 hfail
  have hge := aux_gcat_band_witness_tests_finish cell epshom cdet hcell hepshom hcdet loLim hiLim Vlo Vhi
    errLim ratioLim Verr Vrat ω h1 h2 h3 h4 hfail
  rw [← hlamDef] at hge
  exact hWcov ⟨hωS, ⟨0, hge⟩⟩

end Paper
