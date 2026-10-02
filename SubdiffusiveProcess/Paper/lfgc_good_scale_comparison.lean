import SubdiffusiveProcess.Paper.in_deterministic_good_scale_transfer

/-! At a nonnegative physical level, raw cutoff scores compare the actual coefficient with its rescaled GMC coefficient.
Both the genuine infrared limit and the finite zero-infrared sum are allowed; negative levels are outside this statement. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
noncomputable section
namespace Paper

/-- The raw potential and gradient bounds transfer the good-scale error for either infrared choice. -/
theorem lfgc_good_scale_comparison
    {d : ℕ} (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (l : ℤ) (hl : l ≤ (N : ℤ)) (hl0 : 0 ≤ l)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)) ∨ H = 0)
    (w : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ (-l))
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (B T : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hPbound : ∀ x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0),
      ∀ K : ℕ, ∑ k ∈ Finset.Ico (((N : ℤ) - l).toNat + 1) (N + K + 1),
        |eta k (((3 : ℝ) ^ ((N : ℤ) - l).toNat) • x + ((3 : ℝ) ^ N) • w) -
          eta k (((3 : ℝ) ^ N) • w)| ≤ B)
    (hTbound : ∀ K : ℕ, ∑ k ∈ Finset.Ico (((N : ℤ) - l).toNat + 1) (N + K + 1),
        (3 : ℝ) ^ ((N : ℤ) - l).toNat *
          vectorSupNormOn (translatedCube d ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w))
            (shellGradient (eta k)) ≤ T) :
    let m : ℕ := ((N : ℤ) - l).toNat
    let kappa : ℕ → ℝ := fun J =>
      Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
    let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
      fun ell v beta =>
        if 0 ≤ ell then
          ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
        else
          -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
    let a0 : ℝ := kappa m / kappa N * Real.exp (H omega w + retained l w omega)
    let eps : ℝ := min B ((d : ℝ) * T) * Real.exp B
    I.err w ((3 : ℝ) ^ (-l)) hr (Lane4.cutoffPositiveCoefficient M H omega N w hr)
        w ((3 : ℝ) ^ (-l)) a0 s 2 ≤
      Real.sqrt (2 + 6 * eps ^ 2) *
          section6HomogenizationError M s m m eta (((3 : ℝ) ^ N) • w) +
        Real.sqrt (6 * eps ^ 2) := by
  rcases hIR with hIR | hH0
  · exact aux_in_deterministic_good_scale_transfer_pointwise I M H omega N l hl eta hEta hIR
      w hr s hs B T hB hT hPbound hTbound
  intro m kappa retained a0 eps
  set z : Vec d := ((3 : ℝ) ^ N) • w with hz
  have hk : ∀ J, 0 < kappa J := fun J => mul_pos (Real.exp_pos _) (ahom_pos M J)
  have ha0 : 0 < a0 := mul_pos (div_pos (hk m) (hk N)) (Real.exp_pos _)
  have heps : 0 ≤ eps := mul_nonneg (le_min hB (mul_nonneg (Nat.cast_nonneg d) hT))
    (Real.exp_pos _).le
  refine aux_in_deterministic_good_scale_transfer_chain_actual I M H omega N w
    ((3 : ℝ) ^ (-l)) hr a0 ha0 s hs m eta z eps heps ?_
  intro x hx
  set xp : SpatialCoordinates d := fun i => w i + (3 : ℝ) ^ (-l) * x i with hxp
  -- the exponent `E K` of `ratio_exp`
  let Sm : ℕ → ℝ := fun K => ∑ k ∈ Finset.Ico (m + 1) (N + K + 1),
    (eta k (((3 : ℝ) ^ m) • x + z) - eta k z)
  let bK : ℕ → ℝ := fun K => (H omega xp - H omega w) -
    ∑ n ∈ Finset.range K, (omega (((n + 1 : ℕ) : ℤ)) xp - omega (((n + 1 : ℕ) : ℤ)) w)
  have hre := fun K (hK : m ≤ N + K) =>
    aux_in_deterministic_good_scale_transfer_ratio_exp M H omega N l hl eta hEta w x K hK
  -- all exponents agree with the one at `K = m`
  set X : ℝ := Sm m + bK m with hXdef
  have hXK : ∀ K, m ≤ N + K → X = Sm K + bK K := by
    intro K hK
    have h1 := (hre K hK).1
    have h0 := (hre m (by omega)).1
    simp only at h1 h0
    exact Real.exp_injective (h0.symm.trans h1)
  have hSB : ∀ K, |Sm K| ≤ min B ((d : ℝ) * T) := by
    intro K
    have habs : |Sm K| ≤ ∑ k ∈ Finset.Ico (m + 1) (N + K + 1),
        |eta k (((3 : ℝ) ^ m) • x + z) - eta k z| := Finset.abs_sum_le_sum_abs _ _
    refine le_min (habs.trans (hPbound x hx K)) (habs.trans ?_)
    refine (aux_in_deterministic_good_scale_transfer_gradient_block eta m z hx _ _).trans ?_
    exact mul_le_mul_of_nonneg_left (hTbound K) (Nat.cast_nonneg d)
  have hmN : m ≤ N := by dsimp only [m]; omega
  have hXle : |X| ≤ min B ((d : ℝ) * T) := by
    rw [hXK 0 (by omega)]
    simpa only [bK, hH0, Pi.zero_apply, ContinuousMap.zero_apply, sub_self,
      Finset.range_zero, Finset.sum_empty, sub_zero, add_zero] using hSB 0
  have hXB : |X| ≤ B := hXle.trans (min_le_left _ _)
  have hbound : ∀ t : ℝ, |t| ≤ min B ((d : ℝ) * T) → |t| ≤ B →
      |Real.exp t - 1| ≤ eps := by
    intro t ht htB
    refine (aux_in_deterministic_good_scale_transfer_abs_exp_sub_one t).trans ?_
    exact mul_le_mul ht (Real.exp_le_exp.mpr htB) (Real.exp_pos _).le
      (le_min hB (mul_nonneg (Nat.cast_nonneg d) hT))
  have hm0 := hre m (by omega)
  simp only at hm0
  obtain ⟨hfwd, hbwd⟩ := hm0
  have hXeq : Sm m + bK m = X := rfl
  constructor
  · have := hbwd
    rw [hXeq] at this
    change |(a0 / ahom M m) *
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m (translatePotentialSample z eta) (((3 : ℝ) ^ m) • x) /
        cutoffCoefficient M H omega N xp - 1| ≤ eps
    rw [this]
    exact hbound (-X) (by rw [abs_neg]; exact hXle) (by rw [abs_neg]; exact hXB)
  · have := hfwd
    rw [hXeq] at this
    change |(a0 / ahom M m)⁻¹ * cutoffCoefficient M H omega N xp /
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m (translatePotentialSample z eta)
          (((3 : ℝ) ^ m) • x) - 1| ≤ eps
    rw [this]
    exact hbound X hXle hXB

end Paper
