module

public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GradedAdditiveEnvelope

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open MeasureTheory
open Homogenization Homogenization.IndependentSums
open SubdiffusiveProcess.Frozen.Assumptions
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The index of a row: lattice point × cutoff level -/

/-- The sup-norm lattice box `ℤ^d ∩ [-2ⁿ, 2ⁿ]^d`, the printed `ℤ^d ∩ B_{C2ⁿ}`
in the coordinates the anchored proof actually uses. -/
def latticeBox (d n : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(2 ^ n : ℤ)) (2 ^ n)

/-- The real point carried by a lattice index. -/
def latticePoint (z : Fin d → ℤ) : Vec d := fun i => (z i : ℝ)

@[simp]
theorem latticePoint_zero : latticePoint (d := d) 0 = (0 : Vec d) := by
  funext i
  simp [latticePoint]

theorem zero_mem_latticeBox (d n : ℕ) : (0 : Fin d → ℤ) ∈ latticeBox d n := by
  refine Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ⟨?_, ?_⟩
  · have hpos : (0 : ℤ) ≤ 2 ^ n := by positivity
    simp only [Pi.zero_apply]
    linarith
  · simp only [Pi.zero_apply]
    positivity

/-- The finest cutoff level tracked at dyadic scale `n`: the printed `N(n)`,
the least integer with `3^{N(n)} ≥ 2·2ⁿ`, for which `n+1` is admissible. -/
def maxCutoffLevel (n : ℕ) : ℕ := n + 1

theorem two_mul_two_pow_le_three_pow_maxCutoffLevel (n : ℕ) :
    2 * 2 ^ n ≤ 3 ^ maxCutoffLevel n := by
  have h : (2 : ℕ) ^ (n + 1) ≤ 3 ^ (n + 1) :=
    Nat.pow_le_pow_left (by norm_num) _
  simpa [maxCutoffLevel, pow_succ, mul_comm] using h

/-- Row `n` of the value-maximal index: a lattice point of the box of radius
`2ⁿ` together with a cutoff level at most `N(n)`. -/
def valueIndex (d n : ℕ) : Finset ((Fin d → ℤ) × ℕ) :=
  latticeBox d n ×ˢ Finset.range (maxCutoffLevel n + 1)

/-! ## The row entropy -/

theorem card_latticeBox (d n : ℕ) :
    (latticeBox d n).card = (2 * 2 ^ n + 1) ^ d := by
  rw [latticeBox, Fintype.card_piFinset]
  simp only [Int.card_Icc]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  have hcast : ((2 : ℤ) ^ n + 1 - -(2 ^ n)) = ((2 * 2 ^ n + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hcast, Int.toNat_natCast]

theorem card_valueIndex (d n : ℕ) :
    (valueIndex d n).card = (2 * 2 ^ n + 1) ^ d * (n + 2) := by
  rw [valueIndex, Finset.card_product, card_latticeBox, Finset.card_range,
    maxCutoffLevel]

theorem card_valueIndex_le_pow (d n : ℕ) :
    (valueIndex d n).card ≤ 2 ^ ((2 * d + 1) * (n + 1)) := by
  have hbase : 2 * 2 ^ n + 1 ≤ 2 ^ (n + 2) := by
    have h1 : (1 : ℕ) ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    have h2 : 2 * 2 ^ n = 2 ^ (n + 1) := by ring
    calc 2 * 2 ^ n + 1 ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := by omega
      _ = 2 ^ (n + 2) := by ring
  have hlevel : n + 2 ≤ 2 ^ (n + 1) := Nat.lt_two_pow_self
  calc (valueIndex d n).card = (2 * 2 ^ n + 1) ^ d * (n + 2) := card_valueIndex d n
    _ ≤ (2 ^ (n + 2)) ^ d * 2 ^ (n + 1) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hbase d) hlevel
    _ = 2 ^ ((n + 2) * d + (n + 1)) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ ((2 * d + 1) * (n + 1)) := by
      refine Nat.pow_le_pow_right (by norm_num) ?_
      nlinarith

/-- The row-entropy exponent: `card (valueIndex d n) ≤ exp (rowGrowth d (n+1))`. -/
def rowGrowth (d : ℕ) : ℝ := (2 * (d : ℝ) + 1) * Real.log 2

theorem rowGrowth_nonneg (d : ℕ) : 0 ≤ rowGrowth d := by
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  exact mul_nonneg (by linarith) hlog

theorem card_valueIndex_le (d n : ℕ) :
    ((valueIndex d n).card : ℝ) ≤ Real.exp (rowGrowth d * ((n : ℝ) + 1)) := by
  have hexp : Real.exp (rowGrowth d * ((n : ℝ) + 1)) =
      ((2 ^ ((2 * d + 1) * (n + 1)) : ℕ) : ℝ) := by
    have hrw : rowGrowth d * ((n : ℝ) + 1) =
        (((2 * d + 1) * (n + 1) : ℕ) : ℝ) * Real.log 2 := by
      rw [rowGrowth]
      push_cast
      ring
    rw [hrw, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    push_cast
    ring
  rw [hexp]
  exact_mod_cast card_valueIndex_le_pow d n

/-! ## The graded threshold constants -/

/-- The Gaussian threshold multiplier: any `λ ≥ 1` with `λ² ≥ growth + 2`. -/
def envelopeLam (d : ℕ) : ℝ := 1 + Real.sqrt (rowGrowth d + 2)

theorem one_le_envelopeLam (d : ℕ) : 1 ≤ envelopeLam d := by
  have := Real.sqrt_nonneg (rowGrowth d + 2)
  rw [envelopeLam]
  linarith

theorem rowGrowth_add_two_le_envelopeLam_sq (d : ℕ) :
    rowGrowth d + 2 ≤ envelopeLam d ^ 2 := by
  have hnn : (0 : ℝ) ≤ rowGrowth d + 2 := by
    have := rowGrowth_nonneg d
    linarith
  have hsq : Real.sqrt (rowGrowth d + 2) ^ 2 = rowGrowth d + 2 := Real.sq_sqrt hnn
  have hs : (0 : ℝ) ≤ Real.sqrt (rowGrowth d + 2) := Real.sqrt_nonneg _
  rw [envelopeLam]
  nlinarith

/-! ## The per-entry `Γ₂` input -/

/-- The observable indexed by a row entry: the absolute finite shell sum at the
lattice point, at the given cutoff level. -/
def valueObservable (i : (Fin d → ℤ) × ℕ) (omega : PotentialSample d) : ℝ :=
  |cutoffShellSum i.2 (-1) (latticePoint i.1) omega|

/-- The row scale: the central-limit `Γ₂` scale of the *longest* shell sum
appearing in row `n`. -/
def rowScale (M : GMCModel d) (n : ℕ) : ℝ :=
  cutoffGammaConst * Real.sqrt ((n : ℝ) + 2) * M.delta

theorem rowScale_nonneg (M : GMCModel d) (n : ℕ) : 0 ≤ rowScale M n :=
  mul_nonneg (mul_nonneg cutoffGammaConst_pos.le (Real.sqrt_nonneg _))
    M.shellPrefix.delta_pos.le

theorem isBigOWith_gammaTwo_valueObservable (M : GMCModel d) (n : ℕ)
    {i : (Fin d → ℤ) × ℕ} (hi : i ∈ valueIndex d n) :
    IsBigOWith M.P.toMeasure (gammaSigma 2) (valueObservable i) (rowScale M n) := by
  obtain ⟨z, L⟩ := i
  have hL : L ≤ maxCutoffLevel n := by
    have := (Finset.mem_product.mp hi).2
    have hmem := Finset.mem_range.mp this
    omega
  have hbase := isBigO_gammaTwo_cutoffShellSum_sourceScale M L (-1)
    (latticePoint z) (by norm_num) (by omega)
  have hcast : ((((L : ℤ) - (-1) : ℤ) : ℝ)) = (L : ℝ) + 1 := by
    push_cast
    ring
  rw [hcast] at hbase
  refine IsBigOWith.mono_scale (μ := M.P.toMeasure) (Ψ := gammaSigma 2) hbase ?_
  have hsqrt : Real.sqrt ((L : ℝ) + 1) ≤ Real.sqrt ((n : ℝ) + 2) := by
    refine Real.sqrt_le_sqrt ?_
    have : (L : ℝ) ≤ (n : ℝ) + 1 := by
      exact_mod_cast (by simpa [maxCutoffLevel] using hL : L ≤ n + 1)
    linarith
  rw [rowScale]
  have hd : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  have hc : 0 ≤ cutoffGammaConst := cutoffGammaConst_pos.le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsqrt hc) hd

/-! ## The maximal bound -/

/-- The deterministic slope of the value-maximal bound: a dimensional constant
times the disorder strength. -/
def valueMaximalSlope (d : ℕ) : ℝ := 4 * envelopeLam d * cutoffGammaConst

theorem valueMaximalSlope_pos (d : ℕ) : 0 < valueMaximalSlope d := by
  have h1 : (0 : ℝ) < envelopeLam d :=
    lt_of_lt_of_le zero_lt_one (one_le_envelopeLam d)
  have h2 := cutoffGammaConst_pos
  rw [valueMaximalSlope]
  positivity

/-- The unanchored maximal bound: almost surely, one additive finite random
constant plus the deterministic slope `C δ n` dominates every finite shell sum
at every lattice point of the box of radius `2ⁿ` and every cutoff level at most
`N(n)`. -/
theorem ae_exists_forall_abs_cutoffShellSum_le (M : GMCModel d) :
    ∀ᵐ omega ∂M.P.toMeasure, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ z : Fin d → ℤ, z ∈ latticeBox d n →
        ∀ L : ℕ, L ≤ maxCutoffLevel n →
          |cutoffShellSum L (-1) (latticePoint z) omega| ≤
            (valueMaximalSlope d / 2) * M.delta * ((n : ℝ) + 1) + C := by
  have henv := ae_exists_forall_le_sqrtGradedScale_add_of_isBigOWith_gammaTwo
    (mu := M.P.toMeasure) (I := valueIndex d) (X := fun _ i => valueObservable i)
    (a := rowScale M) (growth := rowGrowth d) (lam := envelopeLam d)
    (rowGrowth_nonneg d) (one_le_envelopeLam d)
    (rowGrowth_add_two_le_envelopeLam_sq d) (rowScale_nonneg M)
    (card_valueIndex_le d) (fun n i hi => isBigOWith_gammaTwo_valueObservable M n hi)
  refine henv.mono ?_
  intro omega ⟨C, hC0, hC⟩
  refine ⟨C, hC0, fun n z hz L hL => ?_⟩
  have hmem : (z, L) ∈ valueIndex d n :=
    Finset.mem_product.2 ⟨hz, Finset.mem_range.2 (by omega)⟩
  have hbound := hC n (z, L) hmem
  refine hbound.trans ?_
  have hkey : sqrtGradedScale (envelopeLam d) (rowScale M) n ≤
      (valueMaximalSlope d / 2) * M.delta * ((n : ℝ) + 1) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hs1 : Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt ((n : ℝ) + 2) :=
      Real.sqrt_le_sqrt (by linarith)
    have hs2 : Real.sqrt ((n : ℝ) + 2) ^ 2 = (n : ℝ) + 2 :=
      Real.sq_sqrt (by linarith)
    have hs0 : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) + 2) := Real.sqrt_nonneg _
    have hprod : Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 2) ≤
        2 * ((n : ℝ) + 1) := by
      nlinarith [Real.sqrt_nonneg ((n : ℝ) + 1)]
    have hlam : (0 : ℝ) < envelopeLam d :=
      lt_of_lt_of_le zero_lt_one (one_le_envelopeLam d)
    have hc := cutoffGammaConst_pos
    have hd := M.shellPrefix.delta_pos
    rw [sqrtGradedScale, rowScale, valueMaximalSlope]
    nlinarith [mul_pos hlam (mul_pos hc hd)]
  linarith



theorem ae_exists_forall_abs_anchoredPartialSum_le (M : GMCModel d) :
    ∀ᵐ omega ∂M.P.toMeasure, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ z : Fin d → ℤ, z ∈ latticeBox d n →
        ∀ L : ℕ, L ≤ maxCutoffLevel n →
          |anchoredPartialSum omega L (latticePoint z)| ≤
            valueMaximalSlope d * M.delta * ((n : ℝ) + 1) + C := by
  refine (ae_exists_forall_abs_cutoffShellSum_le M).mono ?_
  intro omega ⟨C, hC0, hC⟩
  refine ⟨2 * C, by linarith, fun n z hz L hL => ?_⟩
  have hz0 := zero_mem_latticeBox d n
  have h1 := hC n z hz L hL
  have h2 := hC n 0 hz0 L hL
  rw [latticePoint_zero] at h2
  have hsplit : anchoredPartialSum omega L (latticePoint z) =
      cutoffShellSum L (-1) (latticePoint z) omega -
        cutoffShellSum L (-1) (0 : Vec d) omega := by
    have hidx : cutoffShellIndices L (-1) = Finset.range (L + 1) := by
      have hzero : ((-1 : ℤ) + 1).toNat = 0 := by norm_num
      rw [cutoffShellIndices, hzero]
      ext k
      simp [Nat.lt_succ_iff]
    rw [anchoredPartialSum, cutoffShellSum, cutoffShellSum, hidx,
      ← Finset.sum_sub_distrib]
  rw [hsplit]
  refine (abs_sub _ _).trans ?_
  have hhalf : valueMaximalSlope d / 2 * M.delta * ((n : ℝ) + 1) * 2 =
      valueMaximalSlope d * M.delta * ((n : ℝ) + 1) := by ring
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
