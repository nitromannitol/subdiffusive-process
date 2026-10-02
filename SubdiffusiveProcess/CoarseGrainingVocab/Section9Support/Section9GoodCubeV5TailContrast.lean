import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTailResidual
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.Algebra




set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory Set Filter Topology
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.Section9 (centeredAxisCube)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The geometric ratio in the printed shell threshold. -/
def goodCubeV5ShellRatio : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4)

theorem goodCubeV5ShellRatio_pos : 0 < goodCubeV5ShellRatio := by
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem goodCubeV5ShellRatio_lt_one : goodCubeV5ShellRatio < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- The sum of the shell thresholds, with the first shell indexed by one. -/
def goodCubeV5TailBudget (epsilon : ℝ) : ℝ :=
  epsilon * goodCubeV5ShellRatio / (1 - goodCubeV5ShellRatio)

/-- One good shell controls the difference of its values throughout the native cube. -/
theorem goodCubeV5_shell_value_sub_le {d n j : ℕ} {z : Lattice d}
    {epsilon : ℝ} {omega : PotentialSample d}
    (hgood : omega ∉ layerEvent n j 1 epsilon z)
    {x y : Vec d} (hx : x ∈ nativeBox n 1 z) (hy : y ∈ nativeBox n 1 z) :
    |omega (n + j) x - omega (n + j) y| ≤
      epsilon * (3 : ℝ)^(-(j : ℝ) / 4) := by
  have hK := isBounded_nativeBox (d := d) n 1 z
  have hgrad := bddAbove_boxDerivNorm_family hK (omega (n + j))
  have hess := bddAbove_boxDerivLipschitzSeminorm_family hK (omega (n + j))
  have hgrad0 : 0 ≤ boxDerivNorm (nativeBox n 1 z) (omega (n + j)) :=
    supWithZero_nonneg hgrad
  have hess0 : 0 ≤ boxDerivLipschitzSeminorm (nativeBox n 1 z) (omega (n + j)) :=
    supWithZero_nonneg hess
  have hder : ∀ u ∈ nativeBox n 1 z,
      ‖PotentialField.deriv (omega (n + j)) u‖ ≤
        boxDerivNorm (nativeBox n 1 z) (omega (n + j)) :=
    fun u hu => le_supWithZero hgrad ⟨u, hu⟩
  have hconv : Convex ℝ (nativeBox n 1 z) := by
    exact convex_pi fun _ _ => convex_Ioo _ _
  have hdiff := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun u _ => ((omega (n + j)).hasFDerivAt u).hasFDerivWithinAt) hder hy hx
  rw [Real.norm_eq_abs] at hdiff
  have hbound : layerObservable n (nativeBox n 1 z) (omega (n + j)) ≤
      epsilon * (3 : ℝ)^(-(j : ℝ) / 4) := le_of_not_gt hgood
  have hnonneg : 0 ≤ ((3 : ℝ)^n)^2 *
      boxDerivLipschitzSeminorm (nativeBox n 1 z) (omega (n + j)) :=
    mul_nonneg (sq_nonneg _) hess0
  have hnorm := mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_nativeBox_one hx hy) hgrad0
  unfold layerObservable at hbound
  nlinarith



theorem goodCubeV5_anchored_increment_le {d : ℕ} (omega : AnchoredC11Sample d)
    (n : ℕ) (x y : Vec d) {epsilon : ℝ} (_hepsilon : 0 ≤ epsilon)
    (hstep : ∀ j : ℕ, |omega.1 (n + 1 + j) x - omega.1 (n + 1 + j) y| ≤
      epsilon * goodCubeV5ShellRatio^(j + 1)) :
    |(anchoredLog omega x - anchoredLog omega y) -
      (anchoredPartialSum omega.1 n x - anchoredPartialSum omega.1 n y)| ≤
        goodCubeV5TailBudget epsilon := by
  let f : ℕ → ℝ := fun j => omega.1 (n + 1 + j) x - omega.1 (n + 1 + j) y
  have hgeo := hasSum_geometric_of_lt_one goodCubeV5ShellRatio_pos.le
    goodCubeV5ShellRatio_lt_one
  have hmajor : HasSum (fun j : ℕ => epsilon * goodCubeV5ShellRatio^(j + 1))
      (goodCubeV5TailBudget epsilon) := by
    simpa [pow_succ, goodCubeV5TailBudget, div_eq_mul_inv, mul_assoc,
      mul_comm, mul_left_comm] using hgeo.mul_left (epsilon * goodCubeV5ShellRatio)
  have hf : Summable f := Summable.of_norm_bounded hmajor.summable
    (fun j => by simpa [f, Real.norm_eq_abs] using hstep j)
  have hsum : |∑' j, f j| ≤ goodCubeV5TailBudget epsilon := by
    rw [← Real.norm_eq_abs]
    exact (norm_tsum_le_tsum_norm hf.norm).trans
      ((hf.norm.tsum_le_tsum (fun j => by simpa [f, Real.norm_eq_abs] using hstep j)
        hmajor.summable).trans_eq hmajor.tsum_eq)
  have hlim (u : Vec d) : Tendsto (fun N : ℕ => anchoredPartialSum omega.1 (N + n) u)
      atTop (𝓝 (anchoredLog omega u)) :=
    (((anchoredLog_spec omega).value_tendsto {u} isCompact_singleton).tendsto_at
      (Set.mem_singleton u)).comp (tendsto_add_atTop_nat n)
  have hsplit (N : ℕ) : ∑ j ∈ Finset.range N, f j =
      (anchoredPartialSum omega.1 (N + n) x - anchoredPartialSum omega.1 (N + n) y) -
        (anchoredPartialSum omega.1 n x - anchoredPartialSum omega.1 n y) := by
    unfold anchoredPartialSum
    rw [show N + n + 1 = (n + 1) + N by omega]
    simp only [Finset.sum_range_add, Finset.sum_sub_distrib, f]
    ring
  have hlim' : Tendsto (fun N => ∑ j ∈ Finset.range N, f j) atTop
      (𝓝 ((anchoredLog omega x - anchoredLog omega y) -
        (anchoredPartialSum omega.1 n x - anchoredPartialSum omega.1 n y))) := by
    simp_rw [hsplit]
    exact ((hlim x).sub (hlim y)).sub_const _
  rwa [tendsto_nhds_unique hf.hasSum.tendsto_sum_nat hlim'] at hsum

/-- The full good event bounds the nonconstant log ratio on the entire native cube.
The normalization point can be any point of that cube. -/
theorem goodCubeV5_log_ratio_sub_le {d : ℕ} (M : GMCModel d)
    (omega : AnchoredC11Sample d) (n : ℕ) (z : Lattice d)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (E0 : Lattice d → Set (PotentialSample d))
    (hgood : omega.1 ∈ goodCubeEvent (goodCubeEventField n 1 epsilon E0) z)
    {x y : Vec d} (hx : x ∈ nativeBox n 1 z) (hy : y ∈ nativeBox n 1 z) :
    |Real.log (aAnchored M omega x / aCutoff M n omega.1 x) -
      Real.log (aAnchored M omega y / aCutoff M n omega.1 y)| ≤
        goodCubeV5TailBudget epsilon := by
  have hstep (j : ℕ) : |omega.1 (n + 1 + j) x - omega.1 (n + 1 + j) y| ≤
      epsilon * goodCubeV5ShellRatio^(j + 1) := by
    have hj : omega.1 ∉ layerEvent n (j + 1) 1 epsilon z :=
      Set.mem_iInter.mp hgood (j + 1)
    have hb := goodCubeV5_shell_value_sub_le hj hx hy
    have hexp : (3 : ℝ)^(-((j + 1 : ℕ) : ℝ) / 4) =
        goodCubeV5ShellRatio^(j + 1) := by
      rw [goodCubeV5ShellRatio, ← Real.rpow_mul_natCast (by norm_num)]
      congr 1
      ring
    simpa only [Nat.add_assoc, Nat.add_comm 1 j, hexp] using hb
  have h := goodCubeV5_anchored_increment_le omega n x y hepsilon hstep
  have hlog (u : Vec d) : Real.log (aAnchored M omega u / aCutoff M n omega.1 u) =
      anchoredLog omega u - ∑ k ∈ Finset.range (n + 1), (omega.1 k u - tauSq M.P) := by
    rw [aAnchored, aCutoff, ← Real.exp_sub, Real.log_exp]
  rw [hlog x, hlog y]
  convert h using 2
  simp only [anchoredPartialSum, Finset.sum_sub_distrib]
  ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
