import Mathlib
import SubdiffusiveProcess.Sobolev.WeakGradient

/-!
# Stampacchia: a limit point of nested convex sets in the Sobolev-data space

`SobolevData Ω = L²(Ω) × L²(Ω)^d` is complete, and the quadratic form
`N2 z = ‖z₁‖² + ∑ᵢ ‖zᵢ‖²` satisfies the parallelogram law and dominates `‖z‖²`.  For nested nonempty
convex sets `B m` on which `N2` stays bounded, the (almost) minimizers of `N2` on `B m` form a
Cauchy sequence, whose limit lies in every `closure (B m)`.  This replaces weak compactness.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Stampacchia

variable {d : ℕ} {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}

/-- The Hilbert-type quadratic form on Sobolev data. -/
def N2 (z : SobolevData Ω) : ℝ := ‖z.1‖ ^ 2 + ∑ i, ‖z.2 i‖ ^ 2

theorem N2_nonneg (z : SobolevData Ω) : 0 ≤ N2 z := by
  unfold N2; positivity

theorem N2_smul (c : ℝ) (z : SobolevData Ω) : N2 (c • z) = c ^ 2 * N2 z := by
  unfold N2
  simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs]
  rw [mul_add, Finset.mul_sum]

theorem N2_parallelogram (x y : SobolevData Ω) :
    N2 (x + y) + N2 (x - y) = 2 * (N2 x + N2 y) := by
  unfold N2
  have h0 := parallelogram_law_with_norm ℝ x.1 y.1
  have hi : ∀ i, ‖x.2 i + y.2 i‖ ^ 2 + ‖x.2 i - y.2 i‖ ^ 2 = 2 * (‖x.2 i‖ ^ 2 + ‖y.2 i‖ ^ 2) := by
    intro i
    have := parallelogram_law_with_norm ℝ (x.2 i) (y.2 i)
    nlinarith [this]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Pi.add_apply, Pi.sub_apply]
  have hs : ∑ i, (‖x.2 i + y.2 i‖ ^ 2 + ‖x.2 i - y.2 i‖ ^ 2) =
      ∑ i, 2 * (‖x.2 i‖ ^ 2 + ‖y.2 i‖ ^ 2) := Finset.sum_congr rfl fun i _ => hi i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib] at hs
  nlinarith [h0, hs]

theorem sq_norm_le_N2 (z : SobolevData Ω) : ‖z‖ ^ 2 ≤ N2 z := by
  have hN := N2_nonneg z
  have h1 : ‖z.1‖ ≤ Real.sqrt (N2 z) := by
    apply Real.le_sqrt_of_sq_le
    unfold N2
    have : 0 ≤ ∑ i, ‖z.2 i‖ ^ 2 := by positivity
    linarith
  have h2 : ‖z.2‖ ≤ Real.sqrt (N2 z) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    apply Real.le_sqrt_of_sq_le
    unfold N2
    have hi : ‖z.2 i‖ ^ 2 ≤ ∑ i, ‖z.2 i‖ ^ 2 :=
      Finset.single_le_sum (f := fun i => ‖z.2 i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ i)
    have : 0 ≤ ‖z.1‖ ^ 2 := by positivity
    linarith
  have h3 : ‖z‖ ≤ Real.sqrt (N2 z) := by
    rw [Prod.norm_def]; exact max_le h1 h2
  calc ‖z‖ ^ 2 ≤ (Real.sqrt (N2 z)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    _ = N2 z := Real.sq_sqrt hN

/-- **Tail limits of convex combinations (Mazur, without weak compactness).**  For a bounded (in
`N2`) sequence `z` in the Sobolev-data space there are points `y m` of the convex hull of the tail
`{z n | m ≤ n}` which converge in norm. -/
theorem exists_tail_limit (z : ℕ → SobolevData Ω) (M : ℝ) (hM : ∀ n, N2 (z n) ≤ M) :
    ∃ (y : ℕ → SobolevData Ω) (yL : SobolevData Ω),
      (∀ m, y m ∈ convexHull ℝ (z '' Ici m)) ∧ Tendsto y atTop (𝓝 yL) := by
  classical
  set B : ℕ → Set (SobolevData Ω) := fun m => convexHull ℝ (z '' Ici m) with hB
  have hBmono : ∀ m k, m ≤ k → B k ⊆ B m := fun m k h =>
    convexHull_mono (image_mono (Ici_subset_Ici.2 h))
  have hzB : ∀ m, z m ∈ B m := fun m =>
    subset_convexHull ℝ _ (mem_image_of_mem _ (mem_Ici.2 le_rfl))
  have hBcvx : ∀ m, Convex ℝ (B m) := fun m => convex_convexHull ℝ _
  set inf : ℕ → ℝ := fun m => sInf (N2 '' B m) with hinf
  have hbdd : ∀ m, BddBelow (N2 '' B m) := fun m => ⟨0, by
    rintro _ ⟨w, -, rfl⟩; exact N2_nonneg w⟩
  have hne : ∀ m, (N2 '' B m).Nonempty := fun m => ⟨N2 (z m), mem_image_of_mem _ (hzB m)⟩
  have hinf_le : ∀ m, inf m ≤ M := fun m =>
    (csInf_le (hbdd m) (mem_image_of_mem _ (hzB m))).trans (hM m)
  have hinf_mono : Monotone inf := fun m k h =>
    csInf_le_csInf (hbdd m) (hne k) (image_mono (hBmono m k h))
  have hinf_le_N2 : ∀ m (w : SobolevData Ω), w ∈ B m → inf m ≤ N2 w := fun m w hw =>
    csInf_le (hbdd m) (mem_image_of_mem _ hw)
  set L : ℝ := ⨆ m, inf m with hL
  have hbddA : BddAbove (range inf) := ⟨M, by rintro _ ⟨m, rfl⟩; exact hinf_le m⟩
  have hLlim : Tendsto inf atTop (𝓝 L) := tendsto_atTop_ciSup hinf_mono hbddA
  have hinf_L : ∀ m, inf m ≤ L := fun m => le_ciSup hbddA m
  have hpick : ∀ m, ∃ w ∈ B m, N2 w < inf m + 1 / ((m : ℝ) + 1) := by
    intro m
    obtain ⟨_, ⟨w, hw, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hne m)
      (show sInf (N2 '' B m) < inf m + 1 / ((m : ℝ) + 1) by
        have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
        linarith)
    exact ⟨w, hw, hlt⟩
  choose y hyB hyN using hpick
  have hcauchy : CauchySeq y := by
    refine cauchySeq_of_le_tendsto_0 (fun N => Real.sqrt (4 * (L - inf N) + 4 / ((N : ℝ) + 1)))
      (fun n m N hn hm => ?_) ?_
    · have hyn : y n ∈ B N := hBmono N n hn (hyB n)
      have hym : y m ∈ B N := hBmono N m hm (hyB m)
      have hmid : (1 / 2 : ℝ) • (y n + y m) ∈ B N := by
        have := (hBcvx N) hyn hym (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num)
        simpa [smul_add] using this
      have h4 : 4 * inf N ≤ N2 (y n + y m) := by
        have := hinf_le_N2 N _ hmid
        have e : N2 ((1 / 2 : ℝ) • (y n + y m)) = 1 / 4 * N2 (y n + y m) := by
          rw [N2_smul]; ring
        rw [e] at this; linarith
      have hpar := N2_parallelogram (y n) (y m)
      have h1 : N2 (y n) ≤ L + 1 / ((N : ℝ) + 1) := by
        have a := hyN n
        have b : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)
        linarith [hinf_L n]
      have h2 : N2 (y m) ≤ L + 1 / ((N : ℝ) + 1) := by
        have a := hyN m
        have b : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hm)
        linarith [hinf_L m]
      have hdist2 : dist (y n) (y m) ^ 2 ≤ 4 * (L - inf N) + 4 / ((N : ℝ) + 1) := by
        rw [dist_eq_norm]
        have := sq_norm_le_N2 (y n - y m)
        have hN : N2 (y n - y m) = 2 * (N2 (y n) + N2 (y m)) - N2 (y n + y m) := by linarith
        have e : (4 : ℝ) / ((N : ℝ) + 1) = 4 * (1 / ((N : ℝ) + 1)) := by ring
        rw [e]
        nlinarith
      exact Real.le_sqrt_of_sq_le hdist2
    · have h1 : Tendsto (fun N : ℕ => 4 * (L - inf N) + 4 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
        have a : Tendsto (fun N : ℕ => 4 * (L - inf N)) atTop (𝓝 (4 * (L - L))) :=
          (tendsto_const_nhds.sub hLlim).const_mul 4
        have b : Tendsto (fun N : ℕ => 4 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
          have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 4
          rw [mul_zero] at this
          refine this.congr fun N => ?_
          ring
        simpa using a.add b
      have := (Real.continuous_sqrt.tendsto 0).comp h1
      simpa using this
  obtain ⟨yL, hyL⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨y, yL, hyB, hyL⟩

end SubdiffusiveProcess.Stampacchia
