module

public import Mathlib

@[expose] public section

/-!
# Cube trace extension: the scale weight on the open unit cube

For the open unit cube `Q = ball z (1/2)` (sup norm) put `u_i(x) = 1/4 - (x_i - z_i)^2` and
`m(x) = min_i u_i(x)`.  Since `u_i = (1/2-|x_i-z_i|)(1/2+|x_i-z_i|)`, `m` is comparable to the
distance to `∂Q`, is 1-Lipschitz for the sup norm on `Q`, and the sup-ball of radius `m(x)` about
`x ∈ Q` lies in `Q`.  `m` is only used as a weight; it is never differentiated.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal ContDiff Topology
noncomputable section
namespace SubdiffusiveProcess.CubeTrace

variable {d : ℕ}

/-- The coordinate profile `u_i(x) = 1/4 - (x_i - z_i)^2`. -/
def ctU (z x : (Fin d → ℝ)) (i : Fin d) : ℝ := 1 / 4 - (x i - z i) ^ 2

/-- The scale weight `m(x) = min_i u_i(x)`. -/
def ctM [NeZero d] (z x : (Fin d → ℝ)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => ctU z x i)

/-- The open unit cube centered at `z` (the sup-norm ball of radius `1/2`). -/
abbrev ctQ (z : (Fin d → ℝ)) : Set ((Fin d → ℝ)) := Metric.ball z (1 / 2)

theorem abs_sub_lt_of_mem_ctQ {z x : (Fin d → ℝ)} (hx : x ∈ ctQ z) (i : Fin d) :
    |x i - z i| < 1 / 2 := by
  rw [ctQ, mem_ball_iff_norm] at hx
  have h : ‖(x - z) i‖ ≤ ‖x - z‖ := norm_le_pi_norm (x - z) i
  simp only [Pi.sub_apply, Real.norm_eq_abs] at h
  linarith

theorem ctU_pos {z x : (Fin d → ℝ)} (hx : x ∈ ctQ z) (i : Fin d) : 0 < ctU z x i := by
  unfold ctU
  have h : |x i - z i| < 1 / 2 := by
    have h1 : dist (x i) (z i) ≤ dist x z := dist_le_pi_dist x z i
    have h2 : dist x z < 1 / 2 := hx
    simpa [Real.dist_eq] using lt_of_le_of_lt h1 h2
  nlinarith [abs_nonneg (x i - z i), sq_abs (x i - z i)]

theorem ctU_le_quarter (z x : (Fin d → ℝ)) (i : Fin d) : ctU z x i ≤ 1 / 4 := by
  unfold ctU
  nlinarith [sq_nonneg (x i - z i)]

theorem continuous_ctU (z : (Fin d → ℝ)) (i : Fin d) : Continuous (fun x => ctU z x i) := by
  simp only [ctU]
  have h1 : Continuous (fun x : (Fin d → ℝ) => x i) := continuous_apply i
  have h2 : Continuous (fun x : (Fin d → ℝ) => x i - z i) := h1.sub continuous_const
  have h3 : Continuous (fun x : (Fin d → ℝ) => (x i - z i) ^ 2) := h2.pow 2
  exact continuous_const.sub h3

theorem ctM_le_ctU [NeZero d] (z x : (Fin d → ℝ)) (i : Fin d) : ctM z x ≤ ctU z x i := by
  unfold ctM
  exact Finset.inf'_le (fun i => ctU z x i) (Finset.mem_univ i)

theorem exists_ctM_eq [NeZero d] (z x : (Fin d → ℝ)) : ∃ i, ctM z x = ctU z x i := by
  unfold ctM
  obtain ⟨i, _hi_mem, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun j => ctU z x j)
  exact ⟨i, hi⟩

theorem ctM_pos [NeZero d] {z x : (Fin d → ℝ)} (hx : x ∈ ctQ z) : 0 < ctM z x := by
  have h : ctM z x = ctU z x (Classical.choose (exists_ctM_eq z x)) :=
    Classical.choose_spec (exists_ctM_eq z x)
  rw [h]
  exact ctU_pos hx _

theorem ctM_le_quarter [NeZero d] (z x : (Fin d → ℝ)) : ctM z x ≤ 1 / 4 := by
  have i0 : Fin d := ⟨0, Nat.pos_of_neZero d⟩
  exact (ctM_le_ctU z x i0).trans (ctU_le_quarter z x i0)

theorem continuous_ctM [NeZero d] (z : (Fin d → ℝ)) : Continuous (ctM z) := by
  unfold ctM
  exact Continuous.finset_inf'_apply Finset.univ_nonempty (fun i _ => continuous_ctU z i)

/-- `m(x)` is at most the distance from `x_i` to the faces `x_i = z_i ± 1/2`. -/
theorem ctM_le_face [NeZero d] {z x : (Fin d → ℝ)} (hx : x ∈ ctQ z) (i : Fin d) :
    ctM z x ≤ 1 / 2 - |x i - z i| := by
  have ht : |x i - z i| < 1 / 2 := abs_sub_lt_of_mem_ctQ hx i
  have hU : ctU z x i ≤ 1 / 2 - |x i - z i| := by
    unfold ctU
    nlinarith [sq_abs (x i - z i), abs_nonneg (x i - z i),
      sq_nonneg (|x i - z i| - 1 / 2)]
  exact le_trans (ctM_le_ctU z x i) hU

/-- `u_i` is 1-Lipschitz for the sup norm on the (convex) cube. -/
theorem abs_ctU_sub_le {z x y : (Fin d → ℝ)} (hx : x ∈ ctQ z) (hy : y ∈ ctQ z) (i : Fin d) :
    |ctU z x i - ctU z y i| ≤ ‖x - y‖ := by
  have hbx : |x i - z i| < 1/2 := by
    have h : |x i - z i| ≤ ‖x - z‖ := by
      have := norm_le_pi_norm (x - z) i
      simpa [Pi.sub_apply, Real.norm_eq_abs] using this
    have hd : ‖x - z‖ < 1/2 := by simpa [dist_eq_norm] using hx
    linarith
  have hby : |y i - z i| < 1/2 := by
    have h : |y i - z i| ≤ ‖y - z‖ := by
      have := norm_le_pi_norm (y - z) i
      simpa [Pi.sub_apply, Real.norm_eq_abs] using this
    have hd : ‖y - z‖ < 1/2 := by simpa [dist_eq_norm] using hy
    linarith
  have hkey : ctU z x i - ctU z y i = (y i - x i) * ((y i - z i) + (x i - z i)) := by
    unfold ctU
    ring
  rw [hkey, abs_mul]
  have hsum : |(y i - z i) + (x i - z i)| ≤ 1 := by
    have hadd := abs_add_le (y i - z i) (x i - z i)
    linarith
  have hxy : |y i - x i| ≤ ‖x - y‖ := by
    have h := norm_le_pi_norm (x - y) i
    simp only [Pi.sub_apply, Real.norm_eq_abs] at h
    simpa [abs_sub_comm] using h
  calc |y i - x i| * |(y i - z i) + (x i - z i)| ≤ ‖x - y‖ * 1 :=
        mul_le_mul hxy hsum (abs_nonneg _) (norm_nonneg _)
    _ = ‖x - y‖ := by ring

theorem abs_ctM_sub_le [NeZero d] {z x y : (Fin d → ℝ)} (hx : x ∈ ctQ z) (hy : y ∈ ctQ z) :
    |ctM z x - ctM z y| ≤ ‖x - y‖ := by
  rw [abs_le]
  constructor
  · obtain ⟨i, hi⟩ := exists_ctM_eq (z := z) (x := x)
    have h1 : ctM z y ≤ ctU z y i := ctM_le_ctU z y i
    have h2 : -(‖x - y‖) ≤ ctU z x i - ctU z y i := by
      have h3 := neg_abs_le (ctU z x i - ctU z y i)
      linarith [abs_ctU_sub_le hx hy i]
    rw [hi]
    linarith
  · obtain ⟨i, hi⟩ := exists_ctM_eq (z := z) (x := y)
    have h1 : ctM z x ≤ ctU z x i := ctM_le_ctU z x i
    have h2 : ctU z x i - ctU z y i ≤ ‖x - y‖ := by
      have h3 := le_abs_self (ctU z x i - ctU z y i)
      linarith [abs_ctU_sub_le hx hy i]
    rw [hi]
    linarith

/-- The sup-ball of radius `m(x)` about `x ∈ Q` lies in `Q`. -/
theorem mem_ctQ_of_dist_lt_ctM [NeZero d] {z x y : (Fin d → ℝ)} (hx : x ∈ ctQ z)
    (hxy : ‖y - x‖ < ctM z x) : y ∈ ctQ z := by
  rw [ctQ, mem_ball_iff_norm]
  have hlt : (0 : ℝ) < 1 / 2 := by norm_num
  rw [pi_norm_lt_iff hlt]
  intro i
  have h1 : ‖(y - x) i‖ ≤ ‖y - x‖ := norm_le_pi_norm (y - x) i
  simp only [Pi.sub_apply, Real.norm_eq_abs] at h1 ⊢
  have h2 := ctM_le_face hx i
  have h3 : |y i - z i| ≤ |y i - x i| + |x i - z i| := by
    have := abs_add_le (y i - x i) (x i - z i)
    simpa using this
  linarith

/-- Lower bound: `m(x) ≥ (1/2 - |x_i - z_i|)/2` fails in general, but `u_i ≥ (1/2 - |x_i-z_i|)/2`. -/
theorem ctU_ge_face {z x : (Fin d → ℝ)} (hx : x ∈ ctQ z) (i : Fin d) :
    (1 / 2 - |x i - z i|) / 2 ≤ ctU z x i := by
  have hd : dist x z < 1 / 2 := hx
  have h1 : dist (x i) (z i) ≤ dist x z := dist_le_pi_dist x z i
  rw [Real.dist_eq] at h1
  have ht : |x i - z i| < 1 / 2 := lt_of_le_of_lt h1 hd
  have hle : |x i - z i| ≤ 1 / 2 := le_of_lt ht
  have hnn : 0 ≤ |x i - z i| := abs_nonneg _
  rw [ctU]
  nlinarith [sq_abs (x i - z i), mul_nonneg hnn (sub_nonneg.mpr hle)]

/-- Negative powers of `m` are bounded by the sum of negative powers of the coordinate profiles. -/
theorem ctM_rpow_neg_le_sum [NeZero d] {z x : (Fin d → ℝ)} (hx : x ∈ ctQ z)
    {a : ℝ} (ha : 0 ≤ a) :
    ctM z x ^ (-a) ≤ ∑ i : Fin d, ctU z x i ^ (-a) := by
  obtain ⟨i, hi⟩ := exists_ctM_eq (z := z) (x := x)
  rw [hi]
  exact Finset.single_le_sum (f := fun j => ctU z x j ^ (-a))
    (fun j _ => Real.rpow_nonneg (ctU_pos hx j).le _) (Finset.mem_univ i)

/-- `∫_{0}^{1/2} (1/2 - t)^{-a} dt = (1/2)^{1-a}/(1-a)` for `0 ≤ a < 1`. -/
theorem integral_half_rpow {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    IntegrableOn (fun t : ℝ => (1 / 2 - t) ^ (-a)) (Set.Ioo (0 : ℝ) (1 / 2)) volume ∧
      ∫ t in Set.Ioo (0 : ℝ) (1 / 2), (1 / 2 - t) ^ (-a) = (1 / 2 : ℝ) ^ (1 - a) / (1 - a) := by
  have hneg : (-1 : ℝ) < -a := by linarith
  constructor
  · have hh : IntervalIntegrable (fun x : ℝ => x ^ (-a)) volume (0 : ℝ) (1 / 2) :=
      intervalIntegral.intervalIntegrable_rpow' hneg
    have hcomp : IntervalIntegrable (fun x : ℝ => (1 / 2 - x) ^ (-a)) volume (0 : ℝ) (1 / 2) := by
      simpa using (hh.comp_sub_left (1 / 2)).symm
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (show (0 : ℝ) ≤ 1 / 2 by norm_num)] at hcomp
    exact hcomp
  · rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-a)) (1 / 2)]
    rw [integral_rpow (Or.inl hneg)]
    rw [show (1 : ℝ) / 2 - 1 / 2 = 0 by norm_num,
      Real.zero_rpow (show -a + (1 : ℝ) ≠ 0 by linarith)]
    ring_nf

/-- `(1/4 - t²)^{-a} ≤ 2^a (1/2 - |t|)^{-a}` on the open interval. -/
theorem profile_le_half_sub {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (ht : t ∈ Set.Ioo (-1 / 2 : ℝ) (1 / 2)) :
    (1 / 4 - t ^ 2) ^ (-a) ≤ 2 ^ a * (1 / 2 - |t|) ^ (-a) := by
  have hs0 : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hs1 : |t| < 1 / 2 := by
    rw [abs_lt]
    exact ⟨by linarith [ht.1], ht.2⟩
  have hspos : (0 : ℝ) < 1 / 2 - |t| := by linarith
  have hsabs : |t| ^ 2 = t ^ 2 := sq_abs t
  have hle : (1 / 2 - |t|) / 2 ≤ 1 / 4 - t ^ 2 := by
    nlinarith [hsabs, hs0, hspos]
  have hpos1 : (0 : ℝ) < (1 / 2 - |t|) / 2 := by linarith
  have hneg : -a ≤ 0 := by linarith
  have key := Real.rpow_le_rpow_of_nonpos hpos1 hle hneg
  calc (1 / 4 - t ^ 2) ^ (-a) ≤ ((1 / 2 - |t|) / 2) ^ (-a) := key
    _ = 2 ^ a * (1 / 2 - |t|) ^ (-a) := by
        rw [Real.div_rpow (by linarith) (show (0 : ℝ) ≤ 2 by norm_num)]
        rw [Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num) a]
        rw [div_inv_eq_mul]
        ring

/-- The evenness reduction: the integral of `(1/2 - |t|)^{-a}` over `(-1/2,1/2)` is twice the half integral. -/
theorem integral_abs_half_rpow {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    IntegrableOn (fun t : ℝ => (1 / 2 - |t|) ^ (-a)) (Set.Ioo (-1 / 2 : ℝ) (1 / 2)) volume ∧
      ∫ t in Set.Ioo (-1 / 2 : ℝ) (1 / 2), (1 / 2 - |t|) ^ (-a) =
        2 * ((1 / 2 : ℝ) ^ (1 - a) / (1 - a)) := by
  obtain ⟨hgint, hgval⟩ := integral_half_rpow ha ha1
  have hemb : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
  have hpre : (fun x : ℝ => -x) ⁻¹' (Set.Ioo (0 : ℝ) (1 / 2)) = Set.Ioo (-1 / 2) 0 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  have hgint' : IntegrableOn (fun y : ℝ => (1 / 2 - y) ^ (-a)) (Set.Ioo (0 : ℝ) (1 / 2))
      (Measure.map (fun x : ℝ => -x) volume) := by
    rwa [Measure.map_neg_eq_self volume]
  have hLint'' : IntegrableOn ((fun y : ℝ => (1 / 2 - y) ^ (-a)) ∘ (fun x : ℝ => -x))
      ((fun x : ℝ => -x) ⁻¹' (Set.Ioo (0 : ℝ) (1 / 2))) :=
    (hemb.integrableOn_map_iff (f := fun y : ℝ => (1 / 2 - y) ^ (-a))
      (s := Set.Ioo (0 : ℝ) (1 / 2)) (μ := volume)).mp hgint'
  rw [hpre] at hLint''
  have hLint : IntegrableOn (fun x : ℝ => (1 / 2 - |x|) ^ (-a)) (Set.Ioo (-1 / 2 : ℝ) 0) :=
    hLint''.congr_fun (fun x hx => by
      simp only [Function.comp_apply, abs_of_neg hx.2]) measurableSet_Ioo
  have hRint : IntegrableOn (fun x : ℝ => (1 / 2 - |x|) ^ (-a)) (Set.Ioo (0 : ℝ) (1 / 2)) :=
    hgint.congr_fun (fun x hx => by
      simp only [abs_of_pos hx.1]) measurableSet_Ioo
  have hmap : ∫ y in Set.Ioo (0 : ℝ) (1 / 2), (1 / 2 - y) ^ (-a) ∂Measure.map (fun x : ℝ => -x) volume
      = ∫ x in (fun x : ℝ => -x) ⁻¹' (Set.Ioo (0 : ℝ) (1 / 2)), (1 / 2 - (-x)) ^ (-a) :=
    MeasurableEmbedding.setIntegral_map (Homeomorph.neg ℝ).measurableEmbedding
      (fun y : ℝ => (1 / 2 - y) ^ (-a)) (Set.Ioo (0 : ℝ) (1 / 2))
  rw [Measure.map_neg_eq_self volume, hpre] at hmap
  have hLval : ∫ x in Set.Ioo (-1 / 2 : ℝ) 0, (1 / 2 - |x|) ^ (-a) =
      (1 / 2 : ℝ) ^ (1 - a) / (1 - a) := by
    have hcongr : ∫ x in Set.Ioo (-1 / 2 : ℝ) 0, (1 / 2 - (-x)) ^ (-a) =
        ∫ x in Set.Ioo (-1 / 2 : ℝ) 0, (1 / 2 - |x|) ^ (-a) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      simp only [abs_of_neg hx.2]
    rw [← hcongr, ← hmap]
    exact hgval
  have hRval : ∫ x in Set.Ioo (0 : ℝ) (1 / 2), (1 / 2 - |x|) ^ (-a) =
      (1 / 2 : ℝ) ^ (1 - a) / (1 - a) := by
    rw [← hgval]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    simp only [abs_of_pos hx.1]
  have hsplitR : Set.Ioc (-1 / 2 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) (1 / 2) = Set.Ioo (-1 / 2) (1 / 2) := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioo]
    constructor
    · rintro (h | h)
      · exact ⟨h.1, by linarith [h.2]⟩
      · exact ⟨by linarith [h.1], h.2⟩
    · intro hx
      rcases le_or_gt x 0 with h | h
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨h, hx.2⟩
  have hdisj : Disjoint (Set.Ioc (-1 / 2 : ℝ) 0) (Set.Ioo (0 : ℝ) (1 / 2)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact absurd hx2.1 (not_lt.mpr hx1.2)
  have hIntR : IntegrableOn (fun x : ℝ => (1 / 2 - |x|) ^ (-a)) (Set.Ioc (-1 / 2 : ℝ) 0) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo (f := fun x : ℝ => (1 / 2 - |x|) ^ (-a))
      (a := (-1 / 2 : ℝ)) (b := (0 : ℝ))).mpr hLint
  constructor
  · have : IntegrableOn (fun x : ℝ => (1 / 2 - |x|) ^ (-a))
        (Set.Ioc (-1 / 2 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) (1 / 2)) := hIntR.union hRint
    rwa [← hsplitR]
  · rw [← hsplitR, setIntegral_union hdisj measurableSet_Ioo hIntR hRint,
      integral_Ioc_eq_integral_Ioo, hLval, hRval]
    ring

/-- Integral over a product of open intervals of a function of one coordinate. -/
theorem integral_pi_single_coord (i : Fin d) (a b : Fin d → ℝ) (hab : ∀ j, a j ≤ b j) (f : ℝ → ℝ) :
    ∫ x in Set.pi Set.univ (fun j => Set.Ioo (a j) (b j)), f (x i) =
      (∏ j ∈ Finset.univ.erase i, (b j - a j)) * ∫ t in Set.Ioo (a i) (b i), f t := by
  classical
  set g : Fin d → ℝ → ℝ :=
    fun j t => (Set.Ioo (a j) (b j)).indicator (fun s => if j = i then f s else (1 : ℝ)) t with hg
  have hmeas : MeasurableSet (Set.pi Set.univ (fun j => Set.Ioo (a j) (b j))) :=
    MeasurableSet.univ_pi (fun j => isOpen_Ioo.measurableSet)
  have hpoint : ∀ x : (Fin d → ℝ),
      (Set.pi Set.univ (fun j => Set.Ioo (a j) (b j))).indicator (fun x => f (x i)) x =
        ∏ j, g j (x j) := by
    intro x
    by_cases hx : x ∈ Set.pi Set.univ (fun j => Set.Ioo (a j) (b j))
    · rw [Set.indicator_of_mem hx]
      have hgx : ∀ j, g j (x j) = (if j = i then f (x j) else (1 : ℝ)) := by
        intro j
        simp only [hg]
        exact Set.indicator_of_mem (hx j (Set.mem_univ j)) _
      have hp : ∏ j, g j (x j) = ∏ j, (if j = i then f (x j) else (1 : ℝ)) := by
        apply Finset.prod_congr rfl
        intro j _
        exact hgx j
      rw [hp, Finset.prod_ite_eq']
      simp
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨k, hk⟩ : ∃ k, x k ∉ Set.Ioo (a k) (b k) := by
        simpa only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] using hx
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by
        simp only [hg]
        exact Set.indicator_of_notMem hk _)
  have hgi : ∫ t, g i t = ∫ t in Set.Ioo (a i) (b i), f t := by
    have hfun : g i = (Set.Ioo (a i) (b i)).indicator f := by
      funext t
      simp only [hg]
      by_cases ht : t ∈ Set.Ioo (a i) (b i)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
        simp
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
    rw [hfun]
    exact integral_indicator measurableSet_Ioo
  have hgj : ∀ j, j ≠ i → ∫ t, g j t = b j - a j := by
    intro j hj
    have h1 : ∫ t, g j t = volume.real (Set.Ioo (a j) (b j)) := by
      have hfun : g j = (Set.Ioo (a j) (b j)).indicator (fun _ => (1 : ℝ)) := by
        funext t
        simp only [hg]
        by_cases ht : t ∈ Set.Ioo (a j) (b j)
        · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
          simp [hj]
        · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
      rw [hfun]
      exact integral_indicator_one measurableSet_Ioo
    rw [h1, measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr (hab j))]
  calc ∫ x in Set.pi Set.univ (fun j => Set.Ioo (a j) (b j)), f (x i)
      = ∫ x : (Fin d → ℝ), ∏ j, g j (x j) := by
          rw [← integral_indicator hmeas]
          exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∏ j, ∫ t, g j t := integral_fintype_prod_eq_prod (fun j (t : ℝ) => g j t)
    _ = (∏ j ∈ Finset.univ.erase i, (b j - a j)) * ∫ t in Set.Ioo (a i) (b i), f t := by
          rw [← Finset.prod_erase_mul Finset.univ (fun j => ∫ t, g j t) (Finset.mem_univ i)]
          have hp : ∏ x ∈ Finset.univ.erase i, ∫ t, g x t =
              ∏ x ∈ Finset.univ.erase i, (b x - a x) :=
            Finset.prod_congr rfl (fun x hx => hgj x (Finset.mem_erase.mp hx).1)
          rw [hp, hgi]

theorem integrableOn_pi_single_coord (i : Fin d) (a b : Fin d → ℝ) (hab : ∀ j, a j ≤ b j) (f : ℝ → ℝ)
    (hf : IntegrableOn f (Set.Ioo (a i) (b i)) volume) :
    IntegrableOn (fun x : (Fin d → ℝ) => f (x i)) (Set.pi Set.univ (fun j => Set.Ioo (a j) (b j))) volume := by
  classical
  let g : Fin d → ℝ → ℝ := fun j y =>
    if j = i then (Set.Ioo (a j) (b j)).indicator f y
    else (Set.Ioo (a j) (b j)).indicator (fun _ => (1:ℝ)) y
  have hs : MeasurableSet (Set.pi Set.univ (fun j => Set.Ioo (a j) (b j))) :=
    MeasurableSet.pi Set.countable_univ (fun j _ => measurableSet_Ioo)
  have hpt : ∀ x : Fin d → ℝ,
      (∏ j, g j (x j))
      = (Set.pi Set.univ (fun j => Set.Ioo (a j) (b j))).indicator (fun x => f (x i)) x := by
    intro x
    by_cases hx : x ∈ Set.pi Set.univ (fun j => Set.Ioo (a j) (b j))
    · rw [Set.indicator_of_mem hx]
      have hxp : ∀ j, x j ∈ Set.Ioo (a j) (b j) := by
        intro j; exact (Set.mem_pi.mp hx) j (Set.mem_univ j)
      rw [Finset.prod_eq_single i]
      · simp only [g, if_pos rfl, Set.indicator_of_mem (hxp i)]
      · intro b _ hb
        simp only [g, if_neg hb]
        exact Set.indicator_of_mem (hxp b) _
      · intro h; exact absurd (Finset.mem_univ i) h
    · rw [Set.indicator_of_notMem hx]
      have hex : ∃ j, x j ∉ Set.Ioo (a j) (b j) := by
        by_contra h
        apply hx
        rw [Set.mem_pi]
        intro j _
        by_contra hj
        exact h ⟨j, hj⟩
      obtain ⟨j, hj⟩ := hex
      rw [Finset.prod_eq_zero (Finset.mem_univ j)]
      by_cases hji : j = i
      · subst hji
        simp only [g, if_pos rfl, Set.indicator_of_notMem hj]
      · simp only [g, if_neg hji, Set.indicator_of_notMem hj]
  have hmain : Integrable (fun x : Fin d → ℝ => ∏ j, g j (x j)) volume := by
    rw [volume_pi]
    refine Integrable.fintype_prod (μ := fun _ : Fin d => volume) (f := g) ?_
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [g, if_pos rfl]
      exact (integrable_indicator_iff measurableSet_Ioo).mpr hf
    · simp only [g, if_neg hj]
      rw [integrable_indicator_iff measurableSet_Ioo]
      exact integrableOn_const (measure_Ioo_lt_top.ne)
  refine (integrable_indicator_iff hs).mp ?_
  convert hmain using 1
  ext x
  exact (hpt x).symm

theorem ctQ_eq_pi (z : (Fin d → ℝ)) :
    ctQ z = Set.pi Set.univ (fun j => Set.Ioo (z j - 1 / 2) (z j + 1 / 2)) := by
  unfold ctQ
  rw [ball_pi z (by norm_num : (0:ℝ) < 1/2)]
  simp only [Real.ball_eq_Ioo]

/-- Translation of the profile integral. -/
theorem integral_profile_translate {a : ℝ} (c : ℝ) :
    ∫ t in Set.Ioo (c - 1 / 2) (c + 1 / 2), (1 / 4 - (t - c) ^ 2) ^ (-a) =
      ∫ t in Set.Ioo (-1 / 2 : ℝ) (1 / 2), (1 / 4 - t ^ 2) ^ (-a) := by
  have h_c_le : c - 1 / 2 ≤ c + 1 / 2 := by linarith
  have h_zero_le : (-1 / 2 : ℝ) ≤ 1 / 2 := by linarith
  -- Convert both set integrals to interval integrals
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le h_c_le, ← intervalIntegral.integral_of_le h_zero_le]
  -- Now apply the change of variables lemma to the LHS
  rw [(intervalIntegral.integral_comp_sub_right (fun t => (1 / 4 - t ^ 2) ^ (-a)) c)]
  -- Simplify the bounds: (c - 1/2) - c = -1/2 and (c + 1/2) - c = 1/2
  ring_nf

theorem integrableOn_profile_translate {a : ℝ} (c : ℝ)
    (h : IntegrableOn (fun t : ℝ => (1 / 4 - t ^ 2) ^ (-a)) (Set.Ioo (-1 / 2 : ℝ) (1 / 2)) volume) :
    IntegrableOn (fun t : ℝ => (1 / 4 - (t - c) ^ 2) ^ (-a)) (Set.Ioo (c - 1 / 2) (c + 1 / 2)) volume := by
  -- Use MeasurePreserving.integrableOn_comp_preimage with the substitution e := fun t => t - c
  let e := fun t : ℝ => t - c

  -- Show that e is measure-preserving for the Lebesgue measure
  have measure_preserving : MeasurePreserving e volume volume :=
    measurePreserving_sub_right volume c

  -- Show that e is a measurable embedding (use the MeasurableEquiv which gives us this)
  have measurable_embedding : MeasurableEmbedding e :=
    (MeasurableEquiv.subRight c : ℝ ≃ᵐ ℝ).measurableEmbedding

  -- Apply the lemma: IntegrableOn (f ∘ e) (e ⁻¹' s) μ ↔ IntegrableOn f s ν
  -- where f = fun t => (1/4 - t^2)^(-a) and s = Ioo (-1/2) (1/2)
  have key := MeasurePreserving.integrableOn_comp_preimage measure_preserving measurable_embedding (f := fun t => (1 / 4 - t ^ 2) ^ (-a)) (s := Set.Ioo (-1 / 2 : ℝ) (1 / 2))

  -- key : IntegrableOn (fun t => (1/4 - (t - c)^2)^(-a)) (e ⁻¹' Ioo (-1/2) (1/2)) volume ↔ IntegrableOn (fun t => (1/4 - t^2)^(-a)) (Ioo (-1/2) (1/2)) volume

  -- Show that e ⁻¹' Ioo (-1/2) (1/2) = Ioo (c - 1/2) (c + 1/2)
  have preimage_eq : e ⁻¹' Set.Ioo (-1 / 2 : ℝ) (1 / 2) = Set.Ioo (c - 1 / 2) (c + 1 / 2) := by
    ext x
    simp [e, Set.mem_Ioo, Set.mem_preimage]
    constructor <;> (intro ⟨h1, h2⟩; constructor <;> linarith)

  rw [preimage_eq] at key
  exact key.mpr h

/-- One-dimensional integral of the profile: `∫_{-1/2}^{1/2} (1/4 - t^2)^{-a} dt ≤ 4^a/(1-a)`. -/
theorem integral_profile_rpow_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    IntegrableOn (fun t : ℝ => (1 / 4 - t ^ 2) ^ (-a)) (Set.Ioo (-1 / 2 : ℝ) (1 / 2)) volume ∧
      ∫ t in Set.Ioo (-1 / 2 : ℝ) (1 / 2), (1 / 4 - t ^ 2) ^ (-a) ≤ 4 ^ a / (1 - a) := by
  obtain ⟨hint, hval⟩ := integral_abs_half_rpow ha ha1
  have hbase : ∀ t ∈ Set.Ioo (-1 / 2 : ℝ) (1 / 2), 0 < 1 / 4 - t ^ 2 := by
    intro t ht
    have h1 := ht.1
    have h2 := ht.2
    nlinarith
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (1 / 4 - t ^ 2) ^ (-a))
      (volume.restrict (Set.Ioo (-1 / 2 : ℝ) (1 / 2))) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
    apply ContinuousOn.rpow_const (by fun_prop)
    intro t ht
    left
    exact (hbase t ht).ne'
  have hbound : ∀ t ∈ Set.Ioo (-1 / 2 : ℝ) (1 / 2),
      ‖(1 / 4 - t ^ 2) ^ (-a)‖ ≤ 2 ^ a * (1 / 2 - |t|) ^ (-a) := by
    intro t ht
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hbase t ht).le _)]
    exact profile_le_half_sub ha ht
  have hint' : IntegrableOn (fun t : ℝ => (1 / 4 - t ^ 2) ^ (-a)) (Set.Ioo (-1 / 2 : ℝ) (1 / 2))
      volume :=
    Integrable.mono' (hint.const_mul (2 ^ a)) hmeas
      ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall hbound))
  refine ⟨hint', ?_⟩
  calc ∫ t in Set.Ioo (-1 / 2 : ℝ) (1 / 2), (1 / 4 - t ^ 2) ^ (-a)
      ≤ ∫ t in Set.Ioo (-1 / 2 : ℝ) (1 / 2), 2 ^ a * (1 / 2 - |t|) ^ (-a) :=
        setIntegral_mono_on hint' (hint.const_mul _) measurableSet_Ioo
          (fun t ht => profile_le_half_sub ha ht)
    _ = 2 ^ a * (2 * ((1 / 2 : ℝ) ^ (1 - a) / (1 - a))) := by
        rw [integral_const_mul, hval]
    _ = 4 ^ a / (1 - a) := by
        have h1 : (1 / 2 : ℝ) ^ (1 - a) = 2 ^ (a - 1) := by
          rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
          congr 1; ring
        have h2 : (2 : ℝ) * 2 ^ (a - 1) = 2 ^ a := by
          rw [Real.rpow_sub_one (by norm_num) a]; ring
        have h3 : (4 : ℝ) ^ a = 2 ^ a * 2 ^ a := by
          rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
        rw [h1, h3]
        have : (2 : ℝ) ^ a * (2 * (2 ^ (a - 1) / (1 - a))) = 2 ^ a * (2 * 2 ^ (a - 1)) / (1 - a) := by
          ring
        rw [this, h2]

/-- The coordinate-profile integral over the cube (Fubini on the product). -/
theorem integral_ctU_rpow_le (z : (Fin d → ℝ)) (i : Fin d) {a : ℝ} (ha : 0 ≤ a)
    (ha1 : a < 1) :
    IntegrableOn (fun x => ctU z x i ^ (-a)) (ctQ z) volume ∧
      ∫ x in ctQ z, ctU z x i ^ (-a) ≤ 4 ^ a / (1 - a) := by
  rw [ctQ_eq_pi z]
  set g : ℝ → ℝ := fun t => (1 / 4 - (t - z i) ^ 2) ^ (-a) with hg
  have hfun : (fun x : (Fin d → ℝ) => ctU z x i ^ (-a)) = fun x => g (x i) := by
    funext x; simp only [ctU, hg]
  constructor
  · rw [hfun]
    apply integrableOn_pi_single_coord i (fun j => z j - 1 / 2) (fun j => z j + 1 / 2) (f := g)
    · intro j; linarith
    · rw [hg]
      exact integrableOn_profile_translate (z i) (integral_profile_rpow_le ha ha1).1
  · rw [hfun]
    have hint := integral_pi_single_coord i (fun j => z j - 1 / 2) (fun j => z j + 1 / 2)
        (fun j => by linarith) (f := g)
    rw [hint]
    have hprod : (∏ j ∈ Finset.univ.erase i, ((z j + 1 / 2) - (z j - 1 / 2))) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      ring
    rw [hprod, one_mul]
    simp only [hg]
    rw [integral_profile_translate (z i)]
    exact (integral_profile_rpow_le ha ha1).2

/-- **`∫_Q m^{-a} ≤ d 4^a/(1-a)` for `0 ≤ a < 1`.** -/
theorem integral_ctM_rpow_le [NeZero d] (z : (Fin d → ℝ)) {a : ℝ} (ha : 0 ≤ a)
    (ha1 : a < 1) :
    IntegrableOn (fun x => ctM z x ^ (-a)) (ctQ z) volume ∧
      ∫ x in ctQ z, ctM z x ^ (-a) ≤ (d : ℝ) * (4 ^ a / (1 - a)) := by
  constructor
  · have hg : Integrable (fun x => ∑ i : Fin d, ctU z x i ^ (-a)) (volume.restrict (ctQ z)) :=
      MeasureTheory.integrable_finset_sum Finset.univ (fun i _ => (integral_ctU_rpow_le z i ha ha1).1)
    refine MeasureTheory.Integrable.mono' hg ?_ ?_
    · have hcont : ContinuousOn (fun x => ctM z x ^ (-a)) (ctQ z) :=
        (continuous_ctM z).continuousOn.rpow_const (fun x hx => Or.inl (ne_of_gt (ctM_pos hx)))
      exact hcont.aestronglyMeasurable isOpen_ball.measurableSet
    · rw [ae_restrict_iff' isOpen_ball.measurableSet]
      refine Eventually.of_forall (fun x hx => ?_)
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (ctM_pos hx).le _)]
      exact ctM_rpow_neg_le_sum hx ha
  · have hf : Integrable (fun x => ctM z x ^ (-a)) (volume.restrict (ctQ z)) := by
      have hg : Integrable (fun x => ∑ i : Fin d, ctU z x i ^ (-a)) (volume.restrict (ctQ z)) :=
        MeasureTheory.integrable_finset_sum Finset.univ (fun i _ => (integral_ctU_rpow_le z i ha ha1).1)
      refine MeasureTheory.Integrable.mono' hg ?_ ?_
      · have hcont : ContinuousOn (fun x => ctM z x ^ (-a)) (ctQ z) :=
          (continuous_ctM z).continuousOn.rpow_const (fun x hx => Or.inl (ne_of_gt (ctM_pos hx)))
        exact hcont.aestronglyMeasurable isOpen_ball.measurableSet
      · rw [ae_restrict_iff' isOpen_ball.measurableSet]
        refine Eventually.of_forall (fun x hx => ?_)
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (ctM_pos hx).le _)]
        exact ctM_rpow_neg_le_sum hx ha
    have hg : Integrable (fun x => ∑ i : Fin d, ctU z x i ^ (-a)) (volume.restrict (ctQ z)) :=
      MeasureTheory.integrable_finset_sum Finset.univ (fun i _ => (integral_ctU_rpow_le z i ha ha1).1)
    have hmono : ∫ x in ctQ z, ctM z x ^ (-a) ≤ ∫ x in ctQ z, (∑ i : Fin d, ctU z x i ^ (-a)) :=
      setIntegral_mono_on hf hg isOpen_ball.measurableSet (fun x hx => ctM_rpow_neg_le_sum hx ha)
    have hsum : ∫ x in ctQ z, (∑ i : Fin d, ctU z x i ^ (-a)) = ∑ i : Fin d, ∫ x in ctQ z, ctU z x i ^ (-a) := by
      rw [integral_finset_sum]
      exact fun i _ => (integral_ctU_rpow_le z i ha ha1).1
    have hbd : ∑ i : Fin d, ∫ x in ctQ z, ctU z x i ^ (-a) ≤ (d : ℝ) * (4 ^ a / (1 - a)) := by
      calc ∑ i : Fin d, ∫ x in ctQ z, ctU z x i ^ (-a)
          ≤ ∑ _i : Fin d, (4 ^ a / (1 - a)) :=
            Finset.sum_le_sum (fun i _ => (integral_ctU_rpow_le z i ha ha1).2)
        _ = (d : ℝ) * (4 ^ a / (1 - a)) := by
            simp [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    exact le_trans hmono (le_trans (le_of_eq hsum) hbd)

/-- A `β`-Hölder function is continuous. -/
theorem holder_continuous {G : (Fin d → ℝ) → ℝ} {K β : ℝ} (hβ : 0 < β)
    (hG : ∀ x y, |G x - G y| ≤ K * ‖x - y‖ ^ β) : Continuous G := by
  rw [continuous_iff_continuousAt]
  intro x
  have h1 : Tendsto (fun y : Fin d → ℝ => ‖y - x‖) (𝓝 x) (𝓝 0) := by
    have hc : Continuous (fun y : Fin d → ℝ => ‖y - x‖) := (continuous_id.sub continuous_const).norm
    simpa using hc.tendsto x
  have h2 : Tendsto (fun y : Fin d → ℝ => ‖y - x‖ ^ β) (𝓝 x) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const (0 : ℝ) β (Or.inr hβ.le)).tendsto.comp h1
    rwa [Real.zero_rpow hβ.ne'] at this
  have h3 : Tendsto (fun y : Fin d → ℝ => K * ‖y - x‖ ^ β) (𝓝 x) (𝓝 0) := by
    simpa using h2.const_mul K
  have hlim : Tendsto (fun y => G x + K * ‖y - x‖ ^ β) (𝓝 x) (𝓝 (G x)) := by
    simpa using h3.const_add (G x)
  have hlim2 : Tendsto (fun y => G x - K * ‖y - x‖ ^ β) (𝓝 x) (𝓝 (G x)) := by
    simpa using (tendsto_const_nhds (x := G x)).sub h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim2 hlim (fun y => ?_) (fun y => ?_)
  · have h := (abs_le.1 (hG y x)).1
    rw [norm_sub_rev y x] at h
    show G x - K * ‖y - x‖ ^ β ≤ G y
    rw [norm_sub_rev y x]
    linarith
  · have h := (abs_le.1 (hG y x)).2
    show G y ≤ G x + K * ‖y - x‖ ^ β
    linarith

/-- The Euclidean norm is at most `√d` times the sup norm. -/
theorem euclid_le_sqrt_mul_norm (x y : (Fin d → ℝ)) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt (d : ℝ) * ‖x - y‖ := by
  have hsum : ∑ j : Fin d, (x j - y j) ^ 2 ≤ (d : ℝ) * ‖x - y‖ ^ 2 := by
    calc ∑ j : Fin d, (x j - y j) ^ 2 ≤ ∑ _j : Fin d, ‖x - y‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          have h : |x j - y j| ≤ ‖x - y‖ := by
            have := norm_le_pi_norm (x - y) j
            simpa [Real.norm_eq_abs] using this
          have := sq_le_sq' (by linarith [abs_nonneg (x j - y j), neg_abs_le (x j - y j)]) (le_trans (le_abs_self _) h)
          simpa using this
      _ = (d : ℝ) * ‖x - y‖ ^ 2 := by simp
  calc Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt ((d : ℝ) * ‖x - y‖ ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (d : ℝ) * ‖x - y‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- The sup norm is at most the Euclidean norm. -/
theorem norm_le_euclid (x y : (Fin d → ℝ)) :
    ‖x - y‖ ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  rw [Real.norm_eq_abs, Pi.sub_apply]
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun j : Fin d => (x j - y j) ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)

end SubdiffusiveProcess.CubeTrace
