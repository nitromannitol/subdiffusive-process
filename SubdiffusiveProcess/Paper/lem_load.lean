module

public import SubdiffusiveProcess.Paper.lane4_smoothed_neumann_load
public import SubdiffusiveProcess.Main.OriginalGridResponseConvolution
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CubeNegativeL2Norm
public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Sobolev.BoundaryEnergy
public import SubdiffusiveProcess.Sobolev.FoldDiscounts
public import SubdiffusiveProcess.Sobolev.LoadApproximation
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
public import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Paper.lem_load_fourier_face_translation
public import SubdiffusiveProcess.Paper.lane4_neumann_load
public import SubdiffusiveProcess.Paper.lane4_smoothed_load_properties
public import SubdiffusiveProcess.Paper.lane4_neumann_boundary_identity

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

section AuxLemLoad

/-!
Helpers for `lem_load` (physical-space route, no Fourier transform):
the coupling kernel and slab lemma (`aux_lem_load_slab`, a Campanato estimate against the
Gagliardo double integral `aux_lem_load_gag`), the dyadic chain (`aux_lem_load_chain`),
coordinate integration by parts on `H¹(Q)` (`aux_lem_load_weak_ibp`), the slab-flux bound
(`aux_lem_load_flux`), and the face-by-face assembly (`aux_lem_load_face`,
`aux_lem_load_core`, `aux_lem_load_final`).
-/

open Filter
open scoped Topology

/-- One-dimensional cell kernel: `n` times the indicator that `s, t` lie in the same cell
`[k/n, (k+1)/n)`. -/
def aux_lem_load_cell (n : ℕ) (s t : ℝ) : ℝ :=
  if ⌊(n : ℝ) * s⌋ = ⌊(n : ℝ) * t⌋ then (n : ℝ) else 0

theorem aux_lem_load_cell_symm (n : ℕ) (s t : ℝ) :
    aux_lem_load_cell n s t = aux_lem_load_cell n t s := by
  unfold aux_lem_load_cell
  by_cases h : ⌊(n : ℝ) * s⌋ = ⌊(n : ℝ) * t⌋
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem aux_lem_load_cell_nonneg (n : ℕ) (s t : ℝ) : 0 ≤ aux_lem_load_cell n s t := by
  unfold aux_lem_load_cell; split_ifs <;> positivity

theorem aux_lem_load_cell_le (n : ℕ) (s t : ℝ) : aux_lem_load_cell n s t ≤ n := by
  unfold aux_lem_load_cell; split_ifs <;> simp

theorem aux_lem_load_cell_dist {n : ℕ} (hn : 0 < n) {s t : ℝ}
    (h : aux_lem_load_cell n s t ≠ 0) : |s - t| < 1 / n := by
  unfold aux_lem_load_cell at h
  split_ifs at h with hst
  · have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hst
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    rw [← mul_sub, abs_mul, abs_of_pos hn'] at h1
    rw [lt_div_iff₀ hn']
    linarith [mul_comm (n:ℝ) |s - t|]
  · exact absurd rfl h

theorem aux_lem_load_cell_measurable (n : ℕ) :
    Measurable (fun q : ℝ × ℝ => aux_lem_load_cell n q.1 q.2) := by
  unfold aux_lem_load_cell
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_eq_fun
    (Int.measurable_floor.comp (measurable_const.mul measurable_fst))
    (Int.measurable_floor.comp (measurable_const.mul measurable_snd))

theorem aux_lem_load_cell_integral {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) :
    ∫ t in Ioo (0:ℝ) 1, aux_lem_load_cell n s t = 1 := by
  set k := ⌊(n : ℝ) * s⌋ with hk
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hk0 : 0 ≤ k := Int.floor_nonneg.mpr (by nlinarith [hs.1])
  have hkn : k + 1 ≤ n := by
    have : k < n := by
      rw [hk, Int.floor_lt]; push_cast; nlinarith [hs.2]
    omega
  have hset : ∀ t, aux_lem_load_cell n s t =
      (Ico ((k:ℝ)/n) ((k+1)/n)).indicator (fun _ => (n:ℝ)) t := by
    intro t
    unfold aux_lem_load_cell
    rw [← hk]
    by_cases ht : k = ⌊(n:ℝ) * t⌋
    · rw [if_pos ht, indicator_of_mem]
      rw [eq_comm, Int.floor_eq_iff] at ht
      constructor
      · rw [div_le_iff₀ hn']; linarith [ht.1]
      · rw [lt_div_iff₀ hn']; linarith [ht.2]
    · rw [if_neg ht, indicator_of_notMem]
      intro hmem
      apply ht
      rw [eq_comm, Int.floor_eq_iff]
      constructor
      · have := hmem.1; rw [div_le_iff₀ hn'] at this; linarith
      · have := hmem.2; rw [lt_div_iff₀ hn'] at this; linarith
  simp_rw [hset]
  rw [← integral_Icc_eq_integral_Ioo, integral_indicator measurableSet_Ico,
    Measure.restrict_restrict measurableSet_Ico]
  have hsub : Ico ((k:ℝ)/n) ((k+1)/n) ∩ Icc 0 1 = Ico ((k:ℝ)/n) ((k+1)/n) := by
    apply inter_eq_left.mpr
    intro t ht
    constructor
    · exact le_trans (div_nonneg (by exact_mod_cast hk0) hn'.le) ht.1
    · refine le_trans ht.2.le ?_
      rw [div_le_one hn']; exact_mod_cast hkn
  rw [hsub, setIntegral_const, smul_eq_mul]
  have hle : (k:ℝ)/n ≤ (k+1)/n := by
    apply div_le_div_of_nonneg_right _ hn'.le; linarith
  rw [Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
  field_simp
  ring

theorem aux_lem_load_Q_eq (d : ℕ) :
    (unitNeumannCube d : Set (SpatialCoordinates d)) =
      Set.pi Set.univ (fun _ : Fin d => Ioo (0:ℝ) 1) := by
  rw [unitNeumannCube, centeredCube_eq_pi]
  ext x
  simp only [Set.mem_pi, mem_univ, mem_Ioo, forall_const]
  norm_num

theorem aux_lem_load_restrict_Q (d : ℕ) :
    volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)) =
      Measure.pi (fun _ : Fin d => volume.restrict (Ioo (0:ℝ) 1)) := by
  rw [aux_lem_load_Q_eq, volume_pi, Measure.restrict_pi_pi]

theorem aux_lem_load_integral_prod_Q {d : ℕ} (f : Fin d → ℝ → ℝ) :
    ∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), ∏ j, f j (y j) =
      ∏ j, ∫ t in Ioo (0:ℝ) 1, f j t := by
  rw [aux_lem_load_restrict_Q]
  exact integral_fintype_prod_eq_prod (fun j t => f j t)

/-- The coupling kernel on `Q × Q`: product of the normal weights `w1(x_i) w2(y_i)` and the
tangential cell kernels. -/
def aux_lem_load_kernel {d : ℕ} (i : Fin d) (n : ℕ) (w1 w2 : ℝ → ℝ)
    (x y : SpatialCoordinates d) : ℝ :=
  ∏ j, (if j = i then w1 (x j) * w2 (y j) else aux_lem_load_cell n (x j) (y j))

theorem aux_lem_load_kernel_marg_right {d : ℕ} (i : Fin d) {n : ℕ} (hn : 0 < n)
    (w1 w2 : ℝ → ℝ) {x : SpatialCoordinates d}
    (hx : x ∈ (unitNeumannCube d : Set (SpatialCoordinates d))) :
    ∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), aux_lem_load_kernel i n w1 w2 x y =
      w1 (x i) * ∫ t in Ioo (0:ℝ) 1, w2 t := by
  rw [aux_lem_load_Q_eq] at hx
  unfold aux_lem_load_kernel
  rw [aux_lem_load_integral_prod_Q
    (fun j t => if j = i then w1 (x j) * w2 t else aux_lem_load_cell n (x j) t)]
  have h : ∀ j, (∫ t in Ioo (0:ℝ) 1,
      (if j = i then w1 (x j) * w2 t else aux_lem_load_cell n (x j) t)) =
      (if j = i then w1 (x i) * ∫ t in Ioo (0:ℝ) 1, w2 t else 1) := by
    intro j
    by_cases hj : j = i
    · subst hj; simp only [if_true]; exact integral_const_mul _ _
    · simp only [hj, if_false]
      exact aux_lem_load_cell_integral hn (hx j (mem_univ j))
  rw [Finset.prod_congr rfl (fun j _ => h j), Finset.prod_ite_eq']
  simp

theorem aux_lem_load_kernel_marg_left {d : ℕ} (i : Fin d) {n : ℕ} (hn : 0 < n)
    (w1 w2 : ℝ → ℝ) {y : SpatialCoordinates d}
    (hy : y ∈ (unitNeumannCube d : Set (SpatialCoordinates d))) :
    ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), aux_lem_load_kernel i n w1 w2 x y =
      (∫ t in Ioo (0:ℝ) 1, w1 t) * w2 (y i) := by
  rw [aux_lem_load_Q_eq] at hy
  unfold aux_lem_load_kernel
  rw [aux_lem_load_integral_prod_Q
    (fun j t => if j = i then w1 t * w2 (y j) else aux_lem_load_cell n t (y j))]
  have h : ∀ j, (∫ t in Ioo (0:ℝ) 1,
      (if j = i then w1 t * w2 (y j) else aux_lem_load_cell n t (y j))) =
      (if j = i then (∫ t in Ioo (0:ℝ) 1, w1 t) * w2 (y i) else 1) := by
    intro j
    by_cases hj : j = i
    · subst hj; simp only [if_true]; exact integral_mul_const _ _
    · simp only [hj, if_false]
      simp_rw [aux_lem_load_cell_symm n _ (y j)]
      exact aux_lem_load_cell_integral hn (hy j (mem_univ j))
  rw [Finset.prod_congr rfl (fun j _ => h j), Finset.prod_ite_eq']
  simp

theorem aux_lem_load_kernel_nonneg {d : ℕ} (i : Fin d) (n : ℕ) {w1 w2 : ℝ → ℝ}
    (h1 : ∀ t, 0 ≤ w1 t) (h2 : ∀ t, 0 ≤ w2 t) (x y : SpatialCoordinates d) :
    0 ≤ aux_lem_load_kernel i n w1 w2 x y := by
  unfold aux_lem_load_kernel
  apply Finset.prod_nonneg
  intro j _
  split_ifs
  · exact mul_nonneg (h1 _) (h2 _)
  · exact aux_lem_load_cell_nonneg _ _ _

theorem aux_lem_load_kernel_le {d : ℕ} (i : Fin d) (n : ℕ) {w1 w2 : ℝ → ℝ} {B : ℝ}
    (h1 : ∀ t, 0 ≤ w1 t) (h2 : ∀ t, 0 ≤ w2 t) (h1B : ∀ t, w1 t ≤ B) (h2B : ∀ t, w2 t ≤ B)
    (x y : SpatialCoordinates d) :
    aux_lem_load_kernel i n w1 w2 x y ≤ B ^ 2 * (n:ℝ) ^ (d - 1) := by
  classical
  have hB : 0 ≤ B := le_trans (h1 0) (h1B 0)
  unfold aux_lem_load_kernel
  calc (∏ j, (if j = i then w1 (x j) * w2 (y j) else aux_lem_load_cell n (x j) (y j)))
      ≤ ∏ j, (if j = i then B ^ 2 else (n:ℝ)) := by
        apply Finset.prod_le_prod₀
        · intro j _
          split_ifs
          · exact mul_nonneg (h1 _) (h2 _)
          · exact aux_lem_load_cell_nonneg _ _ _
        · intro j _
          split_ifs
          · rw [sq]; exact mul_le_mul (h1B _) (h2B _) (h2 _) hB
          · exact aux_lem_load_cell_le _ _ _
    _ = B ^ 2 * (n:ℝ) ^ (d - 1) := by
        rw [Fintype.prod_eq_mul_prod_compl i]
        simp only [if_true]
        congr 1
        rw [Finset.prod_congr rfl (fun j hj => if_neg (Finset.mem_compl.mp hj |>
          fun h => fun h' => h (Finset.mem_singleton.mpr h'))), Finset.prod_const,
          Finset.card_compl, Finset.card_singleton, Fintype.card_fin]

theorem aux_lem_load_kernel_measurable {d : ℕ} (i : Fin d) (n : ℕ) {w1 w2 : ℝ → ℝ}
    (h1 : Measurable w1) (h2 : Measurable w2) :
    Measurable (fun q : SpatialCoordinates d × SpatialCoordinates d =>
      aux_lem_load_kernel i n w1 w2 q.1 q.2) := by
  unfold aux_lem_load_kernel
  apply Finset.measurable_prod
  intro j _
  by_cases hj : j = i
  · simp only [hj, if_true]
    exact (h1.comp ((measurable_pi_apply i).comp measurable_fst)).mul
      (h2.comp ((measurable_pi_apply i).comp measurable_snd))
  · simp only [hj, if_false]
    exact (aux_lem_load_cell_measurable n).comp
      (by fun_prop : Measurable fun q : SpatialCoordinates d × SpatialCoordinates d =>
        (q.1 j, q.2 j))

theorem aux_lem_load_kernel_ne_zero {d : ℕ} {i : Fin d} {n : ℕ} {w1 w2 : ℝ → ℝ}
    {x y : SpatialCoordinates d} (h : aux_lem_load_kernel i n w1 w2 x y ≠ 0) :
    w1 (x i) ≠ 0 ∧ w2 (y i) ≠ 0 ∧ ∀ j, j ≠ i → aux_lem_load_cell n (x j) (y j) ≠ 0 := by
  unfold aux_lem_load_kernel at h
  rw [Finset.prod_ne_zero_iff] at h
  have hi := h i (Finset.mem_univ i)
  simp only [if_true] at hi
  refine ⟨left_ne_zero_of_mul hi, right_ne_zero_of_mul hi, ?_⟩
  intro j hj
  have := h j (Finset.mem_univ j)
  simpa only [hj, if_false] using this

theorem aux_lem_load_kernel_sqdist {d : ℕ} {i : Fin d} {n : ℕ} (hn : 0 < n)
    {w1 w2 : ℝ → ℝ} {r c L : ℝ} (hr : 0 < r) (hnr : 1 / r ≤ n) (hL : 0 ≤ L)
    (h1s : ∀ t, w1 t ≠ 0 → t ∈ Icc c (c + L * r))
    (h2s : ∀ t, w2 t ≠ 0 → t ∈ Icc c (c + L * r))
    {x y : SpatialCoordinates d} (h : aux_lem_load_kernel i n w1 w2 x y ≠ 0) :
    ∑ j : Fin d, (x j - y j) ^ 2 ≤ d * ((L ^ 2 + 1) * r ^ 2) := by
  obtain ⟨hx, hy, hc⟩ := aux_lem_load_kernel_ne_zero h
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have h1n : 1 / (n:ℝ) ≤ r := by
    rw [div_le_iff₀ hn']
    rw [div_le_iff₀ hr] at hnr
    linarith
  have hterm : ∀ j, (x j - y j) ^ 2 ≤ (L ^ 2 + 1) * r ^ 2 := by
    intro j
    by_cases hj : j = i
    · subst hj
      have hxs := h1s _ hx
      have hys := h2s _ hy
      have habs : |x j - y j| ≤ L * r := by
        rw [abs_le]; constructor <;> linarith [hxs.1, hxs.2, hys.1, hys.2]
      have hLr : 0 ≤ L * r := mul_nonneg hL hr.le
      calc (x j - y j) ^ 2 = |x j - y j| ^ 2 := (sq_abs _).symm
        _ ≤ (L * r) ^ 2 := by gcongr
        _ ≤ (L ^ 2 + 1) * r ^ 2 := by nlinarith [sq_nonneg r]
    · have habs := aux_lem_load_cell_dist hn (hc j hj)
      have h2 : |x j - y j| ≤ r := le_trans habs.le h1n
      calc (x j - y j) ^ 2 = |x j - y j| ^ 2 := (sq_abs _).symm
        _ ≤ r ^ 2 := by gcongr
        _ ≤ (L ^ 2 + 1) * r ^ 2 := by nlinarith [sq_nonneg r, sq_nonneg L]
  calc ∑ j : Fin d, (x j - y j) ^ 2 ≤ ∑ _j : Fin d, (L ^ 2 + 1) * r ^ 2 :=
        Finset.sum_le_sum (fun j _ => hterm j)
    _ = d * ((L ^ 2 + 1) * r ^ 2) := by simp

/-- Scalar bookkeeping for the kernel weight bound. -/
theorem aux_lem_load_scale_algebra {d : ℕ} (hd : 1 ≤ d) {K r L : ℝ} (hr : 0 < r) :
    (K / r) ^ 2 * (2 / r) ^ (d - 1) *
        ((d * ((L ^ 2 + 1) * r ^ 2)) ^ (((d : ℝ) + 2 * (3 / 4 : ℝ)) / 2)) =
      K ^ 2 * 2 ^ (d - 1) * (d * (L ^ 2 + 1)) ^ (((d : ℝ) + 2 * (3 / 4 : ℝ)) / 2) *
        r ^ (1 / 2 : ℝ) := by
  have hdL : 0 ≤ (d:ℝ) * (L ^ 2 + 1) := by positivity
  have hr2 : 0 ≤ r ^ 2 := by positivity
  rw [← mul_assoc (d:ℝ), Real.mul_rpow hdL hr2]
  have hre : (r ^ 2) ^ (((d : ℝ) + 2 * (3 / 4 : ℝ)) / 2) =
      r ^ (d - 1) * r ^ 2 * r ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le, ← Real.rpow_natCast r (d - 1),
      ← Real.rpow_add hr, ← Real.rpow_add hr]
    congr 1
    have : ((d - 1 : ℕ) : ℝ) = (d:ℝ) - 1 := by
      rw [Nat.cast_sub hd]; simp
    rw [this]; push_cast; ring
  rw [hre, div_pow, div_pow]
  have hr0 : r ≠ 0 := hr.ne'
  field_simp

theorem aux_lem_load_kernel_weight {d : ℕ} (i : Fin d) {w1 w2 : ℝ → ℝ} {r c L K : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (h1 : ∀ t, 0 ≤ w1 t) (h2 : ∀ t, 0 ≤ w2 t)
    (h1B : ∀ t, w1 t ≤ K / r) (h2B : ∀ t, w2 t ≤ K / r)
    (h1s : ∀ t, w1 t ≠ 0 → t ∈ Icc c (c + L * r))
    (h2s : ∀ t, w2 t ≠ 0 → t ∈ Icc c (c + L * r)) (x y : SpatialCoordinates d) :
    aux_lem_load_kernel i ⌈1 / r⌉₊ w1 w2 x y *
        Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ ((d : ℝ) + 2 * (3 / 4 : ℝ)) ≤
      K ^ 2 * 2 ^ (d - 1) * (d * (L ^ 2 + 1)) ^ (((d : ℝ) + 2 * (3 / 4 : ℝ)) / 2) *
        r ^ (1 / 2 : ℝ) := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact i.elim0)
  set n := ⌈1 / r⌉₊ with hn_def
  have hinv : 0 < 1 / r := by positivity
  have hn : 0 < n := Nat.ceil_pos.mpr hinv
  have hnr : 1 / r ≤ n := Nat.le_ceil _
  have hn2 : (n:ℝ) ≤ 2 / r := by
    have := Nat.ceil_lt_add_one hinv.le
    have h1r : 1 ≤ 1 / r := by rw [le_div_iff₀ hr]; linarith
    have : (n:ℝ) < 1 / r + 1 := this
    have : 1 / r + 1 ≤ 2 / r := by
      have : 2 / r = 1 / r + 1 / r := by ring
      linarith
    linarith
  have hrhs : 0 ≤ K ^ 2 * 2 ^ (d - 1) * (d * (L ^ 2 + 1)) ^ (((d : ℝ) + 2 * (3 / 4 : ℝ)) / 2) *
      r ^ (1 / 2 : ℝ) := by positivity
  by_cases hk : aux_lem_load_kernel i n w1 w2 x y = 0
  · rw [hk, zero_mul]; exact hrhs
  have hS := aux_lem_load_kernel_sqdist hn hr hnr hL h1s h2s hk
  have hSnn : 0 ≤ ∑ j : Fin d, (x j - y j) ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have he : 0 ≤ ((d : ℝ) + 2 * (3 / 4 : ℝ)) := by positivity
  have hdist : Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ ((d : ℝ) + 2 * (3 / 4 : ℝ)) ≤
      (d * ((L ^ 2 + 1) * r ^ 2)) ^ (((d : ℝ) + 2 * (3 / 4 : ℝ)) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hSnn]
    rw [show (1 / 2 : ℝ) * ((d : ℝ) + 2 * (3 / 4 : ℝ)) = ((d : ℝ) + 2 * (3 / 4 : ℝ)) / 2 by ring]
    exact Real.rpow_le_rpow hSnn hS (by positivity)
  have hkle := aux_lem_load_kernel_le i n h1 h2 h1B h2B x y
  have hKr : 0 ≤ K / r := div_nonneg hK hr.le
  have hpow : (n:ℝ) ^ (d - 1) ≤ (2 / r) ^ (d - 1) := by
    gcongr
  calc aux_lem_load_kernel i n w1 w2 x y *
        Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ ((d : ℝ) + 2 * (3 / 4 : ℝ))
      ≤ ((K / r) ^ 2 * (n:ℝ) ^ (d - 1)) *
          (d * ((L ^ 2 + 1) * r ^ 2)) ^ (((d : ℝ) + 2 * (3 / 4 : ℝ)) / 2) :=
        mul_le_mul hkle hdist (by positivity) (by positivity)
    _ ≤ ((K / r) ^ 2 * (2 / r) ^ (d - 1)) *
          (d * ((L ^ 2 + 1) * r ^ 2)) ^ (((d : ℝ) + 2 * (3 / 4 : ℝ)) / 2) := by
        gcongr
    _ = _ := aux_lem_load_scale_algebra hd hr

/-- The unnormalised Gagliardo double integral of order `3/4` on the unit cube. -/
def aux_lem_load_gag {d : ℕ} (u : SpatialCoordinates d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
    ∫⁻ y in (unitNeumannCube d : Set (SpatialCoordinates d)),
      ENNReal.ofReal ((u x - u y) ^ 2) /
        ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ ((d : ℝ) + 2 * (3 / 4 : ℝ))

theorem aux_lem_load_gag_pointwise {d : ℕ} {u : SpatialCoordinates d → ℝ} {P Kr : ℝ}
    (hKr : 0 ≤ Kr) (x y : SpatialCoordinates d)
    (hP : P * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ ((d : ℝ) + 2 * (3 / 4 : ℝ)) ≤ Kr) :
    ENNReal.ofReal (P * (u x - u y) ^ 2) ≤
      ENNReal.ofReal Kr * (ENNReal.ofReal ((u x - u y) ^ 2) /
        ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ ((d : ℝ) + 2 * (3 / 4 : ℝ))) := by
  have he : (0:ℝ) < (d : ℝ) + 2 * (3 / 4 : ℝ) := by positivity
  have hDnn : 0 ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := Real.sqrt_nonneg _
  rcases hDnn.lt_or_eq with hDpos | hD0
  · have hDe := Real.rpow_pos_of_pos hDpos ((d : ℝ) + 2 * (3 / 4 : ℝ))
    rw [ENNReal.ofReal_rpow_of_pos hDpos, ← ENNReal.ofReal_div_of_pos hDe,
      ← ENNReal.ofReal_mul hKr]
    apply ENNReal.ofReal_le_ofReal
    rw [mul_div_assoc', le_div_iff₀ hDe]
    have ha : 0 ≤ (u x - u y) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hP ha]
  · have hxy : x = y := by
      have hs : ∑ j : Fin d, (x j - y j) ^ 2 = 0 := by
        rw [← Real.sqrt_eq_zero (Finset.sum_nonneg (fun j _ => sq_nonneg (x j - y j)))]
        exact hD0.symm
      funext j
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j - y j))).mp hs j
        (Finset.mem_univ j)
      nlinarith [sq_nonneg (x j - y j)]
    subst hxy
    simp

theorem aux_lem_load_variance {α : Type*} [MeasurableSpace α] {ν : Measure α} {P f : α → ℝ}
    (hPnn : ∀ q, 0 ≤ P q) (hP : Integrable P ν) (hPf : Integrable (fun q => P q * f q) ν)
    (hPf2 : Integrable (fun q => P q * f q ^ 2) ν) (h1 : ∫ q, P q ∂ν = 1) :
    (∫ q, P q * f q ∂ν) ^ 2 ≤ ∫ q, P q * f q ^ 2 ∂ν := by
  set X := ∫ q, P q * f q ∂ν with hX
  have h0 : 0 ≤ ∫ q, P q * (f q - X) ^ 2 ∂ν :=
    integral_nonneg (fun q => mul_nonneg (hPnn q) (sq_nonneg _))
  have hexp : (fun q => P q * (f q - X) ^ 2) =
      fun q => (P q * f q ^ 2 - (2 * X) * (P q * f q)) + X ^ 2 * P q := by
    ext q; ring
  have e1 : ∫ q, ((P q * f q ^ 2 - (2 * X) * (P q * f q)) + X ^ 2 * P q) ∂ν =
      ∫ q, (P q * f q ^ 2 - (2 * X) * (P q * f q)) ∂ν + ∫ q, X ^ 2 * P q ∂ν :=
    integral_add (by exact hPf2.sub (hPf.const_mul (2 * X))) (hP.const_mul _)
  have e2 : ∫ q, (P q * f q ^ 2 - (2 * X) * (P q * f q)) ∂ν =
      ∫ q, P q * f q ^ 2 ∂ν - ∫ q, (2 * X) * (P q * f q) ∂ν :=
    integral_sub hPf2 (hPf.const_mul _)
  rw [hexp, e1, e2, integral_const_mul, integral_const_mul, h1, ← hX] at h0
  nlinarith

theorem aux_lem_load_gag_compare {d : ℕ} {u : SpatialCoordinates d → ℝ} (hum : Measurable u)
    {P : SpatialCoordinates d × SpatialCoordinates d → ℝ} (hPm : Measurable P)
    (hPnn : ∀ q, 0 ≤ P q) {Kr : ℝ} (hKr : 0 ≤ Kr)
    (hPK : ∀ x y, P (x, y) *
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ ((d : ℝ) + 2 * (3 / 4 : ℝ)) ≤ Kr)
    (hG : aux_lem_load_gag u ≠ ⊤) :
    ∫ q, P q * (u q.1 - u q.2) ^ 2 ∂((volume.restrict
        (unitNeumannCube d : Set (SpatialCoordinates d))).prod
        (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)))) ≤
      Kr * (aux_lem_load_gag u).toReal := by
  have hmeas : Measurable (fun q : SpatialCoordinates d × SpatialCoordinates d =>
      P q * (u q.1 - u q.2) ^ 2) :=
    hPm.mul (((hum.comp measurable_fst).sub (hum.comp measurable_snd)).pow_const 2)
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun q => mul_nonneg (hPnn q) (sq_nonneg _))) hmeas.aestronglyMeasurable]
  rw [lintegral_prod _ hmeas.ennreal_ofReal.aemeasurable]
  have hle : ∫⁻ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
      ∫⁻ y in (unitNeumannCube d : Set (SpatialCoordinates d)),
        ENNReal.ofReal (P (x, y) * (u (x, y).1 - u (x, y).2) ^ 2) ≤
      ENNReal.ofReal Kr * aux_lem_load_gag u := by
    unfold aux_lem_load_gag
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro x
    dsimp only
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro y
    exact aux_lem_load_gag_pointwise hKr x y (hPK x y)
  calc _ ≤ (ENNReal.ofReal Kr * aux_lem_load_gag u).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG) hle
    _ = Kr * (aux_lem_load_gag u).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hKr]

theorem aux_lem_load_integral_coord {d : ℕ} (i : Fin d) (w : ℝ → ℝ) :
    ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), w (x i) =
      ∫ t in Ioo (0:ℝ) 1, w t := by
  classical
  have h : ∀ x : SpatialCoordinates d, w (x i) = ∏ j, (if j = i then w (x j) else 1) := by
    intro x
    rw [Finset.prod_ite_eq']
    simp
  simp_rw [h]
  rw [aux_lem_load_integral_prod_Q (fun j t => if j = i then w t else 1)]
  have h2 : ∀ j, (∫ t in Ioo (0:ℝ) 1, (if j = i then w t else 1)) =
      (if j = i then ∫ t in Ioo (0:ℝ) 1, w t else 1) := by
    intro j
    by_cases hj : j = i
    · simp [hj]
    · simp [hj]
  rw [Finset.prod_congr rfl (fun j _ => h2 j), Finset.prod_ite_eq']
  simp

/-- **Slab comparison (Campanato step).** Two normal-coordinate weights of mass one,
supported in a common interval of length `L r` and bounded by `K / r`, have averages of `u`
differing by at most `C r^{1/4}` times the square root of the Gagliardo double integral. -/
theorem aux_lem_load_slab {d : ℕ} (i : Fin d) {u : SpatialCoordinates d → ℝ}
    (hu : MemLp u 2 (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (hum : Measurable u) (hG : aux_lem_load_gag u ≠ ⊤)
    {w1 w2 : ℝ → ℝ} (hw1 : Measurable w1) (hw2 : Measurable w2)
    {r c L K : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (h1 : ∀ t, 0 ≤ w1 t) (h2 : ∀ t, 0 ≤ w2 t)
    (h1B : ∀ t, w1 t ≤ K / r) (h2B : ∀ t, w2 t ≤ K / r)
    (h1s : ∀ t, w1 t ≠ 0 → t ∈ Icc c (c + L * r))
    (h2s : ∀ t, w2 t ≠ 0 → t ∈ Icc c (c + L * r))
    (h1i : ∫ t in Ioo (0:ℝ) 1, w1 t = 1) (h2i : ∫ t in Ioo (0:ℝ) 1, w2 t = 1) :
    |(∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), u x * w1 (x i)) -
        ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), u x * w2 (x i)| ≤
      K * Real.sqrt (2 ^ (d - 1) * (d * (L ^ 2 + 1)) ^ (((d : ℝ) + 2 * (3 / 4 : ℝ)) / 2)) *
        r ^ (1 / 4 : ℝ) * Real.sqrt (aux_lem_load_gag u).toReal := by
  classical
  set μ := volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)) with hμ
  set n := ⌈1 / r⌉₊ with hn_def
  have hn : 0 < n := Nat.ceil_pos.mpr (by positivity)
  set P : SpatialCoordinates d × SpatialCoordinates d → ℝ :=
    fun q => aux_lem_load_kernel i n w1 w2 q.1 q.2 with hP_def
  set A := 2 ^ (d - 1) * (d * (L ^ 2 + 1)) ^ (((d : ℝ) + 2 * (3 / 4 : ℝ)) / 2) with hA_def
  have hA : 0 ≤ A := by positivity
  set Kr := K ^ 2 * A * r ^ (1 / 2 : ℝ) with hKr_def
  have hKr : 0 ≤ Kr := by positivity
  have hPm : Measurable P := aux_lem_load_kernel_measurable i n hw1 hw2
  have hPnn : ∀ q, 0 ≤ P q := fun q => aux_lem_load_kernel_nonneg i n h1 h2 q.1 q.2
  have hPbd : ∀ᵐ q ∂(μ.prod μ), ‖P q‖ ≤ (K / r) ^ 2 * (n:ℝ) ^ (d - 1) := by
    refine ae_of_all _ (fun q => ?_)
    rw [Real.norm_of_nonneg (hPnn q)]
    exact aux_lem_load_kernel_le i n h1 h2 h1B h2B q.1 q.2
  have hPK : ∀ x y, P (x, y) *
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ ((d : ℝ) + 2 * (3 / 4 : ℝ)) ≤ Kr := by
    intro x y
    have := aux_lem_load_kernel_weight i hr hr1 hL hK h1 h2 h1B h2B h1s h2s x y
    simpa only [hKr_def, hA_def, mul_assoc] using this
  have hu1 : Integrable u μ := hu.integrable one_le_two
  have hu2 : Integrable (fun x => u x ^ 2) μ := hu.integrable_sq
  have hIu1 : Integrable (fun q => P q * u q.1) (μ.prod μ) :=
    (hu1.comp_fst μ).bdd_mul hPm.aestronglyMeasurable hPbd
  have hIu2 : Integrable (fun q => P q * u q.2) (μ.prod μ) :=
    (hu1.comp_snd μ).bdd_mul hPm.aestronglyMeasurable hPbd
  have hIP : Integrable P (μ.prod μ) := by
    have := (integrable_const (1:ℝ) : Integrable (fun _ => (1:ℝ)) (μ.prod μ)).bdd_mul
      hPm.aestronglyMeasurable hPbd
    simpa only [mul_one] using this
  have hf2 : Integrable (fun q : SpatialCoordinates d × SpatialCoordinates d =>
      (u q.1 - u q.2) ^ 2) (μ.prod μ) := by
    have e : (fun q : SpatialCoordinates d × SpatialCoordinates d => (u q.1 - u q.2) ^ 2) =
        fun q => (u q.1 ^ 2 - 2 * (u q.1 * u q.2)) + u q.2 ^ 2 := by
      ext q; ring
    rw [e]
    exact ((hu2.comp_fst μ).sub ((hu1.mul_prod hu1).const_mul 2)).add (hu2.comp_snd μ)
  have hIf : Integrable (fun q => P q * (u q.1 - u q.2)) (μ.prod μ) := by
    have e : (fun q => P q * (u q.1 - u q.2)) = fun q => P q * u q.1 - P q * u q.2 := by
      ext q; ring
    rw [e]; exact hIu1.sub hIu2
  have hIf2 : Integrable (fun q => P q * (u q.1 - u q.2) ^ 2) (μ.prod μ) :=
    hf2.bdd_mul hPm.aestronglyMeasurable hPbd
  have hmargA : ∫ q, P q * u q.1 ∂(μ.prod μ) =
      ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), u x * w1 (x i) := by
    rw [integral_prod _ hIu1]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (unitNeumannCube d).isOpen.measurableSet] with x hx
    simp only [hP_def]
    rw [integral_mul_const, aux_lem_load_kernel_marg_right i hn w1 w2 hx, h2i]
    ring
  have hmargB : ∫ q, P q * u q.2 ∂(μ.prod μ) =
      ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), u x * w2 (x i) := by
    rw [integral_prod_symm _ hIu2]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (unitNeumannCube d).isOpen.measurableSet] with y hy
    simp only [hP_def]
    rw [integral_mul_const, aux_lem_load_kernel_marg_left i hn w1 w2 hy, h1i]
    ring
  have hPint : ∫ q, P q ∂(μ.prod μ) = 1 := by
    rw [integral_prod _ hIP]
    have hx : ∀ᵐ x ∂μ, ∫ y, P (x, y) ∂μ = w1 (x i) := by
      filter_upwards [ae_restrict_mem (unitNeumannCube d).isOpen.measurableSet] with x hx
      simp only [hP_def]
      rw [aux_lem_load_kernel_marg_right i hn w1 w2 hx, h2i, mul_one]
    rw [integral_congr_ae hx, aux_lem_load_integral_coord i w1, h1i]
  have hX : (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), u x * w1 (x i)) -
      ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), u x * w2 (x i) =
      ∫ q, P q * (u q.1 - u q.2) ∂(μ.prod μ) := by
    rw [← hmargA, ← hmargB, ← integral_sub hIu1 hIu2]
    congr 1; ext q; ring
  have hvar := aux_lem_load_variance hPnn hIP hIf hIf2 hPint
  have hgag := aux_lem_load_gag_compare hum hPm hPnn hKr hPK hG
  rw [hX]
  have hG0 : 0 ≤ (aux_lem_load_gag u).toReal := ENNReal.toReal_nonneg
  calc |∫ q, P q * (u q.1 - u q.2) ∂(μ.prod μ)|
      ≤ Real.sqrt (Kr * (aux_lem_load_gag u).toReal) :=
        Real.abs_le_sqrt (hvar.trans hgag)
    _ = K * Real.sqrt A * r ^ (1 / 4 : ℝ) * Real.sqrt (aux_lem_load_gag u).toReal := by
        rw [hKr_def, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_mul (by positivity), Real.sqrt_sq hK]
        rw [Real.sqrt_eq_rpow (r ^ (1 / 2 : ℝ)), ← Real.rpow_mul hr.le]
        norm_num

/-- Fixed slab profile: the derivative of Mathlib's smooth transition function. -/
def aux_lem_load_eta : ℝ → ℝ := deriv Real.smoothTransition

theorem aux_lem_load_eta_nonneg (y : ℝ) : 0 ≤ aux_lem_load_eta y :=
  Real.smoothTransition.monotone.deriv_nonneg

theorem aux_lem_load_eta_zero {y : ℝ} (hy : y ∉ Icc (0:ℝ) 1) : aux_lem_load_eta y = 0 := by
  unfold aux_lem_load_eta
  rw [mem_Icc, not_and_or, not_le, not_le] at hy
  rcases hy with hy | hy
  · have h : Real.smoothTransition =ᶠ[𝓝 y] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds hy] with z hz
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hz)
    rw [h.deriv_eq]; simp
  · have h : Real.smoothTransition =ᶠ[𝓝 y] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      exact Real.smoothTransition.one_of_one_le (le_of_lt hz)
    rw [h.deriv_eq]; simp

theorem aux_lem_load_eta_continuous : Continuous aux_lem_load_eta :=
  (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl

theorem aux_lem_load_st_hasDerivAt (y : ℝ) :
    HasDerivAt Real.smoothTransition (aux_lem_load_eta y) y :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) y).hasDerivAt

theorem aux_lem_load_eta_bdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ y, aux_lem_load_eta y ≤ M := by
  obtain ⟨C, hC⟩ := aux_lem_load_eta_continuous.bounded_above_of_compact_support
    (HasCompactSupport.intro isCompact_Icc (fun y hy => aux_lem_load_eta_zero hy))
  exact ⟨C, le_trans (norm_nonneg _) (hC 0), fun y => le_trans (le_abs_self _) (hC y)⟩

theorem aux_lem_load_eta_integral : ∫ y, aux_lem_load_eta y = 1 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (0:ℝ) 1)
    (fun y hy => aux_lem_load_eta_zero hy)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  unfold aux_lem_load_eta
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun x _ => (aux_lem_load_st_hasDerivAt x).differentiableAt)
    (aux_lem_load_eta_continuous.intervalIntegrable 0 1)]
  rw [Real.smoothTransition.one_of_one_le le_rfl, Real.smoothTransition.zero_of_nonpos le_rfl]
  norm_num

/-- Lower slab weight `δ⁻¹ η((t - a)/δ)`, supported in `[a, a + δ]`. -/
def aux_lem_load_wlo (a δ t : ℝ) : ℝ := δ⁻¹ * aux_lem_load_eta ((t - a) / δ)

/-- Upper slab weight `δ⁻¹ η((b - t)/δ)`, supported in `[b - δ, b]`. -/
def aux_lem_load_whi (b δ t : ℝ) : ℝ := δ⁻¹ * aux_lem_load_eta ((b - t) / δ)

theorem aux_lem_load_wlo_nonneg {a δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 ≤ aux_lem_load_wlo a δ t :=
  mul_nonneg (inv_nonneg.mpr hδ.le) (aux_lem_load_eta_nonneg _)

theorem aux_lem_load_whi_nonneg {b δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 ≤ aux_lem_load_whi b δ t :=
  mul_nonneg (inv_nonneg.mpr hδ.le) (aux_lem_load_eta_nonneg _)

theorem aux_lem_load_wlo_le {a δ M : ℝ} (hδ : 0 < δ) (hM : ∀ y, aux_lem_load_eta y ≤ M) (t : ℝ) :
    aux_lem_load_wlo a δ t ≤ M / δ := by
  unfold aux_lem_load_wlo
  rw [div_eq_inv_mul M δ]
  exact mul_le_mul_of_nonneg_left (hM _) (inv_nonneg.mpr hδ.le)

theorem aux_lem_load_whi_le {b δ M : ℝ} (hδ : 0 < δ) (hM : ∀ y, aux_lem_load_eta y ≤ M) (t : ℝ) :
    aux_lem_load_whi b δ t ≤ M / δ := by
  unfold aux_lem_load_whi
  rw [div_eq_inv_mul M δ]
  exact mul_le_mul_of_nonneg_left (hM _) (inv_nonneg.mpr hδ.le)

theorem aux_lem_load_wlo_supp {a δ : ℝ} (hδ : 0 < δ) {t : ℝ} (h : aux_lem_load_wlo a δ t ≠ 0) :
    t ∈ Icc a (a + δ) := by
  unfold aux_lem_load_wlo at h
  have h2 := right_ne_zero_of_mul h
  by_contra hn
  apply h2
  apply aux_lem_load_eta_zero
  intro hmem
  apply hn
  rw [mem_Icc, le_div_iff₀ hδ, div_le_iff₀ hδ] at hmem
  constructor <;> linarith [hmem.1, hmem.2]

theorem aux_lem_load_whi_supp {b δ : ℝ} (hδ : 0 < δ) {t : ℝ} (h : aux_lem_load_whi b δ t ≠ 0) :
    t ∈ Icc (b - δ) b := by
  unfold aux_lem_load_whi at h
  have h2 := right_ne_zero_of_mul h
  by_contra hn
  apply h2
  apply aux_lem_load_eta_zero
  intro hmem
  apply hn
  rw [mem_Icc, le_div_iff₀ hδ, div_le_iff₀ hδ] at hmem
  constructor <;> linarith [hmem.1, hmem.2]

theorem aux_lem_load_wlo_continuous (a δ : ℝ) : Continuous (aux_lem_load_wlo a δ) := by
  unfold aux_lem_load_wlo
  exact continuous_const.mul (aux_lem_load_eta_continuous.comp
    ((continuous_id.sub continuous_const).div_const _))

theorem aux_lem_load_whi_continuous (b δ : ℝ) : Continuous (aux_lem_load_whi b δ) := by
  unfold aux_lem_load_whi
  exact continuous_const.mul (aux_lem_load_eta_continuous.comp
    ((continuous_const.sub continuous_id).div_const _))

theorem aux_lem_load_unit_mass {w : ℝ → ℝ} (hw : ∀ t, w t ≠ 0 → t ∈ Icc (0:ℝ) 1)
    (h : ∫ t, w t = 1) : ∫ t in Ioo (0:ℝ) 1, w t = 1 := by
  rw [← integral_Icc_eq_integral_Ioo, setIntegral_eq_integral_of_forall_compl_eq_zero, h]
  intro t ht
  by_contra hne
  exact ht (hw t hne)

theorem aux_lem_load_wlo_mass {a δ : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (haδ : a + δ ≤ 1) :
    ∫ t in Ioo (0:ℝ) 1, aux_lem_load_wlo a δ t = 1 := by
  apply aux_lem_load_unit_mass
  · intro t ht
    have := aux_lem_load_wlo_supp hδ ht
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · unfold aux_lem_load_wlo
    rw [integral_const_mul,
      integral_sub_right_eq_self (fun t => aux_lem_load_eta (t / δ)) a,
      Measure.integral_comp_div, aux_lem_load_eta_integral, abs_of_pos hδ, smul_eq_mul, mul_one,
      inv_mul_cancel₀ hδ.ne']

theorem aux_lem_load_whi_mass {b δ : ℝ} (hδ : 0 < δ) (hb : b ≤ 1) (hbδ : 0 ≤ b - δ) :
    ∫ t in Ioo (0:ℝ) 1, aux_lem_load_whi b δ t = 1 := by
  apply aux_lem_load_unit_mass
  · intro t ht
    have := aux_lem_load_whi_supp hδ ht
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · unfold aux_lem_load_whi
    rw [integral_const_mul,
      integral_sub_left_eq_self (fun t => aux_lem_load_eta (t / δ)) volume b,
      Measure.integral_comp_div, aux_lem_load_eta_integral, abs_of_pos hδ, smul_eq_mul, mul_one,
      inv_mul_cancel₀ hδ.ne']

/-- Lower slab average `W(a,δ) = ∫_Q u(x) δ⁻¹η((x_i - a)/δ) dx`. -/
def aux_lem_load_Wlo {d : ℕ} (i : Fin d) (u : SpatialCoordinates d → ℝ) (a δ : ℝ) : ℝ :=
  ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), u x * aux_lem_load_wlo a δ (x i)

/-- Upper slab average `W̃(b,δ) = ∫_Q u(x) δ⁻¹η((b - x_i)/δ) dx`. -/
def aux_lem_load_Whi {d : ℕ} (i : Fin d) (u : SpatialCoordinates d → ℝ) (b δ : ℝ) : ℝ :=
  ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), u x * aux_lem_load_whi b δ (x i)

/-- The Campanato constant `√(2^{d-1} (d (L²+1))^{(d+3/2)/2})` of the slab lemma. -/
def aux_lem_load_cst (d : ℕ) (L : ℝ) : ℝ :=
  Real.sqrt (2 ^ (d - 1) * (d * (L ^ 2 + 1)) ^ (((d : ℝ) + 2 * (3 / 4 : ℝ)) / 2))

theorem aux_lem_load_cst_nonneg (d : ℕ) (L : ℝ) : 0 ≤ aux_lem_load_cst d L :=
  Real.sqrt_nonneg _

theorem aux_lem_load_step_lo {d : ℕ} (i : Fin d) {u : SpatialCoordinates d → ℝ}
    (hu : MemLp u 2 (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (hum : Measurable u) (hG : aux_lem_load_gag u ≠ ⊤) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y, aux_lem_load_eta y ≤ M) {a δ : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a)
    (ha1 : a + 2 * δ ≤ 1) :
    |aux_lem_load_Wlo i u a δ - aux_lem_load_Wlo i u a (2 * δ)| ≤
      (2 * M) * aux_lem_load_cst d 1 * (2 * δ) ^ (1 / 4 : ℝ) *
        Real.sqrt (aux_lem_load_gag u).toReal := by
  have h2δ : 0 < 2 * δ := by linarith
  exact aux_lem_load_slab i hu hum hG (aux_lem_load_wlo_continuous a δ).measurable
    (aux_lem_load_wlo_continuous a (2 * δ)).measurable h2δ (by linarith) zero_le_one
    (by linarith) (aux_lem_load_wlo_nonneg hδ) (aux_lem_load_wlo_nonneg h2δ)
    (fun t => (aux_lem_load_wlo_le hδ hM t).trans_eq (by field_simp))
    (fun t => (aux_lem_load_wlo_le h2δ hM t).trans (by
      apply div_le_div_of_nonneg_right _ h2δ.le; linarith))
    (c := a) (L := 1)
    (fun t ht => by
      have := aux_lem_load_wlo_supp hδ ht
      exact ⟨this.1, by linarith [this.2]⟩)
    (fun t ht => by
      have := aux_lem_load_wlo_supp h2δ ht
      exact ⟨this.1, by linarith [this.2]⟩)
    (aux_lem_load_wlo_mass hδ ha (by linarith))
    (aux_lem_load_wlo_mass h2δ ha ha1)

theorem aux_lem_load_step_hi {d : ℕ} (i : Fin d) {u : SpatialCoordinates d → ℝ}
    (hu : MemLp u 2 (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (hum : Measurable u) (hG : aux_lem_load_gag u ≠ ⊤) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y, aux_lem_load_eta y ≤ M) {b δ : ℝ} (hδ : 0 < δ) (hb : b ≤ 1)
    (hb0 : 0 ≤ b - 2 * δ) :
    |aux_lem_load_Whi i u b δ - aux_lem_load_Whi i u b (2 * δ)| ≤
      (2 * M) * aux_lem_load_cst d 1 * (2 * δ) ^ (1 / 4 : ℝ) *
        Real.sqrt (aux_lem_load_gag u).toReal := by
  have h2δ : 0 < 2 * δ := by linarith
  exact aux_lem_load_slab i hu hum hG (aux_lem_load_whi_continuous b δ).measurable
    (aux_lem_load_whi_continuous b (2 * δ)).measurable h2δ (by linarith) zero_le_one
    (by linarith) (aux_lem_load_whi_nonneg hδ) (aux_lem_load_whi_nonneg h2δ)
    (fun t => (aux_lem_load_whi_le hδ hM t).trans_eq (by field_simp))
    (fun t => (aux_lem_load_whi_le h2δ hM t).trans (by
      apply div_le_div_of_nonneg_right _ h2δ.le; linarith))
    (c := b - 2 * δ) (L := 1)
    (fun t ht => by
      have := aux_lem_load_whi_supp hδ ht
      exact ⟨by linarith [this.1], by linarith [this.2]⟩)
    (fun t ht => by
      have := aux_lem_load_whi_supp h2δ ht
      exact ⟨this.1, by linarith [this.2]⟩)
    (aux_lem_load_whi_mass hδ hb (by linarith))
    (aux_lem_load_whi_mass h2δ hb hb0)

theorem aux_lem_load_step_mid {d : ℕ} (i : Fin d) {u : SpatialCoordinates d → ℝ}
    (hu : MemLp u 2 (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (hum : Measurable u) (hG : aux_lem_load_gag u ≠ ⊤) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y, aux_lem_load_eta y ≤ M) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    |aux_lem_load_Whi i u b ((b - a) / 2) - aux_lem_load_Wlo i u a ((b - a) / 2)| ≤
      M * aux_lem_load_cst d 2 * ((b - a) / 2) ^ (1 / 4 : ℝ) *
        Real.sqrt (aux_lem_load_gag u).toReal := by
  have hR : 0 < (b - a) / 2 := by linarith
  exact aux_lem_load_slab i hu hum hG (aux_lem_load_whi_continuous b _).measurable
    (aux_lem_load_wlo_continuous a _).measurable hR (by linarith) zero_le_two hM0
    (aux_lem_load_whi_nonneg hR) (aux_lem_load_wlo_nonneg hR)
    (aux_lem_load_whi_le hR hM) (aux_lem_load_wlo_le hR hM)
    (c := a) (L := 2)
    (fun t ht => by
      have := aux_lem_load_whi_supp hR ht
      exact ⟨by linarith [this.1], by linarith [this.2]⟩)
    (fun t ht => by
      have := aux_lem_load_wlo_supp hR ht
      exact ⟨this.1, by linarith [this.2]⟩)
    (aux_lem_load_whi_mass hR hb (by linarith))
    (aux_lem_load_wlo_mass hR ha (by linarith))

theorem aux_lem_load_telescope {f : ℕ → ℝ} {B q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hB : 0 ≤ B)
    (h : ∀ m, |f (m + 1) - f m| ≤ B * q ^ m) (m : ℕ) : |f m - f 0| ≤ B / (1 - q) := by
  have key : ∀ m, |f m - f 0| ≤ B * ∑ k ∈ Finset.range m, q ^ k := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, mul_add]
      calc |f (m + 1) - f 0| ≤ |f (m + 1) - f m| + |f m - f 0| := abs_sub_le _ _ _
        _ ≤ B * q ^ m + B * ∑ k ∈ Finset.range m, q ^ k := add_le_add (h m) ih
        _ = _ := by ring
  calc |f m - f 0| ≤ B * ∑ k ∈ Finset.range m, q ^ k := key m
    _ ≤ B * (1 / (1 - q)) := by
        apply mul_le_mul_of_nonneg_left _ hB
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := m) hq0 hq1
        rw [← Finset.range_eq_Ico, pow_zero] at this
        exact this
    _ = B / (1 - q) := by ring

/-- The dyadic ratio `2^{-1/4}`. -/
def aux_lem_load_q : ℝ := ((2:ℝ) ^ (1 / 4 : ℝ))⁻¹

theorem aux_lem_load_q_nonneg : 0 ≤ aux_lem_load_q :=
  inv_nonneg.mpr (Real.rpow_nonneg (by norm_num) _)

theorem aux_lem_load_q_lt_one : aux_lem_load_q < 1 :=
  inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by norm_num))

theorem aux_lem_load_pow_dyadic {R : ℝ} (hR : 0 ≤ R) (m : ℕ) :
    (R / 2 ^ m) ^ (1 / 4 : ℝ) = R ^ (1 / 4 : ℝ) * aux_lem_load_q ^ m := by
  rw [Real.div_rpow hR (by positivity), aux_lem_load_q, inv_pow, div_eq_mul_inv]
  congr 2
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), mul_comm]

/-- The flux constant. -/
def aux_lem_load_CF (d : ℕ) (M : ℝ) : ℝ :=
  4 * M * aux_lem_load_cst d 1 / (1 - aux_lem_load_q) + M * aux_lem_load_cst d 2

theorem aux_lem_load_chain {d : ℕ} (i : Fin d) {u : SpatialCoordinates d → ℝ}
    (hu : MemLp u 2 (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (hum : Measurable u) (hG : aux_lem_load_gag u ≠ ⊤) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y, aux_lem_load_eta y ≤ M) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (m : ℕ) :
    |aux_lem_load_Whi i u b ((b - a) / 2 / 2 ^ m) - aux_lem_load_Wlo i u a ((b - a) / 2 / 2 ^ m)| ≤
      aux_lem_load_CF d M * (b - a) ^ (1 / 4 : ℝ) * Real.sqrt (aux_lem_load_gag u).toReal := by
  set R := (b - a) / 2 with hR_def
  have hR : 0 < R := by rw [hR_def]; linarith
  set S := Real.sqrt (aux_lem_load_gag u).toReal with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hq0 := aux_lem_load_q_nonneg
  have hq1 := aux_lem_load_q_lt_one
  have hc1 := aux_lem_load_cst_nonneg d 1
  have hc2 := aux_lem_load_cst_nonneg d 2
  set B := 2 * M * aux_lem_load_cst d 1 * R ^ (1 / 4 : ℝ) * S with hB_def
  have hB : 0 ≤ B := by positivity
  have hδ : ∀ k : ℕ, 0 < R / 2 ^ (k + 1) := fun k => by positivity
  have htwo : ∀ k : ℕ, 2 * (R / 2 ^ (k + 1)) = R / 2 ^ k := fun k => by
    rw [pow_succ]; field_simp
  have hRk : ∀ k : ℕ, R / 2 ^ k ≤ R := fun k =>
    div_le_self hR.le (one_le_pow₀ (by norm_num))
  have hlo : |aux_lem_load_Wlo i u a (R / 2 ^ m) - aux_lem_load_Wlo i u a (R / 2 ^ 0)| ≤
      B / (1 - aux_lem_load_q) := by
    refine aux_lem_load_telescope (f := fun k => aux_lem_load_Wlo i u a (R / 2 ^ k))
      hq0 hq1 hB (fun k => ?_) m
    have hstep := aux_lem_load_step_lo i hu hum hG hM0 hM (hδ k) ha
      (by rw [htwo k]; linarith [hRk k])
    rw [htwo k, aux_lem_load_pow_dyadic hR.le] at hstep
    calc _ ≤ 2 * M * aux_lem_load_cst d 1 * (R ^ (1 / 4 : ℝ) * aux_lem_load_q ^ k) * S := hstep
      _ = B * aux_lem_load_q ^ k := by rw [hB_def]; ring
  have hhi : |aux_lem_load_Whi i u b (R / 2 ^ m) - aux_lem_load_Whi i u b (R / 2 ^ 0)| ≤
      B / (1 - aux_lem_load_q) := by
    refine aux_lem_load_telescope (f := fun k => aux_lem_load_Whi i u b (R / 2 ^ k))
      hq0 hq1 hB (fun k => ?_) m
    have hstep := aux_lem_load_step_hi i hu hum hG hM0 hM (hδ k) hb
      (by rw [htwo k]; linarith [hRk k])
    rw [htwo k, aux_lem_load_pow_dyadic hR.le] at hstep
    calc _ ≤ 2 * M * aux_lem_load_cst d 1 * (R ^ (1 / 4 : ℝ) * aux_lem_load_q ^ k) * S := hstep
      _ = B * aux_lem_load_q ^ k := by rw [hB_def]; ring
  have hmid := aux_lem_load_step_mid i hu hum hG hM0 hM ha hab hb
  rw [← hR_def] at hmid
  simp only [pow_zero, div_one] at hlo hhi
  have hRb : R ^ (1 / 4 : ℝ) ≤ (b - a) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hR.le (by rw [hR_def]; linarith) (by norm_num)
  have h1q : 0 < 1 - aux_lem_load_q := by linarith
  calc |aux_lem_load_Whi i u b (R / 2 ^ m) - aux_lem_load_Wlo i u a (R / 2 ^ m)|
      ≤ |aux_lem_load_Whi i u b (R / 2 ^ m) - aux_lem_load_Whi i u b R| +
        |aux_lem_load_Whi i u b R - aux_lem_load_Wlo i u a R| +
        |aux_lem_load_Wlo i u a R - aux_lem_load_Wlo i u a (R / 2 ^ m)| := by
        have := abs_sub_le (aux_lem_load_Whi i u b (R / 2 ^ m)) (aux_lem_load_Whi i u b R)
          (aux_lem_load_Wlo i u a (R / 2 ^ m))
        have := abs_sub_le (aux_lem_load_Whi i u b R) (aux_lem_load_Wlo i u a R)
          (aux_lem_load_Wlo i u a (R / 2 ^ m))
        linarith
    _ ≤ B / (1 - aux_lem_load_q) + M * aux_lem_load_cst d 2 * R ^ (1 / 4 : ℝ) * S +
        B / (1 - aux_lem_load_q) := by
        rw [abs_sub_comm (aux_lem_load_Wlo i u a R)]
        linarith
    _ = aux_lem_load_CF d M * R ^ (1 / 4 : ℝ) * S := by
        rw [hB_def, aux_lem_load_CF]; field_simp; ring
    _ ≤ aux_lem_load_CF d M * (b - a) ^ (1 / 4 : ℝ) * S := by
        have : 0 ≤ aux_lem_load_CF d M := by
          unfold aux_lem_load_CF; positivity
        gcongr

/-- Coordinate integration by parts for `C¹` data (box divergence theorem): for
`ψ ∈ C¹(ℝ)` vanishing at `0` and `1`, `∫_Q ∂_i φ · ψ(x_i) + ∫_Q φ · ψ'(x_i) = 0`. -/
theorem aux_lem_load_smooth_ibp {n : ℕ} (i : Fin (n + 1)) {φ : SpatialCoordinates (n + 1) → ℝ}
    (hφ : ContDiff ℝ 1 φ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 0) :
    (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        fderiv ℝ φ x (Pi.single i 1) * ψ (x i)) +
      (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        φ x * deriv ψ (x i)) = 0 := by
  classical
  let lo : Fin (n + 1) → ℝ := fun _ => 0
  let hi : Fin (n + 1) → ℝ := fun _ => 1
  have hle : lo ≤ hi := fun _ => zero_le_one
  have hφd : ∀ x, HasFDerivAt φ (fderiv ℝ φ x) x :=
    fun x => (hφ.differentiable (by norm_num) x).hasFDerivAt
  have hψd : ∀ t, HasDerivAt ψ (deriv ψ t) t :=
    fun t => (hψ.differentiable (by norm_num) t).hasDerivAt
  have hcφ' : Continuous (fun x => fderiv ℝ φ x (Pi.single i 1)) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcψ' : Continuous (deriv ψ) := hψ.continuous_deriv (by norm_num)
  let f : Fin (n + 1) → SpatialCoordinates (n + 1) → ℝ :=
    fun j x => if j = i then φ x * ψ (x i) else 0
  let f' : Fin (n + 1) → SpatialCoordinates (n + 1) → (SpatialCoordinates (n + 1) →L[ℝ] ℝ) :=
    fun j x => if j = i then
      φ x • (deriv ψ (x i) • ContinuousLinearMap.proj i) + ψ (x i) • fderiv ℝ φ x else 0
  let g : SpatialCoordinates (n + 1) → ℝ :=
    fun x => φ x * deriv ψ (x i) + ψ (x i) * fderiv ℝ φ x (Pi.single i 1)
  have hg : Continuous g :=
    (hφ.continuous.mul (hcψ'.comp (continuous_apply i))).add
      ((hψ.continuous.comp (continuous_apply i)).mul hcφ')
  have hsum : ∀ x, ∑ j, f' j x (Pi.single j 1) = g x := by
    intro x
    rw [Finset.sum_eq_single i]
    · simp [f', g]
    · intro j _ hj; simp [f', hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable' lo hi hle f f' ∅
    countable_empty
    (fun j => by
      by_cases hj : j = i
      · simp only [f, hj, if_true]
        exact (hφ.continuous.mul (hψ.continuous.comp (continuous_apply i))).continuousOn
      · simp only [f, hj, if_false]; exact continuousOn_const)
    (fun x _ j => by
      by_cases hj : j = i
      · simp only [f, f', hj, if_true]
        exact (hφd x).mul ((hψd (x i)).comp_hasFDerivAt x (hasFDerivAt_apply i x))
      · simp only [f, f', hj, if_false]; exact hasFDerivAt_const _ _)
    (by
      simp_rw [hsum]
      exact hg.integrableOn_Icc)
  have hface : ∀ j (y : Fin n → ℝ) (t : ℝ), t = 0 ∨ t = 1 → f j (Fin.insertNth j t y) = 0 := by
    intro j y t ht
    by_cases hj : j = i
    · subst hj
      simp only [f, if_true, Fin.insertNth_apply_same]
      rcases ht with ht | ht <;> subst ht <;> simp [hψ0, hψ1]
    · simp [f, hj]
  have hrhs : (∑ j : Fin (n + 1),
      ((∫ y in Icc (lo ∘ j.succAbove) (hi ∘ j.succAbove), f j (Fin.insertNth j (hi j) y)) -
        ∫ y in Icc (lo ∘ j.succAbove) (hi ∘ j.succAbove), f j (Fin.insertNth j (lo j) y))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp only [hi, lo, hface j _ 1 (Or.inr rfl), hface j _ 0 (Or.inl rfl), integral_zero, sub_self]
  rw [hrhs] at hdiv
  simp_rw [hsum] at hdiv
  have hQ : (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))) =
      Set.pi Set.univ (fun j => Ioo (lo j) (hi j)) := aux_lem_load_Q_eq (n + 1)
  have hint : ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))), g x = 0 := by
    rw [hQ]
    refine (setIntegral_congr_set ?_).trans hdiv
    exact Measure.univ_pi_Ioo_ae_eq_Icc
  have hsub : (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))) ⊆ Icc lo hi := by
    rw [hQ]; intro x hx
    exact ⟨fun j => (hx j (mem_univ j)).1.le, fun j => (hx j (mem_univ j)).2.le⟩
  have hi1 : IntegrableOn (fun x => fderiv ℝ φ x (Pi.single i 1) * ψ (x i))
      (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))) :=
    ((hcφ'.mul (hψ.continuous.comp (continuous_apply i))).integrableOn_Icc).mono_set hsub
  have hi2 : IntegrableOn (fun x => φ x * deriv ψ (x i))
      (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))) :=
    ((hφ.continuous.mul (hcψ'.comp (continuous_apply i))).integrableOn_Icc).mono_set hsub
  rw [← integral_add hi1 hi2, ← hint]
  congr 1; ext x; simp only [g]; ring

/-- **Coordinate integration by parts on `H¹(Q)`.** For `ψ ∈ C¹(ℝ)` with `ψ(0) = ψ(1) = 0`,
`∫_Q ∂_i v · ψ(x_i) + ∫_Q v · ψ'(x_i) = 0`. Both sides are continuous on the graph and the
`C¹` data are dense (`lane4_neumann_boundary_identity_trace_foundation`). -/
theorem aux_lem_load_weak_ibp {n : ℕ} (hn : 1 ≤ n) (i : Fin (n + 1)) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 0)
    (v : weakSobolevGraph (unitNeumannCube (n + 1))) :
    (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        ((v : SobolevData (unitNeumannCube (n + 1))).2 i) x * ψ (x i)) +
      (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        ((v : SobolevData (unitNeumannCube (n + 1))).1) x * deriv ψ (x i)) = 0 := by
  classical
  have hcψ : Continuous (fun x : SpatialCoordinates (n + 1) => ψ (x i)) :=
    hψ.continuous.comp (continuous_apply i)
  have hcψ' : Continuous (fun x : SpatialCoordinates (n + 1) => deriv ψ (x i)) :=
    (hψ.continuous_deriv (by norm_num)).comp (continuous_apply i)
  let T1 := aux_continuousL2 (n + 1) _ hcψ
  let T2 := aux_continuousL2 (n + 1) _ hcψ'
  let Λ : weakSobolevGraph (unitNeumannCube (n + 1)) → ℝ := fun w =>
    inner ℝ T1 ((w : SobolevData (unitNeumannCube (n + 1))).2 i) +
      inner ℝ T2 (w : SobolevData (unitNeumannCube (n + 1))).1
  have hΛ : ∀ w : weakSobolevGraph (unitNeumannCube (n + 1)), Λ w =
      (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        ((w : SobolevData (unitNeumannCube (n + 1))).2 i) x * ψ (x i)) +
      (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        ((w : SobolevData (unitNeumannCube (n + 1))).1) x * deriv ψ (x i)) := by
    intro w
    simp only [Λ]
    rw [aux_L2_inner_ae T1 _ (fun x => ψ (x i)) _ (aux_continuousL2_coeFn _ _ hcψ)
        Filter.EventuallyEq.rfl,
      aux_L2_inner_ae T2 _ (fun x => deriv ψ (x i)) _ (aux_continuousL2_coeFn _ _ hcψ')
        Filter.EventuallyEq.rfl]
    simp only [mul_comm]
  have hcont : Continuous Λ := by
    apply Continuous.add
    · exact continuous_const.inner
        ((continuous_apply i).comp (continuous_snd.comp continuous_subtype_val))
    · exact continuous_const.inner (continuous_fst.comp continuous_subtype_val)
  have hclosed : IsClosed {w : weakSobolevGraph (unitNeumannCube (n + 1)) | Λ w = 0} :=
    isClosed_eq hcont continuous_const
  have hTF := lane4_neumann_boundary_identity_trace_foundation n hn
  obtain ⟨-, hdense⟩ := hTF
  have hD : {w : weakSobolevGraph (unitNeumannCube (n + 1)) |
      ∃ (φ : SpatialCoordinates (n + 1) → ℝ), ContDiff ℝ 1 φ ∧
        ((w : SobolevData (unitNeumannCube (n + 1))).1 : SpatialCoordinates (n + 1) → ℝ) =ᵐ[
          volume.restrict (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1)))] φ} ⊆
      {w | Λ w = 0} := by
    rintro w ⟨φ, hφ, hwφ⟩
    have hw : w = aux_C1Lift ⟨φ, hφ⟩ :=
      aux_graph_fst_injective (Lp.ext (hwφ.trans (aux_C1Data_fst_ae φ hφ).symm))
    show Λ w = 0
    rw [hΛ, hw]
    change (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        ((aux_C1Data φ hφ).2 i) x * ψ (x i)) +
      (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        ((aux_C1Data φ hφ).1) x * deriv ψ (x i)) = 0
    have e1 : (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        ((aux_C1Data φ hφ).2 i) x * ψ (x i)) =
        ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
          fderiv ℝ φ x (Pi.single i 1) * ψ (x i) := by
      apply integral_congr_ae
      filter_upwards [aux_C1Data_snd_ae φ hφ i] with x hx
      rw [hx]
    have e2 : (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        ((aux_C1Data φ hφ).1) x * deriv ψ (x i)) =
        ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
          φ x * deriv ψ (x i) := by
      apply integral_congr_ae
      filter_upwards [aux_C1Data_fst_ae φ hφ] with x hx
      rw [hx]
    rw [e1, e2]
    exact aux_lem_load_smooth_ibp i hφ hψ hψ0 hψ1
  have hall : closure _ ⊆ _ := closure_minimal hD hclosed
  rw [hdense.closure_eq] at hall
  rw [← hΛ]
  exact hall (mem_univ v)

/-- Smooth cutoff of the slab `(a, b)` at scale `δ`. -/
def aux_lem_load_psi (a b δ t : ℝ) : ℝ :=
  Real.smoothTransition ((t - a) / δ) * Real.smoothTransition ((b - t) / δ)

theorem aux_lem_load_psi_contDiff (a b δ : ℝ) : ContDiff ℝ 1 (aux_lem_load_psi a b δ) := by
  unfold aux_lem_load_psi
  apply ContDiff.mul
  · exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  · exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)

theorem aux_lem_load_psi_zero {a b δ : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) :
    aux_lem_load_psi a b δ 0 = 0 := by
  unfold aux_lem_load_psi
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le),
    zero_mul]

theorem aux_lem_load_psi_one {a b δ : ℝ} (hδ : 0 < δ) (hb : b ≤ 1) :
    aux_lem_load_psi a b δ 1 = 0 := by
  unfold aux_lem_load_psi
  rw [Real.smoothTransition.zero_of_nonpos (x := (b - 1) / δ)
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le), mul_zero]

theorem aux_lem_load_psi_bound (a b δ t : ℝ) : |aux_lem_load_psi a b δ t| ≤ 1 := by
  unfold aux_lem_load_psi
  rw [abs_of_nonneg (mul_nonneg (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.nonneg _))]
  exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem aux_lem_load_psi_deriv {a b δ : ℝ} (hδ : 0 < δ) (h2 : 2 * δ ≤ b - a) (t : ℝ) :
    deriv (aux_lem_load_psi a b δ) t = aux_lem_load_wlo a δ t - aux_lem_load_whi b δ t := by
  have h1 : HasDerivAt (fun t => Real.smoothTransition ((t - a) / δ))
      (aux_lem_load_wlo a δ t) t := by
    have := (aux_lem_load_st_hasDerivAt ((t - a) / δ)).comp t
      (((hasDerivAt_id t).sub_const a).div_const δ)
    convert! this using 1 <;> first | rfl | (unfold aux_lem_load_wlo; ring)
  have h2' : HasDerivAt (fun t => Real.smoothTransition ((b - t) / δ))
      (-aux_lem_load_whi b δ t) t := by
    have := (aux_lem_load_st_hasDerivAt ((b - t) / δ)).comp t
      (((hasDerivAt_id t).const_sub b).div_const δ)
    convert! this using 1 <;> first | rfl | (unfold aux_lem_load_whi; ring)
  have hd := h1.mul h2'
  rw [show aux_lem_load_psi a b δ = (fun t => Real.smoothTransition ((t - a) / δ)) *
    (fun t => Real.smoothTransition ((b - t) / δ)) from rfl, hd.deriv]
  have e1 : aux_lem_load_wlo a δ t * Real.smoothTransition ((b - t) / δ) =
      aux_lem_load_wlo a δ t := by
    by_cases hw : aux_lem_load_wlo a δ t = 0
    · rw [hw, zero_mul]
    · have := aux_lem_load_wlo_supp hδ hw
      rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hδ]; linarith [this.2]),
        mul_one]
  have e2 : Real.smoothTransition ((t - a) / δ) * -aux_lem_load_whi b δ t =
      -aux_lem_load_whi b δ t := by
    by_cases hw : aux_lem_load_whi b δ t = 0
    · rw [hw, neg_zero, mul_zero]
    · have := aux_lem_load_whi_supp hδ hw
      rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hδ]; linarith [this.1]),
        one_mul]
  rw [e1, e2]; ring

theorem aux_lem_load_psi_tendsto {a b : ℝ} {δ : ℕ → ℝ} (hδ : ∀ m, 0 < δ m)
    (hδ0 : Tendsto δ atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun m => aux_lem_load_psi a b (δ m) t) atTop
      (𝓝 ((Ioo a b).indicator (fun _ => (1:ℝ)) t)) := by
  by_cases ht : t ∈ Ioo a b
  · rw [indicator_of_mem ht]
    have hpos : 0 < min (t - a) (b - t) := lt_min (by linarith [ht.1]) (by linarith [ht.2])
    apply tendsto_const_nhds.congr'
    filter_upwards [hδ0.eventually (gt_mem_nhds hpos)] with m hm
    unfold aux_lem_load_psi
    rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, mul_one]
    · rw [le_div_iff₀ (hδ m)]; linarith [min_le_right (t - a) (b - t)]
    · rw [le_div_iff₀ (hδ m)]; linarith [min_le_left (t - a) (b - t)]
  · rw [indicator_of_notMem ht]
    apply tendsto_const_nhds.congr'
    filter_upwards with m
    unfold aux_lem_load_psi
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at ht
    rcases ht with ht | ht
    · rw [Real.smoothTransition.zero_of_nonpos (x := (t - a) / δ m)
        (div_nonpos_of_nonpos_of_nonneg (by linarith) (hδ m).le), zero_mul]
    · rw [Real.smoothTransition.zero_of_nonpos (x := (b - t) / δ m)
        (div_nonpos_of_nonpos_of_nonneg (by linarith) (hδ m).le), mul_zero]

/-- **Flux lemma.** For `v ∈ H¹(Q)` and `0 ≤ a < b ≤ 1`, the flux of `∂_i v` through the slab
`{a < x_i < b}` is at most `C (b - a)^{1/4}` times the square root of the Gagliardo double
integral of `v`. -/
theorem aux_lem_load_flux {n : ℕ} (hn : 1 ≤ n) (i : Fin (n + 1))
    (v : weakSobolevGraph (unitNeumannCube (n + 1)))
    (hG : aux_lem_load_gag ((v : SobolevData (unitNeumannCube (n + 1))).1 :
      SpatialCoordinates (n + 1) → ℝ) ≠ ⊤)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ y, aux_lem_load_eta y ≤ M)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    |∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        ((v : SobolevData (unitNeumannCube (n + 1))).2 i) x *
          (Ioo a b).indicator (fun _ => (1:ℝ)) (x i)| ≤
      aux_lem_load_CF (n + 1) M * (b - a) ^ (1 / 4 : ℝ) *
        Real.sqrt (aux_lem_load_gag ((v : SobolevData (unitNeumannCube (n + 1))).1 :
          SpatialCoordinates (n + 1) → ℝ)).toReal := by
  set u : SpatialCoordinates (n + 1) → ℝ := ((v : SobolevData (unitNeumannCube (n + 1))).1 :
    SpatialCoordinates (n + 1) → ℝ) with hu_def
  set g : SpatialCoordinates (n + 1) → ℝ := ((v : SobolevData (unitNeumannCube (n + 1))).2 i :
    SpatialCoordinates (n + 1) → ℝ) with hg_def
  have hu : MemLp u 2 (volume.restrict
      (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1)))) := Lp.memLp _
  have hum : Measurable u := (Lp.stronglyMeasurable _).measurable
  have hu1 : Integrable u (volume.restrict
      (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1)))) := hu.integrable one_le_two
  have hg1 : Integrable g (volume.restrict
      (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1)))) :=
    (Lp.memLp _).integrable one_le_two
  set δ : ℕ → ℝ := fun m => (b - a) / 2 / 2 ^ m with hδ_def
  have hδ : ∀ m, 0 < δ m := by
    intro m
    have : 0 < b - a := by linarith
    simp only [hδ_def]
    positivity
  have hδ2 : ∀ m, 2 * δ m ≤ b - a := by
    intro m
    have : δ m ≤ (b - a) / 2 := div_le_self (by linarith) (one_le_pow₀ (by norm_num))
    linarith
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    have := tendsto_const_nhds (x := (b - a) / 2).div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1:ℝ) < 2))
    simpa [hδ_def] using this
  have hWint : ∀ w : ℝ → ℝ, Continuous w → (∃ c, ∀ t, |w t| ≤ c) →
      Integrable (fun x : SpatialCoordinates (n + 1) => u x * w (x i)) (volume.restrict
        (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1)))) := by
    intro w hw ⟨c, hc⟩
    have := hu1.bdd_mul (c := c) (hw.comp (continuous_apply i)).aestronglyMeasurable
      (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact hc (x i)))
    refine this.congr (ae_of_all _ (fun x => ?_))
    simp only [Function.comp]
    ring
  obtain ⟨Mb, hMb⟩ : ∃ c, ∀ y, |aux_lem_load_eta y| ≤ c :=
    ⟨M, fun y => by rw [abs_of_nonneg (aux_lem_load_eta_nonneg y)]; exact hM y⟩
  have hkey : ∀ m, (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
      g x * aux_lem_load_psi a b (δ m) (x i)) =
      aux_lem_load_Whi i u b (δ m) - aux_lem_load_Wlo i u a (δ m) := by
    intro m
    have hibp := aux_lem_load_weak_ibp hn i (aux_lem_load_psi_contDiff a b (δ m))
      (aux_lem_load_psi_zero (hδ m) ha) (aux_lem_load_psi_one (hδ m) hb) v
    simp only [aux_lem_load_psi_deriv (hδ m) (hδ2 m)] at hibp
    have hsplit : (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        u x * (aux_lem_load_wlo a (δ m) (x i) - aux_lem_load_whi b (δ m) (x i))) =
        aux_lem_load_Wlo i u a (δ m) - aux_lem_load_Whi i u b (δ m) := by
      unfold aux_lem_load_Wlo aux_lem_load_Whi
      rw [← integral_sub]
      · congr 1; ext x; ring
      · exact hWint _ (aux_lem_load_wlo_continuous a (δ m))
          ⟨Mb * (δ m)⁻¹, fun t => by
            unfold aux_lem_load_wlo
            rw [abs_mul, abs_of_pos (inv_pos.mpr (hδ m)), mul_comm]
            exact mul_le_mul_of_nonneg_right (hMb _) (inv_nonneg.mpr (hδ m).le)⟩
      · exact hWint _ (aux_lem_load_whi_continuous b (δ m))
          ⟨Mb * (δ m)⁻¹, fun t => by
            unfold aux_lem_load_whi
            rw [abs_mul, abs_of_pos (inv_pos.mpr (hδ m)), mul_comm]
            exact mul_le_mul_of_nonneg_right (hMb _) (inv_nonneg.mpr (hδ m).le)⟩
    rw [hsplit] at hibp
    linarith
  have hbound : ∀ m, |∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
      g x * aux_lem_load_psi a b (δ m) (x i)| ≤
      aux_lem_load_CF (n + 1) M * (b - a) ^ (1 / 4 : ℝ) *
        Real.sqrt (aux_lem_load_gag u).toReal := by
    intro m
    rw [hkey m]
    exact aux_lem_load_chain i hu hum hG hM0 hM ha hab hb m
  have hlim : Tendsto (fun m => ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
      g x * aux_lem_load_psi a b (δ m) (x i)) atTop
      (𝓝 (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        g x * (Ioo a b).indicator (fun _ => (1:ℝ)) (x i))) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
    · intro m
      exact hg1.aestronglyMeasurable.mul
        (((aux_lem_load_psi_contDiff a b (δ m)).continuous.comp
          (continuous_apply i)).aestronglyMeasurable)
    · exact hg1.norm
    · intro m
      refine ae_of_all _ (fun x => ?_)
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (by
        rw [Real.norm_eq_abs]; exact aux_lem_load_psi_bound _ _ _ _)
    · refine ae_of_all _ (fun x => ?_)
      exact (aux_lem_load_psi_tendsto hδ hδ0 (x i)).const_mul (g x)
  exact le_of_tendsto hlim.abs (Eventually.of_forall hbound)

theorem aux_lem_load_prim_hasDerivAt {r : ℝ → ℝ} (hr : Continuous r) (t : ℝ) :
    HasDerivAt (fun s => ∫ τ in (0:ℝ)..s, r τ) (r t) t :=
  (hr.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem aux_lem_load_prim_contDiff {r : ℝ → ℝ} (hr : Continuous r) :
    ContDiff ℝ 1 (fun s => ∫ τ in (0:ℝ)..s, r τ) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (aux_lem_load_prim_hasDerivAt hr t).differentiableAt, ?_⟩
  have : deriv (fun s => ∫ τ in (0:ℝ)..s, r τ) = r :=
    funext fun t => (aux_lem_load_prim_hasDerivAt hr t).deriv
  rw [this]; exact hr

theorem aux_lem_load_mul_indicator_integrable {r : ℝ → ℝ} (hr : Integrable r) {S : Set ℝ}
    (hS : MeasurableSet S) : Integrable (fun τ => r τ * S.indicator (fun _ => (1:ℝ)) τ) := by
  have e : (fun τ => r τ * S.indicator (fun _ => (1:ℝ)) τ) = S.indicator r := by
    ext τ; by_cases h : τ ∈ S <;> simp [h]
  rw [e]; exact hr.indicator hS

theorem aux_lem_load_prim_eq {r : ℝ → ℝ} (hr0 : ∀ τ, τ ≤ 0 → r τ = 0) {s : ℝ} (hs : 0 ≤ s) :
    ∫ τ in (0:ℝ)..s, r τ = ∫ τ, r τ * (Iic s).indicator (fun _ => (1:ℝ)) τ := by
  rw [intervalIntegral.integral_of_le hs, ← integral_indicator measurableSet_Ioc]
  congr 1; ext τ
  by_cases h1 : τ ∈ Ioc 0 s
  · rw [indicator_of_mem h1, indicator_of_mem (show τ ∈ Iic s from h1.2), mul_one]
  · rw [indicator_of_notMem h1]
    by_cases h2 : τ ≤ 0
    · rw [hr0 τ h2, zero_mul]
    · have : τ ∉ Iic s := fun h => h1 ⟨lt_of_not_ge h2, h⟩
      rw [indicator_of_notMem this, mul_zero]

theorem aux_lem_load_tail {r : ℝ → ℝ} (hr0 : ∀ τ, τ ≤ 0 → r τ = 0) (hrint : Integrable r)
    (h1 : ∫ τ, r τ = 1) {s : ℝ} (hs : 0 ≤ s) :
    ∫ τ, r τ * (Ioi s).indicator (fun _ => (1:ℝ)) τ = 1 - ∫ τ in (0:ℝ)..s, r τ := by
  rw [aux_lem_load_prim_eq hr0 hs]
  have e : ∫ τ, r τ * (Ioi s).indicator (fun _ => (1:ℝ)) τ =
      (∫ τ, r τ) - ∫ τ, r τ * (Iic s).indicator (fun _ => (1:ℝ)) τ := by
    rw [← integral_sub hrint (aux_lem_load_mul_indicator_integrable hrint measurableSet_Iic)]
    congr 1; ext τ
    by_cases h : τ ≤ s
    · rw [indicator_of_notMem (show τ ∉ Ioi s from not_lt.mpr h),
        indicator_of_mem (show τ ∈ Iic s from h)]; ring
    · rw [indicator_of_mem (show τ ∈ Ioi s from lt_of_not_ge h),
        indicator_of_notMem (show τ ∉ Iic s from h)]; ring
  rw [e, h1]

/-- The two-face kernel `κ(t, τ) = 1[0 < t < τ] + 1[1 - τ < t < 1]`. -/
def aux_lem_load_kappa (t τ : ℝ) : ℝ :=
  (Ioo 0 τ).indicator (fun _ => (1:ℝ)) t + (Ioo (1 - τ) 1).indicator (fun _ => (1:ℝ)) t

theorem aux_lem_load_kappa_measurable :
    Measurable (fun p : ℝ × ℝ => aux_lem_load_kappa p.1 p.2) := by
  unfold aux_lem_load_kappa
  apply Measurable.add
  · have e : (fun p : ℝ × ℝ => (Ioo 0 p.2).indicator (fun _ => (1:ℝ)) p.1) =
        {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2}.indicator (fun _ => 1) := by
      ext p; simp only [indicator, mem_Ioo, mem_setOf_eq]
    rw [e]
    exact measurable_const.indicator
      ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt measurable_fst measurable_snd))
  · have e : (fun p : ℝ × ℝ => (Ioo (1 - p.2) 1).indicator (fun _ => (1:ℝ)) p.1) =
        {p : ℝ × ℝ | 1 - p.2 < p.1 ∧ p.1 < 1}.indicator (fun _ => 1) := by
      ext p; simp only [indicator, mem_Ioo, mem_setOf_eq]
    rw [e]
    exact measurable_const.indicator
      ((measurableSet_lt (measurable_const.sub measurable_snd) measurable_fst).inter
        (measurableSet_lt measurable_fst measurable_const))

theorem aux_lem_load_kappa_nonneg (t τ : ℝ) : 0 ≤ aux_lem_load_kappa t τ := by
  unfold aux_lem_load_kappa
  apply add_nonneg <;> apply indicator_nonneg <;> intros <;> norm_num

theorem aux_lem_load_kappa_le (t τ : ℝ) : aux_lem_load_kappa t τ ≤ 2 := by
  unfold aux_lem_load_kappa
  have h1 : (Ioo 0 τ).indicator (fun _ => (1:ℝ)) t ≤ 1 :=
    indicator_le_self' (fun _ _ => zero_le_one) t |>.trans (le_refl _)
  have h2 : (Ioo (1 - τ) 1).indicator (fun _ => (1:ℝ)) t ≤ 1 :=
    indicator_le_self' (fun _ _ => zero_le_one) t |>.trans (le_refl _)
  linarith

/-- The cutoff `χ(t) = Φ(t) + Φ(1 - t) - 1`, `Φ(t) = ∫_0^t r`. -/
def aux_lem_load_chi (r : ℝ → ℝ) (t : ℝ) : ℝ :=
  (∫ τ in (0:ℝ)..t, r τ) + (∫ τ in (0:ℝ)..(1 - t), r τ) - 1

theorem aux_lem_load_chi_contDiff {r : ℝ → ℝ} (hr : Continuous r) :
    ContDiff ℝ 1 (aux_lem_load_chi r) := by
  unfold aux_lem_load_chi
  exact ((aux_lem_load_prim_contDiff hr).add
    ((aux_lem_load_prim_contDiff hr).comp (contDiff_const.sub contDiff_id))).sub contDiff_const

theorem aux_lem_load_chi_deriv {r : ℝ → ℝ} (hr : Continuous r) (t : ℝ) :
    deriv (aux_lem_load_chi r) t = r t - r (1 - t) := by
  have h1 := aux_lem_load_prim_hasDerivAt hr t
  have h2 := (aux_lem_load_prim_hasDerivAt hr (1 - t)).comp t ((hasDerivAt_id t).const_sub 1)
  have h : HasDerivAt (aux_lem_load_chi r) (r t + r (1 - t) * -1) t :=
    (h1.add h2).sub_const 1
  rw [h.deriv]; ring

theorem aux_lem_load_prim_one {r : ℝ → ℝ} (hr0 : ∀ τ, τ ≤ 0 → r τ = 0)
    (hr1 : ∀ τ, 1 ≤ τ → r τ = 0) (h1 : ∫ τ, r τ = 1) : ∫ τ in (0:ℝ)..1, r τ = 1 := by
  rw [aux_lem_load_prim_eq hr0 zero_le_one]
  calc ∫ τ, r τ * (Iic (1:ℝ)).indicator (fun _ => (1:ℝ)) τ = ∫ τ, r τ := by
        congr 1; ext τ
        by_cases h : τ ≤ 1
        · rw [indicator_of_mem (show τ ∈ Iic (1:ℝ) from h), mul_one]
        · rw [indicator_of_notMem (show τ ∉ Iic (1:ℝ) from h),
            hr1 τ (le_of_lt (lt_of_not_ge h)), zero_mul]
    _ = 1 := h1

theorem aux_lem_load_chi_zero {r : ℝ → ℝ} (hr0 : ∀ τ, τ ≤ 0 → r τ = 0)
    (hr1 : ∀ τ, 1 ≤ τ → r τ = 0) (h1 : ∫ τ, r τ = 1) : aux_lem_load_chi r 0 = 0 := by
  unfold aux_lem_load_chi
  rw [sub_zero, aux_lem_load_prim_one hr0 hr1 h1, intervalIntegral.integral_same]; ring

theorem aux_lem_load_chi_one {r : ℝ → ℝ} (hr0 : ∀ τ, τ ≤ 0 → r τ = 0)
    (hr1 : ∀ τ, 1 ≤ τ → r τ = 0) (h1 : ∫ τ, r τ = 1) : aux_lem_load_chi r 1 = 0 := by
  unfold aux_lem_load_chi
  rw [sub_self, aux_lem_load_prim_one hr0 hr1 h1, intervalIntegral.integral_same]; ring

theorem aux_lem_load_one_sub_chi {r : ℝ → ℝ} (hr0 : ∀ τ, τ ≤ 0 → r τ = 0)
    (hrint : Integrable r) (h1 : ∫ τ, r τ = 1) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    1 - aux_lem_load_chi r t = ∫ τ, r τ * aux_lem_load_kappa t τ := by
  have e : (fun τ => r τ * aux_lem_load_kappa t τ) = fun τ =>
      r τ * (Ioi t).indicator (fun _ => (1:ℝ)) τ +
        r τ * (Ioi (1 - t)).indicator (fun _ => (1:ℝ)) τ := by
    ext τ
    unfold aux_lem_load_kappa
    rw [mul_add]
    congr 2
    · by_cases h : t < τ
      · rw [indicator_of_mem (show t ∈ Ioo 0 τ from ⟨ht.1, h⟩),
          indicator_of_mem (show τ ∈ Ioi t from h)]
      · rw [indicator_of_notMem (show t ∉ Ioo 0 τ from fun hh => h hh.2),
          indicator_of_notMem (show τ ∉ Ioi t from h)]
    · by_cases h : 1 - t < τ
      · rw [indicator_of_mem (show t ∈ Ioo (1 - τ) 1 from ⟨by linarith, ht.2⟩),
          indicator_of_mem (show τ ∈ Ioi (1 - t) from h)]
      · rw [indicator_of_notMem (show t ∉ Ioo (1 - τ) 1 from fun hh => h (by linarith [hh.1])),
          indicator_of_notMem (show τ ∉ Ioi (1 - t) from h)]
  rw [e, integral_add (aux_lem_load_mul_indicator_integrable hrint measurableSet_Ioi)
      (aux_lem_load_mul_indicator_integrable hrint measurableSet_Ioi),
    aux_lem_load_tail hr0 hrint h1 ht.1.le, aux_lem_load_tail hr0 hrint h1 (by linarith [ht.2])]
  unfold aux_lem_load_chi
  ring

theorem aux_lem_load_fubini {d : ℕ} (i : Fin d) {g : SpatialCoordinates d → ℝ}
    (hg : Integrable g (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (hgm : Measurable g) {r : ℝ → ℝ} (hr : Continuous r) (hrint : Integrable r) :
    ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
        g x * (∫ τ, r τ * aux_lem_load_kappa (x i) τ) =
      ∫ τ, r τ * ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
        g x * aux_lem_load_kappa (x i) τ := by
  have hmeas : Measurable (Function.uncurry fun (x : SpatialCoordinates d) (τ : ℝ) =>
      g x * (r τ * aux_lem_load_kappa (x i) τ)) := by
    apply (hgm.comp measurable_fst).mul
    apply (hr.measurable.comp measurable_snd).mul
    exact aux_lem_load_kappa_measurable.comp
      (by fun_prop : Measurable fun p : SpatialCoordinates d × ℝ => (p.1 i, p.2))
  have hI : Integrable (Function.uncurry fun (x : SpatialCoordinates d) (τ : ℝ) =>
      g x * (r τ * aux_lem_load_kappa (x i) τ))
      ((volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))).prod volume) := by
    refine Integrable.mono' ((hg.norm.mul_prod hrint.norm).const_mul 2)
      hmeas.aestronglyMeasurable (ae_of_all _ (fun p => ?_))
    show ‖g p.1 * (r p.2 * aux_lem_load_kappa (p.1 i) p.2)‖ ≤ 2 * (‖g p.1‖ * ‖r p.2‖)
    rw [norm_mul, norm_mul]
    have hk : ‖aux_lem_load_kappa (p.1 i) p.2‖ ≤ 2 := by
      rw [Real.norm_of_nonneg (aux_lem_load_kappa_nonneg _ _)]; exact aux_lem_load_kappa_le _ _
    have h1 := norm_nonneg (g p.1)
    have h2 := norm_nonneg (r p.2)
    calc ‖g p.1‖ * (‖r p.2‖ * ‖aux_lem_load_kappa (p.1 i) p.2‖)
        ≤ ‖g p.1‖ * (‖r p.2‖ * 2) := by gcongr
      _ = 2 * (‖g p.1‖ * ‖r p.2‖) := by ring
  have hswap := integral_integral_swap hI
  have eL : ∀ x : SpatialCoordinates d, g x * (∫ τ, r τ * aux_lem_load_kappa (x i) τ) =
      ∫ τ, g x * (r τ * aux_lem_load_kappa (x i) τ) := fun x => (integral_const_mul _ _).symm
  have eR : ∀ τ : ℝ, (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
      g x * (r τ * aux_lem_load_kappa (x i) τ)) =
      r τ * ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
        g x * aux_lem_load_kappa (x i) τ := by
    intro τ
    rw [← integral_const_mul]
    congr 1; ext x; ring
  simp_rw [eL, hswap, eR]

theorem aux_lem_load_prim_mem {r : ℝ → ℝ} (hr0 : ∀ τ, τ ≤ 0 → r τ = 0) (hrnn : ∀ τ, 0 ≤ r τ)
    (hrint : Integrable r) (h1 : ∫ τ, r τ = 1) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ ∫ τ in (0:ℝ)..s, r τ ∧ ∫ τ in (0:ℝ)..s, r τ ≤ 1 := by
  rw [aux_lem_load_prim_eq hr0 hs]
  have hind : ∀ τ, 0 ≤ (Iic s).indicator (fun _ => (1:ℝ)) τ ∧
      (Iic s).indicator (fun _ => (1:ℝ)) τ ≤ 1 := by
    intro τ; by_cases h : τ ∈ Iic s <;> simp [h]
  constructor
  · exact integral_nonneg (fun τ => mul_nonneg (hrnn τ) (hind τ).1)
  · calc ∫ τ, r τ * (Iic s).indicator (fun _ => (1:ℝ)) τ ≤ ∫ τ, r τ := by
          apply integral_mono (aux_lem_load_mul_indicator_integrable hrint measurableSet_Iic) hrint
          intro τ
          exact mul_le_of_le_one_right (hrnn τ) (hind τ).2
      _ = 1 := h1

/-- **One face pair.** The contribution of coordinate `i` to `L_p - L_{p,ε}` is bounded by
`2 C (2ε)^{1/4}` times the square root of the Gagliardo double integral. -/
theorem aux_lem_load_face {n : ℕ} (hn : 1 ≤ n) (i : Fin (n + 1))
    (v : weakSobolevGraph (unitNeumannCube (n + 1)))
    (hG : aux_lem_load_gag ((v : SobolevData (unitNeumannCube (n + 1))).1 :
      SpatialCoordinates (n + 1) → ℝ) ≠ ⊤)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ y, aux_lem_load_eta y ≤ M)
    {r : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) (hr : Continuous r)
    (hrnn : ∀ τ, 0 ≤ r τ) (hrs : ∀ τ, r τ ≠ 0 → τ ∈ Ioo ε (2 * ε)) (h1 : ∫ τ, r τ = 1) :
    |(∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        ((v : SobolevData (unitNeumannCube (n + 1))).2 i) x) -
      ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        (r (1 - x i) - r (x i)) * ((v : SobolevData (unitNeumannCube (n + 1))).1) x| ≤
      2 * aux_lem_load_CF (n + 1) M * (2 * ε) ^ (1 / 4 : ℝ) *
        Real.sqrt (aux_lem_load_gag ((v : SobolevData (unitNeumannCube (n + 1))).1 :
          SpatialCoordinates (n + 1) → ℝ)).toReal := by
  set u : SpatialCoordinates (n + 1) → ℝ := ((v : SobolevData (unitNeumannCube (n + 1))).1 :
    SpatialCoordinates (n + 1) → ℝ) with hu_def
  set g : SpatialCoordinates (n + 1) → ℝ := ((v : SobolevData (unitNeumannCube (n + 1))).2 i :
    SpatialCoordinates (n + 1) → ℝ) with hg_def
  set μ := volume.restrict (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1)))
    with hμ_def
  set S := Real.sqrt (aux_lem_load_gag u).toReal with hS_def
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hCF : 0 ≤ aux_lem_load_CF (n + 1) M := by
    unfold aux_lem_load_CF
    have := aux_lem_load_q_lt_one
    have := aux_lem_load_cst_nonneg (n + 1) 1
    have := aux_lem_load_cst_nonneg (n + 1) 2
    have : 0 < 1 - aux_lem_load_q := by linarith
    positivity
  have hu1 : Integrable u μ := (Lp.memLp _).integrable one_le_two
  have hg1 : Integrable g μ := (Lp.memLp _).integrable one_le_two
  have hgm : Measurable g := (Lp.stronglyMeasurable _).measurable
  have hr0 : ∀ τ, τ ≤ 0 → r τ = 0 := fun τ hτ => by
    by_contra h; have := hrs τ h; linarith [this.1]
  have hr1 : ∀ τ, 1 ≤ τ → r τ = 0 := fun τ hτ => by
    by_contra h; have := hrs τ h; linarith [this.2]
  have hrint : Integrable r := hr.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := ε) (b := 2 * ε)) (fun τ hτ => by
      by_contra h; exact hτ (Ioo_subset_Icc_self (hrs τ h))))
  have hQ : ∀ᵐ x ∂μ, x i ∈ Ioo (0:ℝ) 1 := by
    filter_upwards [ae_restrict_mem (unitNeumannCube (n + 1)).isOpen.measurableSet] with x hx
    rw [aux_lem_load_Q_eq] at hx
    exact hx i (mem_univ i)
  -- integration by parts against `χ`
  have hibp := aux_lem_load_weak_ibp hn i (aux_lem_load_chi_contDiff hr)
    (aux_lem_load_chi_zero hr0 hr1 h1) (aux_lem_load_chi_one hr0 hr1 h1) v
  simp only [aux_lem_load_chi_deriv hr] at hibp
  have hχb : ∀ᵐ x ∂μ, ‖aux_lem_load_chi r (x i)‖ ≤ 1 := by
    filter_upwards [hQ] with x hx
    have a1 := aux_lem_load_prim_mem hr0 hrnn hrint h1 (s := x i) hx.1.le
    have a2 := aux_lem_load_prim_mem hr0 hrnn hrint h1 (s := 1 - x i) (by linarith [hx.2])
    rw [Real.norm_eq_abs, abs_le]
    unfold aux_lem_load_chi
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  have hgχ : Integrable (fun x => g x * aux_lem_load_chi r (x i)) μ := by
    have := hg1.bdd_mul (((aux_lem_load_chi_contDiff hr).continuous.comp
      (continuous_apply i)).aestronglyMeasurable) hχb
    refine this.congr (ae_of_all _ (fun x => ?_))
    simp only [Function.comp]; ring
  have hstep1 : (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))), g x) -
      ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        (r (1 - x i) - r (x i)) * u x =
      ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        g x * (1 - aux_lem_load_chi r (x i)) := by
    have e1 : (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        g x * (1 - aux_lem_load_chi r (x i))) =
        (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))), g x) -
          ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
            g x * aux_lem_load_chi r (x i) := by
      rw [← integral_sub hg1 hgχ]; congr 1; ext x; ring
    have e2 : (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        (r (1 - x i) - r (x i)) * u x) =
        -∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
          u x * (r (x i) - r (1 - x i)) := by
      rw [← integral_neg]; congr 1; ext x; ring
    rw [e1, e2]
    linarith
  -- the bump-variable representation and Fubini
  have hstep2 : (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
      g x * (1 - aux_lem_load_chi r (x i))) =
      ∫ τ, r τ * ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        g x * aux_lem_load_kappa (x i) τ := by
    rw [← aux_lem_load_fubini i hg1 hgm hr hrint]
    apply integral_congr_ae
    filter_upwards [hQ] with x hx
    rw [aux_lem_load_one_sub_chi hr0 hrint h1 hx]
  -- each slab flux
  have hind_int : ∀ a b : ℝ, Integrable (fun x : SpatialCoordinates (n + 1) =>
      g x * (Ioo a b).indicator (fun _ => (1:ℝ)) (x i)) μ := by
    intro a b
    have hm : Measurable (fun x : SpatialCoordinates (n + 1) =>
        (Ioo a b).indicator (fun _ => (1:ℝ)) (x i)) :=
      (measurable_const.indicator measurableSet_Ioo).comp (measurable_pi_apply i)
    have := hg1.bdd_mul (c := 1) hm.aestronglyMeasurable
      (ae_of_all _ (fun x => by
        by_cases h : x i ∈ Ioo a b <;> simp [h]))
    refine this.congr (ae_of_all _ (fun x => ?_))
    simp only; ring
  have hinner : ∀ τ, (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
      g x * aux_lem_load_kappa (x i) τ) =
      (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        g x * (Ioo 0 τ).indicator (fun _ => (1:ℝ)) (x i)) +
      ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        g x * (Ioo (1 - τ) 1).indicator (fun _ => (1:ℝ)) (x i) := by
    intro τ
    rw [← integral_add (hind_int _ _) (hind_int _ _)]
    congr 1; ext x; unfold aux_lem_load_kappa; ring
  set K := 2 * aux_lem_load_CF (n + 1) M * (2 * ε) ^ (1 / 4 : ℝ) * S with hK_def
  have hpt : ∀ τ, ‖r τ * ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
      g x * aux_lem_load_kappa (x i) τ‖ ≤ r τ * K := by
    intro τ
    by_cases hτ : r τ = 0
    · rw [hτ, zero_mul, zero_mul, norm_zero]
    have hτs := hrs τ hτ
    have hτ0 : 0 < τ := by linarith [hτs.1]
    have hτ1 : τ ≤ 1 := by linarith [hτs.2]
    have hτε : τ ^ (1 / 4 : ℝ) ≤ (2 * ε) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hτ0.le hτs.2.le (by norm_num)
    have hlo := aux_lem_load_flux hn i v hG hM0 hM le_rfl hτ0 hτ1
    have hhi := aux_lem_load_flux hn i v hG hM0 hM (a := 1 - τ) (b := 1) (by linarith)
      (by linarith) le_rfl
    rw [sub_zero] at hlo
    rw [sub_sub_cancel] at hhi
    rw [norm_mul, Real.norm_of_nonneg (hrnn τ), hinner τ]
    apply mul_le_mul_of_nonneg_left _ (hrnn τ)
    rw [Real.norm_eq_abs]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ aux_lem_load_CF (n + 1) M * τ ^ (1 / 4 : ℝ) * S +
          aux_lem_load_CF (n + 1) M * τ ^ (1 / 4 : ℝ) * S := add_le_add hlo hhi
      _ ≤ K := by
        rw [hK_def]
        have : aux_lem_load_CF (n + 1) M * τ ^ (1 / 4 : ℝ) * S ≤
            aux_lem_load_CF (n + 1) M * (2 * ε) ^ (1 / 4 : ℝ) * S := by gcongr
        linarith
  rw [hstep1, hstep2]
  calc |∫ τ, r τ * ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        g x * aux_lem_load_kappa (x i) τ|
      ≤ ∫ τ, r τ * K := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le (hrint.mul_const K) (ae_of_all _ hpt)
    _ = K := by rw [integral_mul_const, h1, one_mul]

theorem aux_lem_load_gag_congr {d : ℕ} {u w : SpatialCoordinates d → ℝ} {c : ℝ}
    (hw : w =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
      fun x => u x - c) :
    aux_lem_load_gag w = aux_lem_load_gag u := by
  unfold aux_lem_load_gag
  apply lintegral_congr_ae
  filter_upwards [hw] with x hx
  apply lintegral_congr_ae
  filter_upwards [hw] with y hy
  rw [hx, hy]
  congr 2
  ring

theorem aux_lem_load_seminorm_eq {d : ℕ} (hd : 2 ≤ d)
    (f : DomainL2 (unitNeumannCube d)) :
    cubeFractionalL2Seminorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
        (fun _ : Fin 1 => f) =
      (ENNReal.ofReal (3 / 4) * aux_lem_load_gag (f : SpatialCoordinates d → ℝ)) ^ (1 / 2 : ℝ) := by
  unfold cubeFractionalL2Seminorm aux_lem_load_gag
  have hvol : volume (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
      Set (SpatialCoordinates d)) = 1 := by
    rw [centeredCube_volume]; simp
  rw [hvol, div_one]
  simp only [Fin.sum_univ_one]
  rfl

theorem aux_lem_load_gag_ne_top {d : ℕ} (hd : 2 ≤ d) (f : DomainL2 (unitNeumannCube d))
    (hf : cubeFractionalL2Seminorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
      (fun _ : Fin 1 => f) < ⊤) :
    aux_lem_load_gag (f : SpatialCoordinates d → ℝ) ≠ ⊤ := by
  intro htop
  rw [aux_lem_load_seminorm_eq, htop, ENNReal.mul_top (by norm_num),
    ENNReal.top_rpow_of_pos (by norm_num)] at hf
  exact lt_irrefl _ hf

theorem aux_lem_load_gag_le_sqNorm {d : ℕ} (hd : 2 ≤ d) (f : DomainL2 (unitNeumannCube d)) :
    Real.sqrt (aux_lem_load_gag (f : SpatialCoordinates d → ℝ)).toReal ≤
      Real.sqrt (4 / 3) *
        Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder f) := by
  rw [← Real.sqrt_mul (by norm_num)]
  apply Real.sqrt_le_sqrt
  unfold cubeFractionalSqNorm cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
  rw [aux_lem_load_seminorm_eq, ← ENNReal.toReal_rpow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num)]
  set G := (aux_lem_load_gag (f : SpatialCoordinates d → ℝ)).toReal
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  have hsq : ((3 / 4 * G) ^ (1 / 2 : ℝ)) ^ 2 = 3 / 4 * G := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  rw [hsq]
  calc G = 4 / 3 * (3 / 4 * G) := by ring
    _ ≤ _ := by
      gcongr
      exact le_add_of_nonneg_right (by positivity)

theorem aux_lem_load_lhs_eq {d : ℕ} (rho : ℝ → ℝ) (p : Fin d → ℝ) (eps : ℝ)
    (hr : Continuous (fun t => eps⁻¹ * rho (t / eps))) {c : ℝ}
    (hc : ∀ t, |eps⁻¹ * rho (t / eps)| ≤ c)
    (v : weakSobolevGraph (unitNeumannCube d)) :
    affineNeumannLoad p (subspaceGradient (weakSobolevGraph (unitNeumannCube d)) v) -
        ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
          faceBump rho p eps x * (v : SobolevData (unitNeumannCube d)).1 x =
      ∑ i : Fin d, p i *
        ((∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
            ((v : SobolevData (unitNeumannCube d)).2 i) x) -
          ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
            (eps⁻¹ * rho ((1 - x i) / eps) - eps⁻¹ * rho (x i / eps)) *
              ((v : SobolevData (unitNeumannCube d)).1) x) := by
  set u : SpatialCoordinates d → ℝ := ((v : SobolevData (unitNeumannCube d)).1 :
    SpatialCoordinates d → ℝ)
  have hu1 : Integrable u (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) :=
    (Lp.memLp _).integrable one_le_two
  have hterm : ∀ i : Fin d, Integrable (fun x : SpatialCoordinates d =>
      (eps⁻¹ * rho ((1 - x i) / eps) - eps⁻¹ * rho (x i / eps)) * u x)
      (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) := by
    intro i
    have hcont : Continuous (fun x : SpatialCoordinates d =>
        eps⁻¹ * rho ((1 - x i) / eps) - eps⁻¹ * rho (x i / eps)) :=
      (hr.comp (continuous_const.sub (continuous_apply i))).sub (hr.comp (continuous_apply i))
    refine hu1.bdd_mul (c := c + c) hcont.aestronglyMeasurable (ae_of_all _ (fun x => ?_))
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (add_le_add (hc _) (hc _))
  have hL : affineNeumannLoad p (subspaceGradient (weakSobolevGraph (unitNeumannCube d)) v) =
      ∑ i : Fin d, p i * ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
        ((v : SobolevData (unitNeumannCube d)).2 i) x := by
    rw [affineNeumannLoad_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← integral_const_mul]
    rfl
  have hF : (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
      faceBump rho p eps x * (v : SobolevData (unitNeumannCube d)).1 x) =
      ∑ i : Fin d, p i * ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
        (eps⁻¹ * rho ((1 - x i) / eps) - eps⁻¹ * rho (x i / eps)) * u x := by
    unfold faceBump
    simp_rw [Finset.sum_mul]
    rw [integral_finset_sum _ (fun i _ => by
      have := (hterm i).const_mul (p i)
      refine this.congr (ae_of_all _ (fun x => ?_))
      simp only; ring)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← integral_const_mul]
    congr 1; ext x; ring
  rw [hL, hF, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem aux_lem_load_bump {rho : ℝ → ℝ} (hrho : ContDiff ℝ ∞ rho) (hrho_nn : ∀ tau, 0 ≤ rho tau)
    (hrho_supp : ∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) (hrho_int : (∫ tau, rho tau) = 1)
    {eps : ℝ} (heps : 0 < eps) :
    Continuous (fun t => eps⁻¹ * rho (t / eps)) ∧ (∀ t, 0 ≤ eps⁻¹ * rho (t / eps)) ∧
      (∀ t, eps⁻¹ * rho (t / eps) ≠ 0 → t ∈ Ioo eps (2 * eps)) ∧
      (∫ t, eps⁻¹ * rho (t / eps)) = 1 ∧ ∃ c, ∀ t, |eps⁻¹ * rho (t / eps)| ≤ c := by
  have hr : Continuous (fun t => eps⁻¹ * rho (t / eps)) :=
    continuous_const.mul (hrho.continuous.comp (continuous_id.div_const _))
  have hrs : ∀ t, eps⁻¹ * rho (t / eps) ≠ 0 → t ∈ Ioo eps (2 * eps) := by
    intro t ht
    have h2 : rho (t / eps) ≠ 0 := right_ne_zero_of_mul ht
    by_contra hno
    apply h2
    apply hrho_supp
    intro hmem
    apply hno
    rw [mem_Ioo, lt_div_iff₀ heps, div_lt_iff₀ heps] at hmem
    exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  refine ⟨hr, fun t => mul_nonneg (inv_nonneg.mpr heps.le) (hrho_nn _), hrs, ?_, ?_⟩
  · rw [integral_const_mul, Measure.integral_comp_div, hrho_int, abs_of_pos heps, smul_eq_mul,
      mul_one, inv_mul_cancel₀ heps.ne']
  · obtain ⟨c, hc⟩ := hr.bounded_above_of_compact_support
      (HasCompactSupport.intro (isCompact_Icc (a := eps) (b := 2 * eps)) (fun t ht => by
        by_contra h; exact ht (Ioo_subset_Icc_self (hrs t h))))
    exact ⟨c, fun t => by rw [← Real.norm_eq_abs]; exact hc t⟩

theorem aux_lem_load_abs_le_one {m : ℕ} {p : Fin m → ℝ} (hp : (∑ i : Fin m, (p i) ^ 2) = 1)
    (i : Fin m) : |p i| ≤ 1 := by
  have : p i ^ 2 ≤ 1 := by
    rw [← hp]
    exact Finset.single_le_sum (f := fun j => p j ^ 2) (fun j _ => sq_nonneg (p j))
      (Finset.mem_univ i)
  exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)

/-- The load estimate with the Gagliardo double integral on the right. -/
theorem aux_lem_load_core {n : ℕ} (hn : 1 ≤ n) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y, aux_lem_load_eta y ≤ M) {rho : ℝ → ℝ} (hrho : ContDiff ℝ ∞ rho)
    (hrho_nn : ∀ tau, 0 ≤ rho tau) (hrho_supp : ∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0)
    (hrho_int : (∫ tau, rho tau) = 1) {p : Fin (n + 1) → ℝ}
    (hp : (∑ i : Fin (n + 1), (p i) ^ 2) = 1) {eps : ℝ} (heps : 0 < eps) (heps8 : eps < 1 / 8)
    (v : weakSobolevGraph (unitNeumannCube (n + 1)))
    (hG : aux_lem_load_gag ((v : SobolevData (unitNeumannCube (n + 1))).1 :
      SpatialCoordinates (n + 1) → ℝ) ≠ ⊤) :
    |affineNeumannLoad p
          (subspaceGradient (weakSobolevGraph (unitNeumannCube (n + 1))) v) -
        ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
          faceBump rho p eps x * (v : SobolevData (unitNeumannCube (n + 1))).1 x| ≤
      ((n : ℝ) + 1) * (2 * aux_lem_load_CF (n + 1) M * (2 : ℝ) ^ (1 / 4 : ℝ)) *
        eps ^ (1 / 4 : ℝ) *
        Real.sqrt (aux_lem_load_gag ((v : SobolevData (unitNeumannCube (n + 1))).1 :
          SpatialCoordinates (n + 1) → ℝ)).toReal := by
  obtain ⟨hr, hrnn, hrs, hr1, c, hc⟩ :=
    aux_lem_load_bump hrho hrho_nn hrho_supp hrho_int heps
  rw [aux_lem_load_lhs_eq rho p eps hr hc v]
  have hterm : ∀ i : Fin (n + 1), |p i *
      ((∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
          ((v : SobolevData (unitNeumannCube (n + 1))).2 i) x) -
        ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
          (eps⁻¹ * rho ((1 - x i) / eps) - eps⁻¹ * rho (x i / eps)) *
            ((v : SobolevData (unitNeumannCube (n + 1))).1) x)| ≤
      2 * aux_lem_load_CF (n + 1) M * (2 * eps) ^ (1 / 4 : ℝ) *
        Real.sqrt (aux_lem_load_gag ((v : SobolevData (unitNeumannCube (n + 1))).1 :
          SpatialCoordinates (n + 1) → ℝ)).toReal := by
    intro i
    have hface := aux_lem_load_face hn i v hG hM0 hM heps heps8 hr hrnn hrs hr1
    rw [abs_mul]
    exact (mul_le_mul (aux_lem_load_abs_le_one hp i) hface (abs_nonneg _) zero_le_one).trans_eq
      (one_mul _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun i _ => hterm i)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Real.mul_rpow (by norm_num) heps.le]
  push_cast
  ring_nf
  exact le_rfl

theorem aux_lem_load_final {n : ℕ} (hd : 2 ≤ n + 1)
    (S : SubdiffusiveProcess.Lane4.SobolevFoundationalInput (n + 1) hd) (hn : 1 ≤ n)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ y, aux_lem_load_eta y ≤ M)
    (hCF : 0 ≤ aux_lem_load_CF (n + 1) M) {rho : ℝ → ℝ} (hrho : ContDiff ℝ ∞ rho)
    (hrho_nn : ∀ tau, 0 ≤ rho tau) (hrho_supp : ∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0)
    (hrho_int : (∫ tau, rho tau) = 1) {p : Fin (n + 1) → ℝ}
    (hp : (∑ i : Fin (n + 1), (p i) ^ 2) = 1) {eps : ℝ} (heps : 0 < eps) (heps8 : eps < 1 / 8)
    (v : weakSobolevGraph (unitNeumannCube (n + 1))) :
    |affineNeumannLoad p
          (subspaceGradient (weakSobolevGraph (unitNeumannCube (n + 1))) v) -
        ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
          faceBump rho p eps x * (v : SobolevData (unitNeumannCube (n + 1))).1 x| ≤
      (((n : ℝ) + 1) * (2 * aux_lem_load_CF (n + 1) M * (2 : ℝ) ^ (1 / 4 : ℝ)) *
        Real.sqrt (4 / 3) + 1) * eps ^ (1 / 4 : ℝ) *
        Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
          threeQuarterOrder
          ((v : SobolevData (unitNeumannCube (n + 1))).1 -
            domainConstantL2 (Ω := unitNeumannCube (n + 1))
              (domainMean ((v : SobolevData (unitNeumannCube (n + 1))).1)))) := by
  have hfin := S.h1_fractional_finite (fun _ => (1 / 2 : ℝ)) 1 one_pos v
  have hG := aux_lem_load_gag_ne_top hd (v : SobolevData (unitNeumannCube (n + 1))).1 hfin
  have hcore := aux_lem_load_core hn hM0 hM hrho hrho_nn hrho_supp hrho_int hp heps heps8 v hG
  have hw : (((v : SobolevData (unitNeumannCube (n + 1))).1 -
      domainConstantL2 (Ω := unitNeumannCube (n + 1))
        (domainMean ((v : SobolevData (unitNeumannCube (n + 1))).1)) :
          DomainL2 (unitNeumannCube (n + 1))) : SpatialCoordinates (n + 1) → ℝ) =ᵐ[volume.restrict
      (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1)))]
      fun x => ((v : SobolevData (unitNeumannCube (n + 1))).1 : SpatialCoordinates (n + 1) → ℝ) x -
        domainMean ((v : SobolevData (unitNeumannCube (n + 1))).1) := by
    filter_upwards [Lp.coeFn_sub (v : SobolevData (unitNeumannCube (n + 1))).1
        (domainConstantL2 (Ω := unitNeumannCube (n + 1))
          (domainMean ((v : SobolevData (unitNeumannCube (n + 1))).1))),
      domainConstantL2_coeFn (Ω := unitNeumannCube (n + 1))
        (domainMean ((v : SobolevData (unitNeumannCube (n + 1))).1))] with x h1 h2
    rw [h1, Pi.sub_apply, h2]
  have hGw := aux_lem_load_gag_congr hw
  have hRHS := aux_lem_load_gag_le_sqNorm hd ((v : SobolevData (unitNeumannCube (n + 1))).1 -
    domainConstantL2 (Ω := unitNeumannCube (n + 1))
      (domainMean ((v : SobolevData (unitNeumannCube (n + 1))).1)))
  rw [hGw] at hRHS
  have hepsq : 0 ≤ eps ^ (1 / 4 : ℝ) := Real.rpow_nonneg heps.le _
  have hN0 := Real.sqrt_nonneg (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
    threeQuarterOrder ((v : SobolevData (unitNeumannCube (n + 1))).1 -
      domainConstantL2 (Ω := unitNeumannCube (n + 1))
        (domainMean ((v : SobolevData (unitNeumannCube (n + 1))).1))))
  have hK : 0 ≤ ((n : ℝ) + 1) * (2 * aux_lem_load_CF (n + 1) M * (2 : ℝ) ^ (1 / 4 : ℝ)) *
      eps ^ (1 / 4 : ℝ) := by positivity
  refine hcore.trans ?_
  calc _ ≤ ((n : ℝ) + 1) * (2 * aux_lem_load_CF (n + 1) M * (2 : ℝ) ^ (1 / 4 : ℝ)) *
        eps ^ (1 / 4 : ℝ) * (Real.sqrt (4 / 3) * Real.sqrt (cubeFractionalSqNorm hd
          (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
          ((v : SobolevData (unitNeumannCube (n + 1))).1 -
            domainConstantL2 (Ω := unitNeumannCube (n + 1))
              (domainMean ((v : SobolevData (unitNeumannCube (n + 1))).1))))) :=
        mul_le_mul_of_nonneg_left hRHS hK
    _ ≤ _ := by
        have h43 : 0 ≤ Real.sqrt (4 / 3) := Real.sqrt_nonneg _
        nlinarith [mul_nonneg hepsq hN0]

end AuxLemLoad



theorem lem_load :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    (_S : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd),
  ∃ C : ℝ, 0 < C ∧
    ∀ (rho : ℝ → ℝ), ContDiff ℝ ∞ rho → (∀ tau, 0 ≤ rho tau) →
      (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) → (∫ tau, rho tau) = 1 →
    ∀ (p : Fin d → ℝ), (∑ i : Fin d, (p i) ^ 2) = 1 →
    ∀ (eps : ℝ), 0 < eps → eps < 1 / 8 →
    ∀ (v : weakSobolevGraph (unitNeumannCube d)),
      |affineNeumannLoad p
            (subspaceGradient (weakSobolevGraph (unitNeumannCube d)) v) -
          ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
            faceBump rho p eps x * (v : SobolevData (unitNeumannCube d)).1 x| ≤
        C * eps ^ (1 / 4 : ℝ) *
          Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
            threeQuarterOrder
            ((v : SobolevData (unitNeumannCube d)).1 -
              domainConstantL2 (Ω := unitNeumannCube d)
                (domainMean ((v : SobolevData (unitNeumannCube d)).1)))) := by
  intro d hd S
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  obtain ⟨M, hM0, hM⟩ := aux_lem_load_eta_bdd
  have hCF : 0 ≤ aux_lem_load_CF (n + 1) M := by
    unfold aux_lem_load_CF
    have := aux_lem_load_q_lt_one
    have := aux_lem_load_cst_nonneg (n + 1) 1
    have := aux_lem_load_cst_nonneg (n + 1) 2
    have : 0 < 1 - aux_lem_load_q := by linarith
    positivity
  have hC0 : 0 ≤ ((n : ℝ) + 1) * (2 * aux_lem_load_CF (n + 1) M * (2 : ℝ) ^ (1 / 4 : ℝ)) *
      Real.sqrt (4 / 3) := by positivity
  refine ⟨((n : ℝ) + 1) * (2 * aux_lem_load_CF (n + 1) M * (2 : ℝ) ^ (1 / 4 : ℝ)) *
      Real.sqrt (4 / 3) + 1, by linarith, ?_⟩
  intro rho hrho hrho_nn hrho_supp hrho_int p hp eps heps heps8 v
  exact aux_lem_load_final hd S (by omega) hM0 hM hCF hrho hrho_nn hrho_supp hrho_int hp
    heps heps8 v

end Paper
