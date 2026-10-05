module

public import Mathlib
public import Homogenization.Sobolev.W1p.ZeroExtensionGraph
public import Homogenization.Sobolev.H1.Algebra.H10Function
public import Homogenization.Sobolev.H1.BasicLemmas

@[expose] public section

/-! # Cell patching for harmonic cutoffs

Deterministic ingredients ported from the proved `tight_static_cut` assembly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

section
open MeasureTheory Metric
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Static

variable {d : ℕ}

/-- Centre of the grid aux_hcut_cell `k` of side `h`. -/
def aux_hcut_cc (h : ℝ) (k : Fin d → ℤ) : Fin d → ℝ := fun i => h * ((k i : ℝ) + 1 / 2)

/-- The open grid aux_hcut_cell `k` of side `h` (a sup-norm ball). -/
def aux_hcut_cell (h : ℝ) (k : Fin d → ℤ) : Set (Fin d → ℝ) := ball (aux_hcut_cc h k) (h / 2)

lemma aux_hcut_mem_cell_iff {h : ℝ} (hh : 0 < h) {k : Fin d → ℤ} {x : Fin d → ℝ} :
    x ∈ aux_hcut_cell h k ↔ ∀ i, |x i - aux_hcut_cc h k i| < h / 2 := by
  simp only [aux_hcut_cell, mem_ball, dist_pi_lt_iff (half_pos hh), Real.dist_eq]

lemma aux_hcut_cell_disjoint {h : ℝ} (hh : 0 < h) {k k' : Fin d → ℤ} (hkk : k ≠ k') :
    Disjoint (aux_hcut_cell h k) (aux_hcut_cell h k') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [aux_hcut_mem_cell_iff hh] at hx hx'
  apply hkk
  funext i
  have h1 := hx i
  have h2 := hx' i
  simp only [aux_hcut_cc] at h1 h2
  have : |(k i : ℝ) - k' i| < 1 := by
    have e : (k i : ℝ) - k' i = ((x i - h * (k' i + 1 / 2)) - (x i - h * (k i + 1 / 2))) / h := by
      field_simp; ring
    rw [e, abs_div, abs_of_pos hh, div_lt_one hh]
    calc |(x i - h * ((k' i : ℝ) + 1 / 2)) - (x i - h * ((k i : ℝ) + 1 / 2))|
        ≤ |x i - h * ((k' i : ℝ) + 1 / 2)| + |x i - h * ((k i : ℝ) + 1 / 2)| := abs_sub _ _
      _ < h / 2 + h / 2 := add_lt_add h2 h1
      _ = h := by ring
  have : |((k i - k' i : ℤ) : ℝ)| < 1 := by push_cast; exact this
  rw [← Int.cast_abs] at this
  have h3 : |k i - k' i| < 1 := by exact_mod_cast this
  rw [abs_lt] at h3
  omega

lemma aux_hcut_floor_bounds {h t : ℝ} (hh : 0 < h) :
    h * (⌊t / h⌋ : ℝ) ≤ t ∧ t < h * ((⌊t / h⌋ : ℝ) + 1) := by
  have h1 := Int.floor_le (t / h)
  have h2 := Int.lt_floor_add_one (t / h)
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hh.le
    rwa [mul_div_cancel₀ _ hh.ne'] at this
  · have := mul_lt_mul_of_pos_left h2 hh
    rwa [mul_div_cancel₀ _ hh.ne'] at this

/-- Closed grid cells cover everything. -/
lemma aux_hcut_exists_closedCell {h : ℝ} (hh : 0 < h) (x : Fin d → ℝ) :
    ∃ k : Fin d → ℤ, x ∈ closedBall (aux_hcut_cc h k) (h / 2) := by
  refine ⟨fun i => ⌊x i / h⌋, ?_⟩
  rw [mem_closedBall, dist_pi_le_iff (half_pos hh).le]
  intro i
  obtain ⟨h1, h2⟩ := aux_hcut_floor_bounds (t := x i) hh
  rw [Real.dist_eq, abs_le]
  simp only [aux_hcut_cc]
  constructor <;> nlinarith

/-- Almost every point lies in an open grid aux_hcut_cell. -/
lemma aux_hcut_ae_mem_cell {h : ℝ} (hh : 0 < h) :
    ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), ∃ k : Fin d → ℤ, x ∈ aux_hcut_cell h k := by
  have hnull : volume (⋃ i : Fin d, ⋃ m : ℤ, {x : Fin d → ℝ | x i = h * m}) = 0 := by
    refine measure_iUnion_null fun i => measure_iUnion_null fun m => ?_
    have : {x : Fin d → ℝ | x i = h * m} = Function.eval i ⁻¹' ({h * (m : ℝ)} : Set ℝ) := rfl
    rw [this, volume_pi]
    exact Measure.pi_eval_preimage_null (fun _ => (volume : Measure ℝ)) Real.volume_singleton
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) hnull
  simp only [Set.mem_ofPred_eq, not_exists] at hx
  by_contra hcon
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists] at hcon
  apply hx (fun i => ⌊x i / h⌋)
  rw [aux_hcut_mem_cell_iff hh]
  intro i
  obtain ⟨h1, h2⟩ := aux_hcut_floor_bounds (t := x i) hh
  have h3 : x i ≠ h * (⌊x i / h⌋ : ℝ) := fun he => hcon i ⌊x i / h⌋ he
  have h4 : x i ≠ h * ((⌊x i / h⌋ + 1 : ℤ) : ℝ) := fun he => hcon i (⌊x i / h⌋ + 1) he
  push_cast at h4
  have h1' : h * (⌊x i / h⌋ : ℝ) < x i := lt_of_le_of_ne h1 (Ne.symm h3)
  simp only [aux_hcut_cc]
  rw [abs_lt]
  constructor <;> nlinarith

lemma aux_hcut_cell_subset_ball {h : ℝ} {k : Fin d → ℤ} {x : Fin d → ℝ} {r : ℝ}
    (hk : (aux_hcut_cell h k ∩ ball x r).Nonempty) : aux_hcut_cell h k ⊆ ball x (r + h) := by
  obtain ⟨y, hy1, hy2⟩ := hk
  intro z hz
  simp only [aux_hcut_cell, mem_ball] at hy1 hz hy2 ⊢
  calc dist z x ≤ dist z (aux_hcut_cc h k) + dist (aux_hcut_cc h k) y + dist y x := dist_triangle4 _ _ _ _
    _ < h / 2 + h / 2 + r := by rw [dist_comm (aux_hcut_cc h k) y]; gcongr
    _ = r + h := by ring

lemma aux_hcut_measurableSet_cell (h : ℝ) (k : Fin d → ℤ) : MeasurableSet (aux_hcut_cell h k) :=
  measurableSet_ball

lemma aux_hcut_volume_cell {h : ℝ} (hh : 0 < h) (k : Fin d → ℤ) :
    volume (aux_hcut_cell h k) = ENNReal.ofReal h ^ d := by
  rw [aux_hcut_cell, Real.volume_pi_ball _ (half_pos hh), Fintype.card_fin, ← ENNReal.ofReal_pow hh.le]
  congr 2; ring

/-- Counting cells meeting a ball, by volume. -/
lemma aux_hcut_card_mul_le {h : ℝ} (hh : 0 < h) (S : Finset (Fin d → ℤ)) {x : Fin d → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hS : ∀ k ∈ S, (aux_hcut_cell h k ∩ ball x r).Nonempty) :
    (S.card : ℝ) * h ^ d ≤ (2 * (r + h)) ^ d := by
  have hdisj : Set.PairwiseDisjoint (S : Set (Fin d → ℤ)) (aux_hcut_cell h) :=
    fun k _ k' _ hkk => aux_hcut_cell_disjoint hh hkk
  have hsub : (⋃ k ∈ S, aux_hcut_cell h k) ⊆ ball x (r + h) :=
    Set.iUnion₂_subset fun k hk => aux_hcut_cell_subset_ball (hS k hk)
  have hvol := measure_mono (μ := (volume : Measure (Fin d → ℝ))) hsub
  rw [measure_biUnion_finset hdisj (fun k _ => aux_hcut_measurableSet_cell h k),
    Real.volume_pi_ball x (by linarith)] at hvol
  simp only [aux_hcut_volume_cell hh, Finset.sum_const, nsmul_eq_mul] at hvol
  rw [← ENNReal.ofReal_pow hh.le, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at hvol
  have h2 : (0 : ℝ) ≤ (2 * (r + h)) ^ d := by positivity
  rw [Fintype.card_fin] at hvol
  exact (ENNReal.ofReal_le_ofReal_iff h2).1 hvol

end SubdiffusiveProcess.Static
end
end


section
open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Static
open Homogenization

/-- A smooth compactly supported function with support in `U`, as an `H¹₀(U)` function. -/
def aux_hcut_h10OfSmooth {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    H10Function U where
  toH1Function := H1Function.ofContDiff hU (hf.of_le (by simp)) hfc
  approx := fun _ => f
  approx_smooth := fun _ => hf
  approx_hasCompactSupport := fun _ => hfc
  approx_support_subset := fun _ => hfU
  tendsto_approx := by
    have : (fun _ : ℕ => eLpNorm (fun x => f x - f x) 2 (volume.restrict U)) = fun _ => 0 := by
      funext n; simp
    simp [H1Function.ofContDiff]
  tendsto_approx_grad := by
    intro i
    simp [H1Function.ofContDiff]

@[simp] lemma aux_hcut_h10OfSmooth_toFun {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    (aux_hcut_h10OfSmooth hU hf hfc hfU).toH1Function.toFun = f := rfl

@[simp] lemma aux_hcut_h10OfSmooth_grad {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    (aux_hcut_h10OfSmooth hU hf hfc hfU).toH1Function.grad = fun x i => (fderiv ℝ f x) (basisVec i) := rfl

/-- Replace `toFun` by an a.e.-equal function (same gradient and approximants). -/
def aux_hcut_h10CongrAe {d : ℕ} {U : Set (Vec d)} (v : H10Function U) (g : Vec d → ℝ)
    (hg : g =ᵐ[volume.restrict U] v.toH1Function.toFun) : H10Function U where
  toH1Function :=
    { toFun := g
      grad := v.toH1Function.grad
      memL2 := v.toH1Function.memL2.ae_eq hg.symm
      gradMemL2 := v.toH1Function.gradMemL2
      hasWeakGradient := by
        intro i φ h1 h2 h3
        rw [← v.toH1Function.hasWeakGradient i φ h1 h2 h3]
        exact integral_congr_ae (hg.mono fun x hx => by simp only [hx]) }
  approx := v.approx
  approx_smooth := v.approx_smooth
  approx_hasCompactSupport := v.approx_hasCompactSupport
  approx_support_subset := v.approx_support_subset
  tendsto_approx := by
    refine v.tendsto_approx.congr fun n => ?_
    exact eLpNorm_congr_ae (hg.mono fun x hx => by simp only [hx])
  tendsto_approx_grad := v.tendsto_approx_grad

@[simp] lemma aux_hcut_h10CongrAe_toFun {d : ℕ} {U : Set (Vec d)} (v : H10Function U) (g : Vec d → ℝ)
    (hg : g =ᵐ[volume.restrict U] v.toH1Function.toFun) :
    (aux_hcut_h10CongrAe v g hg).toH1Function.toFun = g := rfl

@[simp] lemma aux_hcut_h10CongrAe_grad {d : ℕ} {U : Set (Vec d)} (v : H10Function U) (g : Vec d → ℝ)
    (hg : g =ᵐ[volume.restrict U] v.toH1Function.toFun) :
    (aux_hcut_h10CongrAe v g hg).toH1Function.grad = v.toH1Function.grad := rfl

/-- Sum over a list of `H¹₀` functions. -/
def aux_hcut_h10ListSum {d : ℕ} {U : Set (Vec d)} : List (H10Function U) → H10Function U
  | [] => 0
  | v :: l => v + aux_hcut_h10ListSum l

lemma aux_hcut_h10ListSum_toFun {d : ℕ} {U : Set (Vec d)} (l : List (H10Function U)) (x : Vec d) :
    (aux_hcut_h10ListSum l).toH1Function.toFun x = (l.map fun v => v.toH1Function.toFun x).sum := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    simp only [aux_hcut_h10ListSum, List.map_cons, List.sum_cons]
    rw [← ih]; rfl

lemma aux_hcut_h10ListSum_grad {d : ℕ} {U : Set (Vec d)} (l : List (H10Function U)) (x : Vec d) :
    (aux_hcut_h10ListSum l).toH1Function.grad x = (l.map fun v => v.toH1Function.grad x).sum := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    simp only [aux_hcut_h10ListSum, List.map_cons, List.sum_cons]
    rw [← ih]; rfl

end SubdiffusiveProcess.Static
end
end


section
open MeasureTheory Metric Filter Topology
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Static
open Homogenization

variable {d : ℕ}

/-- The closed transition annulus of `f`. -/
def aux_hcut_Ann (R1 R2 h : ℝ) : Set (Fin d → ℝ) := {x | R1 + h ≤ ‖x‖ ∧ ‖x‖ ≤ R2 - 2 * h}

/-- Transition cells: closed aux_hcut_cell meets the annulus. -/
def aux_hcut_IsTrans (h R1 R2 : ℝ) (k : Fin d → ℤ) : Prop :=
  (closedBall (aux_hcut_cc h k) (h / 2) ∩ aux_hcut_Ann R1 R2 h).Nonempty

/-- The gradient vector of a smooth function. -/
def aux_hcut_gradVec (f : (Fin d → ℝ) → ℝ) (z : Fin d → ℝ) : Fin d → ℝ :=
  fun i => fderiv ℝ f z (basisVec i)

lemma aux_hcut_gradVec_eq_zero_of_eventuallyEq_const {f : (Fin d → ℝ) → ℝ} {z : Fin d → ℝ} {c : ℝ}
    (h : f =ᶠ[𝓝 z] fun _ => c) : aux_hcut_gradVec f z = 0 := by
  funext i
  simp only [aux_hcut_gradVec, h.fderiv_eq]
  simp

lemma aux_hcut_gradVec_eq_zero_off_Ann {f : (Fin d → ℝ) → ℝ} {R1 R2 h : ℝ}
    (hf1 : ∀ x, ‖x‖ ≤ R1 + h → f x = 1) (hf0 : ∀ x, R2 - 2 * h ≤ ‖x‖ → f x = 0)
    {z : Fin d → ℝ} (hz : z ∉ aux_hcut_Ann R1 R2 h) : aux_hcut_gradVec f z = 0 := by
  simp only [aux_hcut_Ann, Set.mem_ofPred_eq, not_and_or, not_le] at hz
  rcases hz with hz | hz
  · refine aux_hcut_gradVec_eq_zero_of_eventuallyEq_const (c := 1) ?_
    have : {x : Fin d → ℝ | ‖x‖ < R1 + h} ∈ 𝓝 z :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds hz
    filter_upwards [this] with x hx using hf1 x hx.le
  · refine aux_hcut_gradVec_eq_zero_of_eventuallyEq_const (c := 0) ?_
    have : {x : Fin d → ℝ | R2 - 2 * h < ‖x‖} ∈ 𝓝 z :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hz
    filter_upwards [this] with x hx using hf0 x hx.le

lemma aux_hcut_trans_geom {R1 R2 h : ℝ} {k : Fin d → ℤ} (hk : aux_hcut_IsTrans h R1 R2 k)
    {z : Fin d → ℝ} (hz : z ∈ closedBall (aux_hcut_cc h k) (h / 2)) : R1 ≤ ‖z‖ ∧ ‖z‖ ≤ R2 - h := by
  obtain ⟨a, ha1, ha2⟩ := hk
  have hza : dist z a ≤ h := by
    calc dist z a ≤ dist z (aux_hcut_cc h k) + dist (aux_hcut_cc h k) a := dist_triangle _ _ _
      _ ≤ h / 2 + h / 2 := by rw [dist_comm (aux_hcut_cc h k) a]; exact add_le_add hz ha1
      _ = h := by ring
  have h1 : ‖a‖ ≤ ‖z‖ + dist z a := by
    rw [dist_eq_norm]; calc ‖a‖ = ‖z - (z - a)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖z‖ + ‖z - a‖ := norm_sub_le _ _
  have h2 : ‖z‖ ≤ ‖a‖ + dist z a := by
    rw [dist_eq_norm]; calc ‖z‖ = ‖a + (z - a)‖ := by rw [add_sub_cancel]
      _ ≤ ‖a‖ + ‖z - a‖ := norm_add_le _ _
  obtain ⟨ha3, ha4⟩ := ha2
  constructor <;> linarith

lemma aux_hcut_trans_cell_subset {R1 R2 h : ℝ} (hh : 0 < h) {k : Fin d → ℤ} (hk : aux_hcut_IsTrans h R1 R2 k) :
    closedBall (aux_hcut_cc h k) (h / 2) ⊆ ball (0 : Fin d → ℝ) R2 := by
  intro z hz
  rw [mem_ball_zero_iff]
  have := (aux_hcut_trans_geom hk hz).2
  linarith

lemma aux_hcut_trans_cell_disjoint_inner {R1 R2 h : ℝ} {k : Fin d → ℤ} (hk : aux_hcut_IsTrans h R1 R2 k)
    {z : Fin d → ℝ} (hz : z ∈ ball (0 : Fin d → ℝ) R1) : z ∉ closedBall (aux_hcut_cc h k) (h / 2) := by
  intro hzc
  have := (aux_hcut_trans_geom hk hzc).1
  rw [mem_ball_zero_iff] at hz
  linarith

lemma aux_hcut_trans_finite {R1 R2 h : ℝ} (hh : 0 < h) : {k : Fin d → ℤ | aux_hcut_IsTrans h R1 R2 k}.Finite := by
  set N : ℕ := ⌈|R2| / h⌉₊ + 1
  refine (Set.Finite.pi (t := fun _ : Fin d => (Finset.Icc (-(N : ℤ)) N : Set ℤ))
    (fun _ => Finset.finite_toSet _)).subset ?_
  intro k hk
  simp only [Set.mem_pi, Set.mem_univ, Finset.coe_Icc, Set.mem_Icc, true_implies]
  intro i
  have hc := (aux_hcut_trans_geom hk (mem_closedBall_self (by positivity : 0 ≤ h / 2)))
  have hci : |aux_hcut_cc h k i| ≤ ‖aux_hcut_cc h k‖ := by
    have := norm_le_pi_norm (aux_hcut_cc h k) i; rwa [Real.norm_eq_abs] at this
  simp only [aux_hcut_cc] at hci
  have hR : R2 - h ≤ |R2| := by linarith [le_abs_self R2]
  have h1 : |h * ((k i : ℝ) + 1 / 2)| ≤ |R2| := by linarith [hc.2]
  rw [abs_mul, abs_of_pos hh] at h1
  have h2 : |(k i : ℝ) + 1 / 2| ≤ |R2| / h := by rw [le_div_iff₀ hh]; linarith
  have hceil : |R2| / h ≤ (⌈|R2| / h⌉₊ : ℝ) := Nat.le_ceil _
  have h3 : |(k i : ℝ)| ≤ (N : ℝ) := by
    have e : ((k i : ℝ) + 1 / 2) - 1 / 2 = (k i : ℝ) := by ring
    have h4 := abs_sub ((k i : ℝ) + 1 / 2) (1 / 2)
    rw [e] at h4
    have h5 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    have hN : (N : ℝ) = (⌈|R2| / h⌉₊ : ℝ) + 1 := by push_cast [N]; ring
    linarith
  rw [abs_le] at h3
  exact ⟨by exact_mod_cast h3.1, by exact_mod_cast h3.2⟩

end SubdiffusiveProcess.Static
end
end


section
open MeasureTheory Metric Filter Topology
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Static
open Homogenization

variable {d : ℕ}

lemma aux_hcut_sum_single_cell {M : Type*} [AddCommMonoid M] {h : ℝ} (hh : 0 < h) (T : Finset (Fin d → ℤ))
    (G : (Fin d → ℤ) → (Fin d → ℝ) → M) (hG : ∀ k ∈ T, ∀ x, x ∉ aux_hcut_cell h k → G k x = 0)
    {k0 : Fin d → ℤ} (hk0 : k0 ∈ T) {x : Fin d → ℝ} (hx : x ∈ aux_hcut_cell h k0) :
    ∑ k ∈ T, G k x = G k0 x := by
  refine Finset.sum_eq_single_of_mem k0 hk0 fun k hk hne => hG k hk x fun hxk => ?_
  exact Set.disjoint_left.1 (aux_hcut_cell_disjoint hh hne) hxk hx

lemma aux_hcut_sum_no_cell {M : Type*} [AddCommMonoid M] {h : ℝ} (T : Finset (Fin d → ℤ))
    (G : (Fin d → ℤ) → (Fin d → ℝ) → M) (hG : ∀ k ∈ T, ∀ x, x ∉ aux_hcut_cell h k → G k x = 0)
    {x : Fin d → ℝ} (hx : ∀ k ∈ T, x ∉ aux_hcut_cell h k) : ∑ k ∈ T, G k x = 0 :=
  Finset.sum_eq_zero fun k hk => hG k hk x (hx k hk)

/-- The raw interpolant `f + Σ_{k∈T} E_k`. -/
def aux_hcut_rawChi {R2 : ℝ} (F : H10Function (ball (0 : Fin d → ℝ) R2)) (T : Finset (Fin d → ℤ))
    (E : (Fin d → ℤ) → H10Function (ball (0 : Fin d → ℝ) R2)) :
    H10Function (ball (0 : Fin d → ℝ) R2) :=
  F + aux_hcut_h10ListSum (T.toList.map E)

lemma aux_hcut_rawChi_toFun {R2 : ℝ} (F : H10Function (ball (0 : Fin d → ℝ) R2)) (T : Finset (Fin d → ℤ))
    (E : (Fin d → ℤ) → H10Function (ball (0 : Fin d → ℝ) R2)) (x : Fin d → ℝ) :
    (aux_hcut_rawChi F T E).toH1Function.toFun x =
      F.toH1Function.toFun x + ∑ k ∈ T, (E k).toH1Function.toFun x := by
  show F.toH1Function.toFun x + (aux_hcut_h10ListSum (T.toList.map E)).toH1Function.toFun x = _
  rw [aux_hcut_h10ListSum_toFun, List.map_map]
  congr 1
  exact Finset.sum_map_toList T _

lemma aux_hcut_rawChi_grad {R2 : ℝ} (F : H10Function (ball (0 : Fin d → ℝ) R2)) (T : Finset (Fin d → ℤ))
    (E : (Fin d → ℤ) → H10Function (ball (0 : Fin d → ℝ) R2)) (x : Fin d → ℝ) :
    (aux_hcut_rawChi F T E).toH1Function.grad x =
      F.toH1Function.grad x + ∑ k ∈ T, (E k).toH1Function.grad x := by
  show F.toH1Function.grad x + (aux_hcut_h10ListSum (T.toList.map E)).toH1Function.grad x = _
  rw [aux_hcut_h10ListSum_grad, List.map_map]
  congr 1
  exact Finset.sum_map_toList T _

end SubdiffusiveProcess.Static
end
end
