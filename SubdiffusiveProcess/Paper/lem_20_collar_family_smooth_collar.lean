module

public import SubdiffusiveProcess.Paper.lem_cutoffs
public import SubdiffusiveProcess.VariationalResponses.KilledTest

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_lem_20_collar_family_smooth_collar_compl_nonempty
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) :
    ((centeredCube z R hR : Set (SpatialCoordinates d))ᶜ).Nonempty := by
  have hd0 : 0 < d := lt_of_lt_of_le Nat.zero_lt_two hd
  let i : Fin d := ⟨0, hd0⟩
  let y : SpatialCoordinates d := Function.update z i (z i + R)
  refine ⟨y, ?_⟩
  intro hy
  rw [centeredCube_eq_pi z hR] at hy
  have hyi := hy i (Set.mem_univ i)
  simp [y] at hyi
  linarith

theorem aux_lem_20_collar_family_smooth_collar_coordinate_dist_le
    (d : ℕ) (x y : SpatialCoordinates d) (i : Fin d) :
    dist (x i) (y i) ≤ dist x y := by
  simpa only [dist_eq_norm, Pi.sub_apply] using norm_le_pi_norm (x - y) i

theorem aux_lem_20_collar_family_smooth_collar_dist_update_of_le
    (d : ℕ) (x : SpatialCoordinates d) (a : ℝ) (i : Fin d)
    (hxa : a ≤ x i) :
    dist x (Function.update x i a) = x i - a := by
  have hnonneg : 0 ≤ x i - a := sub_nonneg.mpr hxa
  apply le_antisymm
  · rw [dist_eq_norm, pi_norm_le_iff_of_nonneg hnonneg]
    intro j
    by_cases hji : j = i
    · subst j
      simp [Function.update, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    · have hu : Function.update x i a j = x j := by
        simp [Function.update, hji]
      rw [Pi.sub_apply, hu, sub_self, norm_zero]
      exact hnonneg
  · have hi := norm_le_pi_norm (x - Function.update x i a) i
    rw [Pi.sub_apply] at hi
    have hui : Function.update x i a i = a := by simp [Function.update]
    rw [hui, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hi
    simpa only [dist_eq_norm, neg_sub] using hi

theorem aux_lem_20_collar_family_smooth_collar_dist_update_of_ge
    (d : ℕ) (x : SpatialCoordinates d) (a : ℝ) (i : Fin d)
    (hxa : x i ≤ a) :
    dist x (Function.update x i a) = a - x i := by
  have hnonneg : 0 ≤ a - x i := sub_nonneg.mpr hxa
  apply le_antisymm
  · rw [dist_eq_norm, pi_norm_le_iff_of_nonneg hnonneg]
    intro j
    by_cases hji : j = i
    · subst j
      have hnonpos : x i - a ≤ 0 := sub_nonpos.mpr hxa
      simp [Function.update, Real.norm_eq_abs, abs_of_nonpos hnonpos]
    · have hu : Function.update x i a j = x j := by
        simp [Function.update, hji]
      rw [Pi.sub_apply, hu, sub_self, norm_zero]
      exact hnonneg
  · have hi := norm_le_pi_norm (x - Function.update x i a) i
    rw [Pi.sub_apply] at hi
    have hui : Function.update x i a i = a := by simp [Function.update]
    have hnonpos : x i - a ≤ 0 := sub_nonpos.mpr hxa
    rw [hui, Real.norm_eq_abs, abs_of_nonpos hnonpos] at hi
    simpa only [dist_eq_norm, neg_sub] using hi

theorem aux_lem_20_collar_family_smooth_collar_margins_ge
    (d : ℕ)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (x : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
    (h : s ≤ Metric.infDist x
      (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ) :
    ∀ i : Fin d,
      s ≤ x i - (z i - R / 2) ∧ s ≤ (z i + R / 2) - x i := by
  have hxQ : x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) := by
    by_contra hx
    have hx' : x ∈ (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ := hx
    have hz := Metric.infDist_zero_of_mem hx'
    linarith
  rw [centeredCube_eq_pi z hR] at hxQ
  intro i
  have hxi : z i - R / 2 < x i ∧ x i < z i + R / 2 := by
    simpa only [mem_Ioo] using hxQ i (Set.mem_univ i)
  constructor
  · let y : SpatialCoordinates d := Function.update x i (z i - R / 2)
    have hy : y ∈ (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ := by
      intro hyQ
      rw [centeredCube_eq_pi z hR] at hyQ
      have hyi := hyQ i (Set.mem_univ i)
      have hbad : z i - R / 2 < z i - R / 2 := by
        simpa [y] using hyi.1
      exact (lt_irrefl _ hbad)
    have hdist := Metric.infDist_le_dist_of_mem (x := x)
      (s := (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ) hy
    have hle : s ≤ dist x y := h.trans hdist
    rw [aux_lem_20_collar_family_smooth_collar_dist_update_of_le d x
      (z i - R / 2) i hxi.1.le] at hle
    exact hle
  · let y : SpatialCoordinates d := Function.update x i (z i + R / 2)
    have hy : y ∈ (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ := by
      intro hyQ
      rw [centeredCube_eq_pi z hR] at hyQ
      have hyi := hyQ i (Set.mem_univ i)
      have hbad : z i + R / 2 < z i + R / 2 := by
        simpa [y] using hyi.2
      exact (lt_irrefl _ hbad)
    have hdist := Metric.infDist_le_dist_of_mem (x := x)
      (s := (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ) hy
    have hle : s ≤ dist x y := h.trans hdist
    rw [aux_lem_20_collar_family_smooth_collar_dist_update_of_ge d x
      (z i + R / 2) i hxi.2.le] at hle
    exact hle

theorem aux_lem_20_collar_family_smooth_collar_margin_small
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (x : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h : Metric.infDist x
      (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ r) :
    ∃ i : Fin d,
      x i - (z i - R / 2) ≤ r ∨ (z i + R / 2) - x i ≤ r := by
  have hcomp : ((centeredCube z R hR : Set (SpatialCoordinates d))ᶜ).Nonempty :=
    aux_lem_20_collar_family_smooth_collar_compl_nonempty d hd z R hR
  by_contra hnone
  push Not at hnone
  have hmargin : ∀ i : Fin d,
      r < min (x i - (z i - R / 2)) ((z i + R / 2) - x i) := by
    intro i
    exact (lt_min_iff).2 ⟨(hnone i).1, (hnone i).2⟩
  have hd0 : 0 < d := lt_of_lt_of_le Nat.zero_lt_two hd
  have hfin : (Finset.univ : Finset (Fin d)).Nonempty := by
    exact ⟨⟨0, hd0⟩, Finset.mem_univ _⟩
  let m : ℝ := (Finset.univ : Finset (Fin d)).inf' hfin
    (fun i => min (x i - (z i - R / 2)) ((z i + R / 2) - x i))
  have hrm : r < m := by
    dsimp [m]
    exact (Finset.lt_inf'_iff hfin).2 (fun i hi => hmargin i)
  have hxQ : x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) := by
    rw [centeredCube_eq_pi z hR]
    intro i hi
    exact ⟨by linarith [(hnone i).1], by linarith [(hnone i).2]⟩
  have hmInf : m ≤ Metric.infDist x
      (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ := by
    rw [Metric.le_infDist hcomp]
    intro y hy
    have hycoord : ∃ i : Fin d,
        y i ≤ z i - R / 2 ∨ z i + R / 2 ≤ y i := by
      by_contra hcoord
      push Not at hcoord
      apply hy
      rw [centeredCube_eq_pi z hR]
      intro i hi
      exact hcoord i
    rcases hycoord with ⟨i, hiy | hiy⟩
    · have hm : m ≤ x i - (z i - R / 2) := by
        dsimp [m]
        exact (Finset.inf'_le (fun j =>
          min (x j - (z j - R / 2)) ((z j + R / 2) - x j))
          (Finset.mem_univ i)).trans (min_le_left _ _)
      have hxy : x i - (z i - R / 2) ≤ x i - y i := by linarith
      have hdist : x i - y i = dist (x i) (y i) := by
        have hnonneg : 0 ≤ x i - y i := by linarith
        rw [Real.dist_eq, abs_of_nonneg hnonneg]
      calc
        m ≤ x i - (z i - R / 2) := hm
        _ ≤ x i - y i := hxy
        _ = dist (x i) (y i) := hdist
        _ ≤ dist x y :=
          aux_lem_20_collar_family_smooth_collar_coordinate_dist_le d x y i
    · have hm : m ≤ (z i + R / 2) - x i := by
        dsimp [m]
        exact (Finset.inf'_le (fun j =>
          min (x j - (z j - R / 2)) ((z j + R / 2) - x j))
          (Finset.mem_univ i)).trans (min_le_right _ _)
      have hxy : (z i + R / 2) - x i ≤ y i - x i := by linarith
      have hdist : y i - x i = dist (x i) (y i) := by
        have hnonpos : x i - y i ≤ 0 := by linarith
        rw [Real.dist_eq, abs_of_nonpos hnonpos]
        ring
      calc
        m ≤ (z i + R / 2) - x i := hm
        _ ≤ y i - x i := hxy
        _ = dist (x i) (y i) := hdist
        _ ≤ dist x y :=
          aux_lem_20_collar_family_smooth_collar_coordinate_dist_le d x y i
  have hmr : m ≤ r := hmInf.trans h
  linarith



theorem lem_20_collar_family_smooth_collar
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) :
    ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∃ theta : SpatialCoordinates d → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) theta ∧
          (∀ x, 0 ≤ theta x ∧ theta x ≤ 1) ∧
          (∀ x,
            Metric.infDist x
                (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ r →
              theta x = 0) ∧
          (∀ x,
            3 * r ≤ Metric.infDist x
                (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
              theta x = 1) ∧
      (∀ x,
            3 * r < Metric.infDist x
                (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
              fderiv ℝ theta x = 0) := by
  intro r hr hr1
  let Q : Set (SpatialCoordinates d) := centeredCube z R hR
  let lower : Fin d → SpatialCoordinates d → ℝ :=
    fun i x => (x i - (z i - R / 2) - r) / (2 * r)
  let upper : Fin d → SpatialCoordinates d → ℝ :=
    fun i x => ((z i + R / 2) - x i - r) / (2 * r)
  let theta : SpatialCoordinates d → ℝ :=
    fun x => ∏ i : Fin d, Real.smoothTransition (lower i x) *
      Real.smoothTransition (upper i x)
  have hcomp : Qᶜ.Nonempty := by
    exact aux_lem_20_collar_family_smooth_collar_compl_nonempty d hd z R hR
  have hlower : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (lower i) := by
    intro i
    dsimp [lower]
    fun_prop
  have hupper : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (upper i) := by
    intro i
    dsimp [upper]
    fun_prop
  have htheta : ContDiff ℝ (⊤ : ℕ∞) theta := by
    dsimp [theta]
    apply contDiff_prod
    intro i hi
    exact (Real.smoothTransition.contDiff.comp (hlower i)).mul
      (Real.smoothTransition.contDiff.comp (hupper i))
  refine ⟨theta, htheta, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · dsimp [theta]
      exact Finset.prod_nonneg (fun i hi => mul_nonneg
        (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))
    · dsimp [theta]
      exact Finset.prod_le_one₀ (fun i hi => mul_nonneg
        (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))
        (fun i hi => (mul_le_of_le_one_left (Real.smoothTransition.nonneg _)
          (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _))
  · intro x hx
    obtain ⟨i, hi | hi⟩ :=
      aux_lem_20_collar_family_smooth_collar_margin_small d hd z R hR x r hr
        (by simpa [Q] using hx)
    · have hnum : x i - (z i - R / 2) - r ≤ 0 := by linarith
      have hzero : lower i x ≤ 0 := by
        dsimp [lower]
        exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
      dsimp [theta]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [mul_eq_zero]
      left
      exact Real.smoothTransition.zero_of_nonpos hzero
    · have hnum : (z i + R / 2) - x i - r ≤ 0 := by linarith
      have hzero : upper i x ≤ 0 := by
        dsimp [upper]
        exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
      dsimp [theta]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [mul_eq_zero]
      right
      exact Real.smoothTransition.zero_of_nonpos hzero
  · intro x hx
    have hs : 0 < 3 * r := by positivity
    have hm := aux_lem_20_collar_family_smooth_collar_margins_ge d z R hR x
      (3 * r) hs (by simpa [Q] using hx)
    dsimp [theta]
    apply Finset.prod_eq_one
    intro i hi
    have hl : 1 ≤ lower i x := by
      dsimp [lower]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * r)]
      linarith [hm i |>.1]
    have hu : 1 ≤ upper i x := by
      dsimp [upper]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * r)]
      linarith [hm i |>.2]
    rw [Real.smoothTransition.one_of_one_le hl,
      Real.smoothTransition.one_of_one_le hu, mul_one]
  · intro x hx
    have hs : 0 < Metric.infDist x Qᶜ := by
      have h3 : 0 < 3 * r := by positivity
      exact h3.trans hx
    have hm := aux_lem_20_collar_family_smooth_collar_margins_ge d z R hR x
      (Metric.infDist x Qᶜ) hs le_rfl
    have hlow : ∀ i : Fin d, 1 < lower i x := by
      intro i
      dsimp [lower]
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * r)]
      linarith [hx, hm i |>.1]
    have hupp : ∀ i : Fin d, 1 < upper i x := by
      intro i
      dsimp [upper]
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * r)]
      linarith [hx, hm i |>.2]
    have hev : ∀ i : Fin d, ∀ᶠ y in 𝓝 x,
        1 < lower i y ∧ 1 < upper i y := by
      intro i
      have hli : ∀ᶠ y in 𝓝 x, 1 < lower i y :=
        (hlower i).continuous.continuousAt (isOpen_Ioi.mem_nhds (hlow i))
      have hui : ∀ᶠ y in 𝓝 x, 1 < upper i y :=
        (hupper i).continuous.continuousAt (isOpen_Ioi.mem_nhds (hupp i))
      exact hli.and hui
    have hall : ∀ᶠ y in 𝓝 x, ∀ i : Fin d,
        1 < lower i y ∧ 1 < upper i y := by
      have hfinite : ∀ s : Finset (Fin d), ∀ᶠ y in 𝓝 x,
          ∀ i ∈ s, 1 < lower i y ∧ 1 < upper i y := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
            exact Filter.Eventually.of_forall (fun y => by simp)
        | @insert i s hi ih =>
            filter_upwards [hev i, ih] with y hiy hys
            intro j hj
            simp only [Finset.mem_insert] at hj
            rcases hj with rfl | hj
            · exact hiy
            · exact hys j hj
      simpa only [Finset.mem_univ, forall_true_left] using hfinite Finset.univ
    have heq : theta =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [hall] with y hy
      dsimp [theta]
      apply Finset.prod_eq_one
      intro i hi
      rw [Real.smoothTransition.one_of_one_le (le_of_lt (hy i).1),
        Real.smoothTransition.one_of_one_le (le_of_lt (hy i).2), mul_one]
    rw [heq.fderiv_eq]
    exact congrFun (fderiv_const (𝕜 := ℝ) (E := SpatialCoordinates d)
      (F := ℝ) 1) x

/-- The explicit product profile used in the proof of
`lem_20_collar_family_smooth_collar` (its local `theta` after unfolding
`lower` and `upper`). -/
def aux_lem_20_collar_family_smooth_collar_profile
    (d : ℕ) (z : SpatialCoordinates d) (R r : ℝ) :
    SpatialCoordinates d → ℝ :=
  fun x => ∏ i : Fin d,
    Real.smoothTransition ((x i - (z i - R / 2) - r) / (2 * r)) *
      Real.smoothTransition (((z i + R / 2) - x i - r) / (2 * r))

/-- The derivative of `Real.smoothTransition` vanishes off `[0,1]`. -/
theorem aux_lem_20_collar_family_smooth_collar_deriv_transition_eq_zero
    (t : ℝ) (ht : t ∉ Set.Icc (0 : ℝ) 1) :
    deriv Real.smoothTransition t = 0 := by
  rcases not_and_or.mp (show ¬ (0 ≤ t ∧ t ≤ 1) from ht) with h | h
  · push Not at h
    have heq : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with s hs
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
    rw [heq.deriv_eq]
    simp
  · push Not at h
    have heq : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h] with s hs
      exact Real.smoothTransition.one_of_one_le (le_of_lt hs)
    rw [heq.deriv_eq]
    simp

/-- A global bound for the derivative of `Real.smoothTransition`: it is
continuous and supported in `[0,1]`. -/
theorem aux_lem_20_collar_family_smooth_collar_deriv_transition_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ M := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hsupp : HasCompactSupport (deriv Real.smoothTransition) :=
    HasCompactSupport.intro isCompact_Icc
      aux_lem_20_collar_family_smooth_collar_deriv_transition_eq_zero
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
  exact ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun t => (hC t).trans (le_max_left _ _)⟩

/-- A coordinate projection has operator norm at most one for the sup norm. -/
theorem aux_lem_20_collar_family_smooth_collar_norm_proj_le
    (d : ℕ) (i : Fin d) :
    ‖(ContinuousLinearMap.proj i : SpatialCoordinates d →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y => by
    simpa using norm_le_pi_norm y i)

/-- A one-variable profile of one coordinate: its derivative is a multiple of
the coordinate projection, with norm at most the one-variable slope. -/
theorem aux_lem_20_collar_family_smooth_collar_coord_fderiv
    (d : ℕ) (g : ℝ → ℝ) (i : Fin d) (x : SpatialCoordinates d) (c : ℝ)
    (hg : HasDerivAt g c (x i)) :
    HasFDerivAt (fun y : SpatialCoordinates d => g (y i))
        (c • (ContinuousLinearMap.proj i : SpatialCoordinates d →L[ℝ] ℝ)) x ∧
      ‖c • (ContinuousLinearMap.proj i : SpatialCoordinates d →L[ℝ] ℝ)‖ ≤ ‖c‖ := by
  refine ⟨hg.comp_hasFDerivAt x (hasFDerivAt_apply i x), ?_⟩
  rw [norm_smul]
  calc ‖c‖ * ‖(ContinuousLinearMap.proj i : SpatialCoordinates d →L[ℝ] ℝ)‖
      ≤ ‖c‖ * 1 := mul_le_mul_of_nonneg_left
        (aux_lem_20_collar_family_smooth_collar_norm_proj_le d i) (norm_nonneg _)
    _ = ‖c‖ := mul_one _

/-- The lower-margin factor has derivative of norm at most `M / (2 * r)`. -/
theorem aux_lem_20_collar_family_smooth_collar_lower_fderiv
    (d : ℕ) (z : SpatialCoordinates d) (R r : ℝ) (hr : 0 < r) (M : ℝ)
    (hM : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ M)
    (i : Fin d) (x : SpatialCoordinates d) :
    ∃ L : SpatialCoordinates d →L[ℝ] ℝ,
      HasFDerivAt (fun y : SpatialCoordinates d =>
          Real.smoothTransition ((y i - (z i - R / 2) - r) / (2 * r))) L x ∧
        ‖L‖ ≤ M / (2 * r) := by
  have hdiff : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)
  let a : ℝ → ℝ := fun t => (t - (z i - R / 2) - r) / (2 * r)
  have ha : HasDerivAt a (1 / (2 * r)) (x i) := by
    have h := (((hasDerivAt_id (x i)).sub_const (z i - R / 2)).sub_const r).div_const
      (2 * r)
    simpa [a] using h
  have hcomp : HasDerivAt (fun t => Real.smoothTransition (a t))
      (deriv Real.smoothTransition (a (x i)) * (1 / (2 * r))) (x i) :=
    (hdiff (a (x i))).hasDerivAt.comp (x i) ha
  obtain ⟨hF, hnorm⟩ := aux_lem_20_collar_family_smooth_collar_coord_fderiv d
    (fun t => Real.smoothTransition (a t)) i x _ hcomp
  refine ⟨_, hF, hnorm.trans ?_⟩
  have h2r : (0 : ℝ) < 2 * r := by positivity
  rw [norm_mul, Real.norm_eq_abs (1 / (2 * r)), abs_of_pos (by positivity),
    mul_one_div]
  exact div_le_div_of_nonneg_right (hM _) h2r.le

/-- The upper-margin factor has derivative of norm at most `M / (2 * r)`. -/
theorem aux_lem_20_collar_family_smooth_collar_upper_fderiv
    (d : ℕ) (z : SpatialCoordinates d) (R r : ℝ) (hr : 0 < r) (M : ℝ)
    (hM : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ M)
    (i : Fin d) (x : SpatialCoordinates d) :
    ∃ L : SpatialCoordinates d →L[ℝ] ℝ,
      HasFDerivAt (fun y : SpatialCoordinates d =>
          Real.smoothTransition (((z i + R / 2) - y i - r) / (2 * r))) L x ∧
        ‖L‖ ≤ M / (2 * r) := by
  have hdiff : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)
  let a : ℝ → ℝ := fun t => ((z i + R / 2) - t - r) / (2 * r)
  have ha : HasDerivAt a (-1 / (2 * r)) (x i) := by
    have h := (((hasDerivAt_id (x i)).const_sub (z i + R / 2)).sub_const r).div_const
      (2 * r)
    simpa [a] using h
  have hcomp : HasDerivAt (fun t => Real.smoothTransition (a t))
      (deriv Real.smoothTransition (a (x i)) * (-1 / (2 * r))) (x i) :=
    (hdiff (a (x i))).hasDerivAt.comp (x i) ha
  obtain ⟨hF, hnorm⟩ := aux_lem_20_collar_family_smooth_collar_coord_fderiv d
    (fun t => Real.smoothTransition (a t)) i x _ hcomp
  refine ⟨_, hF, hnorm.trans ?_⟩
  have h2r : (0 : ℝ) < 2 * r := by positivity
  rw [norm_mul, Real.norm_eq_abs (-1 / (2 * r)), neg_div, abs_neg,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * r)), mul_one_div]
  exact div_le_div_of_nonneg_right (hM _) h2r.le

/-- Derivative of a product of two `[0,1]`-bounded factors. -/
theorem aux_lem_20_collar_family_smooth_collar_mul_fderiv
    (d : ℕ) (f g : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d)
    (f' g' : SpatialCoordinates d →L[ℝ] ℝ)
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (hf1 : ‖f x‖ ≤ 1) (hg1 : ‖g x‖ ≤ 1) :
    ∃ L : SpatialCoordinates d →L[ℝ] ℝ,
      HasFDerivAt (fun y => f y * g y) L x ∧ ‖L‖ ≤ ‖f'‖ + ‖g'‖ := by
  refine ⟨_, hf.mul hg, ?_⟩
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, add_comm ‖f'‖]
  exact add_le_add
    ((mul_le_mul_of_nonneg_right hf1 (norm_nonneg _)).trans_eq (one_mul _))
    ((mul_le_mul_of_nonneg_right hg1 (norm_nonneg _)).trans_eq (one_mul _))

/-- Derivative of a finite product of `[0,1]`-bounded factors: its norm is at
most the sum of the norms of the factor derivatives. -/
theorem aux_lem_20_collar_family_smooth_collar_prod_fderiv
    (d : ℕ) (g : Fin d → SpatialCoordinates d → ℝ)
    (g' : Fin d → SpatialCoordinates d →L[ℝ] ℝ) (x : SpatialCoordinates d)
    (hg : ∀ i, HasFDerivAt (g i) (g' i) x) (hg1 : ∀ i, ‖g i x‖ ≤ 1) :
    ‖fderiv ℝ (fun y => ∏ i, g i y) x‖ ≤ ∑ i, ‖g' i‖ := by
  classical
  rw [(HasFDerivAt.finsetProd (u := Finset.univ) (fun i _ => hg i)).fderiv]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul]
  have hp : ‖∏ j ∈ Finset.univ.erase i, g j x‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun j _ => norm_nonneg _) (fun j _ => hg1 j)
  exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans_eq (one_mul _)

/-- The derivative of the explicit collar profile is bounded by `d * M / r`
at every point, for every width `r > 0`. -/
theorem aux_lem_20_collar_family_smooth_collar_profile_fderiv_le
    (d : ℕ) (z : SpatialCoordinates d) (R r : ℝ) (hr : 0 < r) (M : ℝ)
    (hM : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ M)
    (x : SpatialCoordinates d) :
    ‖fderiv ℝ (aux_lem_20_collar_family_smooth_collar_profile d z R r) x‖ ≤
      (d : ℝ) * M / r := by
  have hfac : ∀ i : Fin d, ∃ L : SpatialCoordinates d →L[ℝ] ℝ,
      HasFDerivAt (fun y : SpatialCoordinates d =>
          Real.smoothTransition ((y i - (z i - R / 2) - r) / (2 * r)) *
            Real.smoothTransition (((z i + R / 2) - y i - r) / (2 * r))) L x ∧
        ‖L‖ ≤ M / r := by
    intro i
    obtain ⟨Ll, hLl, hLln⟩ := aux_lem_20_collar_family_smooth_collar_lower_fderiv
      d z R r hr M hM i x
    obtain ⟨Lu, hLu, hLun⟩ := aux_lem_20_collar_family_smooth_collar_upper_fderiv
      d z R r hr M hM i x
    have h1 : ∀ s : ℝ, ‖Real.smoothTransition s‖ ≤ 1 := fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg s)]
      exact Real.smoothTransition.le_one s
    obtain ⟨L, hL, hLn⟩ := aux_lem_20_collar_family_smooth_collar_mul_fderiv d _ _ x
      Ll Lu hLl hLu (h1 _) (h1 _)
    refine ⟨L, hL, hLn.trans ?_⟩
    have hsum : M / (2 * r) + M / (2 * r) = M / r := by
      field_simp
      ring
    linarith
  choose L hL hLn using hfac
  have hbound := aux_lem_20_collar_family_smooth_collar_prod_fderiv d
    (fun i y => Real.smoothTransition ((y i - (z i - R / 2) - r) / (2 * r)) *
      Real.smoothTransition (((z i + R / 2) - y i - r) / (2 * r))) L x hL
    (fun i => by
      rw [norm_mul]
      have h1 : ∀ s : ℝ, ‖Real.smoothTransition s‖ ≤ 1 := fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg s)]
        exact Real.smoothTransition.le_one s
      exact (mul_le_mul (h1 _) (h1 _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul _))
  have hsum : ∑ i, ‖L i‖ ≤ ∑ _i : Fin d, M / r :=
    Finset.sum_le_sum fun i _ => hLn i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [mul_div_assoc]
  exact hbound.trans hsum

/-- All clauses of `lem_20_collar_family_smooth_collar`, proved for the
explicit profile, plus the global derivative bound `d * M / r`. -/
theorem aux_lem_20_collar_family_smooth_collar_profile_spec
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (M : ℝ)
    (hM : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ M)
    (r : ℝ) (hr : 0 < r) :
    let theta := aux_lem_20_collar_family_smooth_collar_profile d z R r
    ContDiff ℝ (⊤ : ℕ∞) theta ∧
      (∀ x, 0 ≤ theta x ∧ theta x ≤ 1) ∧
      (∀ x,
        Metric.infDist x
            (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ r →
          theta x = 0) ∧
      (∀ x,
        3 * r ≤ Metric.infDist x
            (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
          theta x = 1) ∧
      (∀ x,
        3 * r < Metric.infDist x
            (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
          fderiv ℝ theta x = 0) ∧
      (∀ x, ‖fderiv ℝ theta x‖ ≤ (d : ℝ) * M / r) := by
  intro theta
  let Q : Set (SpatialCoordinates d) := centeredCube z R hR
  let lower : Fin d → SpatialCoordinates d → ℝ :=
    fun i x => (x i - (z i - R / 2) - r) / (2 * r)
  let upper : Fin d → SpatialCoordinates d → ℝ :=
    fun i x => ((z i + R / 2) - x i - r) / (2 * r)
  have htheta_def : theta = fun x => ∏ i : Fin d,
      Real.smoothTransition (lower i x) * Real.smoothTransition (upper i x) := rfl
  have hlower : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (lower i) := by
    intro i
    dsimp [lower]
    fun_prop
  have hupper : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (upper i) := by
    intro i
    dsimp [upper]
    fun_prop
  have htheta : ContDiff ℝ (⊤ : ℕ∞) theta := by
    rw [htheta_def]
    apply contDiff_prod
    intro i hi
    exact (Real.smoothTransition.contDiff.comp (hlower i)).mul
      (Real.smoothTransition.contDiff.comp (hupper i))
  refine ⟨htheta, ?_, ?_, ?_, ?_,
    aux_lem_20_collar_family_smooth_collar_profile_fderiv_le d z R r hr M hM⟩
  · intro x
    rw [htheta_def]
    constructor
    · exact Finset.prod_nonneg (fun i hi => mul_nonneg
        (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))
    · exact Finset.prod_le_one₀ (fun i hi => mul_nonneg
        (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))
        (fun i hi => (mul_le_of_le_one_left (Real.smoothTransition.nonneg _)
          (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _))
  · intro x hx
    obtain ⟨i, hi | hi⟩ :=
      aux_lem_20_collar_family_smooth_collar_margin_small d hd z R hR x r hr hx
    · have hnum : x i - (z i - R / 2) - r ≤ 0 := by linarith
      have hzero : lower i x ≤ 0 := by
        dsimp [lower]
        exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
      rw [htheta_def]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [mul_eq_zero]
      left
      exact Real.smoothTransition.zero_of_nonpos hzero
    · have hnum : (z i + R / 2) - x i - r ≤ 0 := by linarith
      have hzero : upper i x ≤ 0 := by
        dsimp [upper]
        exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
      rw [htheta_def]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [mul_eq_zero]
      right
      exact Real.smoothTransition.zero_of_nonpos hzero
  · intro x hx
    have hs : 0 < 3 * r := by positivity
    have hm := aux_lem_20_collar_family_smooth_collar_margins_ge d z R hR x
      (3 * r) hs hx
    rw [htheta_def]
    apply Finset.prod_eq_one
    intro i hi
    have hl : 1 ≤ lower i x := by
      dsimp [lower]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * r)]
      linarith [hm i |>.1]
    have hu : 1 ≤ upper i x := by
      dsimp [upper]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * r)]
      linarith [hm i |>.2]
    rw [Real.smoothTransition.one_of_one_le hl,
      Real.smoothTransition.one_of_one_le hu, mul_one]
  · intro x hx
    have hs : 0 < Metric.infDist x Qᶜ := by
      have h3 : 0 < 3 * r := by positivity
      exact h3.trans hx
    have hm := aux_lem_20_collar_family_smooth_collar_margins_ge d z R hR x
      (Metric.infDist x Qᶜ) hs le_rfl
    have hlow : ∀ i : Fin d, 1 < lower i x := by
      intro i
      dsimp [lower]
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * r)]
      linarith [hx, hm i |>.1]
    have hupp : ∀ i : Fin d, 1 < upper i x := by
      intro i
      dsimp [upper]
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * r)]
      linarith [hx, hm i |>.2]
    have hall : ∀ᶠ y in 𝓝 x, ∀ i : Fin d,
        1 < lower i y ∧ 1 < upper i y := by
      rw [Filter.eventually_all]
      intro i
      have hli : ∀ᶠ y in 𝓝 x, 1 < lower i y :=
        (hlower i).continuous.continuousAt (isOpen_Ioi.mem_nhds (hlow i))
      have hui : ∀ᶠ y in 𝓝 x, 1 < upper i y :=
        (hupper i).continuous.continuousAt (isOpen_Ioi.mem_nhds (hupp i))
      exact hli.and hui
    have heq : theta =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [hall] with y hy
      rw [htheta_def]
      apply Finset.prod_eq_one
      intro i hi
      rw [Real.smoothTransition.one_of_one_le (le_of_lt (hy i).1),
        Real.smoothTransition.one_of_one_le (le_of_lt (hy i).2), mul_one]
    rw [heq.fderiv_eq]
    exact congrFun (fderiv_const (𝕜 := ℝ) (E := SpatialCoordinates d)
      (F := ℝ) 1) x



theorem aux_lem_20_collar_family_smooth_collar_uniform_grad
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) :
    ∃ Cgrad : ℝ, 0 < Cgrad ∧
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        ∃ theta : SpatialCoordinates d → ℝ,
          theta = aux_lem_20_collar_family_smooth_collar_profile d z R r ∧
          ContDiff ℝ (⊤ : ℕ∞) theta ∧
            (∀ x, 0 ≤ theta x ∧ theta x ≤ 1) ∧
            (∀ x,
              Metric.infDist x
                  (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ r →
                theta x = 0) ∧
            (∀ x,
              3 * r ≤ Metric.infDist x
                  (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
                theta x = 1) ∧
            (∀ x,
              3 * r < Metric.infDist x
                  (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
                fderiv ℝ theta x = 0) ∧
            (∀ x, ‖fderiv ℝ theta x‖ ≤ Cgrad / r) := by
  obtain ⟨M, hMpos, hM⟩ :=
    aux_lem_20_collar_family_smooth_collar_deriv_transition_bound
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le two_pos hd)
  refine ⟨(d : ℝ) * M, mul_pos hd0 hMpos, ?_⟩
  intro r hr _hr1
  exact ⟨_, rfl, aux_lem_20_collar_family_smooth_collar_profile_spec
    d hd z R hR M hM r hr⟩

/-- For a point of the open cube, the distance to the frontier equals the
distance to the complement. -/
theorem aux_lem_20_collar_family_smooth_collar_infDist_frontier_eq
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (x : SpatialCoordinates d)
    (hx : x ∈ (centeredCube z R hR : Set (SpatialCoordinates d))) :
    Metric.infDist x
        (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) =
      Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ := by
  have hQne : (centeredCube z R hR : Set (SpatialCoordinates d)) ≠ Set.univ := by
    intro h
    obtain ⟨y, hy⟩ :=
      aux_lem_20_collar_family_smooth_collar_compl_nonempty d hd z R hR
    exact hy (h ▸ Set.mem_univ y)
  obtain ⟨y, hyf, hyd⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hQne
  have hsub : frontier (centeredCube z R hR : Set (SpatialCoordinates d)) ⊆
      (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ := by
    intro w hw
    rw [(centeredCube z R hR).isOpen.frontier_eq] at hw
    exact hw.2
  apply le_antisymm
  · rw [hyd]
    exact Metric.infDist_le_dist_of_mem hyf
  · exact Metric.infDist_le_infDist_of_subset hsub ⟨y, hyf⟩

/-- The collar premises of the `lem_cutoffs` collar clause, in its
exact `frontier` form, for every width `rho > 0`, from one constant fixed
before the width. The witness is the explicit product profile. -/
theorem aux_lem_20_collar_family_smooth_collar_cutoffs_premises
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) :
    ∃ Cgrad : ℝ, 0 < Cgrad ∧
      ∀ rho : ℝ, 0 < rho →
        ∃ thetaR : SpatialCoordinates d → ℝ,
          thetaR = aux_lem_20_collar_family_smooth_collar_profile d z R rho ∧
          ContDiff ℝ ∞ thetaR ∧
          (∀ x : SpatialCoordinates d,
            0 ≤ thetaR x ∧ thetaR x ≤ 1) ∧
          (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
            Metric.infDist x
                (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) ≤ rho →
              thetaR x = 0) ∧
          (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
            3 * rho ≤ Metric.infDist x
                (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) →
              thetaR x = 1) ∧
          (∀ x : SpatialCoordinates d,
            norm (fderiv ℝ thetaR x) ≤ Cgrad / rho) := by
  obtain ⟨M, hMpos, hM⟩ :=
    aux_lem_20_collar_family_smooth_collar_deriv_transition_bound
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le two_pos hd)
  refine ⟨(d : ℝ) * M, mul_pos hd0 hMpos, ?_⟩
  intro rho hrho
  obtain ⟨hC, hrange, hzero, hone, -, hgrad⟩ :=
    aux_lem_20_collar_family_smooth_collar_profile_spec d hd z R hR M hM rho hrho
  refine ⟨_, rfl, hC, hrange, ?_, ?_, hgrad⟩
  · intro x hx hdist
    rw [aux_lem_20_collar_family_smooth_collar_infDist_frontier_eq d hd z R hR x hx]
      at hdist
    exact hzero x hdist
  · intro x hx hdist
    rw [aux_lem_20_collar_family_smooth_collar_infDist_frontier_eq d hd z R hR x hx]
      at hdist
    exact hone x hdist

end SubdiffusiveProcess.Paper
