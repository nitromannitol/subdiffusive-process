module

public import SubdiffusiveProcess.Paper.lem_20_collar_family_smooth_collar

@[expose] public section

/-!
# Buffered smooth collars

An explicit smooth transition on an axis-aligned cube, with zero and unit
regions separated from the requested collar boundaries. The derivative bound
is dimension-only after dividing by the collar width.
-/

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal BigOperators Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- A smooth collar profile with separated zero and unit thresholds. -/
def bufferedCollarProfile
    (d : ℕ) (z : SpatialCoordinates d) (R r : ℝ) :
    SpatialCoordinates d → ℝ :=
  fun x => ∏ i : Fin d,
    Real.smoothTransition ((x i - (z i - R / 2) - 3 * r / 2) / r) *
      Real.smoothTransition (((z i + R / 2) - x i - 3 * r / 2) / r)

/-- Derivative bound for the lower coordinate factor of the buffered profile. -/
theorem aux_buffered_collar_lower_fderiv
    (d : ℕ) (z : SpatialCoordinates d) (R r : ℝ) (hr : 0 < r)
    (M : ℝ) (hM : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ M)
    (i : Fin d) (x : SpatialCoordinates d) :
    ∃ L : SpatialCoordinates d →L[ℝ] ℝ,
      HasFDerivAt (fun y => Real.smoothTransition
        ((y i - (z i - R / 2) - 3 * r / 2) / r)) L x ∧
      ‖L‖ ≤ M / r := by
  have hdiff : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  let a : ℝ → ℝ := fun t => (t - (z i - R / 2) - 3 * r / 2) / r
  have ha : HasDerivAt a (1 / r) (x i) := by
    have h := (((hasDerivAt_id (x i)).sub_const (z i - R / 2)).sub_const
      (3 * r / 2)).div_const r
    simpa [a] using h
  have hcomp : HasDerivAt (fun t => Real.smoothTransition (a t))
      (deriv Real.smoothTransition (a (x i)) * (1 / r)) (x i) :=
    (hdiff (a (x i))).hasDerivAt.comp (x i) ha
  obtain ⟨hF, hnorm⟩ := aux_lem_20_collar_family_smooth_collar_coord_fderiv d
    (fun t => Real.smoothTransition (a t)) i x _ hcomp
  refine ⟨_, hF, hnorm.trans ?_⟩
  rw [norm_mul, Real.norm_eq_abs (1 / r), abs_of_pos (by positivity), mul_one_div]
  exact div_le_div_of_nonneg_right (hM _) hr.le

/-- Derivative bound for the upper coordinate factor of the buffered profile. -/
theorem aux_buffered_collar_upper_fderiv
    (d : ℕ) (z : SpatialCoordinates d) (R r : ℝ) (hr : 0 < r)
    (M : ℝ) (hM : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ M)
    (i : Fin d) (x : SpatialCoordinates d) :
    ∃ L : SpatialCoordinates d →L[ℝ] ℝ,
      HasFDerivAt (fun y => Real.smoothTransition
        (((z i + R / 2) - y i - 3 * r / 2) / r)) L x ∧
      ‖L‖ ≤ M / r := by
  have hdiff : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  let a : ℝ → ℝ := fun t => ((z i + R / 2) - t - 3 * r / 2) / r
  have ha : HasDerivAt a (-1 / r) (x i) := by
    have h := (((hasDerivAt_id (x i)).const_sub (z i + R / 2)).sub_const
      (3 * r / 2)).div_const r
    simpa [a] using h
  have hcomp : HasDerivAt (fun t => Real.smoothTransition (a t))
      (deriv Real.smoothTransition (a (x i)) * (-1 / r)) (x i) :=
    (hdiff (a (x i))).hasDerivAt.comp (x i) ha
  obtain ⟨hF, hnorm⟩ := aux_lem_20_collar_family_smooth_collar_coord_fderiv d
    (fun t => Real.smoothTransition (a t)) i x _ hcomp
  refine ⟨_, hF, hnorm.trans ?_⟩
  rw [norm_mul, Real.norm_eq_abs (-1 / r), neg_div, abs_neg,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / r), mul_one_div]
  exact div_le_div_of_nonneg_right (hM _) hr.le

/-- Global derivative estimate for the buffered profile. -/
theorem aux_buffered_collar_profile_fderiv_le
    (d : ℕ) (z : SpatialCoordinates d) (R r M : ℝ)
    (hr : 0 < r)
    (hM : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ M)
    (x : SpatialCoordinates d) :
    ‖fderiv ℝ (bufferedCollarProfile d z R r) x‖ ≤
      (d : ℝ) * (2 * M) / r := by
  have hfac : ∀ i : Fin d, ∃ L : SpatialCoordinates d →L[ℝ] ℝ,
      HasFDerivAt (fun y : SpatialCoordinates d =>
        Real.smoothTransition ((y i - (z i - R / 2) - 3 * r / 2) / r) *
          Real.smoothTransition (((z i + R / 2) - y i - 3 * r / 2) / r)) L x ∧
      ‖L‖ ≤ 2 * M / r := by
    intro i
    obtain ⟨Ll, hLl, hLln⟩ := aux_buffered_collar_lower_fderiv
      d z R r hr M hM i x
    obtain ⟨Lu, hLu, hLun⟩ := aux_buffered_collar_upper_fderiv
      d z R r hr M hM i x
    have h1 : ∀ s : ℝ, ‖Real.smoothTransition s‖ ≤ 1 := fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg s)]
      exact Real.smoothTransition.le_one s
    obtain ⟨L, hL, hLn⟩ := aux_lem_20_collar_family_smooth_collar_mul_fderiv
      d _ _ x Ll Lu hLl hLu (h1 _) (h1 _)
    refine ⟨L, hL, hLn.trans ?_⟩
    have hsum : M / r + M / r = 2 * M / r := by ring
    exact (add_le_add hLln hLun).trans_eq hsum
  choose L hL hLn using hfac
  have hbound := aux_lem_20_collar_family_smooth_collar_prod_fderiv d
    (fun i y => Real.smoothTransition
      ((y i - (z i - R / 2) - 3 * r / 2) / r) *
        Real.smoothTransition (((z i + R / 2) - y i - 3 * r / 2) / r)) L x hL
    (fun i => by
      rw [norm_mul]
      have h1 : ∀ s : ℝ, ‖Real.smoothTransition s‖ ≤ 1 := fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg s)]
        exact Real.smoothTransition.le_one s
      exact (mul_le_mul (h1 _) (h1 _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul _))
  have hsum : ∑ i, ‖L i‖ ≤ ∑ _i : Fin d, (2 * M / r) :=
    Finset.sum_le_sum fun i _ => hLn i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  exact hbound.trans (by simpa [mul_div_assoc] using hsum)

/-- The buffered profile is smooth, takes values in `[0,1]`, vanishes up to
distance `3r/2` from the cube complement, and equals one from distance `5r/2`.
It is locally constant beyond the outer threshold. -/
theorem aux_buffered_collar_profile_regions
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (r : ℝ) (hr : 0 < r) :
    let theta := bufferedCollarProfile d z R r
    ContDiff ℝ (⊤ : ℕ∞) theta ∧
      (∀ x, 0 ≤ theta x ∧ theta x ≤ 1) ∧
      (∀ x, Metric.infDist x
        (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r / 2 →
        theta x = 0) ∧
      (∀ x, 5 * r / 2 ≤ Metric.infDist x
        (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        theta x = 1) ∧
      (∀ x, 5 * r / 2 < Metric.infDist x
        (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        fderiv ℝ theta x = 0) := by
  intro theta
  let Q : Set (SpatialCoordinates d) := centeredCube z R hR
  let lower : Fin d → SpatialCoordinates d → ℝ :=
    fun i x => (x i - (z i - R / 2) - 3 * r / 2) / r
  let upper : Fin d → SpatialCoordinates d → ℝ :=
    fun i x => ((z i + R / 2) - x i - 3 * r / 2) / r
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
  refine ⟨htheta, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [htheta_def]
    constructor
    · exact Finset.prod_nonneg (fun i _ => mul_nonneg
        (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))
    · exact Finset.prod_le_one₀ (fun i _ => mul_nonneg
        (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))
        (fun i _ => (mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
          (Real.smoothTransition.nonneg _)).trans
          (by simpa only [one_mul] using Real.smoothTransition.le_one _))
  · intro x hx
    obtain ⟨i, hi | hi⟩ :=
      aux_lem_20_collar_family_smooth_collar_margin_small d hd z R hR x
        (3 * r / 2) (by positivity) (by simpa [Q] using hx)
    · have hnum : x i - (z i - R / 2) - 3 * r / 2 ≤ 0 := by linarith
      have hzero : lower i x ≤ 0 := by
        dsimp [lower]
        exact div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hr)
      rw [htheta_def]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [mul_eq_zero]
      left
      exact Real.smoothTransition.zero_of_nonpos hzero
    · have hnum : (z i + R / 2) - x i - 3 * r / 2 ≤ 0 := by linarith
      have hzero : upper i x ≤ 0 := by
        dsimp [upper]
        exact div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hr)
      rw [htheta_def]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [mul_eq_zero]
      right
      exact Real.smoothTransition.zero_of_nonpos hzero
  · intro x hx
    have hs : 0 < 5 * r / 2 := by positivity
    have hm := aux_lem_20_collar_family_smooth_collar_margins_ge d z R hR x
      (5 * r / 2) hs (by simpa [Q] using hx)
    rw [htheta_def]
    apply Finset.prod_eq_one
    intro i hi
    have hl : 1 ≤ lower i x := by
      dsimp [lower]
      rw [le_div_iff₀ hr]
      linarith [hm i |>.1]
    have hu : 1 ≤ upper i x := by
      dsimp [upper]
      rw [le_div_iff₀ hr]
      linarith [hm i |>.2]
    rw [Real.smoothTransition.one_of_one_le hl,
      Real.smoothTransition.one_of_one_le hu, mul_one]
  · intro x hx
    have hs : 0 < Metric.infDist x Qᶜ := by
      exact (by positivity : (0 : ℝ) < 5 * r / 2).trans hx
    have hm := aux_lem_20_collar_family_smooth_collar_margins_ge d z R hR x
      (Metric.infDist x Qᶜ) hs le_rfl
    have hlow : ∀ i : Fin d, 1 < lower i x := by
      intro i
      dsimp [lower]
      rw [lt_div_iff₀ hr]
      linarith [hx, hm i |>.1]
    have hupp : ∀ i : Fin d, 1 < upper i x := by
      intro i
      dsimp [upper]
      rw [lt_div_iff₀ hr]
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

/-- Uniform buffered profile package: the transition derivative bound is
chosen once, before the collar width, and the resulting gradient constant
depends only on the dimension. -/
theorem aux_buffered_collar_profile_uniform
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) :
    ∃ Cgrad : ℝ, 0 < Cgrad ∧
      ∀ r : ℝ, 0 < r → r < R / 2 →
        let theta := bufferedCollarProfile d z R r
        ContDiff ℝ (⊤ : ℕ∞) theta ∧
          (∀ x, 0 ≤ theta x ∧ theta x ≤ 1) ∧
          (∀ x, Metric.infDist x
            (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r / 2 →
            theta x = 0) ∧
          (∀ x, 5 * r / 2 ≤ Metric.infDist x
            (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
            theta x = 1) ∧
          (∀ x, 5 * r / 2 < Metric.infDist x
            (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
            fderiv ℝ theta x = 0) ∧
          (∀ x, ‖fderiv ℝ theta x‖ ≤ Cgrad / r) := by
  obtain ⟨M, hMpos, hM⟩ :=
    aux_lem_20_collar_family_smooth_collar_deriv_transition_bound
  have hd0 : (0 : ℝ) < d := by
    exact_mod_cast (lt_of_lt_of_le two_pos hd)
  refine ⟨(d : ℝ) * (2 * M), mul_pos hd0 (mul_pos (by norm_num) hMpos), ?_⟩
  intro r hr hwidth
  let theta := bufferedCollarProfile d z R r
  have hregions := aux_buffered_collar_profile_regions d hd z R hR r hr
  have hgradient := aux_buffered_collar_profile_fderiv_le d z R r M hr hM
  refine ⟨hregions.1, hregions.2.1, hregions.2.2.1,
    hregions.2.2.2.1, hregions.2.2.2.2, ?_⟩
  intro x
  calc
    ‖fderiv ℝ theta x‖ ≤ (d : ℝ) * (2 * M) / r := by
      simpa [theta] using hgradient x
    _ = ((d : ℝ) * (2 * M)) / r := rfl

end SubdiffusiveProcess.Paper
