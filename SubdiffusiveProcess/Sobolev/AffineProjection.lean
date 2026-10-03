module

public import SubdiffusiveProcess.Geometry.CoordinateReflection
public import SubdiffusiveProcess.Lane4.Carriers

@[expose] public section

/-!
The L²(Q0)-orthogonal projection onto affine functions, on the reference unit cube, bounded on
`C^α` and fixing affine functions (paper P:3700-3737's missing ingredient for
`lem_affine_gcn_competitor`: the true best-affine-fit `ℓ_q` need not match `u` at the cube's
center, unlike the currently staged Taylor-shifted competitor).
-/

noncomputable section
open MeasureTheory Set SubdiffusiveProcess
open scoped ENNReal

namespace Paper
namespace AffineProjection

variable {d : ℕ} [NeZero d]

/-- The reference open unit cube, side `1`, centered at the origin. -/
def Q0 (d : ℕ) : Set (SpatialCoordinates d) :=
  (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))

/-- The reference domain used throughout: the closed unit cube. -/
def S0 (d : ℕ) : Set (SpatialCoordinates d) := closure (Q0 d)

theorem Q0_isOpen : IsOpen (Q0 d) := (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen

theorem S0_eq_pi : S0 d = Set.pi Set.univ (fun _ : Fin d => Set.Icc (-(1 / 2) : ℝ) (1 / 2)) := by
  unfold S0 Q0
  rw [centeredCube_eq_pi, closure_pi_set]
  congr 1; funext i
  have h0 : (0 : SpatialCoordinates d) i - 1 / 2 = -(1 / 2) ∧
      (0 : SpatialCoordinates d) i + 1 / 2 = (1 / 2 : ℝ) := by
    constructor <;> simp
  rw [h0.1, h0.2, closure_Ioo (show (-(1 / 2) : ℝ) ≠ 1 / 2 by norm_num)]

theorem mem_S0_iff (x : SpatialCoordinates d) : x ∈ S0 d ↔ ∀ i, |x i| ≤ 1 / 2 := by
  rw [S0_eq_pi]
  simp [Set.mem_pi, abs_le, Pi.le_def, forall_and]

theorem S0_isCompact : IsCompact (S0 d) := (centeredCube_isBounded (0 : SpatialCoordinates d)
  (one_pos)).isCompact_closure

theorem S0_measurableSet : MeasurableSet (S0 d) := measurableSet_closure

theorem Q0_volume : volume (Q0 d) = 1 := by
  simpa using! centeredCube_volume (0 : SpatialCoordinates d) (one_pos)

theorem S0_volume : volume (S0 d) = 1 := by
  have hsub : Q0 d ⊆ S0 d := subset_closure
  have hsup : S0 d ⊆ Metric.closedBall (0 : SpatialCoordinates d) (1 / 2) := by
    rw [S0_eq_pi]
    intro x hx
    rw [Metric.mem_closedBall, dist_pi_le_iff (by norm_num : (0:ℝ) ≤ 1/2)]
    intro j
    have hj := hx j (Set.mem_univ j)
    simp only [Real.dist_eq, Pi.zero_apply, sub_zero]
    simpa [abs_le] using! hj
  have hclosed : volume (Metric.closedBall (0 : SpatialCoordinates d) (1 / 2)) = 1 := by
    rw [Real.volume_pi_closedBall (0 : SpatialCoordinates d) (by norm_num : (0:ℝ) ≤ 1/2)]
    norm_num
  have h1 : volume (Q0 d) ≤ volume (S0 d) := measure_mono hsub
  have h2 : volume (S0 d) ≤ volume (Metric.closedBall (0 : SpatialCoordinates d) (1 / 2)) :=
    measure_mono hsup
  rw [Q0_volume] at h1
  rw [hclosed] at h2
  exact le_antisymm h2 h1

theorem S0_volume_real : volume.real (S0 d) = 1 := by rw [Measure.real, S0_volume]; simp

theorem Q0_ae_eq_S0 : (Q0 d) =ᵐ[volume] (S0 d) := by
  have hsub : Q0 d ⊆ S0 d := subset_closure
  have hQ0meas : MeasurableSet (Q0 d) := Q0_isOpen.measurableSet
  have hdiff : volume (S0 d \ Q0 d) = 0 := by
    have h := measure_diff hsub hQ0meas.nullMeasurableSet
      (by rw [Q0_volume]; exact ENNReal.one_ne_top)
    rwa [S0_volume, Q0_volume, tsub_self] at h
  apply measure_symmDiff_eq_zero_iff.mp
  rwa [symmDiff_of_le hsub]

theorem integral_Q0_eq_S0 (f : SpatialCoordinates d → ℝ) :
    ∫ x in Q0 d, f x = ∫ x in S0 d, f x := setIntegral_congr_set Q0_ae_eq_S0

theorem integrableOn_S0_of_continuousOn {f : SpatialCoordinates d → ℝ}
    (hf : ContinuousOn f (S0 d)) : IntegrableOn f (S0 d) volume :=
  hf.integrableOn_compact S0_isCompact

theorem integrableOn_Q0_of_continuousOn {f : SpatialCoordinates d → ℝ}
    (hf : ContinuousOn f (S0 d)) : IntegrableOn f (Q0 d) volume :=
  (integrableOn_S0_of_continuousOn hf).mono_set subset_closure

theorem exists_bound_of_continuousOn {v : SpatialCoordinates d → ℝ}
    (hv : ContinuousOn v (S0 d)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S0 d, |v x| ≤ C := by
  obtain ⟨C, hC⟩ := bddAbove_def.mp (S0_isCompact.bddAbove_image hv.norm)
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  exact le_trans (by simpa using! hC _ ⟨x, hx, rfl⟩) (le_max_left _ _)

theorem coordRefl_fixes_zero (I : Finset (Fin d)) :
    coordinateReflection (0 : SpatialCoordinates d) I 0 = 0 := by
  funext i; simp [coordinateReflection]

theorem integral_reflect_Q0 (I : Finset (Fin d)) (f : SpatialCoordinates d → ℝ) :
    ∫ x in Q0 d, f (coordinateReflection 0 I x) = ∫ y in Q0 d, f y := by
  have h := integral_coordinateReflection_cube (0 : SpatialCoordinates d) I 0 one_pos f
  rwa [coordRefl_fixes_zero] at h

theorem integral_coord_S0 (i : Fin d) : ∫ x in S0 d, x i = 0 := by
  rw [← integral_Q0_eq_S0]
  have hrefl := integral_reflect_Q0 ({i} : Finset (Fin d)) (fun x => x i)
  have hval : ∀ x : SpatialCoordinates d,
      coordinateReflection (0 : SpatialCoordinates d) {i} x i = -(x i) := by
    intro x; simp [coordinateReflection]
  simp only [hval] at hrefl
  rw [integral_neg] at hrefl
  linarith

theorem integral_coord_mul_coord_S0 (i j : Fin d) (hij : i ≠ j) :
    ∫ x in S0 d, x i * x j = 0 := by
  rw [← integral_Q0_eq_S0]
  have hrefl := integral_reflect_Q0 ({i} : Finset (Fin d)) (fun x => x i * x j)
  have hval : ∀ x : SpatialCoordinates d,
      coordinateReflection (0 : SpatialCoordinates d) {i} x i *
        coordinateReflection (0 : SpatialCoordinates d) {i} x j = -(x i * x j) := by
    intro x
    have h1 : coordinateReflection (0 : SpatialCoordinates d) {i} x i = -(x i) := by
      simp [coordinateReflection]
    have h2 : coordinateReflection (0 : SpatialCoordinates d) {i} x j = x j := by
      simp [coordinateReflection, Finset.mem_singleton, hij.symm]
    rw [h1, h2]; ring
  simp only [hval] at hrefl
  rw [integral_neg] at hrefl
  linarith

/-- The `i`-th coordinate's second moment: a fixed positive constant, `d`-dependent only. -/
def sigma (d : ℕ) [NeZero d] (i : Fin d) : ℝ := ∫ x in S0 d, (x i) ^ 2

theorem sigma_pos (i : Fin d) : 0 < sigma d i := by
  unfold sigma
  rw [← integral_Q0_eq_S0]
  have hf : IntegrableOn (fun x : SpatialCoordinates d => (x i) ^ 2) (Q0 d) volume :=
    integrableOn_Q0_of_continuousOn ((continuous_apply i).pow 2).continuousOn
  have hnonneg : 0 ≤ᵐ[volume.restrict (Q0 d)] (fun x : SpatialCoordinates d => (x i) ^ 2) :=
    Filter.Eventually.of_forall fun x => sq_nonneg (x i)
  apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hf).mpr
  apply IsOpen.measure_pos
  · have hsupp : (Function.support fun x : SpatialCoordinates d => (x i) ^ 2) =
        (fun x : SpatialCoordinates d => x i) ⁻¹' {y : ℝ | y ≠ 0} := by
      ext x; simp [Function.mem_support]
    rw [hsupp]
    exact (isOpen_ne.preimage (continuous_apply i)).inter Q0_isOpen
  · refine ⟨fun j => if j = i then (1 / 4 : ℝ) else 0, ?_, ?_⟩
    · simp
    · change (fun j => if j = i then (1 / 4 : ℝ) else 0) ∈ Metric.ball (0 : SpatialCoordinates d) (1 / 2)
      rw [Metric.mem_ball, dist_pi_lt_iff (by norm_num : (0:ℝ) < 1/2)]
      intro j
      rw [Real.dist_eq]
      split_ifs <;> norm_num

/-- The affine coefficients of the L²(S0)-orthogonal projection: `a` the mean, `b i` the
`i`-th (already-orthogonal) regression slope. -/
def coeffA (v : SpatialCoordinates d → ℝ) : ℝ := ∫ x in S0 d, v x

def coeffB (v : SpatialCoordinates d → ℝ) (i : Fin d) : ℝ :=
  (sigma d i)⁻¹ * ∫ x in S0 d, v x * x i

/-- The L²(S0)-orthogonal projection onto affine functions. -/
def proj (v : SpatialCoordinates d → ℝ) : SpatialCoordinates d → ℝ :=
  fun x => coeffA v + ∑ i, coeffB v i * x i

theorem coeffA_affine (c : ℝ) (m : Fin d → ℝ) :
    coeffA (fun x => c + ∑ i, m i * x i) = c := by
  unfold coeffA
  rw [integral_add (integrableOn_S0_of_continuousOn continuousOn_const)
    (integrableOn_S0_of_continuousOn (by fun_prop))]
  rw [integral_const, integral_finset_sum _ (fun i _ =>
    integrableOn_S0_of_continuousOn (by fun_prop : ContinuousOn (fun x => m i * x i) (S0 d)))]
  have : ∀ i, ∫ x in S0 d, m i * x i = 0 := by
    intro i
    rw [integral_const_mul, integral_coord_S0, mul_zero]
  simp [this, S0_volume_real]

theorem coeffB_affine (c : ℝ) (m : Fin d → ℝ) (i : Fin d) :
    coeffB (fun x => c + ∑ j, m j * x j) i = m i := by
  unfold coeffB
  have hpt : ∀ x : SpatialCoordinates d,
      (c + ∑ j, m j * x j) * x i = c * x i + ∑ j, m j * (x j * x i) := by
    intro x; rw [add_mul, Finset.sum_mul]; congr 1; apply Finset.sum_congr rfl
    intro j _; ring
  simp only [hpt]
  rw [integral_add (integrableOn_S0_of_continuousOn (by fun_prop))
    (integrableOn_S0_of_continuousOn (by fun_prop))]
  rw [integral_const_mul, integral_coord_S0, mul_zero, zero_add]
  rw [integral_finset_sum _ (fun j _ => integrableOn_S0_of_continuousOn
    (by fun_prop : ContinuousOn (fun x => m j * (x j * x i)) (S0 d)))]
  have hterm : ∀ j, ∫ x in S0 d, m j * (x j * x i) = if j = i then m i * sigma d i else 0 := by
    intro j
    rw [integral_const_mul]
    by_cases hji : j = i
    · subst hji
      rw [if_pos rfl]
      unfold sigma
      congr 1
      congr 1; funext x; ring
    · rw [integral_coord_mul_coord_S0 j i hji, mul_zero, if_neg hji]
  simp only [hterm, Finset.sum_ite_eq' Finset.univ i, Finset.mem_univ, if_true]
  field_simp [(sigma_pos i).ne']

/-- (i): the projection fixes every affine function. -/
theorem proj_affine (c : ℝ) (m : Fin d → ℝ) :
    proj (fun x => c + ∑ i, m i * x i) = (fun x => c + ∑ i, m i * x i) := by
  funext x
  simp only [proj, coeffA_affine, coeffB_affine]

theorem coeffA_proj (v : SpatialCoordinates d → ℝ) : coeffA (proj v) = coeffA v := by
  unfold proj; exact coeffA_affine (coeffA v) (coeffB v)

theorem coeffB_proj (v : SpatialCoordinates d → ℝ) (i : Fin d) :
    coeffB (proj v) i = coeffB v i := by
  unfold proj; exact coeffB_affine (coeffA v) (coeffB v) i

theorem proj_continuous (v : SpatialCoordinates d → ℝ) : Continuous (proj v) := by
  unfold proj; fun_prop

theorem coeffA_residual (v : SpatialCoordinates d → ℝ) (hv : ContinuousOn v (S0 d)) :
    coeffA (fun x => v x - proj v x) = 0 := by
  unfold coeffA
  rw [integral_sub (integrableOn_S0_of_continuousOn hv)
    (integrableOn_S0_of_continuousOn (proj_continuous v).continuousOn)]
  have h1 : (∫ x in S0 d, proj v x) = coeffA v := coeffA_proj v
  have h2 : coeffA v = ∫ x in S0 d, v x := rfl
  rw [h1, h2]; ring

theorem coeffB_residual (v : SpatialCoordinates d → ℝ) (hv : ContinuousOn v (S0 d)) (i : Fin d) :
    ∫ x in S0 d, (v x - proj v x) * x i = 0 := by
  have hpt : ∀ x : SpatialCoordinates d, (v x - proj v x) * x i = v x * x i - proj v x * x i :=
    fun x => by ring
  simp only [hpt]
  have he := integral_sub (integrableOn_S0_of_continuousOn (hv.mul (continuous_apply i).continuousOn))
    (integrableOn_S0_of_continuousOn
      ((proj_continuous v).continuousOn.mul (continuous_apply i).continuousOn))
  simp only [Pi.mul_apply, Pi.sub_apply] at he
  rw [he]
  have h1 : sigma d i * coeffB v i = ∫ x in S0 d, v x * x i := by
    unfold coeffB; rw [← mul_assoc, mul_inv_cancel₀ (sigma_pos i).ne', one_mul]
  have h2 : sigma d i * coeffB (proj v) i = ∫ x in S0 d, proj v x * x i := by
    unfold coeffB; rw [← mul_assoc, mul_inv_cancel₀ (sigma_pos i).ne', one_mul]
  rw [coeffB_proj] at h2
  rw [← h1, ← h2]; ring

/-- Orthogonality of the residual `v - proj v` to every affine function: the defining property
of the L²(S0)-projection. -/
theorem residual_orthogonal_affine (v : SpatialCoordinates d → ℝ) (hv : ContinuousOn v (S0 d))
    (c : ℝ) (m : Fin d → ℝ) :
    ∫ x in S0 d, (v x - proj v x) * (c + ∑ i, m i * x i) = 0 := by
  have hrescont : ContinuousOn (fun x => v x - proj v x) (S0 d) :=
    hv.sub (proj_continuous v).continuousOn
  have hresint : IntegrableOn (fun x => v x - proj v x) (S0 d) volume :=
    integrableOn_S0_of_continuousOn hrescont
  have hterm_int : ∀ i : Fin d,
      IntegrableOn (fun x => m i * ((v x - proj v x) * x i)) (S0 d) volume := fun i =>
    integrableOn_S0_of_continuousOn
      (continuousOn_const.mul (hrescont.mul (continuous_apply i).continuousOn))
  have hpt : ∀ x : SpatialCoordinates d,
      (v x - proj v x) * (c + ∑ i, m i * x i)
        = c * (v x - proj v x) + ∑ i, m i * ((v x - proj v x) * x i) := by
    intro x
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun i _ => by ring)
  simp only [hpt]
  rw [integral_add (hresint.const_mul c)
    (integrable_finset_sum Finset.univ (fun i _ => hterm_int i))]
  rw [integral_const_mul,
    show (∫ a in S0 d, v a - proj v a) = 0 from coeffA_residual v hv, mul_zero, zero_add]
  rw [integral_finset_sum _ (fun i _ => hterm_int i)]
  have hzero : ∀ i, ∫ x in S0 d, m i * ((v x - proj v x) * x i) = 0 := by
    intro i
    rw [integral_const_mul, coeffB_residual v hv i, mul_zero]
  simp [hzero]

/-- The L²(S0)-orthogonal-projection optimality: `proj v` is at least as good an affine
approximant of `v` as any other affine function, in the squared-`L²(S0)`-norm. This is the
"Optimality gives the same L² bound after adding `u - ū`" step of paper P:3700-3737 / Fix 5: no
extra pointwise correction term is needed, unlike the currently staged `z`-matching competitor. -/
theorem integral_sq_proj_le (v : SpatialCoordinates d → ℝ) (hv : ContinuousOn v (S0 d))
    (c : ℝ) (m : Fin d → ℝ) :
    ∫ x in S0 d, (v x - proj v x) ^ 2 ≤ ∫ x in S0 d, (v x - (c + ∑ i, m i * x i)) ^ 2 := by
  have hrescont : ContinuousOn (fun x => v x - proj v x) (S0 d) :=
    hv.sub (proj_continuous v).continuousOn
  have hqcont : Continuous (fun x : SpatialCoordinates d => proj v x - (c + ∑ i, m i * x i)) :=
    (proj_continuous v).sub (by fun_prop)
  have hresintsq : IntegrableOn (fun x => (v x - proj v x) ^ 2) (S0 d) volume :=
    integrableOn_S0_of_continuousOn (hrescont.pow 2)
  have hqintsq : IntegrableOn (fun x => (proj v x - (c + ∑ i, m i * x i)) ^ 2) (S0 d) volume :=
    integrableOn_S0_of_continuousOn (hqcont.continuousOn.pow 2)
  have hcrossint : IntegrableOn (fun x => (v x - proj v x) *
      (proj v x - (c + ∑ i, m i * x i))) (S0 d) volume :=
    integrableOn_S0_of_continuousOn (hrescont.mul hqcont.continuousOn)
  have hcross : ∫ x in S0 d, (v x - proj v x) *
      (proj v x - (c + ∑ i, m i * x i)) = 0 := by
    have hptproj : ∀ x : SpatialCoordinates d,
        proj v x - (c + ∑ i, m i * x i)
          = (coeffA v - c) + ∑ i, (coeffB v i - m i) * x i := by
      intro x
      unfold proj
      have hs : (∑ i, (coeffB v i - m i) * x i)
          = (∑ i, coeffB v i * x i) - ∑ i, m i * x i := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [hs]; ring
    simp only [hptproj]
    exact residual_orthogonal_affine v hv (coeffA v - c) (fun i => coeffB v i - m i)
  have hpt : ∀ x : SpatialCoordinates d,
      (v x - (c + ∑ i, m i * x i)) ^ 2
        = (v x - proj v x) ^ 2 + 2 * ((v x - proj v x) *
              (proj v x - (c + ∑ i, m i * x i))) +
          (proj v x - (c + ∑ i, m i * x i)) ^ 2 := by
    intro x; ring
  have hsum12 : IntegrableOn (fun x => (v x - proj v x) ^ 2 + 2 * ((v x - proj v x) *
      (proj v x - (c + ∑ i, m i * x i)))) (S0 d) volume :=
    integrableOn_S0_of_continuousOn ((hrescont.pow 2).add
      (continuousOn_const.mul (hrescont.mul hqcont.continuousOn)))
  have hcrossint2 : IntegrableOn (fun x => 2 * ((v x - proj v x) *
      (proj v x - (c + ∑ i, m i * x i)))) (S0 d) volume :=
    integrableOn_S0_of_continuousOn (continuousOn_const.mul (hrescont.mul hqcont.continuousOn))
  simp only [hpt]
  rw [integral_add hsum12 hqintsq, integral_add hresintsq hcrossint2, integral_const_mul,
    hcross, mul_zero]
  have hqnonneg : 0 ≤ ∫ x in S0 d, (proj v x - (c + ∑ i, m i * x i)) ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  linarith

/-! ### Property (ii): `proj` is bounded on `C^α`, and preserves constants (already property (i)).
This is nitro-7b's Corollary: `‖v - proj v‖_{C^β} ≤ (1+C)‖v-ℓ‖_{C^β}` for every affine `ℓ`. -/

theorem abs_coeffA_le (v : SpatialCoordinates d → ℝ) (C : ℝ)
    (hCv : ∀ x ∈ S0 d, |v x| ≤ C) : |coeffA v| ≤ C := by
  unfold coeffA
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := S0 d)
    (f := v) (by rw [S0_volume]; exact ENNReal.one_lt_top)
    (fun x hx => by simpa using! hCv x hx)
  simpa [S0_volume_real] using! h

theorem abs_coeffB_le (v : SpatialCoordinates d → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hCv : ∀ x ∈ S0 d, |v x| ≤ C) (i : Fin d) :
    |coeffB v i| ≤ (sigma d i)⁻¹ * (C / 2) := by
  unfold coeffB
  rw [abs_mul, abs_of_pos (inv_pos.mpr (sigma_pos i))]
  apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr (sigma_pos i)).le
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := S0 d)
    (f := fun x => v x * x i) (by rw [S0_volume]; exact ENNReal.one_lt_top)
    (fun x hx => by
      have hxi := (mem_S0_iff x).mp hx i
      rw [Real.norm_eq_abs, abs_mul]
      calc |v x| * |x i| ≤ C * (1 / 2) :=
            mul_le_mul (hCv x hx) hxi (abs_nonneg _) hC0
        _ = C / 2 := by ring)
  simpa [S0_volume_real] using! h

theorem abs_proj_le (v : SpatialCoordinates d → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hCv : ∀ x ∈ S0 d, |v x| ≤ C) (x : SpatialCoordinates d) (hx : x ∈ S0 d) :
    |proj v x| ≤ C * (1 + (∑ i, (sigma d i)⁻¹) / 4) := by
  unfold proj
  have hxb := (mem_S0_iff x).mp hx
  calc |coeffA v + ∑ i, coeffB v i * x i|
      ≤ |coeffA v| + |∑ i, coeffB v i * x i| := abs_add_le _ _
    _ ≤ |coeffA v| + ∑ i, |coeffB v i * x i| := by
        gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ C + ∑ i, ((sigma d i)⁻¹ * (C / 2)) * (1 / 2) := by
        gcongr with i _
        · exact abs_coeffA_le v C hCv
        rw [abs_mul]
        exact mul_le_mul (abs_coeffB_le v C hC0 hCv i) (hxb i) (abs_nonneg _)
          (mul_nonneg (inv_pos.mpr (sigma_pos i)).le (by linarith))
    _ = C * (1 + (∑ i, (sigma d i)⁻¹) / 4) := by
        have hsum : (∑ i, ((sigma d i)⁻¹ * (C / 2)) * (1 / 2))
            = (∑ i, (sigma d i)⁻¹) * (C / 4) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [hsum]; ring

theorem euclidean_dist_le_of_mem_S0 (x y : SpatialCoordinates d) (hx : x ∈ S0 d)
    (hy : y ∈ S0 d) : Real.sqrt (∑ j, (x j - y j) ^ 2) ≤ Real.sqrt d := by
  apply Real.sqrt_le_sqrt
  have hxb := (mem_S0_iff x).mp hx
  have hyb := (mem_S0_iff y).mp hy
  calc ∑ j, (x j - y j) ^ 2 ≤ ∑ _j : Fin d, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        have hxj := abs_le.1 (hxb j)
        have hyj := abs_le.1 (hyb j)
        have h1 : |x j - y j| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
        nlinarith [sq_abs (x j - y j)]
    _ = (d : ℝ) := by simp

theorem coord_diff_le_euclidean_dist (x y : SpatialCoordinates d) (i : Fin d) :
    |x i - y i| ≤ Real.sqrt (∑ j, (x j - y j) ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (f := fun j => (x j - y j) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem holderSeminorm_proj_le (v : SpatialCoordinates d → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hCv : ∀ x ∈ S0 d, |v x| ≤ C) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    Lane4.holderSeminorm β (S0 d) (proj v) ≤
      (∑ i, (sigma d i)⁻¹) * (C / 2) * (Real.sqrt d) ^ (1 - β) := by
  unfold Lane4.holderSeminorm
  apply Real.sSup_le
  · rintro w ⟨x, hx, y, hy, hxy, rfl⟩
    set r := Real.sqrt (∑ j, (x j - y j) ^ 2) with hr_def
    have hrpos : 0 < r := by
      rw [hr_def, Real.sqrt_pos]
      by_contra h
      push_neg at h
      have hnn : 0 ≤ ∑ j, (x j - y j) ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
      have hz : ∑ j, (x j - y j) ^ 2 = 0 := le_antisymm h hnn
      apply hxy
      funext j
      have hj0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).1 hz j
        (Finset.mem_univ j)
      nlinarith [sq_eq_zero_iff.1 hj0]
    have hBsum : |proj v x - proj v y| ≤ (∑ i, (sigma d i)⁻¹ * (C / 2)) * r := by
      unfold proj
      have heq : (coeffA v + ∑ i, coeffB v i * x i) - (coeffA v + ∑ i, coeffB v i * y i)
          = ∑ i, coeffB v i * (x i - y i) := by
        have hsum : (∑ i, coeffB v i * x i) - (∑ i, coeffB v i * y i)
            = ∑ i, coeffB v i * (x i - y i) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [← hsum]; ring
      rw [heq]
      calc |∑ i, coeffB v i * (x i - y i)| ≤ ∑ i, |coeffB v i * (x i - y i)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i, |coeffB v i| * |x i - y i| := Finset.sum_congr rfl
            (fun i _ => by rw [abs_mul])
        _ ≤ ∑ i, ((sigma d i)⁻¹ * (C / 2)) * r := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul (abs_coeffB_le v C hC0 hCv i) (coord_diff_le_euclidean_dist x y i)
              (abs_nonneg _) (mul_nonneg (inv_pos.mpr (sigma_pos i)).le (by linarith))
        _ = (∑ i, (sigma d i)⁻¹ * (C / 2)) * r := by rw [Finset.sum_mul]
    have hrle : r ≤ Real.sqrt d := euclidean_dist_le_of_mem_S0 x y hx hy
    have hpow : r ^ (1 - β) ≤ (Real.sqrt d) ^ (1 - β) :=
      Real.rpow_le_rpow hrpos.le hrle (by linarith)
    have hrw : r / r ^ β = r ^ (1 - β) := by
      rw [Real.rpow_sub hrpos, Real.rpow_one]
    have hcbnn : (0:ℝ) ≤ ∑ i, (sigma d i)⁻¹ * (C / 2) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (inv_pos.mpr (sigma_pos i)).le (by linarith))
    calc |proj v x - proj v y| / r ^ β
        ≤ ((∑ i, (sigma d i)⁻¹ * (C / 2)) * r) / r ^ β :=
          div_le_div_of_nonneg_right hBsum (Real.rpow_pos_of_pos hrpos β).le
      _ = (∑ i, (sigma d i)⁻¹ * (C / 2)) * (r / r ^ β) := by ring
      _ = (∑ i, (sigma d i)⁻¹ * (C / 2)) * r ^ (1 - β) := by rw [hrw]
      _ ≤ (∑ i, (sigma d i)⁻¹ * (C / 2)) * (Real.sqrt d) ^ (1 - β) :=
          mul_le_mul_of_nonneg_left hpow hcbnn
      _ = (∑ i, (sigma d i)⁻¹) * (C / 2) * (Real.sqrt d) ^ (1 - β) := by
          rw [← Finset.sum_mul, Finset.sum_mul]
  · have hd0 : (0:ℝ) ≤ (∑ i, (sigma d i)⁻¹) := Finset.sum_nonneg (fun i _ => (inv_pos.mpr (sigma_pos i)).le)
    have hpow0 : (0:ℝ) ≤ (Real.sqrt d) ^ (1 - β) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    exact mul_nonneg (mul_nonneg hd0 (by linarith)) hpow0

/-- **Property (ii)**: `proj` is bounded on `C^α` (nitro-7b's request). -/
theorem cAlphaNorm_proj_le (v : SpatialCoordinates d → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hCv : ∀ x ∈ S0 d, |v x| ≤ C) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    Lane4.cAlphaNorm β (S0 d) (proj v) ≤
      (1 + (∑ i, (sigma d i)⁻¹) / 4 + (∑ i, (sigma d i)⁻¹) * (Real.sqrt d) ^ (1 - β) / 2) * C := by
  unfold Lane4.cAlphaNorm
  have hsup : sSup {w : ℝ | ∃ x ∈ S0 d, w = |proj v x|} ≤ C * (1 + (∑ i, (sigma d i)⁻¹) / 4) := by
    apply Real.sSup_le
    · rintro w ⟨x, hx, rfl⟩
      exact abs_proj_le v C hC0 hCv x hx
    · have hd0 : (0:ℝ) ≤ (∑ i, (sigma d i)⁻¹) :=
        Finset.sum_nonneg (fun i _ => (inv_pos.mpr (sigma_pos i)).le)
      exact mul_nonneg hC0 (by linarith)
  have hsemi := holderSeminorm_proj_le v C hC0 hCv β hβ0 hβ1
  nlinarith [hsup, hsemi]

theorem coeffA_sub_affine (v : SpatialCoordinates d → ℝ) (hv : ContinuousOn v (S0 d))
    (c : ℝ) (m : Fin d → ℝ) :
    coeffA (fun x => v x - (c + ∑ i, m i * x i)) = coeffA v - c := by
  unfold coeffA
  rw [integral_sub (integrableOn_S0_of_continuousOn hv)
    (integrableOn_S0_of_continuousOn (by fun_prop))]
  congr 1
  exact coeffA_affine c m

theorem coeffB_sub_affine (v : SpatialCoordinates d → ℝ) (hv : ContinuousOn v (S0 d))
    (c : ℝ) (m : Fin d → ℝ) (i : Fin d) :
    coeffB (fun x => v x - (c + ∑ j, m j * x j)) i = coeffB v i - m i := by
  have hpt : ∀ x : SpatialCoordinates d,
      (v x - (c + ∑ j, m j * x j)) * x i = v x * x i - (c + ∑ j, m j * x j) * x i :=
    fun x => by ring
  unfold coeffB
  simp only [hpt]
  have he := integral_sub (integrableOn_S0_of_continuousOn (hv.mul (continuous_apply i).continuousOn))
    (integrableOn_S0_of_continuousOn (by fun_prop : ContinuousOn
      (fun x => (c + ∑ j, m j * x j) * x i) (S0 d)))
  simp only [Pi.mul_apply, Pi.sub_apply] at he
  rw [he]
  have h1 : sigma d i * coeffB v i = ∫ x in S0 d, v x * x i := by
    unfold coeffB; rw [← mul_assoc, mul_inv_cancel₀ (sigma_pos i).ne', one_mul]
  have h2 : sigma d i * m i = ∫ x in S0 d, (c + ∑ j, m j * x j) * x i := by
    have hb := coeffB_affine c m i
    unfold coeffB at hb
    rw [← hb, ← mul_assoc, mul_inv_cancel₀ (sigma_pos i).ne', one_mul]
  rw [← h1, ← h2]
  field_simp [(sigma_pos i).ne']

/-- The `proj` operator is linear, so it commutes with subtracting any affine competitor. -/
theorem proj_sub_affine (v : SpatialCoordinates d → ℝ) (hv : ContinuousOn v (S0 d))
    (c : ℝ) (m : Fin d → ℝ) :
    proj (fun x => v x - (c + ∑ i, m i * x i))
      = fun x => proj v x - (c + ∑ i, m i * x i) := by
  funext x
  unfold proj
  rw [coeffA_sub_affine v hv c m]
  have hb : ∀ i, coeffB (fun x => v x - (c + ∑ j, m j * x j)) i = coeffB v i - m i :=
    coeffB_sub_affine v hv c m
  simp only [hb]
  have hs : (∑ i, (coeffB v i - m i) * x i)
      = (∑ i, coeffB v i * x i) - ∑ i, m i * x i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hs]; ring

/- The final GCN-facing corollary ("‖v-Πv‖_{C^β} ≤ (1+C)‖v-ℓ‖_{C^β}") is NOT delivered here: it
needs (a) a `Lane4.cAlphaNorm` subadditivity lemma (short, standard sSup-of-a-sum argument, not
yet written in this file or the libraries) and (b) `w := v - ℓ` assumed `Lane4.IsHolderOn β (S0 d)`
(available at the GCN call site via `hHol`, but not assumable from a bare sup bound as I first
tried — a merely-bounded `w` need not be Hölder at all, so a sup-only hypothesis cannot give a
meaningful `cAlphaNorm` conclusion). `proj_sub_affine` above already supplies the needed identity
`proj(v-ℓ) = proj v - ℓ`; combining it with (a)+(b) is the remaining step. -/

end AffineProjection
end Paper





