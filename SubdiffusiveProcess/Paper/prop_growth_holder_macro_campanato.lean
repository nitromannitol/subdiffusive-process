import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Paper.prop_growth_holder_micro_campanato
import SubdiffusiveProcess.Paper.prop_growth_energy_assembly
import SubdiffusiveProcess.Paper.aux_macro_energy_recurrence
import SubdiffusiveProcess.Paper.aux_macro_moment_bank
import SubdiffusiveProcess.Paper.prop_growth_macro_energy
import SubdiffusiveProcess.Paper.lane4_lambda_inv_moments
import Mathlib.Tactic

-- ===== MCOsc =====
/-!
# Averages and variances on sets

`aux_prop_growth_holder_macro_campanato_avg S f` is `|S|⁻¹ ∫_S f` and
`aux_prop_growth_holder_macro_campanato_var S f` is `∫_S (f - avg_S f)²`, both for Lebesgue
measure.  These are exactly the `avg`/`osc` carriers of `in_6_16.holder_estimate`
(`osc S = √(|S|⁻¹ var S)`).
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators Pointwise
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- `|S|⁻¹ ∫_S f`. -/
def aux_prop_growth_holder_macro_campanato_avg (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) : ℝ :=
  (volume.real S)⁻¹ * ∫ y in S, f y

/-- `∫_S (f - avg_S f)²`. -/
def aux_prop_growth_holder_macro_campanato_var (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) : ℝ :=
  ∫ y in S, (f y - aux_prop_growth_holder_macro_campanato_avg S f) ^ 2

theorem aux_prop_growth_holder_macro_campanato_var_nonneg (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) : 0 ≤ aux_prop_growth_holder_macro_campanato_var S f :=
  setIntegral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => sq_nonneg _)

/-- The exact decomposition `∫_S (f - c)² = var_S f + |S| (avg_S f - c)²`. -/
theorem aux_prop_growth_holder_macro_campanato_integral_sq_sub_eq
    {S : Set (SpatialCoordinates d)} (hSfin : volume S ≠ ⊤) (hSpos : 0 < volume.real S)
    {f : SpatialCoordinates d → ℝ} (hf : MemLp f 2 (volume.restrict S)) (c : ℝ) :
    ∫ y in S, (f y - c) ^ 2 =
      aux_prop_growth_holder_macro_campanato_var S f +
        volume.real S * (aux_prop_growth_holder_macro_campanato_avg S f - c) ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSfin
  set m := aux_prop_growth_holder_macro_campanato_avg S f with hm
  have hfm : MemLp (fun y => f y - m) 2 (volume.restrict S) := hf.sub (memLp_const m)
  have hI1 : Integrable (fun y => (f y - m) ^ 2) (volume.restrict S) := hfm.integrable_sq
  have hI2 : Integrable (fun y => f y - m) (volume.restrict S) := hfm.integrable one_le_two
  have hlin : ∫ y in S, (f y - m) = 0 := by
    rw [integral_sub (hf.integrable one_le_two) (integrable_const m), setIntegral_const,
      smul_eq_mul, hm]
    unfold aux_prop_growth_holder_macro_campanato_avg
    field_simp
    ring
  have hexp : (fun y => (f y - c) ^ 2) =
      fun y => ((f y - m) ^ 2 + (2 * (m - c)) * (f y - m)) + (m - c) ^ 2 := by
    funext y; ring
  have e1 : ∫ y in S, ((f y - m) ^ 2 + 2 * (m - c) * (f y - m) + (m - c) ^ 2) =
      (∫ y in S, ((f y - m) ^ 2 + 2 * (m - c) * (f y - m))) + ∫ _y in S, (m - c) ^ 2 :=
    integral_add (hI1.add (hI2.const_mul _)) (integrable_const _)
  have e2 : ∫ y in S, ((f y - m) ^ 2 + 2 * (m - c) * (f y - m)) =
      (∫ y in S, (f y - m) ^ 2) + ∫ y in S, 2 * (m - c) * (f y - m) :=
    integral_add hI1 (hI2.const_mul _)
  rw [hexp, e1, e2, integral_const_mul, hlin, setIntegral_const, smul_eq_mul]
  unfold aux_prop_growth_holder_macro_campanato_var
  rw [← hm]
  ring

/-- The average minimizes the quadratic deviation. -/
theorem aux_prop_growth_holder_macro_campanato_var_le
    {S : Set (SpatialCoordinates d)} (hSfin : volume S ≠ ⊤) (hSpos : 0 < volume.real S)
    {f : SpatialCoordinates d → ℝ} (hf : MemLp f 2 (volume.restrict S)) (c : ℝ) :
    aux_prop_growth_holder_macro_campanato_var S f ≤ ∫ y in S, (f y - c) ^ 2 := by
  rw [aux_prop_growth_holder_macro_campanato_integral_sq_sub_eq hSfin hSpos hf c]
  have : 0 ≤ volume.real S * (aux_prop_growth_holder_macro_campanato_avg S f - c) ^ 2 :=
    mul_nonneg hSpos.le (sq_nonneg _)
  linarith

/-- `|S| (avg_S f - c)² ≤ ∫_S (f - c)²`. -/
theorem aux_prop_growth_holder_macro_campanato_vol_mul_sq_le
    {S : Set (SpatialCoordinates d)} (hSfin : volume S ≠ ⊤) (hSpos : 0 < volume.real S)
    {f : SpatialCoordinates d → ℝ} (hf : MemLp f 2 (volume.restrict S)) (c : ℝ) :
    volume.real S * (aux_prop_growth_holder_macro_campanato_avg S f - c) ^ 2 ≤
      ∫ y in S, (f y - c) ^ 2 := by
  rw [aux_prop_growth_holder_macro_campanato_integral_sq_sub_eq hSfin hSpos hf c]
  have := aux_prop_growth_holder_macro_campanato_var_nonneg S f
  linarith

/-- Monotonicity of a nonnegative quadratic integral in the set. -/
theorem aux_prop_growth_holder_macro_campanato_sq_mono {A B : Set (SpatialCoordinates d)}
    (hAB : A ⊆ B) (hBfin : volume B ≠ ⊤)
    {f : SpatialCoordinates d → ℝ} (hf : MemLp f 2 (volume.restrict B)) (c : ℝ) :
    ∫ y in A, (f y - c) ^ 2 ≤ ∫ y in B, (f y - c) ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hBfin
  have hI : Integrable (fun y => (f y - c) ^ 2) (volume.restrict B) :=
    (hf.sub (memLp_const c)).integrable_sq
  exact setIntegral_mono_set hI (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    (Filter.Eventually.of_forall hAB)

/-- **Sub-average bound.** For `A ⊆ B`, `|A| (avg_A f - avg_B f)² ≤ var_B f`. -/
theorem aux_prop_growth_holder_macro_campanato_avg_sub_sq_le
    {A B : Set (SpatialCoordinates d)} (hAB : A ⊆ B)
    (hBfin : volume B ≠ ⊤) (hApos : 0 < volume.real A)
    {f : SpatialCoordinates d → ℝ} (hf : MemLp f 2 (volume.restrict B)) :
    volume.real A * (aux_prop_growth_holder_macro_campanato_avg A f -
        aux_prop_growth_holder_macro_campanato_avg B f) ^ 2 ≤
      aux_prop_growth_holder_macro_campanato_var B f := by
  have hAfin : volume A ≠ ⊤ := (measure_mono hAB).trans_lt (lt_top_iff_ne_top.2 hBfin) |>.ne
  have hfA : MemLp f 2 (volume.restrict A) := hf.mono_measure (Measure.restrict_mono hAB le_rfl)
  refine (aux_prop_growth_holder_macro_campanato_vol_mul_sq_le hAfin hApos hfA _).trans ?_
  exact aux_prop_growth_holder_macro_campanato_sq_mono hAB hBfin hf _

/-- Cellwise split: `∫_T (f - c)² ≤ 2 var_T f + 2 |T| (avg_T f - c)²` (in fact equality up to
the factor `2`). -/
theorem aux_prop_growth_holder_macro_campanato_cell_split
    {T : Set (SpatialCoordinates d)} (hTfin : volume T ≠ ⊤) (hTpos : 0 < volume.real T)
    {f : SpatialCoordinates d → ℝ} (hf : MemLp f 2 (volume.restrict T)) (c : ℝ) :
    ∫ y in T, (f y - c) ^ 2 ≤
      2 * aux_prop_growth_holder_macro_campanato_var T f +
        2 * (volume.real T * (aux_prop_growth_holder_macro_campanato_avg T f - c) ^ 2) := by
  rw [aux_prop_growth_holder_macro_campanato_integral_sq_sub_eq hTfin hTpos hf c]
  have h1 := aux_prop_growth_holder_macro_campanato_var_nonneg T f
  have h2 : 0 ≤ volume.real T * (aux_prop_growth_holder_macro_campanato_avg T f - c) ^ 2 :=
    mul_nonneg hTpos.le (sq_nonneg _)
  linarith

/-- Perturbation: `var_S f ≤ 2 var_S g + 2 ∫_S (f - g)²`. -/
theorem aux_prop_growth_holder_macro_campanato_var_perturb
    {S : Set (SpatialCoordinates d)} (hSfin : volume S ≠ ⊤) (hSpos : 0 < volume.real S)
    {f g : SpatialCoordinates d → ℝ} (hf : MemLp f 2 (volume.restrict S))
    (hg : MemLp g 2 (volume.restrict S)) :
    aux_prop_growth_holder_macro_campanato_var S f ≤
      2 * aux_prop_growth_holder_macro_campanato_var S g + 2 * ∫ y in S, (f y - g y) ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSfin
  set m := aux_prop_growth_holder_macro_campanato_avg S g
  refine (aux_prop_growth_holder_macro_campanato_var_le hSfin hSpos hf m).trans ?_
  have hI1 : Integrable (fun y => (g y - m) ^ 2) (volume.restrict S) :=
    (hg.sub (memLp_const m)).integrable_sq
  have hI2 : Integrable (fun y => (f y - g y) ^ 2) (volume.restrict S) := (hf.sub hg).integrable_sq
  have hI0 : Integrable (fun y => (f y - m) ^ 2) (volume.restrict S) :=
    (hf.sub (memLp_const m)).integrable_sq
  unfold aux_prop_growth_holder_macro_campanato_var
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hI1.const_mul 2) (hI2.const_mul 2)]
  refine integral_mono hI0 ((hI1.const_mul 2).add (hI2.const_mul 2)) fun y => ?_
  have : (f y - m) = (g y - m) + (f y - g y) := by ring
  rw [this]
  nlinarith [sq_nonneg ((g y - m) - (f y - g y))]

/-- A nonnegative integral over a set covered almost everywhere by finitely many sets. -/
theorem aux_prop_growth_holder_macro_campanato_integral_le_sum_of_cover {ι : Type*}
    (s : Finset ι) (T : ι → Set (SpatialCoordinates d)) (hT : ∀ i, MeasurableSet (T i))
    {S : Set (SpatialCoordinates d)} (hS : MeasurableSet S)
    (hcov : ∀ᵐ y ∂volume, y ∈ S → ∃ i ∈ s, y ∈ T i)
    {g : SpatialCoordinates d → ℝ} (hg0 : ∀ y, 0 ≤ g y)
    (hgi : ∀ i ∈ s, IntegrableOn g (T i)) :
    ∫ y in S, g y ≤ ∑ i ∈ s, ∫ y in T i, g y := by
  classical
  have hsum_int : Integrable (fun y => ∑ i ∈ s, (T i).indicator g y) volume :=
    integrable_finset_sum s fun i hi => (integrable_indicator_iff (hT i)).2 (hgi i hi)
  have hpt : ∀ᵐ y ∂volume, S.indicator g y ≤ ∑ i ∈ s, (T i).indicator g y := by
    filter_upwards [hcov] with y hy
    by_cases hyS : y ∈ S
    · obtain ⟨i, hi, hyi⟩ := hy hyS
      rw [indicator_of_mem hyS]
      calc g y = (T i).indicator g y := (indicator_of_mem hyi g).symm
        _ ≤ ∑ j ∈ s, (T j).indicator g y :=
          Finset.single_le_sum (f := fun j => (T j).indicator g y)
            (fun j _ => indicator_nonneg (fun z _ => hg0 z) y) hi
    · rw [indicator_of_notMem hyS]
      exact Finset.sum_nonneg fun j _ => indicator_nonneg (fun z _ => hg0 z) y
  rw [← integral_indicator hS]
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
    indicator_nonneg (fun z _ => hg0 z) y) hsum_int hpt).trans (le_of_eq ?_)
  rw [integral_finset_sum s fun i hi => (integrable_indicator_iff (hT i)).2 (hgi i hi)]
  exact Finset.sum_congr rfl fun i _ => integral_indicator (hT i)

/-! ### Dilation invariance -/

/-- Averages are invariant under dilation. -/
theorem aux_prop_growth_holder_macro_campanato_avg_smul {s : ℝ} (hs : 0 < s)
    (S : Set (SpatialCoordinates d)) (_hS : MeasurableSet S) (f U : SpatialCoordinates d → ℝ)
    (hU : ∀ᵐ y ∂volume.restrict (s • S), U y = f (s⁻¹ • y)) :
    aux_prop_growth_holder_macro_campanato_avg (s • S) U =
      aux_prop_growth_holder_macro_campanato_avg S f := by
  unfold aux_prop_growth_holder_macro_campanato_avg
  have hint : ∫ y in s • S, U y = ∫ y in s • S, f (s⁻¹ • y) := integral_congr_ae hU
  rw [hint, aux_aux_macro_energy_recurrence_setIntegral_smul hs,
    aux_aux_macro_energy_recurrence_volume_real_smul hs]
  have hss : ∀ x : SpatialCoordinates d, s⁻¹ • s • x = x := fun x => by
    rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  simp only [hss]
  have hsd : s ^ d ≠ 0 := pow_ne_zero _ hs.ne'
  field_simp

/-- Variances scale by `s^d` under dilation. -/
theorem aux_prop_growth_holder_macro_campanato_var_smul {s : ℝ} (hs : 0 < s)
    (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) (f U : SpatialCoordinates d → ℝ)
    (hU : ∀ᵐ y ∂volume.restrict (s • S), U y = f (s⁻¹ • y)) :
    aux_prop_growth_holder_macro_campanato_var (s • S) U =
      s ^ d * aux_prop_growth_holder_macro_campanato_var S f := by
  unfold aux_prop_growth_holder_macro_campanato_var
  rw [aux_prop_growth_holder_macro_campanato_avg_smul hs S hS f U hU]
  set m := aux_prop_growth_holder_macro_campanato_avg S f
  have hint : ∫ y in s • S, (U y - m) ^ 2 = ∫ y in s • S, (f (s⁻¹ • y) - m) ^ 2 :=
    integral_congr_ae (hU.mono fun y hy => by dsimp only; rw [hy])
  rw [hint, aux_aux_macro_energy_recurrence_setIntegral_smul hs]
  have hss : ∀ x : SpatialCoordinates d, s⁻¹ • s • x = x := fun x => by
    rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  simp only [hss]




/-- On a subset of the domain, `setAverage` is the plain average of the representative. -/
theorem aux_prop_growth_holder_macro_campanato_setAverage_eq
    {Ω : Opens (SpatialCoordinates d)} {S : Set (SpatialCoordinates d)} (hS : MeasurableSet S)
    (hSΩ : S ⊆ Ω) (u : DomainL2 Ω) :
    setAverage S u = aux_prop_growth_holder_macro_campanato_avg S (u : SpatialCoordinates d → ℝ) := by
  unfold setAverage aux_prop_growth_holder_macro_campanato_avg
  rw [Measure.restrict_restrict hS, Set.inter_eq_left.2 hSΩ]

/-- The target's localized quadratic deviation is the plain variance. -/
theorem aux_prop_growth_holder_macro_campanato_target_eq
    {Ω : Opens (SpatialCoordinates d)} {S : Set (SpatialCoordinates d)} (hS : MeasurableSet S)
    (hSΩ : S ⊆ Ω) (u : DomainL2 Ω) :
    ∫ y in S, ((u : SpatialCoordinates d → ℝ) y - setAverage S u) ^ 2
        ∂volume.restrict (Ω : Set (SpatialCoordinates d)) =
      aux_prop_growth_holder_macro_campanato_var S (u : SpatialCoordinates d → ℝ) := by
  rw [aux_prop_growth_holder_macro_campanato_setAverage_eq hS hSΩ u]
  unfold aux_prop_growth_holder_macro_campanato_var
  rw [Measure.restrict_restrict hS, Set.inter_eq_left.2 hSΩ]

/-- `L²` classes on a domain are square integrable on its subsets. -/
theorem aux_prop_growth_holder_macro_campanato_memLp_sub
    {Ω : Opens (SpatialCoordinates d)} {S : Set (SpatialCoordinates d)}
    (hSΩ : S ⊆ Ω) (u : DomainL2 Ω) :
    MemLp (u : SpatialCoordinates d → ℝ) 2 (volume.restrict S) :=
  (Lp.memLp u).mono_measure (Measure.restrict_mono hSΩ le_rfl)

end Paper

-- ===== MCGeom =====
/-!
# Triadic cells of a unit cube

The depth-`j` cell with index `k ∈ ℤ^d` of the unit cube about `z` is the open (max-norm)
ball of radius `3^{-j}/2` about `z + 3^{-j} k`; it lies in the cube exactly when
`2|k_i| + 1 ≤ 3^j` for every coordinate.
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators Pointwise
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- The side `3^{-j}` of a depth-`j` cell. -/
def aux_prop_growth_holder_macro_campanato_side (j : ℕ) : ℝ := ((3 : ℝ) ^ j)⁻¹

theorem aux_prop_growth_holder_macro_campanato_side_pos (j : ℕ) :
    0 < aux_prop_growth_holder_macro_campanato_side j := by
  unfold aux_prop_growth_holder_macro_campanato_side; positivity

theorem aux_prop_growth_holder_macro_campanato_side_succ (j : ℕ) :
    aux_prop_growth_holder_macro_campanato_side j =
      3 * aux_prop_growth_holder_macro_campanato_side (j + 1) := by
  unfold aux_prop_growth_holder_macro_campanato_side
  rw [pow_succ]
  field_simp

theorem aux_prop_growth_holder_macro_campanato_side_mul_pow (j : ℕ) :
    aux_prop_growth_holder_macro_campanato_side j * (3 : ℝ) ^ j = 1 := by
  unfold aux_prop_growth_holder_macro_campanato_side
  exact inv_mul_cancel₀ (by positivity)

theorem aux_prop_growth_holder_macro_campanato_side_anti {i j : ℕ} (hij : i ≤ j) :
    aux_prop_growth_holder_macro_campanato_side j ≤ aux_prop_growth_holder_macro_campanato_side i := by
  unfold aux_prop_growth_holder_macro_campanato_side
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hij)

theorem aux_prop_growth_holder_macro_campanato_side_le_one (j : ℕ) :
    aux_prop_growth_holder_macro_campanato_side j ≤ 1 := by
  have := aux_prop_growth_holder_macro_campanato_side_anti (Nat.zero_le j)
  simpa [aux_prop_growth_holder_macro_campanato_side] using this

/-- The centre of the depth-`j` cell with index `k`. -/
def aux_prop_growth_holder_macro_campanato_center (z : SpatialCoordinates d) (j : ℕ)
    (k : Fin d → ℤ) : SpatialCoordinates d :=
  fun i => z i + aux_prop_growth_holder_macro_campanato_side j * (k i : ℝ)

/-- The open depth-`j` cell with index `k`. -/
def aux_prop_growth_holder_macro_campanato_cell (z : SpatialCoordinates d) (j : ℕ)
    (k : Fin d → ℤ) : Set (SpatialCoordinates d) :=
  ball (aux_prop_growth_holder_macro_campanato_center z j k)
    (aux_prop_growth_holder_macro_campanato_side j / 2)

/-- Admissible indices: the cell lies in the unit cube. -/
def aux_prop_growth_holder_macro_campanato_Adm (j : ℕ) (k : Fin d → ℤ) : Prop :=
  ∀ i, 2 * |k i| + 1 ≤ (3 : ℤ) ^ j

theorem aux_prop_growth_holder_macro_campanato_cell_measurable (z : SpatialCoordinates d) (j : ℕ)
    (k : Fin d → ℤ) : MeasurableSet (aux_prop_growth_holder_macro_campanato_cell z j k) :=
  measurableSet_ball

theorem aux_prop_growth_holder_macro_campanato_cell_volume (z : SpatialCoordinates d) (j : ℕ)
    (k : Fin d → ℤ) :
    volume.real (aux_prop_growth_holder_macro_campanato_cell z j k) =
      aux_prop_growth_holder_macro_campanato_side j ^ d := by
  have hs := aux_prop_growth_holder_macro_campanato_side_pos j
  unfold aux_prop_growth_holder_macro_campanato_cell
  rw [measureReal_def, Real.volume_pi_ball _ (half_pos hs), Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]
  ring_nf

theorem aux_prop_growth_holder_macro_campanato_cell_volume_ne_top (z : SpatialCoordinates d)
    (j : ℕ) (k : Fin d → ℤ) : volume (aux_prop_growth_holder_macro_campanato_cell z j k) ≠ ⊤ :=
  measure_ball_lt_top.ne

theorem aux_prop_growth_holder_macro_campanato_cell_volume_pos (z : SpatialCoordinates d)
    (j : ℕ) (k : Fin d → ℤ) :
    0 < volume.real (aux_prop_growth_holder_macro_campanato_cell z j k) := by
  rw [aux_prop_growth_holder_macro_campanato_cell_volume]
  exact pow_pos (aux_prop_growth_holder_macro_campanato_side_pos j) _

/-- Coordinatewise membership in a max-norm ball. -/
theorem aux_prop_growth_holder_macro_campanato_mem_ball_iff {c y : SpatialCoordinates d} {R : ℝ}
    (hR : 0 < R) : y ∈ ball c R ↔ ∀ i, |y i - c i| < R := by
  rw [mem_ball, dist_pi_lt_iff hR]
  simp only [Real.dist_eq]

theorem aux_prop_growth_holder_macro_campanato_mem_closedBall_iff {c y : SpatialCoordinates d}
    {R : ℝ} (hR : 0 ≤ R) : y ∈ closedBall c R ↔ ∀ i, |y i - c i| ≤ R := by
  rw [mem_closedBall, dist_pi_le_iff hR]
  simp only [Real.dist_eq]

/-- `3^j` is odd. -/
theorem aux_prop_growth_holder_macro_campanato_three_pow_odd (j : ℕ) :
    ∃ m : ℤ, (3 : ℤ) ^ j = 2 * m + 1 := by
  obtain ⟨m, hm⟩ := (show Odd (3 : ℤ) by decide).pow (n := j)
  exact ⟨m, hm⟩

/-- Real form of admissibility. -/
theorem aux_prop_growth_holder_macro_campanato_adm_real {j : ℕ} {k : Fin d → ℤ}
    (hk : aux_prop_growth_holder_macro_campanato_Adm j k) (i : Fin d) :
    aux_prop_growth_holder_macro_campanato_side j * (2 * |(k i : ℝ)| + 1) ≤ 1 := by
  have h := hk i
  have h' : (2 * |(k i : ℝ)| + 1) ≤ (3 : ℝ) ^ j := by
    have : ((2 * |k i| + 1 : ℤ) : ℝ) ≤ (((3 : ℤ) ^ j : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at this
    exact this
  have hs := aux_prop_growth_holder_macro_campanato_side_pos j
  calc aux_prop_growth_holder_macro_campanato_side j * (2 * |(k i : ℝ)| + 1)
      ≤ aux_prop_growth_holder_macro_campanato_side j * (3 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_left h' hs.le
    _ = 1 := aux_prop_growth_holder_macro_campanato_side_mul_pow j

/-- Admissible cells lie in the unit cube. -/
theorem aux_prop_growth_holder_macro_campanato_cell_subset (z : SpatialCoordinates d) {j : ℕ}
    {k : Fin d → ℤ} (hk : aux_prop_growth_holder_macro_campanato_Adm j k) :
    aux_prop_growth_holder_macro_campanato_cell z j k ⊆ ball z (1 / 2) := by
  intro y hy
  have hs := aux_prop_growth_holder_macro_campanato_side_pos j
  unfold aux_prop_growth_holder_macro_campanato_cell at hy
  rw [aux_prop_growth_holder_macro_campanato_mem_ball_iff (half_pos hs)] at hy
  rw [aux_prop_growth_holder_macro_campanato_mem_ball_iff (by norm_num)]
  intro i
  have h1 := hy i
  have h2 := aux_prop_growth_holder_macro_campanato_adm_real hk i
  unfold aux_prop_growth_holder_macro_campanato_center at h1
  have h3 : |y i - z i| ≤ |y i - (z i + aux_prop_growth_holder_macro_campanato_side j * k i)| +
      |aux_prop_growth_holder_macro_campanato_side j * k i| := by
    have := abs_add_le (y i - (z i + aux_prop_growth_holder_macro_campanato_side j * k i))
      (aux_prop_growth_holder_macro_campanato_side j * k i)
    rwa [show y i - (z i + aux_prop_growth_holder_macro_campanato_side j * k i) +
      aux_prop_growth_holder_macro_campanato_side j * k i = y i - z i by ring] at this
  rw [abs_mul, abs_of_pos hs] at h3
  nlinarith

/-- A point near an admissible cell. -/
theorem aux_prop_growth_holder_macro_campanato_closedCell_mem (z : SpatialCoordinates d) {j : ℕ}
    {k : Fin d → ℤ} (hk : aux_prop_growth_holder_macro_campanato_Adm j k)
    {p : SpatialCoordinates d}
    (hp : p ∈ closedBall (aux_prop_growth_holder_macro_campanato_center z j k)
      (aux_prop_growth_holder_macro_campanato_side j / 2)) :
    ∀ i, |p i - z i| ≤ 1 / 2 := by
  have hs := aux_prop_growth_holder_macro_campanato_side_pos j
  rw [aux_prop_growth_holder_macro_campanato_mem_closedBall_iff (by positivity)] at hp
  intro i
  have h1 := hp i
  have h2 := aux_prop_growth_holder_macro_campanato_adm_real hk i
  unfold aux_prop_growth_holder_macro_campanato_center at h1
  have h3 : |p i - z i| ≤ |p i - (z i + aux_prop_growth_holder_macro_campanato_side j * k i)| +
      |aux_prop_growth_holder_macro_campanato_side j * k i| := by
    have := abs_add_le (p i - (z i + aux_prop_growth_holder_macro_campanato_side j * k i))
      (aux_prop_growth_holder_macro_campanato_side j * k i)
    rwa [show p i - (z i + aux_prop_growth_holder_macro_campanato_side j * k i) +
      aux_prop_growth_holder_macro_campanato_side j * k i = p i - z i by ring] at this
  rw [abs_mul, abs_of_pos hs] at h3
  nlinarith

/-- **Rounding.** Every point of the open unit cube lies in the closure of an admissible
cell; off the grid hyperplanes it lies in the open cell. -/
theorem aux_prop_growth_holder_macro_campanato_round (z : SpatialCoordinates d) (j : ℕ)
    {y : SpatialCoordinates d} (hy : y ∈ ball z (1 / 2)) :
    ∃ k : Fin d → ℤ, aux_prop_growth_holder_macro_campanato_Adm j k ∧
      y ∈ closedBall (aux_prop_growth_holder_macro_campanato_center z j k)
        (aux_prop_growth_holder_macro_campanato_side j / 2) ∧
      ((∀ i, ∀ m : ℤ, y i ≠ z i + aux_prop_growth_holder_macro_campanato_side j * ((m : ℝ) - 1 / 2)) →
        y ∈ aux_prop_growth_holder_macro_campanato_cell z j k) := by
  have hs := aux_prop_growth_holder_macro_campanato_side_pos j
  have h3 : (0 : ℝ) < 3 ^ j := by positivity
  have hsp := aux_prop_growth_holder_macro_campanato_side_mul_pow j
  rw [aux_prop_growth_holder_macro_campanato_mem_ball_iff (by norm_num)] at hy
  let t : Fin d → ℝ := fun i => (y i - z i) * (3 : ℝ) ^ j
  let k : Fin d → ℤ := fun i => ⌊t i + 1 / 2⌋
  have hyt : ∀ i, y i = z i + aux_prop_growth_holder_macro_campanato_side j * t i := by
    intro i
    simp only [t]
    rw [mul_comm ((y i - z i)), ← mul_assoc, hsp, one_mul]
    ring
  have htb : ∀ i, |t i| < (3 : ℝ) ^ j / 2 := by
    intro i
    simp only [t]
    rw [abs_mul, abs_of_pos h3]
    have := hy i
    nlinarith
  have hfl : ∀ i, (k i : ℝ) ≤ t i + 1 / 2 ∧ t i + 1 / 2 < k i + 1 := fun i =>
    ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  refine ⟨k, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨m, hm⟩ := aux_prop_growth_holder_macro_campanato_three_pow_odd j
    have hmR : (3 : ℝ) ^ j = 2 * m + 1 := by exact_mod_cast hm
    have hb := htb i
    rw [abs_lt] at hb
    obtain ⟨h1, h2⟩ := hfl i
    have hup : (k i : ℝ) < m + 1 := by linarith
    have hlo : -(m : ℝ) - 1 < k i := by linarith
    have hup' : k i ≤ m := by exact_mod_cast (Int.lt_add_one_iff.1 (by exact_mod_cast hup))
    have hlo' : -m ≤ k i := by
      have : -m - 1 < k i := by exact_mod_cast hlo
      omega
    rw [hm]
    rcases abs_cases (k i) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
  · rw [aux_prop_growth_holder_macro_campanato_mem_closedBall_iff (by positivity)]
    intro i
    unfold aux_prop_growth_holder_macro_campanato_center
    rw [hyt i, show z i + aux_prop_growth_holder_macro_campanato_side j * t i -
      (z i + aux_prop_growth_holder_macro_campanato_side j * k i) =
        aux_prop_growth_holder_macro_campanato_side j * (t i - k i) by ring, abs_mul,
      abs_of_pos hs]
    obtain ⟨h1, h2⟩ := hfl i
    have : |t i - k i| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    nlinarith
  · intro hoff
    unfold aux_prop_growth_holder_macro_campanato_cell
    rw [aux_prop_growth_holder_macro_campanato_mem_ball_iff (half_pos hs)]
    intro i
    unfold aux_prop_growth_holder_macro_campanato_center
    rw [hyt i, show z i + aux_prop_growth_holder_macro_campanato_side j * t i -
      (z i + aux_prop_growth_holder_macro_campanato_side j * k i) =
        aux_prop_growth_holder_macro_campanato_side j * (t i - k i) by ring, abs_mul,
      abs_of_pos hs]
    obtain ⟨h1, h2⟩ := hfl i
    have hne : t i - k i ≠ -(1 / 2) := by
      intro heq
      apply hoff i (k i)
      rw [hyt i, show t i = k i - 1 / 2 by linarith]
    have : |t i - k i| < 1 / 2 := by
      rw [abs_lt]; constructor
      · rcases lt_or_eq_of_le (show -(1 / 2 : ℝ) ≤ t i - k i by linarith) with h | h
        · exact h
        · exact absurd h.symm hne
      · linarith
    nlinarith

/-- Almost every point avoids all grid hyperplanes of depth `j`. -/
theorem aux_prop_growth_holder_macro_campanato_ae_offgrid (z : SpatialCoordinates d) (j : ℕ) :
    ∀ᵐ y ∂(volume : Measure (SpatialCoordinates d)),
      ∀ i, ∀ m : ℤ, y i ≠ z i + aux_prop_growth_holder_macro_campanato_side j * ((m : ℝ) - 1 / 2) := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro m
  exact Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i _

/-- **Children.** A point of the closed parent lies in the closure of an admissible child
contained in the parent. -/
theorem aux_prop_growth_holder_macro_campanato_child (z : SpatialCoordinates d) {j : ℕ}
    {k : Fin d → ℤ} (hk : aux_prop_growth_holder_macro_campanato_Adm j k)
    {p : SpatialCoordinates d}
    (hp : p ∈ closedBall (aux_prop_growth_holder_macro_campanato_center z j k)
      (aux_prop_growth_holder_macro_campanato_side j / 2)) :
    ∃ k' : Fin d → ℤ, aux_prop_growth_holder_macro_campanato_Adm (j + 1) k' ∧
      aux_prop_growth_holder_macro_campanato_cell z (j + 1) k' ⊆
        aux_prop_growth_holder_macro_campanato_cell z j k ∧
      p ∈ closedBall (aux_prop_growth_holder_macro_campanato_center z (j + 1) k')
        (aux_prop_growth_holder_macro_campanato_side (j + 1) / 2) := by
  set s := aux_prop_growth_holder_macro_campanato_side j with hsdef
  set s' := aux_prop_growth_holder_macro_campanato_side (j + 1) with hs'def
  have hs' : 0 < s' := aux_prop_growth_holder_macro_campanato_side_pos (j + 1)
  have hss : s = 3 * s' := aux_prop_growth_holder_macro_campanato_side_succ j
  rw [aux_prop_growth_holder_macro_campanato_mem_closedBall_iff (by rw [hss]; linarith)] at hp
  let c := aux_prop_growth_holder_macro_campanato_center z j k
  let e : Fin d → ℤ := fun i =>
    if p i - c i < -(s' / 2) then -1 else if s' / 2 < p i - c i then 1 else 0
  have he : ∀ i, |e i| ≤ 1 := by
    intro i; simp only [e]; split_ifs <;> norm_num
  have hpe : ∀ i, |p i - c i - s' * e i| ≤ s' / 2 := by
    intro i
    have h := hp i
    rw [abs_le] at h ⊢
    simp only [e]
    split_ifs with h1 h2
    · push_cast; constructor <;> nlinarith
    · push_cast; constructor <;> nlinarith
    · push_cast; push_neg at h1 h2; constructor <;> linarith
  have hcenter : ∀ i, aux_prop_growth_holder_macro_campanato_center z (j + 1)
      (fun i => 3 * k i + e i) i = c i + s' * e i := by
    intro i
    simp only [aux_prop_growth_holder_macro_campanato_center, c]
    rw [← hs'def, ← hsdef, hss]
    push_cast
    ring
  refine ⟨fun i => 3 * k i + e i, ?_, ?_, ?_⟩
  · intro i
    have h1 := hk i
    have h2 := he i
    have h3 : |3 * k i + e i| ≤ 3 * |k i| + 1 := by
      calc |3 * k i + e i| ≤ |3 * k i| + |e i| := abs_add_le _ _
        _ = 3 * |k i| + |e i| := by rw [abs_mul]; norm_num
        _ ≤ 3 * |k i| + 1 := by linarith
    rw [pow_succ]
    nlinarith
  · intro y hy
    unfold aux_prop_growth_holder_macro_campanato_cell at hy ⊢
    rw [aux_prop_growth_holder_macro_campanato_mem_ball_iff (half_pos hs')] at hy
    rw [aux_prop_growth_holder_macro_campanato_mem_ball_iff (half_pos (aux_prop_growth_holder_macro_campanato_side_pos j))]
    intro i
    have h1 := hy i
    rw [hcenter i] at h1
    have h2 := he i
    have h2' : |(e i : ℝ)| ≤ 1 := by exact_mod_cast h2
    change |y i - c i| < s / 2
    have h3 : |y i - c i| ≤ |y i - (c i + s' * e i)| + |s' * e i| := by
      have := abs_add_le (y i - (c i + s' * e i)) (s' * e i)
      rwa [show y i - (c i + s' * e i) + s' * e i = y i - c i by ring] at this
    rw [abs_mul, abs_of_pos hs'] at h3
    rw [hss]
    nlinarith
  · rw [aux_prop_growth_holder_macro_campanato_mem_closedBall_iff (by positivity)]
    intro i
    rw [hcenter i, show p i - (c i + s' * e i) = p i - c i - s' * e i by ring]
    exact hpe i

/-- A cell is inside the ball of radius its side about any point of its closure. -/
theorem aux_prop_growth_holder_macro_campanato_cell_subset_ball (z : SpatialCoordinates d)
    (j : ℕ) (k : Fin d → ℤ) {p : SpatialCoordinates d}
    (hp : p ∈ closedBall (aux_prop_growth_holder_macro_campanato_center z j k)
      (aux_prop_growth_holder_macro_campanato_side j / 2)) :
    aux_prop_growth_holder_macro_campanato_cell z j k ⊆
      ball p (aux_prop_growth_holder_macro_campanato_side j) := by
  intro y hy
  unfold aux_prop_growth_holder_macro_campanato_cell at hy
  rw [mem_ball] at hy ⊢
  rw [mem_closedBall] at hp
  calc dist y p ≤ dist y (aux_prop_growth_holder_macro_campanato_center z j k) +
        dist (aux_prop_growth_holder_macro_campanato_center z j k) p := dist_triangle _ _ _
    _ < aux_prop_growth_holder_macro_campanato_side j / 2 +
        aux_prop_growth_holder_macro_campanato_side j / 2 := by
        rw [dist_comm _ p]; linarith
    _ = aux_prop_growth_holder_macro_campanato_side j := by ring

/-- **Midpoints.** The midpoint of the centres of two neighbouring admissible cells lies in the
open unit cube and in both closed cells. -/
theorem aux_prop_growth_holder_macro_campanato_midpoint (z : SpatialCoordinates d) {j : ℕ}
    {k k' : Fin d → ℤ} (hk : aux_prop_growth_holder_macro_campanato_Adm j k)
    (hk' : aux_prop_growth_holder_macro_campanato_Adm j k') (hkk : ∀ i, |k i - k' i| ≤ 1) :
    let p : SpatialCoordinates d := fun i =>
      z i + aux_prop_growth_holder_macro_campanato_side j * (((k i : ℝ) + k' i) / 2)
    p ∈ ball z (1 / 2) ∧
      p ∈ closedBall (aux_prop_growth_holder_macro_campanato_center z j k)
        (aux_prop_growth_holder_macro_campanato_side j / 2) ∧
      p ∈ closedBall (aux_prop_growth_holder_macro_campanato_center z j k')
        (aux_prop_growth_holder_macro_campanato_side j / 2) := by
  intro p
  have hs := aux_prop_growth_holder_macro_campanato_side_pos j
  have hdiff : ∀ i, |(k i : ℝ) - k' i| ≤ 1 := by
    intro i; have := hkk i; exact_mod_cast this
  refine ⟨?_, ?_, ?_⟩
  · rw [aux_prop_growth_holder_macro_campanato_mem_ball_iff (by norm_num)]
    intro i
    have h1 := aux_prop_growth_holder_macro_campanato_adm_real hk i
    have h2 := aux_prop_growth_holder_macro_campanato_adm_real hk' i
    simp only [p]
    rw [show z i + aux_prop_growth_holder_macro_campanato_side j * (((k i : ℝ) + k' i) / 2) - z i =
      aux_prop_growth_holder_macro_campanato_side j * (((k i : ℝ) + k' i) / 2) by ring, abs_mul,
      abs_of_pos hs, abs_div, abs_two]
    have h3 : |(k i : ℝ) + k' i| ≤ |(k i : ℝ)| + |(k' i : ℝ)| := abs_add_le _ _
    nlinarith
  · rw [aux_prop_growth_holder_macro_campanato_mem_closedBall_iff (by positivity)]
    intro i
    simp only [p, aux_prop_growth_holder_macro_campanato_center]
    rw [show z i + aux_prop_growth_holder_macro_campanato_side j * (((k i : ℝ) + k' i) / 2) -
      (z i + aux_prop_growth_holder_macro_campanato_side j * k i) =
        aux_prop_growth_holder_macro_campanato_side j * (((k' i : ℝ) - k i) / 2) by ring, abs_mul,
      abs_of_pos hs, abs_div, abs_two, abs_sub_comm]
    have := hdiff i
    nlinarith
  · rw [aux_prop_growth_holder_macro_campanato_mem_closedBall_iff (by positivity)]
    intro i
    simp only [p, aux_prop_growth_holder_macro_campanato_center]
    rw [show z i + aux_prop_growth_holder_macro_campanato_side j * (((k i : ℝ) + k' i) / 2) -
      (z i + aux_prop_growth_holder_macro_campanato_side j * k' i) =
        aux_prop_growth_holder_macro_campanato_side j * (((k i : ℝ) - k' i) / 2) by ring, abs_mul,
      abs_of_pos hs, abs_div, abs_two]
    have := hdiff i
    nlinarith

/-- **Neighbours.** Cells meeting a ball of radius at most half their side about a point of a
closed cell have indices within one of that cell's index. -/
theorem aux_prop_growth_holder_macro_campanato_neighbour (z : SpatialCoordinates d) {j : ℕ}
    {k k0 : Fin d → ℤ} {x y : SpatialCoordinates d} {ρ : ℝ}
    (hρ : ρ ≤ aux_prop_growth_holder_macro_campanato_side j / 2)
    (hx : x ∈ closedBall (aux_prop_growth_holder_macro_campanato_center z j k0)
      (aux_prop_growth_holder_macro_campanato_side j / 2))
    (hy : y ∈ aux_prop_growth_holder_macro_campanato_cell z j k) (hxy : y ∈ ball x ρ) :
    ∀ i, |k i - k0 i| ≤ 1 := by
  have hs := aux_prop_growth_holder_macro_campanato_side_pos j
  have hρ0 : 0 < ρ := lt_of_le_of_lt dist_nonneg (mem_ball.1 hxy)
  rw [aux_prop_growth_holder_macro_campanato_mem_closedBall_iff (by positivity)] at hx
  unfold aux_prop_growth_holder_macro_campanato_cell at hy
  rw [aux_prop_growth_holder_macro_campanato_mem_ball_iff (half_pos hs)] at hy
  rw [aux_prop_growth_holder_macro_campanato_mem_ball_iff hρ0] at hxy
  intro i
  have h1 := hx i
  have h2 := hy i
  have h3 := hxy i
  unfold aux_prop_growth_holder_macro_campanato_center at h1 h2
  have h4 : |aux_prop_growth_holder_macro_campanato_side j * ((k i : ℝ) - k0 i)| <
      3 / 2 * aux_prop_growth_holder_macro_campanato_side j := by
    have e : aux_prop_growth_holder_macro_campanato_side j * ((k i : ℝ) - k0 i) =
        (x i - (z i + aux_prop_growth_holder_macro_campanato_side j * k0 i)) -
          (y i - (z i + aux_prop_growth_holder_macro_campanato_side j * k i)) + (y i - x i) := by
      ring
    rw [e]
    calc _ ≤ |(x i - (z i + aux_prop_growth_holder_macro_campanato_side j * k0 i)) -
            (y i - (z i + aux_prop_growth_holder_macro_campanato_side j * k i))| + |y i - x i| :=
          abs_add_le _ _
      _ ≤ |x i - (z i + aux_prop_growth_holder_macro_campanato_side j * k0 i)| +
            |y i - (z i + aux_prop_growth_holder_macro_campanato_side j * k i)| + |y i - x i| := by
          gcongr; exact abs_sub _ _
      _ < _ := by linarith
  rw [abs_mul, abs_of_pos hs] at h4
  have h5 : |(k i : ℝ) - k0 i| < 3 / 2 := by
    by_contra hcon; push_neg at hcon; nlinarith
  have h6 : |k i - k0 i| < 2 := by
    have : ((|k i - k0 i| : ℤ) : ℝ) < 3 / 2 := by push_cast; exact h5
    have : ((|k i - k0 i| : ℤ) : ℝ) < 2 := by linarith
    exact_mod_cast this
  omega

end Paper

-- ===== MCUnit =====
/-!
# The deterministic unit-cube Campanato assembly

Inputs, on the unit cube `Q = ball z (1/2)`:
* (grid) every admissible depth-`j` cell with `P0 ≤ j ≤ n` has `var ≤ (Cg 3^{-αj} X)² |cell|`;
* (wavelength) every ball of radius `ρmin ≤ ρ ≤ 3^{-n}` about a point of `Q` has
  `var ≤ W² ρ^{2α} |B ∩ Q|`;
* (root) `var_Q ≤ X0²`.
Output: every ball `B(x,ρ) ∩ Q`, `x ∈ Q`, `ρmin ≤ ρ ≤ 1`, has
`var ≤ (Kd (Cg X + W + (2·3^{P0})^{α+d/2} X0))² ρ^{2α} |B ∩ Q|`, with `Kd = Kd(d, α)`.
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators Pointwise
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- `3^{-(j+i)α} = 3^{-jα} (3^{-α})^i`. -/
theorem aux_prop_growth_holder_macro_campanato_side_rpow_add (α : ℝ) (j i : ℕ) :
    aux_prop_growth_holder_macro_campanato_side (j + i) ^ α =
      aux_prop_growth_holder_macro_campanato_side j ^ α *
        (aux_prop_growth_holder_macro_campanato_side 1 ^ α) ^ i := by
  have h1 : aux_prop_growth_holder_macro_campanato_side (j + i) =
      aux_prop_growth_holder_macro_campanato_side j * aux_prop_growth_holder_macro_campanato_side 1 ^ i := by
    unfold aux_prop_growth_holder_macro_campanato_side
    rw [pow_add, mul_inv, pow_one, inv_pow]
  have h0 : 0 ≤ aux_prop_growth_holder_macro_campanato_side 1 :=
    (aux_prop_growth_holder_macro_campanato_side_pos 1).le
  rw [h1, Real.mul_rpow (aux_prop_growth_holder_macro_campanato_side_pos j).le (pow_nonneg h0 _),
    ← Real.rpow_natCast (aux_prop_growth_holder_macro_campanato_side 1) i, ← Real.rpow_mul h0,
    mul_comm (i : ℝ), Real.rpow_mul h0, Real.rpow_natCast]

/-- The ratio `3^{-α}` lies in `[0,1)`. -/
theorem aux_prop_growth_holder_macro_campanato_ratio_lt (α : ℝ) (hα : 0 < α) :
    0 ≤ aux_prop_growth_holder_macro_campanato_side 1 ^ α ∧
      aux_prop_growth_holder_macro_campanato_side 1 ^ α < 1 := by
  have h0 := aux_prop_growth_holder_macro_campanato_side_pos 1
  refine ⟨Real.rpow_nonneg h0.le _, Real.rpow_lt_one h0.le ?_ hα⟩
  unfold aux_prop_growth_holder_macro_campanato_side; norm_num

/-- Geometric sums. -/
theorem aux_prop_growth_holder_macro_campanato_geom_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (m : ℕ) : ∑ i ∈ Finset.range m, q ^ i ≤ (1 - q)⁻¹ := by
  have h := geom_sum_mul_neg q m
  have hpos : 0 < 1 - q := by linarith
  rw [← one_div, le_div_iff₀ hpos, h]
  linarith [pow_nonneg hq0 m]

/-- `|a| ≤ b` from `a² ≤ b²`, `0 ≤ b`. -/
theorem aux_prop_growth_holder_macro_campanato_abs_le_of_sq {a b : ℝ} (hb : 0 ≤ b)
    (h : a ^ 2 ≤ b ^ 2) : |a| ≤ b :=
  (sq_le_sq₀ (abs_nonneg a) hb).1 (by rwa [sq_abs])

/-- `x^{2α} = (x^α)²`. -/
theorem aux_prop_growth_holder_macro_campanato_rpow_two_mul {x : ℝ} (hx : 0 ≤ x) (α : ℝ) :
    x ^ (2 * α) = (x ^ α) ^ 2 := by
  rw [← Real.rpow_natCast (x ^ α) 2, ← Real.rpow_mul hx]
  norm_num
  ring_nf

/-- Volume of a ball cut by the unit cube. -/
theorem aux_prop_growth_holder_macro_campanato_ballcut_volume_le (z p : SpatialCoordinates d)
    {s : ℝ} (hs : 0 < s) :
    volume.real (ball p s ∩ ball z (1 / 2)) ≤ (2 * s) ^ d := by
  have h := measureReal_mono (μ := volume) (Set.inter_subset_left : ball p s ∩ ball z (1 / 2) ⊆ ball p s)
    measure_ball_lt_top.ne
  have hb : volume.real (ball p s) = (2 * s) ^ d := by
    rw [measureReal_def, Real.volume_pi_ball p hs, Fintype.card_fin,
      ENNReal.toReal_ofReal (by positivity)]
  exact h.trans_eq hb

theorem aux_prop_growth_holder_macro_campanato_ballcut_pos (z : SpatialCoordinates d)
    {p : SpatialCoordinates d} (hp : p ∈ ball z (1 / 2)) {s : ℝ} (hs : 0 < s) :
    0 < volume.real (ball p s ∩ ball z (1 / 2)) := by
  have hpos : 0 < volume (ball p s ∩ ball z (1 / 2)) :=
    (isOpen_ball.inter isOpen_ball).measure_pos volume ⟨p, mem_ball_self hs, hp⟩
  have hfin : volume (ball p s ∩ ball z (1 / 2)) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt measure_ball_lt_top).ne
  exact ENNReal.toReal_pos hpos.ne' hfin

theorem aux_prop_growth_holder_macro_campanato_ballcut_ne_top (z p : SpatialCoordinates d)
    (s : ℝ) : volume (ball p s ∩ ball z (1 / 2)) ≠ ⊤ :=
  ((measure_mono Set.inter_subset_left).trans_lt measure_ball_lt_top).ne

/-- **Descent** from an admissible cell to the wavelength ball about a point of its closure. -/
theorem aux_prop_growth_holder_macro_campanato_descent (z : SpatialCoordinates d)
    (v : SpatialCoordinates d → ℝ) (hv : MemLp v 2 (volume.restrict (ball z (1 / 2))))
    (α : ℝ) (n P0 : ℕ) (Cg X W : ℝ) (hCg : 0 ≤ Cg) (hX : 0 ≤ X) (hW : 0 ≤ W)
    (H1 : ∀ j : ℕ, P0 ≤ j → j ≤ n → ∀ k : Fin d → ℤ,
      aux_prop_growth_holder_macro_campanato_Adm j k →
      aux_prop_growth_holder_macro_campanato_var (aux_prop_growth_holder_macro_campanato_cell z j k) v ≤
        (Cg * aux_prop_growth_holder_macro_campanato_side j ^ α * X) ^ 2 *
          volume.real (aux_prop_growth_holder_macro_campanato_cell z j k))
    (H2 : ∀ p ∈ ball z (1 / 2),
      aux_prop_growth_holder_macro_campanato_var
          (ball p (aux_prop_growth_holder_macro_campanato_side n) ∩ ball z (1 / 2)) v ≤
        W ^ 2 * aux_prop_growth_holder_macro_campanato_side n ^ (2 * α) *
          volume.real (ball p (aux_prop_growth_holder_macro_campanato_side n) ∩ ball z (1 / 2))) :
    ∀ m j : ℕ, j + m = n → P0 ≤ j → ∀ k : Fin d → ℤ,
      aux_prop_growth_holder_macro_campanato_Adm j k →
      ∀ p ∈ ball z (1 / 2),
      p ∈ closedBall (aux_prop_growth_holder_macro_campanato_center z j k)
        (aux_prop_growth_holder_macro_campanato_side j / 2) →
      |aux_prop_growth_holder_macro_campanato_avg (aux_prop_growth_holder_macro_campanato_cell z j k) v -
        aux_prop_growth_holder_macro_campanato_avg
          (ball p (aux_prop_growth_holder_macro_campanato_side n) ∩ ball z (1 / 2)) v| ≤
        3 ^ d * Cg * X * ∑ i ∈ Finset.range m, aux_prop_growth_holder_macro_campanato_side (j + i) ^ α +
          2 ^ d * W * aux_prop_growth_holder_macro_campanato_side n ^ α := by
  intro m
  induction m with
  | zero =>
    intro j hj _ k hk p hpQ hp
    simp only [add_zero] at hj
    subst hj
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add]
    set s := aux_prop_growth_holder_macro_campanato_side j with hsdef
    have hs : 0 < s := aux_prop_growth_holder_macro_campanato_side_pos j
    set B := ball p s ∩ ball z (1 / 2) with hB
    have hcB : aux_prop_growth_holder_macro_campanato_cell z j k ⊆ B :=
      subset_inter (aux_prop_growth_holder_macro_campanato_cell_subset_ball z j k hp)
        (aux_prop_growth_holder_macro_campanato_cell_subset z hk)
    have hvB : MemLp v 2 (volume.restrict B) :=
      hv.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl)
    have hsub := aux_prop_growth_holder_macro_campanato_avg_sub_sq_le hcB
      (aux_prop_growth_holder_macro_campanato_ballcut_ne_top z p s)
      (aux_prop_growth_holder_macro_campanato_cell_volume_pos z j k) hvB
    rw [aux_prop_growth_holder_macro_campanato_cell_volume] at hsub
    have h2 := H2 p hpQ
    have hvol := aux_prop_growth_holder_macro_campanato_ballcut_volume_le z p hs
    have hsd : 0 < s ^ d := pow_pos hs d
    have hsa : 0 ≤ s ^ α := Real.rpow_nonneg hs.le α
    rw [aux_prop_growth_holder_macro_campanato_rpow_two_mul hs.le] at h2
    apply aux_prop_growth_holder_macro_campanato_abs_le_of_sq (by positivity)
    have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    have key : s ^ d * (aux_prop_growth_holder_macro_campanato_avg
        (aux_prop_growth_holder_macro_campanato_cell z j k) v -
          aux_prop_growth_holder_macro_campanato_avg B v) ^ 2 ≤
        s ^ d * (2 ^ d * W * s ^ α) ^ 2 := by
      calc _ ≤ _ := hsub
        _ ≤ W ^ 2 * (s ^ α) ^ 2 * volume.real B := h2
        _ ≤ W ^ 2 * (s ^ α) ^ 2 * (2 * s) ^ d :=
            mul_le_mul_of_nonneg_left hvol (by positivity)
        _ = s ^ d * (2 ^ d * (W * s ^ α) ^ 2) := by rw [mul_pow]; ring
        _ ≤ s ^ d * ((2 ^ d) ^ 2 * (W * s ^ α) ^ 2) := by
            gcongr
            nlinarith
        _ = s ^ d * (2 ^ d * W * s ^ α) ^ 2 := by ring
    exact le_of_mul_le_mul_left key hsd
  | succ m ih =>
    intro j hj hP k hk p hpQ hp
    obtain ⟨k', hk', hsub', hp'⟩ := aux_prop_growth_holder_macro_campanato_child z hk hp
    have hih := ih (j + 1) (by omega) (by omega) k' hk' p hpQ hp'
    set s := aux_prop_growth_holder_macro_campanato_side j with hsdef
    have hs : 0 < s := aux_prop_growth_holder_macro_campanato_side_pos j
    have hss : s = 3 * aux_prop_growth_holder_macro_campanato_side (j + 1) :=
      aux_prop_growth_holder_macro_campanato_side_succ j
    have hvC : MemLp v 2 (volume.restrict (aux_prop_growth_holder_macro_campanato_cell z j k)) :=
      hv.mono_measure (Measure.restrict_mono
        (aux_prop_growth_holder_macro_campanato_cell_subset z hk) le_rfl)
    have hstep0 := aux_prop_growth_holder_macro_campanato_avg_sub_sq_le hsub'
      (aux_prop_growth_holder_macro_campanato_cell_volume_ne_top z j k)
      (aux_prop_growth_holder_macro_campanato_cell_volume_pos z (j + 1) k') hvC
    have hH := H1 j hP (by omega) k hk
    rw [aux_prop_growth_holder_macro_campanato_cell_volume] at hstep0 hH
    have hs1 : 0 < aux_prop_growth_holder_macro_campanato_side (j + 1) :=
      aux_prop_growth_holder_macro_campanato_side_pos (j + 1)
    have hsd1 : 0 < aux_prop_growth_holder_macro_campanato_side (j + 1) ^ d := pow_pos hs1 d
    have hsa : 0 ≤ s ^ α := Real.rpow_nonneg hs.le α
    have h3d : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
    have hstep : |aux_prop_growth_holder_macro_campanato_avg (aux_prop_growth_holder_macro_campanato_cell z j k) v -
        aux_prop_growth_holder_macro_campanato_avg (aux_prop_growth_holder_macro_campanato_cell z (j + 1) k') v| ≤
        3 ^ d * Cg * X * s ^ α := by
      rw [abs_sub_comm]
      apply aux_prop_growth_holder_macro_campanato_abs_le_of_sq (by positivity)
      have key : aux_prop_growth_holder_macro_campanato_side (j + 1) ^ d *
          (aux_prop_growth_holder_macro_campanato_avg (aux_prop_growth_holder_macro_campanato_cell z (j + 1) k') v -
            aux_prop_growth_holder_macro_campanato_avg (aux_prop_growth_holder_macro_campanato_cell z j k) v) ^ 2 ≤
          aux_prop_growth_holder_macro_campanato_side (j + 1) ^ d * (3 ^ d * Cg * X * s ^ α) ^ 2 := by
        calc _ ≤ _ := hstep0
          _ ≤ (Cg * s ^ α * X) ^ 2 * s ^ d := hH
          _ = aux_prop_growth_holder_macro_campanato_side (j + 1) ^ d * (3 ^ d * (Cg * X * s ^ α) ^ 2) := by
              rw [hss, mul_pow]; ring
          _ ≤ aux_prop_growth_holder_macro_campanato_side (j + 1) ^ d * ((3 ^ d) ^ 2 * (Cg * X * s ^ α) ^ 2) := by
              gcongr
              nlinarith
          _ = _ := by ring
      exact le_of_mul_le_mul_left key hsd1
    have hsum : ∑ i ∈ Finset.range (m + 1), aux_prop_growth_holder_macro_campanato_side (j + i) ^ α =
        ∑ i ∈ Finset.range m, aux_prop_growth_holder_macro_campanato_side (j + 1 + i) ^ α + s ^ α := by
      rw [Finset.sum_range_succ']
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      omega
    rw [hsum]
    calc _ ≤ |aux_prop_growth_holder_macro_campanato_avg (aux_prop_growth_holder_macro_campanato_cell z j k) v -
          aux_prop_growth_holder_macro_campanato_avg (aux_prop_growth_holder_macro_campanato_cell z (j + 1) k') v| +
        |aux_prop_growth_holder_macro_campanato_avg (aux_prop_growth_holder_macro_campanato_cell z (j + 1) k') v -
          aux_prop_growth_holder_macro_campanato_avg
            (ball p (aux_prop_growth_holder_macro_campanato_side n) ∩ ball z (1 / 2)) v| :=
          abs_sub_le _ _ _
      _ ≤ 3 ^ d * Cg * X * s ^ α + (3 ^ d * Cg * X * ∑ i ∈ Finset.range m,
            aux_prop_growth_holder_macro_campanato_side (j + 1 + i) ^ α +
            2 ^ d * W * aux_prop_growth_holder_macro_campanato_side n ^ α) := add_le_add hstep hih
      _ = _ := by ring

/-- The neighbourhood family of cell indices. -/
def aux_prop_growth_holder_macro_campanato_family (j : ℕ) (k0 : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  (Fintype.piFinset fun i => Finset.Icc (k0 i - 1) (k0 i + 1)).filter
    (fun k => ∀ i, 2 * |k i| + 1 ≤ (3 : ℤ) ^ j)

theorem aux_prop_growth_holder_macro_campanato_family_card (j : ℕ) (k0 : Fin d → ℤ) :
    ((aux_prop_growth_holder_macro_campanato_family j k0).card : ℝ) ≤ 3 ^ d := by
  have h1 := Finset.card_filter_le (Fintype.piFinset fun i : Fin d => Finset.Icc (k0 i - 1) (k0 i + 1))
    (fun k => ∀ i, 2 * |k i| + 1 ≤ (3 : ℤ) ^ j)
  rw [Fintype.card_piFinset] at h1
  have h2 : ∏ i : Fin d, (Finset.Icc (k0 i - 1) (k0 i + 1)).card = 3 ^ d := by
    rw [Finset.prod_congr rfl (fun i _ => by rw [Int.card_Icc]; omega :
      ∀ i ∈ (Finset.univ : Finset (Fin d)), (Finset.Icc (k0 i - 1) (k0 i + 1)).card = 3)]
    simp
  rw [h2] at h1
  unfold aux_prop_growth_holder_macro_campanato_family
  exact_mod_cast h1

/-- The large-scale case: the root variance bounds everything once `ρ ≥ (2·3^{P0})⁻¹`. -/
theorem aux_prop_growth_holder_macro_campanato_unit_triv (z : SpatialCoordinates d)
    (v : SpatialCoordinates d → ℝ) (hv : MemLp v 2 (volume.restrict (ball z (1 / 2))))
    (α : ℝ) (hα0 : 0 < α) (P0 : ℕ) (X0 : ℝ) (_hX0 : 0 ≤ X0)
    (H3 : aux_prop_growth_holder_macro_campanato_var (ball z (1 / 2)) v ≤ X0 ^ 2)
    {x : SpatialCoordinates d} (hx : x ∈ ball z (1 / 2)) {ρ : ℝ}
    (hρP : (2 * 3 ^ P0 : ℝ)⁻¹ ≤ ρ) (hρ1 : ρ ≤ 1) :
    aux_prop_growth_holder_macro_campanato_var (ball x ρ ∩ ball z (1 / 2)) v ≤
      (((2 : ℝ) * 3 ^ P0) ^ (α + (d : ℝ) / 2) * X0) ^ 2 * ρ ^ (2 * α) *
        volume.real (ball x ρ ∩ ball z (1 / 2)) := by
  have hc1 : (1 : ℝ) ≤ 2 * 3 ^ P0 := by
    have : (1 : ℝ) ≤ 3 ^ P0 := one_le_pow₀ (by norm_num)
    linarith
  have hc0 : (0 : ℝ) < 2 * 3 ^ P0 := by linarith
  have hρ0 : 0 < ρ := lt_of_lt_of_le (inv_pos.2 hc0) hρP
  set Q := ball z (1 / 2)
  set S0 := ball x ρ ∩ Q
  have hS0fin : volume S0 ≠ ⊤ := aux_prop_growth_holder_macro_campanato_ballcut_ne_top z x ρ
  have hS0pos : 0 < volume.real S0 := aux_prop_growth_holder_macro_campanato_ballcut_pos z hx hρ0
  have hvS0 : MemLp v 2 (volume.restrict S0) :=
    hv.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl)
  have hvolS0 : ρ ^ d ≤ volume.real S0 :=
    aux_prop_growth_holder_micro_campanato_volume_ge z x (R := 1 / 2) hρ0 (by linarith) hx
  have hQfin : volume Q ≠ ⊤ := measure_ball_lt_top.ne
  have h1 := aux_prop_growth_holder_macro_campanato_var_le hS0fin hS0pos hvS0
    (aux_prop_growth_holder_macro_campanato_avg Q v)
  have h2 := aux_prop_growth_holder_macro_campanato_sq_mono (Set.inter_subset_right : S0 ⊆ Q)
    hQfin hv (aux_prop_growth_holder_macro_campanato_avg Q v)
  have hVQ : aux_prop_growth_holder_macro_campanato_var S0 v ≤ X0 ^ 2 := h1.trans (h2.trans H3)
  set Y : ℝ := ((2 : ℝ) * 3 ^ P0) ^ (α + (d : ℝ) / 2) with hYdef
  have he : 0 ≤ 2 * α + d := by positivity
  have hY2 : Y ^ 2 = (2 * 3 ^ P0 : ℝ) ^ (2 * α + d) := by
    rw [hYdef, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
    congr 1; push_cast; ring
  have hpow : ((2 * 3 ^ P0 : ℝ)⁻¹) ^ (2 * α + d) ≤ ρ ^ (2 * α + d) :=
    Real.rpow_le_rpow (by positivity) hρP he
  have hprod : 1 ≤ Y ^ 2 * (ρ ^ (2 * α) * ρ ^ d) := by
    rw [hY2, ← Real.rpow_natCast ρ d, ← Real.rpow_add hρ0]
    calc (1 : ℝ) = (2 * 3 ^ P0 : ℝ) ^ (2 * α + d) * ((2 * 3 ^ P0 : ℝ)⁻¹) ^ (2 * α + d) := by
          rw [← Real.mul_rpow hc0.le (by positivity), mul_inv_cancel₀ hc0.ne', Real.one_rpow]
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hρa : 0 ≤ ρ ^ (2 * α) := Real.rpow_nonneg hρ0.le _
  calc aux_prop_growth_holder_macro_campanato_var S0 v ≤ X0 ^ 2 := hVQ
    _ ≤ X0 ^ 2 * (Y ^ 2 * (ρ ^ (2 * α) * ρ ^ d)) := le_mul_of_one_le_right (sq_nonneg _) hprod
    _ = (Y * X0) ^ 2 * ρ ^ (2 * α) * ρ ^ d := by ring
    _ ≤ (Y * X0) ^ 2 * ρ ^ (2 * α) * volume.real S0 :=
        mul_le_mul_of_nonneg_left hvolS0 (mul_nonneg (sq_nonneg _) hρa)

/-- `6^{2α} ≤ 36` for `α ≤ 1`. -/
theorem aux_prop_growth_holder_macro_campanato_six_rpow {α : ℝ} (hα1 : α ≤ 1) :
    (6 : ℝ) ^ (2 * α) ≤ 36 := by
  calc (6 : ℝ) ^ (2 * α) ≤ 6 ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 36 := by norm_num

/-- Neighbouring cell averages differ by at most `D 3^{-jα}`. -/
theorem aux_prop_growth_holder_macro_campanato_pair (z : SpatialCoordinates d)
    (v : SpatialCoordinates d → ℝ) (hv : MemLp v 2 (volume.restrict (ball z (1 / 2))))
    (α : ℝ) (hα0 : 0 < α) (n P0 j : ℕ) (Cg X W : ℝ) (hCg : 0 ≤ Cg) (hX : 0 ≤ X) (hW : 0 ≤ W)
    (hPj : P0 ≤ j) (hjn : j ≤ n)
    (H1 : ∀ j : ℕ, P0 ≤ j → j ≤ n → ∀ k : Fin d → ℤ,
      aux_prop_growth_holder_macro_campanato_Adm j k →
      aux_prop_growth_holder_macro_campanato_var (aux_prop_growth_holder_macro_campanato_cell z j k) v ≤
        (Cg * aux_prop_growth_holder_macro_campanato_side j ^ α * X) ^ 2 *
          volume.real (aux_prop_growth_holder_macro_campanato_cell z j k))
    (H2 : ∀ p ∈ ball z (1 / 2),
      aux_prop_growth_holder_macro_campanato_var
          (ball p (aux_prop_growth_holder_macro_campanato_side n) ∩ ball z (1 / 2)) v ≤
        W ^ 2 * aux_prop_growth_holder_macro_campanato_side n ^ (2 * α) *
          volume.real (ball p (aux_prop_growth_holder_macro_campanato_side n) ∩ ball z (1 / 2)))
    {k k0 : Fin d → ℤ} (hk : aux_prop_growth_holder_macro_campanato_Adm j k)
    (hk0 : aux_prop_growth_holder_macro_campanato_Adm j k0) (hkk : ∀ i, |k i - k0 i| ≤ 1) :
    |aux_prop_growth_holder_macro_campanato_avg (aux_prop_growth_holder_macro_campanato_cell z j k) v -
      aux_prop_growth_holder_macro_campanato_avg (aux_prop_growth_holder_macro_campanato_cell z j k0) v| ≤
      2 * (3 ^ d * Cg * X * (1 - aux_prop_growth_holder_macro_campanato_side 1 ^ α)⁻¹ + 2 ^ d * W) *
        aux_prop_growth_holder_macro_campanato_side j ^ α := by
  obtain ⟨hq0, hq1⟩ := aux_prop_growth_holder_macro_campanato_ratio_lt α hα0
  set s := aux_prop_growth_holder_macro_campanato_side j with hsdef
  have hs0 : 0 < s := aux_prop_growth_holder_macro_campanato_side_pos j
  have hsa : 0 ≤ s ^ α := Real.rpow_nonneg hs0.le α
  set G := (1 - aux_prop_growth_holder_macro_campanato_side 1 ^ α)⁻¹
  have hdesc := aux_prop_growth_holder_macro_campanato_descent z v hv α n P0 Cg X W hCg hX hW H1 H2
  have hsum_geo : ∑ i ∈ Finset.range (n - j), aux_prop_growth_holder_macro_campanato_side (j + i) ^ α ≤
      s ^ α * G := by
    simp only [aux_prop_growth_holder_macro_campanato_side_rpow_add α j]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (aux_prop_growth_holder_macro_campanato_geom_le hq0 hq1 _) hsa
  have hsn : aux_prop_growth_holder_macro_campanato_side n ^ α ≤ s ^ α :=
    Real.rpow_le_rpow (aux_prop_growth_holder_macro_campanato_side_pos n).le
      (aux_prop_growth_holder_macro_campanato_side_anti hjn) hα0.le
  have hone : ∀ k', aux_prop_growth_holder_macro_campanato_Adm j k' → ∀ p ∈ ball z (1 / 2),
      p ∈ closedBall (aux_prop_growth_holder_macro_campanato_center z j k') (s / 2) →
      |aux_prop_growth_holder_macro_campanato_avg (aux_prop_growth_holder_macro_campanato_cell z j k') v -
        aux_prop_growth_holder_macro_campanato_avg
          (ball p (aux_prop_growth_holder_macro_campanato_side n) ∩ ball z (1 / 2)) v| ≤
        (3 ^ d * Cg * X * G + 2 ^ d * W) * s ^ α := by
    intro k' hk' p hp hpk
    have h := hdesc (n - j) j (by omega) hPj k' hk' p hp hpk
    have h3 : 0 ≤ 3 ^ d * Cg * X := by positivity
    have h4 : 0 ≤ (2 : ℝ) ^ d * W := by positivity
    calc _ ≤ _ := h
      _ ≤ 3 ^ d * Cg * X * (s ^ α * G) + 2 ^ d * W * s ^ α :=
          add_le_add (mul_le_mul_of_nonneg_left hsum_geo h3) (mul_le_mul_of_nonneg_left hsn h4)
      _ = (3 ^ d * Cg * X * G + 2 ^ d * W) * s ^ α := by ring
  obtain ⟨hpQ, hpk, hpk0⟩ := aux_prop_growth_holder_macro_campanato_midpoint z hk hk0 hkk
  have e1 := hone k hk _ hpQ hpk
  have e2 := hone k0 hk0 _ hpQ hpk0
  rw [abs_sub_comm] at e2
  calc _ ≤ _ := abs_sub_le _ (aux_prop_growth_holder_macro_campanato_avg
        (ball (fun i => z i + aux_prop_growth_holder_macro_campanato_side j * (((k i : ℝ) + k0 i) / 2))
          (aux_prop_growth_holder_macro_campanato_side n) ∩ ball z (1 / 2)) v) _
    _ ≤ _ := add_le_add e1 e2
    _ = _ := by ring

/-- The cover of `B(x,ρ) ∩ Q` by the neighbouring cells, and the resulting sum. -/
theorem aux_prop_growth_holder_macro_campanato_cover_sum (z : SpatialCoordinates d)
    (v : SpatialCoordinates d → ℝ) (hv : MemLp v 2 (volume.restrict (ball z (1 / 2))))
    (j : ℕ) (k0 : Fin d → ℤ) {x : SpatialCoordinates d} {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρs : 2 * ρ ≤ aux_prop_growth_holder_macro_campanato_side j) (hx : x ∈ ball z (1 / 2))
    (hxk0 : x ∈ closedBall (aux_prop_growth_holder_macro_campanato_center z j k0)
      (aux_prop_growth_holder_macro_campanato_side j / 2)) (c0 T : ℝ) (hT0 : 0 ≤ T)
    (hterm : ∀ k, aux_prop_growth_holder_macro_campanato_Adm j k → (∀ i, |k i - k0 i| ≤ 1) →
      ∫ y in aux_prop_growth_holder_macro_campanato_cell z j k, (v y - c0) ^ 2 ≤ T) :
    aux_prop_growth_holder_macro_campanato_var (ball x ρ ∩ ball z (1 / 2)) v ≤ 3 ^ d * T := by
  set S0 := ball x ρ ∩ ball z (1 / 2)
  have hS0m : MeasurableSet S0 := measurableSet_ball.inter measurableSet_ball
  have hS0fin : volume S0 ≠ ⊤ := aux_prop_growth_holder_macro_campanato_ballcut_ne_top z x ρ
  have hS0pos : 0 < volume.real S0 := aux_prop_growth_holder_macro_campanato_ballcut_pos z hx hρ0
  have hvS0 : MemLp v 2 (volume.restrict S0) :=
    hv.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl)
  set F := aux_prop_growth_holder_macro_campanato_family j k0 with hF
  have hmemF : ∀ k ∈ F, aux_prop_growth_holder_macro_campanato_Adm j k ∧ ∀ i, |k i - k0 i| ≤ 1 := by
    intro k hk
    refine ⟨(Finset.mem_filter.1 hk).2, fun i => ?_⟩
    have := (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hk).1) i
    rw [Finset.mem_Icc] at this
    rw [abs_le]; constructor <;> omega
  have hcov : ∀ᵐ y ∂volume, y ∈ S0 →
      ∃ k ∈ F, y ∈ aux_prop_growth_holder_macro_campanato_cell z j k := by
    filter_upwards [aux_prop_growth_holder_macro_campanato_ae_offgrid z j] with y hoff hyS
    obtain ⟨k, hk, -, hyk⟩ := aux_prop_growth_holder_macro_campanato_round z j hyS.2
    have hyk' := hyk hoff
    have hkk := aux_prop_growth_holder_macro_campanato_neighbour z (by linarith) hxk0 hyk' hyS.1
    refine ⟨k, ?_, hyk'⟩
    rw [hF, aux_prop_growth_holder_macro_campanato_family, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, hk⟩
    have := hkk i
    rw [abs_le] at this
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hint : ∀ k ∈ F, IntegrableOn (fun y => (v y - c0) ^ 2)
      (aux_prop_growth_holder_macro_campanato_cell z j k) := by
    intro k hk
    haveI : IsFiniteMeasure (volume.restrict (aux_prop_growth_holder_macro_campanato_cell z j k)) :=
      isFiniteMeasure_restrict.2 (aux_prop_growth_holder_macro_campanato_cell_volume_ne_top z j k)
    have hvk : MemLp v 2 (volume.restrict (aux_prop_growth_holder_macro_campanato_cell z j k)) :=
      hv.mono_measure (Measure.restrict_mono
        (aux_prop_growth_holder_macro_campanato_cell_subset z (hmemF k hk).1) le_rfl)
    exact (hvk.sub (memLp_const c0)).integrable_sq
  have hsplit := aux_prop_growth_holder_macro_campanato_integral_le_sum_of_cover F
    (aux_prop_growth_holder_macro_campanato_cell z j)
    (aux_prop_growth_holder_macro_campanato_cell_measurable z j) hS0m hcov
    (g := fun y => (v y - c0) ^ 2) (fun y => sq_nonneg _) hint
  have hsumT : ∑ k ∈ F, ∫ y in aux_prop_growth_holder_macro_campanato_cell z j k, (v y - c0) ^ 2 ≤
      3 ^ d * T := by
    calc _ ≤ ∑ _k ∈ F, T := Finset.sum_le_sum fun k hk => hterm k (hmemF k hk).1 (hmemF k hk).2
      _ = (F.card : ℝ) * T := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 3 ^ d * T := mul_le_mul_of_nonneg_right
          (aux_prop_growth_holder_macro_campanato_family_card j k0) hT0
  exact (aux_prop_growth_holder_macro_campanato_var_le hS0fin hS0pos hvS0 c0).trans
    (hsplit.trans hsumT)

/-- Arithmetic of the grid case. -/
theorem aux_prop_growth_holder_macro_campanato_grid_arith (d : ℕ) {α s ρ V D Kd' CX W : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hs0 : 0 < s) (hρ0 : 0 < ρ) (hs6 : s < 6 * ρ) (hV : ρ ^ d ≤ V)
    (hCX : 0 ≤ CX) (hD0 : 0 ≤ D) (_hW : 0 ≤ W) (hCD : CX + D ≤ Kd' * (CX + W)) :
    3 ^ d * (2 * s ^ d * (s ^ α) ^ 2 * (CX ^ 2 + D ^ 2)) ≤
      (9 * 18 ^ d * Kd' * (CX + W)) ^ 2 * ρ ^ (2 * α) * V := by
  have hsd : s ^ d ≤ 6 ^ d * V := by
    calc s ^ d ≤ (6 * ρ) ^ d := pow_le_pow_left₀ hs0.le hs6.le d
      _ = 6 ^ d * ρ ^ d := mul_pow _ _ _
      _ ≤ 6 ^ d * V := mul_le_mul_of_nonneg_left hV (by positivity)
  have hρa : 0 ≤ ρ ^ (2 * α) := Real.rpow_nonneg hρ0.le _
  have hsα : (s ^ α) ^ 2 ≤ 36 * ρ ^ (2 * α) := by
    rw [← aux_prop_growth_holder_macro_campanato_rpow_two_mul hs0.le]
    calc s ^ (2 * α) ≤ (6 * ρ) ^ (2 * α) := Real.rpow_le_rpow hs0.le hs6.le (by positivity)
      _ = 6 ^ (2 * α) * ρ ^ (2 * α) := Real.mul_rpow (by norm_num) hρ0.le
      _ ≤ 36 * ρ ^ (2 * α) :=
          mul_le_mul_of_nonneg_right (aux_prop_growth_holder_macro_campanato_six_rpow hα1) hρa
  have hCD2 : CX ^ 2 + D ^ 2 ≤ (Kd' * (CX + W)) ^ 2 := by
    have h1 : CX ^ 2 + D ^ 2 ≤ (CX + D) ^ 2 := by nlinarith [mul_nonneg hCX hD0]
    exact h1.trans (pow_le_pow_left₀ (add_nonneg hCX hD0) hCD 2)
  have hV0 : 0 ≤ V := (pow_nonneg hρ0.le d).trans hV
  have e1 : 2 * s ^ d * (s ^ α) ^ 2 * (CX ^ 2 + D ^ 2) ≤
      2 * (6 ^ d * V) * (36 * ρ ^ (2 * α)) * (Kd' * (CX + W)) ^ 2 :=
    mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hsd (by norm_num)) hsα (sq_nonneg _)
      (by positivity)) hCD2 (by positivity) (by positivity)
  have h18 : (1 : ℝ) ≤ 18 ^ d := one_le_pow₀ (by norm_num)
  have e2 : (3 : ℝ) ^ d * (6 ^ d) = 18 ^ d := by rw [← mul_pow]; norm_num
  have hX0 : 0 ≤ (Kd' * (CX + W)) ^ 2 * ρ ^ (2 * α) * V := by positivity
  calc 3 ^ d * (2 * s ^ d * (s ^ α) ^ 2 * (CX ^ 2 + D ^ 2))
      ≤ 3 ^ d * (2 * (6 ^ d * V) * (36 * ρ ^ (2 * α)) * (Kd' * (CX + W)) ^ 2) :=
        mul_le_mul_of_nonneg_left e1 (by positivity)
    _ = 72 * (3 ^ d * 6 ^ d) * ((Kd' * (CX + W)) ^ 2 * ρ ^ (2 * α) * V) := by ring
    _ = 72 * 18 ^ d * ((Kd' * (CX + W)) ^ 2 * ρ ^ (2 * α) * V) := by rw [e2]
    _ ≤ (9 * 18 ^ d) ^ 2 * ((Kd' * (CX + W)) ^ 2 * ρ ^ (2 * α) * V) := by
        apply mul_le_mul_of_nonneg_right _ hX0
        nlinarith
    _ = _ := by ring

/-- The grid case of the unit assembly. -/
theorem aux_prop_growth_holder_macro_campanato_unit_grid (z : SpatialCoordinates d)
    (v : SpatialCoordinates d → ℝ) (hv : MemLp v 2 (volume.restrict (ball z (1 / 2))))
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (n P0 j : ℕ) (Cg X W : ℝ) (hCg : 0 ≤ Cg) (hX : 0 ≤ X)
    (hW : 0 ≤ W) (hPj : P0 ≤ j) (hjn : j ≤ n)
    (H1 : ∀ j : ℕ, P0 ≤ j → j ≤ n → ∀ k : Fin d → ℤ,
      aux_prop_growth_holder_macro_campanato_Adm j k →
      aux_prop_growth_holder_macro_campanato_var (aux_prop_growth_holder_macro_campanato_cell z j k) v ≤
        (Cg * aux_prop_growth_holder_macro_campanato_side j ^ α * X) ^ 2 *
          volume.real (aux_prop_growth_holder_macro_campanato_cell z j k))
    (H2 : ∀ p ∈ ball z (1 / 2),
      aux_prop_growth_holder_macro_campanato_var
          (ball p (aux_prop_growth_holder_macro_campanato_side n) ∩ ball z (1 / 2)) v ≤
        W ^ 2 * aux_prop_growth_holder_macro_campanato_side n ^ (2 * α) *
          volume.real (ball p (aux_prop_growth_holder_macro_campanato_side n) ∩ ball z (1 / 2)))
    {x : SpatialCoordinates d} (hx : x ∈ ball z (1 / 2)) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hsj : 2 * ρ ≤ aux_prop_growth_holder_macro_campanato_side j)
    (hsj6 : aux_prop_growth_holder_macro_campanato_side j < 6 * ρ) :
    aux_prop_growth_holder_macro_campanato_var (ball x ρ ∩ ball z (1 / 2)) v ≤
      (9 * 18 ^ d * (1 + 2 * 3 ^ d * (1 - aux_prop_growth_holder_macro_campanato_side 1 ^ α)⁻¹ +
        2 ^ (d + 1)) * (Cg * X + W)) ^ 2 * ρ ^ (2 * α) *
        volume.real (ball x ρ ∩ ball z (1 / 2)) := by
  obtain ⟨hq0, hq1⟩ := aux_prop_growth_holder_macro_campanato_ratio_lt α hα0
  set G := (1 - aux_prop_growth_holder_macro_campanato_side 1 ^ α)⁻¹ with hGdef
  have hG0 : 0 ≤ G := inv_nonneg.2 (by linarith)
  set s := aux_prop_growth_holder_macro_campanato_side j with hsdef
  have hs0 : 0 < s := aux_prop_growth_holder_macro_campanato_side_pos j
  obtain ⟨k0, hk0, hxk0, -⟩ := aux_prop_growth_holder_macro_campanato_round z j hx
  set c0 := aux_prop_growth_holder_macro_campanato_avg (aux_prop_growth_holder_macro_campanato_cell z j k0) v
  set D := 2 * (3 ^ d * Cg * X * G + 2 ^ d * W) with hD
  have hD0 : 0 ≤ D := by positivity
  set T := 2 * s ^ d * (s ^ α) ^ 2 * ((Cg * X) ^ 2 + D ^ 2) with hT
  have hT0 : 0 ≤ T := by positivity
  have hterm : ∀ k, aux_prop_growth_holder_macro_campanato_Adm j k → (∀ i, |k i - k0 i| ≤ 1) →
      ∫ y in aux_prop_growth_holder_macro_campanato_cell z j k, (v y - c0) ^ 2 ≤ T := by
    intro k hk hkk
    have hvk : MemLp v 2 (volume.restrict (aux_prop_growth_holder_macro_campanato_cell z j k)) :=
      hv.mono_measure (Measure.restrict_mono
        (aux_prop_growth_holder_macro_campanato_cell_subset z hk) le_rfl)
    have h1 := aux_prop_growth_holder_macro_campanato_cell_split
      (aux_prop_growth_holder_macro_campanato_cell_volume_ne_top z j k)
      (aux_prop_growth_holder_macro_campanato_cell_volume_pos z j k) hvk c0
    have h2 := H1 j hPj hjn k hk
    have h3 := aux_prop_growth_holder_macro_campanato_pair z v hv α hα0 n P0 j Cg X W hCg hX hW
      hPj hjn H1 H2 hk hk0 hkk
    rw [aux_prop_growth_holder_macro_campanato_cell_volume] at h1 h2
    have h3' : (aux_prop_growth_holder_macro_campanato_avg
        (aux_prop_growth_holder_macro_campanato_cell z j k) v - c0) ^ 2 ≤ (D * s ^ α) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h3 2
    have hsd0 : 0 ≤ s ^ d := pow_nonneg hs0.le d
    calc _ ≤ _ := h1
      _ ≤ 2 * ((Cg * s ^ α * X) ^ 2 * s ^ d) + 2 * (s ^ d * (D * s ^ α) ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left h2 (by norm_num))
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3' hsd0) (by norm_num))
      _ = T := by rw [hT]; ring
  have hvar := aux_prop_growth_holder_macro_campanato_cover_sum z v hv j k0 hρ0 hsj hx hxk0 c0 T
    hT0 hterm
  have hV : ρ ^ d ≤ volume.real (ball x ρ ∩ ball z (1 / 2)) :=
    aux_prop_growth_holder_micro_campanato_volume_ge z x (R := 1 / 2) hρ0
      (by have := aux_prop_growth_holder_macro_campanato_side_le_one j; linarith) hx
  have hCD : Cg * X + D ≤ (1 + 2 * 3 ^ d * G + 2 ^ (d + 1)) * (Cg * X + W) := by
    rw [hD]
    have h0 : 0 ≤ Cg * X := mul_nonneg hCg hX
    have e : (2 : ℝ) ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
    rw [e]
    have : 0 ≤ 2 * 3 ^ d * G * W := by positivity
    have : 0 ≤ 2 * 2 ^ d * (Cg * X) := by positivity
    nlinarith
  exact hvar.trans (aux_prop_growth_holder_macro_campanato_grid_arith d hα0.le hα1 hs0 hρ0 hsj6 hV
    (mul_nonneg hCg hX) hD0 hW hCD)

/-- **The deterministic unit-cube Campanato assembly.** -/
theorem aux_prop_growth_holder_macro_campanato_unit (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ Kd : ℝ, 1 ≤ Kd ∧ ∀ (z : SpatialCoordinates d) (v : SpatialCoordinates d → ℝ),
      MemLp v 2 (volume.restrict (ball z (1 / 2))) →
      ∀ (n P0 : ℕ) (Cg X W X0 ρmin : ℝ), 0 ≤ Cg → 0 ≤ X → 0 ≤ W → 0 ≤ X0 → 0 < ρmin →
      ρmin ≤ aux_prop_growth_holder_macro_campanato_side n →
      (∀ j : ℕ, P0 ≤ j → j ≤ n → ∀ k : Fin d → ℤ,
        aux_prop_growth_holder_macro_campanato_Adm j k →
        aux_prop_growth_holder_macro_campanato_var (aux_prop_growth_holder_macro_campanato_cell z j k) v ≤
          (Cg * aux_prop_growth_holder_macro_campanato_side j ^ α * X) ^ 2 *
            volume.real (aux_prop_growth_holder_macro_campanato_cell z j k)) →
      (∀ p ∈ ball z (1 / 2), ∀ ρ : ℝ, ρmin ≤ ρ → ρ ≤ aux_prop_growth_holder_macro_campanato_side n →
        aux_prop_growth_holder_macro_campanato_var (ball p ρ ∩ ball z (1 / 2)) v ≤
          W ^ 2 * ρ ^ (2 * α) * volume.real (ball p ρ ∩ ball z (1 / 2))) →
      aux_prop_growth_holder_macro_campanato_var (ball z (1 / 2)) v ≤ X0 ^ 2 →
      ∀ x ∈ ball z (1 / 2), ∀ ρ : ℝ, ρmin ≤ ρ → ρ ≤ 1 →
        aux_prop_growth_holder_macro_campanato_var (ball x ρ ∩ ball z (1 / 2)) v ≤
          (Kd * (Cg * X + W + ((2 : ℝ) * 3 ^ P0) ^ (α + (d : ℝ) / 2) * X0)) ^ 2 * ρ ^ (2 * α) *
            volume.real (ball x ρ ∩ ball z (1 / 2)) := by
  obtain ⟨hq0, hq1⟩ := aux_prop_growth_holder_macro_campanato_ratio_lt α hα0
  set G := (1 - aux_prop_growth_holder_macro_campanato_side 1 ^ α)⁻¹ with hGdef
  have hG0 : 0 ≤ G := inv_nonneg.2 (by linarith)
  set Kd' : ℝ := 1 + 2 * 3 ^ d * G + 2 ^ (d + 1) with hKd'
  have hKd'1 : 1 ≤ Kd' := by
    rw [hKd']
    have : (0 : ℝ) ≤ 2 * 3 ^ d * G := by positivity
    have : (0 : ℝ) ≤ 2 ^ (d + 1) := by positivity
    linarith
  have h18 : (1 : ℝ) ≤ 18 ^ d := one_le_pow₀ (by norm_num)
  have hKd1 : 1 ≤ 9 * 18 ^ d * Kd' := by nlinarith
  refine ⟨9 * 18 ^ d * Kd', hKd1, ?_⟩
  intro z v hv n P0 Cg X W X0 ρmin hCg hX hW hX0 hρmin hρn H1 H2 H3 x hx ρ hρ1 hρ2
  have hρ0 : 0 < ρ := hρmin.trans_le hρ1
  set V := volume.real (ball x ρ ∩ ball z (1 / 2)) with hVdef
  have hV0 : 0 ≤ V := measureReal_nonneg
  have hρa : 0 ≤ ρ ^ (2 * α) := Real.rpow_nonneg hρ0.le _
  set Y : ℝ := ((2 : ℝ) * 3 ^ P0) ^ (α + (d : ℝ) / 2) with hYdef
  have hY0 : 0 ≤ Y := Real.rpow_nonneg (by positivity) _
  have hCX : 0 ≤ Cg * X := mul_nonneg hCg hX
  have hYX : 0 ≤ Y * X0 := mul_nonneg hY0 hX0
  -- monotonicity in the constant
  have hmono : ∀ A : ℝ, 0 ≤ A → A ≤ 9 * 18 ^ d * Kd' * (Cg * X + W + Y * X0) →
      A ^ 2 * ρ ^ (2 * α) * V ≤ (9 * 18 ^ d * Kd' * (Cg * X + W + Y * X0)) ^ 2 * ρ ^ (2 * α) * V := by
    intro A hA0 hA
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hA0 hA 2) hρa) hV0
  have hsum0 : 0 ≤ Cg * X + W + Y * X0 := by positivity
  have hbase : Cg * X + W + Y * X0 ≤ 9 * 18 ^ d * Kd' * (Cg * X + W + Y * X0) :=
    le_mul_of_one_le_left hsum0 hKd1
  have htriv : (2 * 3 ^ P0 : ℝ)⁻¹ ≤ ρ →
      aux_prop_growth_holder_macro_campanato_var (ball x ρ ∩ ball z (1 / 2)) v ≤
        (9 * 18 ^ d * Kd' * (Cg * X + W + Y * X0)) ^ 2 * ρ ^ (2 * α) * V := fun hρP =>
    (aux_prop_growth_holder_macro_campanato_unit_triv z v hv α hα0 P0 X0 hX0 H3 hx hρP hρ2).trans
      (hmono _ hYX (by linarith))
  by_cases hA : ρ ≤ aux_prop_growth_holder_macro_campanato_side n
  · exact (H2 x hx ρ hρ1 hA).trans (hmono _ hW (by linarith))
  push_neg at hA
  by_cases h2 : 2 * ρ ≤ 1
  swap
  · apply htriv
    push_neg at h2
    have : (2 * 3 ^ P0 : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      have : (1 : ℝ) ≤ 3 ^ P0 := one_le_pow₀ (by norm_num)
      linarith
    linarith
  obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near (x := (2 * ρ)⁻¹)
    (by rw [le_inv_comm₀ (by norm_num) (by positivity)]; simpa using h2) (by norm_num : (1 : ℝ) < 3)
  have hsj : 2 * ρ ≤ aux_prop_growth_holder_macro_campanato_side j := by
    unfold aux_prop_growth_holder_macro_campanato_side
    rw [le_inv_comm₀ (by positivity) (by positivity)]; exact hj1
  have hsj1 : aux_prop_growth_holder_macro_campanato_side (j + 1) < 2 * ρ := by
    unfold aux_prop_growth_holder_macro_campanato_side
    rw [inv_lt_comm₀ (by positivity) (by positivity)]; exact hj2
  have hsj6 : aux_prop_growth_holder_macro_campanato_side j < 6 * ρ := by
    rw [aux_prop_growth_holder_macro_campanato_side_succ j]; linarith
  by_cases hPj : P0 ≤ j
  swap
  · apply htriv
    push_neg at hPj
    have h1 : aux_prop_growth_holder_macro_campanato_side P0 ≤
        aux_prop_growth_holder_macro_campanato_side (j + 1) :=
      aux_prop_growth_holder_macro_campanato_side_anti (by omega)
    have : (2 * 3 ^ P0 : ℝ)⁻¹ = aux_prop_growth_holder_macro_campanato_side P0 / 2 := by
      unfold aux_prop_growth_holder_macro_campanato_side; rw [mul_inv]; ring
    rw [this]; linarith
  have hjn : j ≤ n := by
    by_contra hcon
    push_neg at hcon
    have := aux_prop_growth_holder_macro_campanato_side_anti hcon.le
    have := aux_prop_growth_holder_macro_campanato_side_pos j
    linarith
  have hg := aux_prop_growth_holder_macro_campanato_unit_grid z v hv α hα0 hα1 n P0 j Cg X W hCg hX
    hW hPj hjn H1 (fun p hp => H2 p hp _ hρn le_rfl) hx hρ0 hsj hsj6
  refine hg.trans (hmono _ (by positivity) ?_)
  have : 9 * 18 ^ d * Kd' * (Cg * X + W) ≤ 9 * 18 ^ d * Kd' * (Cg * X + W + Y * X0) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  exact this

end Paper

-- ===== MCFinite =====
/-!
# The finite-infrared grid oscillation estimate

`in_6_16.holder_estimate` (`e.Holder.estimate.boxes.local`) read on the unit cube: for a
coefficient `a' = c · a_L(3^N ·)` and the Dirichlet solution `u'`, every admissible depth-`j`
cell with `prefix ≤ j ≤ N` has
`var_cell u' ≤ (C 3^{-jα} (osc_Q u' + Cp (c ⟨b⟩)⁻¹ Kf + d Cφ))² |cell|`.
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators Pointwise ContDiff
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- The physical image of a cell is the grid ball of `holder_estimate`. -/
theorem aux_prop_growth_holder_macro_campanato_phys_cell (z : SpatialCoordinates d) {N j : ℕ}
    (hjN : j ≤ N) (k : Fin d → ℤ) (hk : aux_prop_growth_holder_macro_campanato_Adm j k)
    (hR : (0 : ℝ) < 3 ^ N) :
    (3 : ℝ) ^ N • aux_prop_growth_holder_macro_campanato_cell z j k =
      ball ((3 : ℝ) ^ N • aux_prop_growth_holder_macro_campanato_center z j k) ((3 : ℝ) ^ (N - j) / 2) ∩
        (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR : Set (SpatialCoordinates d)) ∧
    (∀ i, ((3 : ℝ) ^ N • aux_prop_growth_holder_macro_campanato_center z j k) i =
      ((3 : ℝ) ^ N • z) i + (3 : ℝ) ^ (N - j) * (k i : ℝ)) := by
  have h3j : (3 : ℝ) ^ N * aux_prop_growth_holder_macro_campanato_side j = (3 : ℝ) ^ (N - j) := by
    unfold aux_prop_growth_holder_macro_campanato_side
    rw [← div_eq_mul_inv, pow_sub₀ (3 : ℝ) (by norm_num) hjN, div_eq_mul_inv]
  have hball : (3 : ℝ) ^ N • aux_prop_growth_holder_macro_campanato_cell z j k =
      ball ((3 : ℝ) ^ N • aux_prop_growth_holder_macro_campanato_center z j k) ((3 : ℝ) ^ (N - j) / 2) := by
    unfold aux_prop_growth_holder_macro_campanato_cell
    rw [_root_.smul_ball hR.ne', Real.norm_eq_abs, abs_of_pos hR, ← h3j]
    ring_nf
  have hsub : (3 : ℝ) ^ N • aux_prop_growth_holder_macro_campanato_cell z j k ⊆
      (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR : Set (SpatialCoordinates d)) := by
    rw [aux_aux_macro_energy_recurrence_cube_smul_one z hR one_pos hR]
    exact Set.smul_set_mono (aux_prop_growth_holder_macro_campanato_cell_subset z hk)
  refine ⟨?_, ?_⟩
  · rw [← hball]
    exact (Set.inter_eq_left.2 hsub).symm
  · intro i
    simp only [Pi.smul_apply, smul_eq_mul, aux_prop_growth_holder_macro_campanato_center]
    rw [← h3j]
    ring

/-- The `holder_estimate` oscillation of the physical cell is the normalized variance of the
unit cell. -/
theorem aux_prop_growth_holder_macro_campanato_phys_osc {s : ℝ} (hs : 0 < s)
    (A : Set (SpatialCoordinates d)) (hA : MeasurableSet A) (f U : SpatialCoordinates d → ℝ)
    (hU : ∀ᵐ y ∂volume.restrict (s • A), U y = f (s⁻¹ • y)) :
    Real.sqrt ((volume.real (s • A))⁻¹ * ∫ w in s • A, (U w - (volume.real (s • A))⁻¹ *
        ∫ w in s • A, U w) ^ 2) =
      Real.sqrt ((volume.real A)⁻¹ * aux_prop_growth_holder_macro_campanato_var A f) := by
  have h := aux_prop_growth_holder_macro_campanato_var_smul hs A hA f U hU
  change Real.sqrt ((volume.real (s • A))⁻¹ * aux_prop_growth_holder_macro_campanato_var (s • A) U) = _
  rw [h, aux_aux_macro_energy_recurrence_volume_real_smul hs]
  congr 1
  have hsd : s ^ d ≠ 0 := pow_ne_zero _ hs.ne'
  rw [mul_inv, mul_assoc, ← mul_assoc (volume.real A)⁻¹, mul_comm (volume.real A)⁻¹, mul_assoc,
    ← mul_assoc, inv_mul_cancel₀ hsd, one_mul]

/-- `3^{-α(N - (N-j))} = 3^{-jα}` and `3^{α((N-j)-(N-j))} = 1`. -/
theorem aux_prop_growth_holder_macro_campanato_exp_eq (α : ℝ) {N j : ℕ} (hjN : j ≤ N) :
    (3 : ℝ) ^ (-α * ((N : ℝ) - ((N - j : ℕ) : ℝ))) = aux_prop_growth_holder_macro_campanato_side j ^ α ∧
      (3 : ℝ) ^ (α * (((N - j : ℕ) : ℝ) - ((N - j : ℕ) : ℝ))) = 1 := by
  refine ⟨?_, by simp⟩
  rw [Nat.cast_sub hjN, show (N : ℝ) - ((N : ℝ) - j) = j by ring]
  unfold aux_prop_growth_holder_macro_campanato_side
  rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_neg (by norm_num)]
  ring_nf

/-- The source factor `⟨b⟩⁻¹ 3^{3N/2} [g] ≤ Cp (c ⟨b⟩)⁻¹ Kf`. -/
theorem aux_prop_growth_holder_macro_campanato_source_arith (N : ℕ) {refA c Cp Kf gS : ℝ}
    (hrefA : 0 < refA) (hc : 0 < c)
    (hgS : gS ≤ Cp * Real.sqrt ((3 : ℝ) ^ N) * (c⁻¹ * (((3 : ℝ) ^ N)⁻¹) ^ 2 * Kf)) :
    refA⁻¹ * (3 : ℝ) ^ (3 * (N : ℝ) / 2) * gS ≤ Cp * (c * refA)⁻¹ * Kf := by
  have h3 : (0 : ℝ) < 3 ^ N := by positivity
  have hsq : Real.sqrt ((3 : ℝ) ^ N) * Real.sqrt ((3 : ℝ) ^ N) = (3 : ℝ) ^ N :=
    Real.mul_self_sqrt h3.le
  have hpow : (3 : ℝ) ^ (3 * (N : ℝ) / 2) = (3 : ℝ) ^ N * Real.sqrt ((3 : ℝ) ^ N) := by
    rw [aux_aux_macro_energy_recurrence_rpow_half N |>.symm, ← Real.rpow_natCast,
      ← Real.rpow_add (by norm_num)]
    congr 1; ring
  rw [hpow]
  have hA : 0 ≤ refA⁻¹ * ((3 : ℝ) ^ N * Real.sqrt ((3 : ℝ) ^ N)) := by positivity
  calc refA⁻¹ * ((3 : ℝ) ^ N * Real.sqrt ((3 : ℝ) ^ N)) * gS
      ≤ refA⁻¹ * ((3 : ℝ) ^ N * Real.sqrt ((3 : ℝ) ^ N)) *
          (Cp * Real.sqrt ((3 : ℝ) ^ N) * (c⁻¹ * (((3 : ℝ) ^ N)⁻¹) ^ 2 * Kf)) :=
        mul_le_mul_of_nonneg_left hgS hA
    _ = Cp * (c * refA)⁻¹ * Kf * ((Real.sqrt ((3 : ℝ) ^ N) * Real.sqrt ((3 : ℝ) ^ N)) *
          ((3 : ℝ) ^ N * (((3 : ℝ) ^ N)⁻¹) ^ 2)) := by rw [mul_inv]; ring
    _ = Cp * (c * refA)⁻¹ * Kf := by
        rw [hsq]
        field_simp

/-- `if P then 0 else B ≤ X` from `B ≤ X` and `0 ≤ X`. -/
theorem aux_prop_growth_holder_macro_campanato_ite_le {P : Prop} {hP : Decidable P} {B X : ℝ}
    (hB : B ≤ X) (hX : 0 ≤ X) : @ite ℝ P hP 0 B ≤ X := by
  rcases hP with h | h
  · exact hB
  · exact hX

/-- The closing arithmetic of the finite oscillation estimate. -/
theorem aux_prop_growth_holder_macro_campanato_finite_close (d : ℕ) {C sa oscS oscR src bd Ro Kf' Cφ V var : ℝ}
    (hC : 0 ≤ C) (hsa : 0 ≤ sa) (hV : 0 < V) (hvar0 : 0 ≤ var)
    (hosc : oscS = Real.sqrt (V⁻¹ * var))
    (hmain : 1 * oscS ≤ C * sa * (oscR + src) + bd)
    (hoscR : oscR ≤ Ro) (hsrc : src ≤ Kf') (hbd : bd ≤ C * sa * (d * Cφ)) :
    var ≤ (C * sa * (Ro + Kf' + d * Cφ)) ^ 2 * V := by
  have hX : oscS ≤ C * sa * (Ro + Kf' + d * Cφ) := by
    have h1 : C * sa * (oscR + src) ≤ C * sa * (Ro + Kf') :=
      mul_le_mul_of_nonneg_left (add_le_add hoscR hsrc) (mul_nonneg hC hsa)
    calc oscS = 1 * oscS := (one_mul _).symm
      _ ≤ _ := hmain
      _ ≤ C * sa * (Ro + Kf') + C * sa * (d * Cφ) := add_le_add h1 hbd
      _ = _ := by ring
  have hos0 : 0 ≤ oscS := by rw [hosc]; exact Real.sqrt_nonneg _
  have hsq : oscS ^ 2 = V⁻¹ * var := by
    rw [hosc, Real.sq_sqrt (mul_nonneg (inv_nonneg.2 hV.le) hvar0)]
  have h2 : V⁻¹ * var ≤ (C * sa * (Ro + Kf' + d * Cφ)) ^ 2 := by
    rw [← hsq]; exact pow_le_pow_left₀ hos0 hX 2
  calc var = V * (V⁻¹ * var) := by field_simp
    _ ≤ V * (C * sa * (Ro + Kf' + d * Cφ)) ^ 2 := mul_le_mul_of_nonneg_left h2 hV.le
    _ = _ := by ring

/-- `phys_osc` for a set given as a dilate. -/
theorem aux_prop_growth_holder_macro_campanato_phys_osc' {s : ℝ} (hs : 0 < s)
    (A T : Set (SpatialCoordinates d)) (hTA : T = s • A) (hA : MeasurableSet A)
    (f U : SpatialCoordinates d → ℝ)
    (hU : ∀ᵐ y ∂volume.restrict T, U y = f (s⁻¹ • y)) :
    Real.sqrt ((volume.real T)⁻¹ * ∫ w in T, (U w - (volume.real T)⁻¹ * ∫ w in T, U w) ^ 2) =
      Real.sqrt ((volume.real A)⁻¹ * aux_prop_growth_holder_macro_campanato_var A f) := by
  subst hTA
  exact aux_prop_growth_holder_macro_campanato_phys_osc hs A hA f U hU

/-- **The finite-infrared grid oscillation estimate** (paper 740–743 with
`e.Holder.estimate.boxes.local`): `holder_estimate` at the physical centre of each cell. -/
theorem aux_prop_growth_holder_macro_campanato_finite_osc {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ Cp : ℝ, 0 < Cp ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
      (L : ℕ) (om' : BilateralField d) (alpha : ℝ), M.delta ≤ Sreg.C⁻¹ →
        alpha ∈ Sreg.alphaRange →
      ∀ (N : ℕ) (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) (hR : (0 : ℝ) < 3 ^ N)
        (a' : PositiveCoefficient (centeredCube z 1 h1)) (c : ℝ), 0 < c →
        (∀ᵐ x ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
          a'.val x = c * (Sreg.cutoffOn L om' ((3 : ℝ) ^ N • z) (3 ^ N) hR).val
            ((3 : ℝ) ^ N • x)) →
      ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
        AEMeasurable F (volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
          |F x| ≤ Kf) →
      ∀ (φ : SpatialCoordinates d → ℝ) (Cφ : ℝ), ContDiff ℝ 2 φ →
        c2Norm (closedCube z 1 h1 : Set (SpatialCoordinates d)) φ ≤ Cφ →
      ∀ (b u' : weakSobolevGraph (centeredCube z 1 h1)),
        ((b : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))] φ →
        SolvesDirichlet a' F b u' →
      ∀ (Ro : ℝ), Real.sqrt (aux_prop_growth_holder_macro_campanato_var
          (centeredCube z 1 h1 : Set (SpatialCoordinates d))
          ((u' : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)) ≤ Ro →
      ∀ j : ℕ, j ≤ N → (Sreg.prefixLen L alpha N ((3 : ℝ) ^ N • z) om' : ℤ) ≤ j →
      ∀ k : Fin d → ℤ, aux_prop_growth_holder_macro_campanato_Adm j k →
        aux_prop_growth_holder_macro_campanato_var (aux_prop_growth_holder_macro_campanato_cell z j k)
            ((u' : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ) ≤
          (Sreg.C * aux_prop_growth_holder_macro_campanato_side j ^ alpha *
            (Ro + Cp * (c * Sreg.refAvg L N ((3 : ℝ) ^ N • z) om')⁻¹ * Kf + d * Cφ)) ^ 2 *
            volume.real (aux_prop_growth_holder_macro_campanato_cell z j k) := by
  obtain ⟨Cp, hCp, hphys⟩ := aux_aux_macro_energy_recurrence_physical_problem hd
  refine ⟨Cp, hCp, ?_⟩
  intro M Sreg L om' alpha hδ hα N z h1 hR a' c hc hcoef F Kf hKf hFm hFb φ Cφ hφ hCφ
    b u' hb hsol Ro hRo j hjN hjP k hk
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hT : (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR : Set (SpatialCoordinates d)) =
      (3 : ℝ) ^ N • (centeredCube z 1 h1 : Set (SpatialCoordinates d)) :=
    aux_aux_macro_energy_recurrence_cube_smul_one z hR h1 hR
  have hQT : (centeredCube z 1 h1 : Set (SpatialCoordinates d)) =
      ((3 : ℝ) ^ N)⁻¹ • (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR :
        Set (SpatialCoordinates d)) := by
    rw [hT, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  obtain ⟨U, hU1, hU2⟩ := aux_aux_macro_energy_recurrence_weak_unscale (inv_pos.2 hR) hQT u'
  obtain ⟨hh, hh1, hh2⟩ := aux_aux_macro_energy_recurrence_weak_unscale (inv_pos.2 hR) hQT b
  have hDir := aux_aux_macro_energy_recurrence_dirichlet_push hR hT hQT u' b hsol.1 U hh hU1 hU2
    hh1 hh2
  obtain ⟨g, hgrad, hgi, hgH, hgS, heq⟩ := hphys (centeredCube z 1 h1) ((3 : ℝ) ^ N • z)
    ((3 : ℝ) ^ N) hR ((3 : ℝ) ^ N) c hR hc hT (Sreg.cutoffOn L om' ((3 : ℝ) ^ N • z) (3 ^ N) hR)
    a' hcoef F Kf hKf hFm hFb b u' hsol (U : SobolevData _) hU2
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hbgrad := aux_aux_macro_energy_recurrence_datum_grad φ hφ1 b hb
    (fun i => aux_aux_macro_energy_recurrence_memLp_fderiv (closedCube z 1 h1)
      (centeredCube_subset_closedCube z h1) φ hφ1 i)
  have hghtie : ∀ i : Fin d,
      (sobolevGradient (hh : SobolevData (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR)) i :
          SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR :
          Set (SpatialCoordinates d))]
          (fun y => aux_aux_macro_energy_recurrence_gh φ ((3 : ℝ) ^ N) y i) := by
    intro i
    have hp := aux_aux_macro_energy_recurrence_ae_push hR
      (centeredCube z 1 h1).isOpen.measurableSet
      (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR).isOpen.measurableSet hT (hbgrad i)
    filter_upwards [hh2 i, hp] with y e1 e2
    change ((hh : SobolevData (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR)).2 i :
      SpatialCoordinates d → ℝ) y = _
    rw [e1, e2]
    rfl
  obtain ⟨hghH, hghN⟩ := aux_aux_macro_energy_recurrence_gh_bounds hd1 z h1 hR hR φ hφ Cφ hCφ
  -- the grid point
  obtain ⟨hScell, hgridpt⟩ := aux_prop_growth_holder_macro_campanato_phys_cell z hjN k hk hR
  have hcellQ := aux_prop_growth_holder_macro_campanato_cell_subset z hk
  have hcenterQ : aux_prop_growth_holder_macro_campanato_center z j k ∈
      (centeredCube z 1 h1 : Set (SpatialCoordinates d)) :=
    hcellQ (mem_ball_self (half_pos (aux_prop_growth_holder_macro_campanato_side_pos j)))
  have hxpT : (3 : ℝ) ^ N • aux_prop_growth_holder_macro_campanato_center z j k ∈
      centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR := by
    change _ ∈ (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR : Set (SpatialCoordinates d))
    rw [hT]; exact Set.smul_mem_smul_set hcenterQ
  have hn : ((N - j : ℕ) : ℤ) ≤ (N : ℤ) - Sreg.prefixLen L alpha N ((3 : ℝ) ^ N • z) om' := by
    rw [Nat.cast_sub hjN]; linarith
  have hI := Sreg.holder_estimate L om' alpha hδ hα N ((3 : ℝ) ^ N • z) hR g hgrad hgi hgH hh U
    (aux_aux_macro_energy_recurrence_gh φ ((3 : ℝ) ^ N)) hghtie hghH heq hDir
    ((3 : ℝ) ^ N • aux_prop_growth_holder_macro_campanato_center z j k) hxpT (N - j) hn (N - j)
    le_rfl ((3 : ℝ) ^ N • aux_prop_growth_holder_macro_campanato_center z j k) ⟨k, hgridpt⟩
    ⟨mem_ball_self (by positivity), hxpT⟩
  dsimp only at hI
  -- the two oscillations
  have hU1cell : ∀ᵐ y ∂volume.restrict ((3 : ℝ) ^ N • aux_prop_growth_holder_macro_campanato_cell z j k),
      ((U : SobolevData (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR)).1 :
        SpatialCoordinates d → ℝ) y =
        ((u' : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)
          (((3 : ℝ) ^ N)⁻¹ • y) := by
    refine ae_restrict_of_ae_restrict_of_subset ?_ hU1
    rw [hT]; exact Set.smul_set_mono hcellQ
  have hoscS := aux_prop_growth_holder_macro_campanato_phys_osc' hR
    (aux_prop_growth_holder_macro_campanato_cell z j k) _ hScell.symm
    (aux_prop_growth_holder_macro_campanato_cell_measurable z j k) _ _
    (by rw [← hScell]; exact hU1cell)
  have hoscR := aux_prop_growth_holder_macro_campanato_phys_osc' hR
    (centeredCube z 1 h1 : Set (SpatialCoordinates d)) _ hT
    (centeredCube z 1 h1).isOpen.measurableSet _ _ hU1
  rw [centeredCube_volume_real z h1, one_pow, inv_one, one_mul] at hoscR
  obtain ⟨hexp1, hexp2⟩ := aux_prop_growth_holder_macro_campanato_exp_eq alpha hjN
  rw [hexp1, hexp2, hoscR] at hI
  -- the source and boundary terms
  have hsrc := aux_prop_growth_holder_macro_campanato_source_arith N
    (Sreg.refAvg_pos L N ((3 : ℝ) ^ N • z) om') hc hgS
  have hsa : 0 ≤ aux_prop_growth_holder_macro_campanato_side j ^ alpha :=
    Real.rpow_nonneg (aux_prop_growth_holder_macro_campanato_side_pos j).le _
  have hCsa : 0 ≤ Sreg.C * aux_prop_growth_holder_macro_campanato_side j ^ alpha :=
    mul_nonneg Sreg.C_pos.le hsa
  have hN3 : (3 : ℝ) ^ (N : ℝ) * halfHolderNorm ((3 : ℝ) ^ N)
      (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR : Set (SpatialCoordinates d))
      (aux_aux_macro_energy_recurrence_gh φ ((3 : ℝ) ^ N)) ≤ d * Cφ := by
    rw [Real.rpow_natCast]
    calc _ ≤ (3 : ℝ) ^ N * (((3 : ℝ) ^ N)⁻¹ * d * Cφ) :=
          mul_le_mul_of_nonneg_left hghN (by positivity)
      _ = d * Cφ := by field_simp
  have hdCφ : 0 ≤ (d : ℝ) * Cφ := by
    have := (aux_aux_macro_energy_recurrence_halfHolderNorm_nonneg ((3 : ℝ) ^ N)
      (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR : Set (SpatialCoordinates d))
      (aux_aux_macro_energy_recurrence_gh φ ((3 : ℝ) ^ N)))
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (N : ℝ) := by positivity
    exact (mul_nonneg h3 this).trans hN3
  have hB : Sreg.C * aux_prop_growth_holder_macro_campanato_side j ^ alpha * (3 : ℝ) ^ (N : ℝ) *
      halfHolderNorm ((3 : ℝ) ^ N)
        (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR : Set (SpatialCoordinates d))
        (aux_aux_macro_energy_recurrence_gh φ ((3 : ℝ) ^ N)) ≤
      Sreg.C * aux_prop_growth_holder_macro_campanato_side j ^ alpha * (d * Cφ) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hN3 hCsa
  exact aux_prop_growth_holder_macro_campanato_finite_close d Sreg.C_pos.le hsa
    (aux_prop_growth_holder_macro_campanato_cell_volume_pos z j k)
    (aux_prop_growth_holder_macro_campanato_var_nonneg _ _) hoscS hI hRo hsrc
    (aux_prop_growth_holder_macro_campanato_ite_le hB (mul_nonneg hCsa hdCφ))

end Paper

-- ===== MCCore =====
/-!
# Removing the infrared truncation from the grid oscillation estimate

Paper Step 6 (lines 727–738, and the Hölder paragraph's last sentence): the finite-infrared
solutions converge to the actual one in `L²` (stability + killed Poincaré), so the grid
oscillation estimate passes to the limit.
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators Pointwise ContDiff
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The statement of the finite-infrared grid oscillation estimate for a primitive constant. -/
def aux_prop_growth_holder_macro_campanato_FO {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) : Prop :=
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
      (L : ℕ) (om' : BilateralField d) (alpha : ℝ), M.delta ≤ Sreg.C⁻¹ →
        alpha ∈ Sreg.alphaRange →
      ∀ (N : ℕ) (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) (hR : (0 : ℝ) < 3 ^ N)
        (a' : PositiveCoefficient (centeredCube z 1 h1)) (c : ℝ), 0 < c →
        (∀ᵐ x ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
          a'.val x = c * (Sreg.cutoffOn L om' ((3 : ℝ) ^ N • z) (3 ^ N) hR).val
            ((3 : ℝ) ^ N • x)) →
      ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
        AEMeasurable F (volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
          |F x| ≤ Kf) →
      ∀ (φ : SpatialCoordinates d → ℝ) (Cφ : ℝ), ContDiff ℝ 2 φ →
        c2Norm (closedCube z 1 h1 : Set (SpatialCoordinates d)) φ ≤ Cφ →
      ∀ (b u' : weakSobolevGraph (centeredCube z 1 h1)),
        ((b : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))] φ →
        SolvesDirichlet a' F b u' →
      ∀ (Ro : ℝ), Real.sqrt (aux_prop_growth_holder_macro_campanato_var
          (centeredCube z 1 h1 : Set (SpatialCoordinates d))
          ((u' : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)) ≤ Ro →
      ∀ j : ℕ, j ≤ N → (Sreg.prefixLen L alpha N ((3 : ℝ) ^ N • z) om' : ℤ) ≤ j →
      ∀ k : Fin d → ℤ, aux_prop_growth_holder_macro_campanato_Adm j k →
        aux_prop_growth_holder_macro_campanato_var (aux_prop_growth_holder_macro_campanato_cell z j k)
            ((u' : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ) ≤
          (Sreg.C * aux_prop_growth_holder_macro_campanato_side j ^ alpha *
            (Ro + Cp * (c * Sreg.refAvg L N ((3 : ℝ) ^ N • z) om')⁻¹ * Kf + d * Cφ)) ^ 2 *
            volume.real (aux_prop_growth_holder_macro_campanato_cell z j k)

theorem aux_prop_growth_holder_macro_campanato_FO_exists {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ Cp : ℝ, 0 < Cp ∧ aux_prop_growth_holder_macro_campanato_FO (d := d) Cp :=
  aux_prop_growth_holder_macro_campanato_finite_osc hd

variable {d : ℕ}

/-- `L²` distance of two solutions with the same Dirichlet datum, by the killed Poincaré
inequality. -/
theorem aux_prop_growth_holder_macro_campanato_l2_diff {Ω : Opens (SpatialCoordinates d)}
    {K : ℝ≥0} (hK : ∀ w : killedSobolevGraph Ω,
      ‖(w : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) w‖)
    (b u u' : weakSobolevGraph Ω)
    (hu : (u : SobolevData Ω) - (b : SobolevData Ω) ∈ killedSobolevGraph Ω)
    (hu' : (u' : SobolevData Ω) - (b : SobolevData Ω) ∈ killedSobolevGraph Ω) :
    ∫ y in (Ω : Set (SpatialCoordinates d)),
        (((u : SobolevData Ω).1 : SpatialCoordinates d → ℝ) y -
          ((u' : SobolevData Ω).1 : SpatialCoordinates d → ℝ) y) ^ 2 ≤
      (K : ℝ) ^ 2 * aux_aux_macro_energy_recurrence_gradSq
        ((u : SobolevData Ω) - (u' : SobolevData Ω)) := by
  have hw : (u : SobolevData Ω) - (u' : SobolevData Ω) ∈ killedSobolevGraph Ω := by
    have := Submodule.sub_mem _ hu hu'
    rwa [sub_sub_sub_cancel_right] at this
  set w : killedSobolevGraph Ω := ⟨_, hw⟩
  have h1 := hK w
  have hn : ‖subspaceGradient (killedSobolevGraph Ω) w‖ ^ 2 =
      aux_aux_macro_energy_recurrence_gradSq ((u : SobolevData Ω) - (u' : SobolevData Ω)) := by
    change ‖sobolevGradient ((u : SobolevData Ω) - (u' : SobolevData Ω))‖ ^ 2 = _
    rw [sobolevGradient_norm_sq]
    unfold aux_aux_macro_energy_recurrence_gradSq
    exact Finset.sum_congr rfl fun i _ => aux_prop_growth_holder_micro_campanato_norm_sq _
  have hv : ‖(w : SobolevData Ω).1‖ ^ 2 = ∫ y in (Ω : Set (SpatialCoordinates d)),
      (((u : SobolevData Ω).1 : SpatialCoordinates d → ℝ) y -
        ((u' : SobolevData Ω).1 : SpatialCoordinates d → ℝ) y) ^ 2 := by
    rw [aux_prop_growth_holder_micro_campanato_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u : SobolevData Ω).1 (u' : SobolevData Ω).1] with y hy
    change (((u : SobolevData Ω).1 - (u' : SobolevData Ω).1 : DomainL2 Ω) :
      SpatialCoordinates d → ℝ) y ^ 2 = _
    rw [hy, Pi.sub_apply]
  rw [← hv, ← hn, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-- The closing arithmetic of the truncation removal. -/
theorem aux_prop_growth_holder_macro_campanato_core_arith {C sa o r x δ V ε var : ℝ}
    (_hC : 0 ≤ C) (_hsa : 0 ≤ sa) (ho : 0 ≤ o) (hr : 0 ≤ r) (hV : 0 ≤ V) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (_hε : 0 < ε)
    (hδε : δ ≤ ε / (4 * C ^ 2 * sa ^ 2 * (2 * (o + r) + 1) * V + 3))
    (hx0 : 0 ≤ x) (hxr : x ≤ r)
    (hvar : var ≤ 2 * ((C * sa * (Real.sqrt 2 * (o + δ) + x)) ^ 2 * V) + 2 * δ ^ 2) :
    var ≤ (2 * C * sa * (o + r)) ^ 2 * V + ε := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : 1 ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hA : Real.sqrt 2 * (o + δ) + x ≤ Real.sqrt 2 * (o + r + δ) := by nlinarith
  have hA0 : 0 ≤ Real.sqrt 2 * (o + δ) + x := by positivity
  have hsq : (C * sa * (Real.sqrt 2 * (o + δ) + x)) ^ 2 ≤ 2 * (C * sa) ^ 2 * (o + r + δ) ^ 2 := by
    calc (C * sa * (Real.sqrt 2 * (o + δ) + x)) ^ 2
        = (C * sa) ^ 2 * (Real.sqrt 2 * (o + δ) + x) ^ 2 := by ring
      _ ≤ (C * sa) ^ 2 * (Real.sqrt 2 * (o + r + δ)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA0 hA 2) (sq_nonneg _)
      _ = 2 * (C * sa) ^ 2 * (o + r + δ) ^ 2 := by
          have : (Real.sqrt 2 * (o + r + δ)) ^ 2 = 2 * (o + r + δ) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (by norm_num)]
          rw [this]; ring
  have hE : 0 < 4 * C ^ 2 * sa ^ 2 * (2 * (o + r) + 1) * V + 3 := by positivity
  have hδE : (4 * C ^ 2 * sa ^ 2 * (2 * (o + r) + 1) * V + 3) * δ ≤ ε := by
    rwa [le_div_iff₀ hE, mul_comm] at hδε
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith
  have hexp : (o + r + δ) ^ 2 ≤ (o + r) ^ 2 + (2 * (o + r) + 1) * δ := by nlinarith
  have hW : 0 ≤ (C * sa) ^ 2 * V := by positivity
  calc var ≤ 2 * ((C * sa * (Real.sqrt 2 * (o + δ) + x)) ^ 2 * V) + 2 * δ ^ 2 := hvar
    _ ≤ 2 * (2 * (C * sa) ^ 2 * (o + r + δ) ^ 2 * V) + 2 * δ := by
        gcongr
    _ ≤ 2 * (2 * (C * sa) ^ 2 * ((o + r) ^ 2 + (2 * (o + r) + 1) * δ) * V) + 2 * δ := by
        gcongr
    _ = (2 * C * sa * (o + r)) ^ 2 * V + (4 * C ^ 2 * sa ^ 2 * (2 * (o + r) + 1) * V + 2) * δ := by
        ring
    _ ≤ (2 * C * sa * (o + r)) ^ 2 * V + (4 * C ^ 2 * sa ^ 2 * (2 * (o + r) + 1) * V + 3) * δ := by
        nlinarith
    _ ≤ _ := by linarith

/-- Root oscillation of a nearby function. -/
theorem aux_prop_growth_holder_macro_campanato_root_near {Q : Set (SpatialCoordinates d)}
    (hQfin : volume Q ≠ ⊤) (hQpos : 0 < volume.real Q) {f g : SpatialCoordinates d → ℝ}
    (hf : MemLp f 2 (volume.restrict Q)) (hg : MemLp g 2 (volume.restrict Q)) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hfg : ∫ y in Q, (f y - g y) ^ 2 ≤ δ ^ 2) :
    Real.sqrt (aux_prop_growth_holder_macro_campanato_var Q g) ≤
      Real.sqrt 2 * (Real.sqrt (aux_prop_growth_holder_macro_campanato_var Q f) + δ) := by
  have hvarQ := aux_prop_growth_holder_macro_campanato_var_perturb hQfin hQpos hg hf
  have hsym : ∫ y in Q, (g y - f y) ^ 2 = ∫ y in Q, (f y - g y) ^ 2 := by
    congr 1; funext y; ring
  rw [hsym] at hvarQ
  have ho0 : 0 ≤ Real.sqrt (aux_prop_growth_holder_macro_campanato_var Q f) := Real.sqrt_nonneg _
  have ho2 : Real.sqrt (aux_prop_growth_holder_macro_campanato_var Q f) ^ 2 =
      aux_prop_growth_holder_macro_campanato_var Q f :=
    Real.sq_sqrt (aux_prop_growth_holder_macro_campanato_var_nonneg _ _)
  have h1' : aux_prop_growth_holder_macro_campanato_var Q g ≤
      2 * (Real.sqrt (aux_prop_growth_holder_macro_campanato_var Q f) + δ) ^ 2 := by
    nlinarith
  calc _ ≤ Real.sqrt (2 * (Real.sqrt (aux_prop_growth_holder_macro_campanato_var Q f) + δ) ^ 2) :=
        Real.sqrt_le_sqrt h1'
    _ = _ := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]

/-- Cell variance of a nearby function. -/
theorem aux_prop_growth_holder_macro_campanato_cell_near {Q T : Set (SpatialCoordinates d)}
    (hTQ : T ⊆ Q) (hQfin : volume Q ≠ ⊤) (hTfin : volume T ≠ ⊤) (hTpos : 0 < volume.real T)
    {f g : SpatialCoordinates d → ℝ}
    (hf : MemLp f 2 (volume.restrict Q)) (hg : MemLp g 2 (volume.restrict Q)) {δ B : ℝ}
    (hfg : ∫ y in Q, (f y - g y) ^ 2 ≤ δ ^ 2)
    (hB : aux_prop_growth_holder_macro_campanato_var T g ≤ B) :
    aux_prop_growth_holder_macro_campanato_var T f ≤ 2 * B + 2 * δ ^ 2 := by
  have hfT : MemLp f 2 (volume.restrict T) := hf.mono_measure (Measure.restrict_mono hTQ le_rfl)
  have hgT : MemLp g 2 (volume.restrict T) := hg.mono_measure (Measure.restrict_mono hTQ le_rfl)
  have hpert := aux_prop_growth_holder_macro_campanato_var_perturb hTfin hTpos hfT hgT
  have hsub : ∫ y in T, (f y - g y) ^ 2 ≤ ∫ y in Q, (f y - g y) ^ 2 := by
    have := aux_prop_growth_holder_macro_campanato_sq_mono (f := fun y => f y - g y)
      hTQ hQfin (hf.sub hg) 0
    simpa using this
  linarith

/-- The `L²` distance between the actual and a finite-infrared solution. -/
theorem aux_prop_growth_holder_macro_campanato_trunc_l2 {Ω : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (A a' : PositiveCoefficient Ω) (lam η : ℝ) (hlam : 0 < lam) (_hη0 : 0 ≤ η)
    (hA : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), lam ≤ A.val x)
    (hη : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), |a'.val x - A.val x| ≤ η)
    (hηl : η ≤ lam / 2) (KP : ℝ≥0)
    (hKP : ∀ w : killedSobolevGraph Ω,
      ‖(w : SobolevData Ω).1‖ ≤ KP * ‖subspaceGradient (killedSobolevGraph Ω) w‖)
    (F : SpatialCoordinates d → ℝ) (b u u' : weakSobolevGraph Ω)
    (hu : SolvesDirichlet A F b u) (hu' : SolvesDirichlet a' F b u') :
    ∫ y in (Ω : Set (SpatialCoordinates d)),
        (((u : SobolevData Ω).1 : SpatialCoordinates d → ℝ) y -
          ((u' : SobolevData Ω).1 : SpatialCoordinates d → ℝ) y) ^ 2 ≤
      ((KP : ℝ) * (2 * η / lam) *
        Real.sqrt (aux_aux_macro_energy_recurrence_gradSq (u : SobolevData Ω))) ^ 2 := by
  have hstab := aux_aux_macro_energy_recurrence_stability A a' lam η hlam hA hη hηl F b u u' hu hu'
  have hdiff := aux_prop_growth_holder_macro_campanato_l2_diff hKP b u u' hu.1 hu'.1
  have hG20 := aux_aux_macro_energy_recurrence_gradSq_nonneg (u : SobolevData Ω)
  refine hdiff.trans ?_
  have hK0 : (0 : ℝ) ≤ (KP : ℝ) ^ 2 := sq_nonneg _
  calc (KP : ℝ) ^ 2 * aux_aux_macro_energy_recurrence_gradSq ((u : SobolevData Ω) - (u' : SobolevData Ω))
      ≤ (KP : ℝ) ^ 2 * (4 * η ^ 2 / lam ^ 2 *
          aux_aux_macro_energy_recurrence_gradSq (u : SobolevData Ω)) :=
        mul_le_mul_of_nonneg_left hstab hK0
    _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hG20]; ring

/-- The finite estimate with the reference factor bounded. -/
theorem aux_prop_growth_holder_macro_campanato_src_bound {C sa R Cp cr Kf Kr dC V var : ℝ}
    (hC : 0 ≤ C) (hsa : 0 ≤ sa) (hV : 0 ≤ V) (hCp : 0 ≤ Cp) (hKf : 0 ≤ Kf) (hcr : 0 < cr)
    (hR : 0 ≤ R) (hdC : 0 ≤ dC) (href : cr⁻¹ ≤ 2 * Kr)
    (hvar : var ≤ (C * sa * (R + Cp * cr⁻¹ * Kf + dC)) ^ 2 * V) :
    var ≤ (C * sa * (R + (2 * Cp * Kr * Kf + dC))) ^ 2 * V := by
  refine hvar.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ 2) hV)
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hsa)
  have := mul_le_mul_of_nonneg_left href hCp
  have := mul_le_mul_of_nonneg_right this hKf
  linarith

/-- **One prefix-good infrared cutoff** of the truncation removal. -/
theorem aux_prop_growth_holder_macro_campanato_core_step (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hCp : 0 ≤ Cp) (hFO : aux_prop_growth_holder_macro_campanato_FO (d := d) Cp)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M) (alpha : ℝ)
    (hδ : M.delta ≤ Sreg.C⁻¹) (hα : alpha ∈ Sreg.alphaRange)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) (hR : (0 : ℝ) < 3 ^ N)
    (lam Kr : ℝ) (hlam : 0 < lam)
    (hlamA : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
      lam ≤ cutoffCoefficient M H om N x)
    (hKr : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)), Real.exp |H om x| ≤ Kr)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (φ : SpatialCoordinates d → ℝ) (Cφ : ℝ) (hφ : ContDiff ℝ 2 φ)
    (hCφ : c2Norm (closedCube z 1 h1 : Set (SpatialCoordinates d)) φ ≤ Cφ)
    (b u : weakSobolevGraph (centeredCube z 1 h1))
    (hb : ((b : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))] φ)
    (hu : SolvesDirichlet (cutoffPositiveCoefficient M H om N z h1) F b u)
    (KP : ℝ≥0) (hKP : ∀ w : killedSobolevGraph (centeredCube z 1 h1),
      ‖(w : SobolevData (centeredCube z 1 h1)).1‖ ≤
        KP * ‖subspaceGradient (killedSobolevGraph (centeredCube z 1 h1)) w‖)
    (L' : ℕ) (aFin : PositiveCoefficient (centeredCube z 1 h1)) (cFin : ℝ) (hcF : 0 < cFin)
    (hcoef : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      aFin.val y = cFin * (Sreg.cutoffOn (N + L') (aux_aux_macro_energy_recurrence_relabel N om)
        ((3 : ℝ) ^ N • z) (3 ^ N) hR).val ((3 : ℝ) ^ N • y))
    (η : ℝ) (hη0 : 0 ≤ η) (hηl : η ≤ lam / 2)
    (hη : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      |aFin.val y - cutoffCoefficient M H om N y| < η)
    (j : ℕ) (hjN : j ≤ N)
    (hjP : (Sreg.prefixLen (N + L') alpha N ((3 : ℝ) ^ N • z)
      (aux_aux_macro_energy_recurrence_relabel N om) : ℤ) ≤ j)
    (k : Fin d → ℤ) (hk : aux_prop_growth_holder_macro_campanato_Adm j k) :
    aux_prop_growth_holder_macro_campanato_var (aux_prop_growth_holder_macro_campanato_cell z j k)
        ((u : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ) ≤
      2 * ((Sreg.C * aux_prop_growth_holder_macro_campanato_side j ^ alpha *
        (Real.sqrt 2 * (Real.sqrt (aux_prop_growth_holder_macro_campanato_var
            (centeredCube z 1 h1 : Set (SpatialCoordinates d))
            ((u : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)) +
          KP * (2 * η / lam) * Real.sqrt (aux_aux_macro_energy_recurrence_gradSq
            (u : SobolevData (centeredCube z 1 h1)))) +
          (2 * Cp * Kr * Kf + d * Cφ))) ^ 2 *
        volume.real (aux_prop_growth_holder_macro_campanato_cell z j k)) +
      2 * (KP * (2 * η / lam) * Real.sqrt (aux_aux_macro_energy_recurrence_gradSq
        (u : SobolevData (centeredCube z 1 h1)))) ^ 2 := by
  have hAae := aux_aux_macro_energy_recurrence_coeff_ae M H om N z h1
  have hmem := ae_restrict_mem (μ := volume) (centeredCube z 1 h1).isOpen.measurableSet
  have hAl : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      lam ≤ (cutoffPositiveCoefficient M H om N z h1).val y := by
    filter_upwards [hAae, hmem] with y h1' h2'
    rw [h1']; exact hlamA y (centeredCube_subset_closedCube z h1 h2')
  have hη' : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      |aFin.val y - (cutoffPositiveCoefficient M H om N z h1).val y| ≤ η := by
    filter_upwards [hAae, hη] with y h1' h2'
    rw [h1']; exact h2'.le
  obtain ⟨u', hu'⟩ := aux_aux_macro_energy_recurrence_exists_solution ⟨KP, hKP⟩ aFin F Kf hFm hFb b
  have hL2 := aux_prop_growth_holder_macro_campanato_trunc_l2 _ aFin lam η hlam hη0 hAl hη' hηl KP
    hKP F b u u' hu hu'
  have hδ0 : 0 ≤ (KP : ℝ) * (2 * η / lam) * Real.sqrt (aux_aux_macro_energy_recurrence_gradSq
      (u : SobolevData (centeredCube z 1 h1))) := by positivity
  have hQfin : volume (centeredCube z 1 h1 : Set (SpatialCoordinates d)) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hQpos : 0 < volume.real (centeredCube z 1 h1 : Set (SpatialCoordinates d)) :=
    centeredCube_volume_pos z h1
  have hRo := aux_prop_growth_holder_macro_campanato_root_near hQfin hQpos (Lp.memLp _)
    (Lp.memLp _) hδ0 hL2
  have hFOi := hFO M Sreg (N + L') (aux_aux_macro_energy_recurrence_relabel N om) alpha hδ hα N z
    h1 hR aFin cFin hcF hcoef F Kf hKf hFm hFb φ Cφ hφ hCφ b u' hb hu' _ hRo j hjN hjP k hk
  have href := aux_aux_macro_energy_recurrence_reference_bounds Sreg H om N L' z h1 hR aFin cFin
    hcoef lam η Kr hlam hηl hlamA (hη.mono fun y hy => hy.le) hKr
  have hCφ0 : 0 ≤ Cφ := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ φ).trans hCφ
  have hsa : 0 ≤ aux_prop_growth_holder_macro_campanato_side j ^ alpha :=
    Real.rpow_nonneg (aux_prop_growth_holder_macro_campanato_side_pos j).le _
  have hcr := mul_pos hcF (Sreg.refAvg_pos (N + L') N ((3 : ℝ) ^ N • z)
    (aux_aux_macro_energy_recurrence_relabel N om))
  have hB := aux_prop_growth_holder_macro_campanato_src_bound Sreg.C_pos.le hsa
    (aux_prop_growth_holder_macro_campanato_cell_volume_pos z j k).le hCp hKf hcr
    (by positivity) (by positivity) href.2 hFOi
  exact aux_prop_growth_holder_macro_campanato_cell_near
    (aux_prop_growth_holder_macro_campanato_cell_subset z hk) hQfin
    (aux_prop_growth_holder_macro_campanato_cell_volume_ne_top z j k)
    (aux_prop_growth_holder_macro_campanato_cell_volume_pos z j k) (Lp.memLp _) (Lp.memLp _) hL2 hB

/-- The choice of the cutoff tolerance. -/
theorem aux_prop_growth_holder_macro_campanato_eta_choice {K G lam δ0 : ℝ} (hK : 0 ≤ K)
    (hG : 0 ≤ G) (hlam : 0 < lam) (hδ0 : 0 < δ0) :
    0 < min (lam / 2) (δ0 * lam / (2 * (K * G + 1))) ∧
      min (lam / 2) (δ0 * lam / (2 * (K * G + 1))) ≤ lam / 2 ∧
      K * (2 * min (lam / 2) (δ0 * lam / (2 * (K * G + 1))) / lam) * G ≤ δ0 := by
  have hKG : 0 < K * G + 1 := by positivity
  refine ⟨lt_min (by positivity) (by positivity), min_le_left _ _, ?_⟩
  have hη : min (lam / 2) (δ0 * lam / (2 * (K * G + 1))) ≤ δ0 * lam / (2 * (K * G + 1)) :=
    min_le_right _ _
  have h1 : 2 * min (lam / 2) (δ0 * lam / (2 * (K * G + 1))) / lam ≤ δ0 / (K * G + 1) := by
    rw [div_le_div_iff₀ hlam hKG]
    calc 2 * min (lam / 2) (δ0 * lam / (2 * (K * G + 1))) * (K * G + 1)
        ≤ 2 * (δ0 * lam / (2 * (K * G + 1))) * (K * G + 1) := by gcongr
      _ = δ0 * lam := by field_simp
  have h0 : 0 ≤ 2 * min (lam / 2) (δ0 * lam / (2 * (K * G + 1))) / lam := by
    have := lt_min (show 0 < lam / 2 by positivity) (show 0 < δ0 * lam / (2 * (K * G + 1)) by positivity)
    positivity
  calc K * (2 * min (lam / 2) (δ0 * lam / (2 * (K * G + 1))) / lam) * G
      = (K * G) * (2 * min (lam / 2) (δ0 * lam / (2 * (K * G + 1))) / lam) := by ring
    _ ≤ (K * G) * (δ0 / (K * G + 1)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ δ0 := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ hKG]
        nlinarith

/-- **Removing the truncation** from the grid oscillation estimate: the actual coefficient on the
unit cube, along prefix-good infrared cutoffs. -/
theorem aux_prop_growth_holder_macro_campanato_core_osc (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hCp : 0 ≤ Cp) (hFO : aux_prop_growth_holder_macro_campanato_FO (d := d) Cp)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M) (alpha : ℝ)
    (hδ : M.delta ≤ Sreg.C⁻¹) (hα : alpha ∈ Sreg.alphaRange)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) (hR : (0 : ℝ) < 3 ^ N)
    (lam Kr : ℝ) (hlam : 0 < lam)
    (hlamA : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
      lam ≤ cutoffCoefficient M H om N x)
    (hKr : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)), Real.exp |H om x| ≤ Kr)
    (aFin : ℕ → PositiveCoefficient (centeredCube z 1 h1))
    (hfinc : ∀ L' : ℕ, ∃ cFin : ℝ, 0 < cFin ∧
      ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
        (aFin L').val y = cFin * (Sreg.cutoffOn (N + L') (aux_aux_macro_energy_recurrence_relabel N om)
          ((3 : ℝ) ^ N • z) (3 ^ N) hR).val ((3 : ℝ) ^ N • y))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L' : ℕ, L₀ ≤ L' →
      ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
        |(aFin L').val y - cutoffCoefficient M H om N y| < ε)
    (P0 : ℕ) (hpre : ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧
      Sreg.prefixLen (N + L') alpha N ((3 : ℝ) ^ N • z)
        (aux_aux_macro_energy_recurrence_relabel N om) ≤ P0)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (φ : SpatialCoordinates d → ℝ) (Cφ : ℝ) (hφ : ContDiff ℝ 2 φ)
    (hCφ : c2Norm (closedCube z 1 h1 : Set (SpatialCoordinates d)) φ ≤ Cφ)
    (b u : weakSobolevGraph (centeredCube z 1 h1))
    (hb : ((b : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))] φ)
    (hu : SolvesDirichlet (cutoffPositiveCoefficient M H om N z h1) F b u)
    (j : ℕ) (hjN : j ≤ N) (hjP : P0 ≤ j)
    (k : Fin d → ℤ) (hk : aux_prop_growth_holder_macro_campanato_Adm j k) :
    aux_prop_growth_holder_macro_campanato_var (aux_prop_growth_holder_macro_campanato_cell z j k)
        ((u : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ) ≤
      (2 * Sreg.C * aux_prop_growth_holder_macro_campanato_side j ^ alpha *
        (Real.sqrt (aux_prop_growth_holder_macro_campanato_var
            (centeredCube z 1 h1 : Set (SpatialCoordinates d))
            ((u : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)) +
          (2 * Cp * Kr * Kf + d * Cφ))) ^ 2 *
        volume.real (aux_prop_growth_holder_macro_campanato_cell z j k) := by
  obtain ⟨KP, hKP⟩ := aux_aux_macro_moment_bank_killed_poincare hd z 1 h1
  have hCφ0 : 0 ≤ Cφ := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ φ).trans hCφ
  have hKr0 : 0 ≤ Kr := (Real.exp_pos _).le.trans (hKr z (Metric.mem_closedBall_self (by norm_num)))
  have hr0 : 0 ≤ 2 * Cp * Kr * Kf + d * Cφ := by positivity
  have hsa : 0 ≤ aux_prop_growth_holder_macro_campanato_side j ^ alpha :=
    Real.rpow_nonneg (aux_prop_growth_holder_macro_campanato_side_pos j).le _
  have hV0 := (aux_prop_growth_holder_macro_campanato_cell_volume_pos z j k).le
  have ho0 : 0 ≤ Real.sqrt (aux_prop_growth_holder_macro_campanato_var
      (centeredCube z 1 h1 : Set (SpatialCoordinates d))
      ((u : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)) := Real.sqrt_nonneg _
  have hG0 : 0 ≤ Real.sqrt (aux_aux_macro_energy_recurrence_gradSq
      (u : SobolevData (centeredCube z 1 h1))) := Real.sqrt_nonneg _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = 4 * Sreg.C ^ 2 * (aux_prop_growth_holder_macro_campanato_side j ^ alpha) ^ 2 *
      (2 * (Real.sqrt (aux_prop_growth_holder_macro_campanato_var
            (centeredCube z 1 h1 : Set (SpatialCoordinates d))
            ((u : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)) +
          (2 * Cp * Kr * Kf + d * Cφ)) + 1) *
        volume.real (aux_prop_growth_holder_macro_campanato_cell z j k) + 3 := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; positivity
  obtain ⟨hη0, hηl, hδle⟩ := aux_prop_growth_holder_macro_campanato_eta_choice KP.2 hG0 hlam
    (lt_min one_pos (div_pos hε hE0) : 0 < min 1 (ε / E))
  obtain ⟨L₀, hL₀⟩ := hconv _ hη0
  obtain ⟨L', hL'1, hL'2⟩ := hpre L₀
  obtain ⟨cFin, hcF, hcoef⟩ := hfinc L'
  have hjP' : (Sreg.prefixLen (N + L') alpha N ((3 : ℝ) ^ N • z)
      (aux_aux_macro_energy_recurrence_relabel N om) : ℤ) ≤ j := by
    have : Sreg.prefixLen (N + L') alpha N ((3 : ℝ) ^ N • z)
        (aux_aux_macro_energy_recurrence_relabel N om) ≤ j := hL'2.trans hjP
    exact_mod_cast this
  have hstep := aux_prop_growth_holder_macro_campanato_core_step hd Cp hCp hFO M Sreg alpha hδ hα H
    om N z h1 hR lam Kr hlam hlamA hKr F Kf hKf hFm hFb φ Cφ hφ hCφ b u hb hu KP hKP L' (aFin L')
    cFin hcF hcoef _ hη0.le hηl (hL₀ L' hL'1) j hjN hjP' k hk
  have hδ0 : 0 ≤ (KP : ℝ) * (2 * min (lam / 2) (min 1 (ε / E) * lam / (2 * (KP * Real.sqrt
      (aux_aux_macro_energy_recurrence_gradSq (u : SobolevData (centeredCube z 1 h1))) + 1))) / lam) *
      Real.sqrt (aux_aux_macro_energy_recurrence_gradSq (u : SobolevData (centeredCube z 1 h1))) := by
    have := hη0.le
    positivity
  have hfin := aux_prop_growth_holder_macro_campanato_core_arith Sreg.C_pos.le hsa ho0 hr0 hV0 hδ0
    (hδle.trans (min_le_left _ _)) hε (by rw [← hE]; exact hδle.trans (min_le_right _ _)) hr0 le_rfl
    hstep
  calc _ ≤ _ := hfin
    _ = _ := by ring

end Paper

-- ===== MCMiddle =====
/-!
# The residual-model unit cube: grid and wavelength inputs of the assembly
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators Pointwise ContDiff
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- **Dirichlet transfer along a dilation**, exporting the pointwise relation of the
solutions (`aux_prop_growth_macro_energy_dirichlet_transfer` plus `v = u(r ·)`). -/
theorem aux_prop_growth_holder_macro_campanato_transfer {Q T : Opens (SpatialCoordinates d)}
    {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hQT : (Q : Set (SpatialCoordinates d)) = r • (T : Set (SpatialCoordinates d)))
    (hTQ : (T : Set (SpatialCoordinates d)) = r⁻¹ • (Q : Set (SpatialCoordinates d)))
    (aQ : PositiveCoefficient Q) (aT : PositiveCoefficient T)
    (hcoef : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      aQ.val x = c * aT.val (r⁻¹ • x))
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ)
    (hFm : AEMeasurable F (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (phi : SpatialCoordinates d → ℝ) (b u : weakSobolevGraph Q)
    (hb : ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi)
    (hsol : SolvesDirichlet aQ F b u) :
    ∃ (F' : SpatialCoordinates d → ℝ) (b' v : weakSobolevGraph T),
      AEMeasurable F' (volume.restrict (T : Set (SpatialCoordinates d))) ∧
      (∀ᵐ y ∂volume.restrict (T : Set (SpatialCoordinates d)), |F' y| ≤ c⁻¹ * r ^ 2 * Kf) ∧
      (((b' : SobolevData T).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))] fun y => phi (r • y)) ∧
      SolvesDirichlet aT F' b' v ∧
      (∀ (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) (hrS : MeasurableSet (r⁻¹ • S)),
        localGradientEnergy aT hrS (sobolevGradient (v : SobolevData T)) =
          c⁻¹ * (r⁻¹) ^ d * r ^ 2 *
            localGradientEnergy aQ hS (sobolevGradient (u : SobolevData Q))) ∧
      (((v : SobolevData T).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))]
          fun y => ((u : SobolevData Q).1 : SpatialCoordinates d → ℝ) (r • y)) := by
  have hri : 0 < r⁻¹ := inv_pos.2 hr
  have hinv : (r⁻¹)⁻¹ = r := inv_inv r
  have hQT' : (Q : Set (SpatialCoordinates d)) = (r⁻¹)⁻¹ • (T : Set (SpatialCoordinates d)) := by
    rw [hinv]; exact hQT
  obtain ⟨v, hv1, hv2⟩ := aux_aux_macro_energy_recurrence_weak_unscale hr hQT u
  obtain ⟨b', hb'1, hb'2⟩ := aux_aux_macro_energy_recurrence_weak_unscale hr hQT b
  have hv2' : ∀ i : Fin d, (((v : SobolevData T).2 i : DomainL2 T) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))]
        fun y => (r⁻¹)⁻¹ * ((u : SobolevData Q).2 i : SpatialCoordinates d → ℝ) ((r⁻¹)⁻¹ • y) := by
    intro i; rw [hinv]; exact hv2 i
  have hv1' : ((v : SobolevData T).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))]
        fun y => ((u : SobolevData Q).1 : SpatialCoordinates d → ℝ) ((r⁻¹)⁻¹ • y) := by
    rw [hinv]; exact hv1
  have hb'1' : ((b' : SobolevData T).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))]
        fun y => ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ) ((r⁻¹)⁻¹ • y) := by
    rw [hinv]; exact hb'1
  have hb'2' : ∀ i : Fin d, (((b' : SobolevData T).2 i : DomainL2 T) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))]
        fun y => (r⁻¹)⁻¹ * ((b : SobolevData Q).2 i : SpatialCoordinates d → ℝ) ((r⁻¹)⁻¹ • y) := by
    intro i; rw [hinv]; exact hb'2 i
  have hDir := aux_aux_macro_energy_recurrence_dirichlet_push hri hTQ hQT' u b hsol.1 v b'
    hv1' hv2' hb'1' hb'2'
  set Fm := hFm.mk F with hFmdef
  have hFmm : Measurable Fm := hFm.measurable_mk
  refine ⟨fun y => c⁻¹ * r ^ 2 * Fm (r • y), b', v,
    (measurable_const.mul (hFmm.comp (measurable_const_smul r))).aemeasurable, ?_, ?_,
    ⟨hDir, fun Φ => ?_⟩, ?_, hv1⟩
  · have h1 := aux_aux_macro_energy_recurrence_ae_pull hr T.isOpen.measurableSet
      Q.isOpen.measurableSet hQT hFb
    have h2 := aux_aux_macro_energy_recurrence_ae_pull hr T.isOpen.measurableSet
      Q.isOpen.measurableSet hQT hFm.ae_eq_mk
    filter_upwards [h1, h2] with y hy1 hy2
    have hy3 : Fm (r • y) = F (r • y) := hy2.symm
    rw [hy3, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < c⁻¹ * r ^ 2)]
    exact mul_le_mul_of_nonneg_left hy1 (by positivity)
  · have h1 := aux_aux_macro_energy_recurrence_ae_pull hr T.isOpen.measurableSet
      Q.isOpen.measurableSet hQT hb
    filter_upwards [hb'1, h1] with y hy1 hy2
    rw [hy1, hy2]
  · have hcoef' : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
        aQ.val x = c * aT.val (r⁻¹ • x) := hcoef
    rw [aux_aux_macro_energy_recurrence_equation_T hri hc hTQ aT aQ hcoef' F b u hsol
      (v : SobolevData T) hv2' Φ]
    refine integral_congr_ae ?_
    have h2 := aux_aux_macro_energy_recurrence_ae_pull hr T.isOpen.measurableSet
      Q.isOpen.measurableSet hQT hFm.ae_eq_mk
    filter_upwards [h2] with y hy
    rw [hinv, hy]
  · intro S hS hrS
    rw [aux_aux_macro_energy_recurrence_localEnergy_scale hri hc hTQ aT aQ hcoef
      (v : SobolevData T) (u : SobolevData Q) hv2' hS hrS, hinv]

/-- **The grid input** on the residual unit cube: `core_osc` with the finite-infrared
coefficients of the residual model, at any exponent `α ≤ α_M`. -/
theorem aux_prop_growth_holder_macro_campanato_unit_H1 (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hCp : 0 ≤ Cp) (hFO : aux_prop_growth_holder_macro_campanato_FO (d := d) Cp)
    (M' : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg' : in_6_16 d M') (alphaM alpha : ℝ)
    (hδC : M'.delta ≤ Sreg'.C⁻¹) (hα : alphaM ∈ Sreg'.alphaRange) (hαα : alpha ≤ alphaM)
    (H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (om' : BilateralField d)
    (hom' : Filter.Tendsto (infraredPartialSum om') Filter.atTop (nhds (H' om')))
    (z' : SpatialCoordinates d) (n P0 : ℕ)
    (hpre : ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧
      Sreg'.prefixLen (n + L') alphaM n ((3 : ℝ) ^ n • z')
        (aux_aux_macro_energy_recurrence_relabel n om') ≤ P0)
    (Rs : ℝ) (hRs : ∀ x ∈ (closedCube z' 1 one_pos : Set (SpatialCoordinates d)),
      Real.exp |H' om' x| ≤ Rs)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F
      (volume.restrict (centeredCube z' 1 one_pos : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z' 1 one_pos : Set (SpatialCoordinates d)),
      |F x| ≤ Kf)
    (φ : SpatialCoordinates d → ℝ) (Cφ : ℝ) (hφ : ContDiff ℝ 2 φ)
    (hCφ : c2Norm (closedCube z' 1 one_pos : Set (SpatialCoordinates d)) φ ≤ Cφ)
    (b v : weakSobolevGraph (centeredCube z' 1 one_pos))
    (hb : ((b : SobolevData (centeredCube z' 1 one_pos)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z' 1 one_pos : Set (SpatialCoordinates d))] φ)
    (hv : SolvesDirichlet (cutoffPositiveCoefficient M' H' om' n z' one_pos) F b v) :
    ∀ j : ℕ, P0 ≤ j → j ≤ n → ∀ k : Fin d → ℤ,
      aux_prop_growth_holder_macro_campanato_Adm j k →
      aux_prop_growth_holder_macro_campanato_var (aux_prop_growth_holder_macro_campanato_cell z' j k)
          ((v : SobolevData (centeredCube z' 1 one_pos)).1 : SpatialCoordinates d → ℝ) ≤
        (2 * Sreg'.C * aux_prop_growth_holder_macro_campanato_side j ^ alpha *
          (Real.sqrt (aux_prop_growth_holder_macro_campanato_var
              (centeredCube z' 1 one_pos : Set (SpatialCoordinates d))
              ((v : SobolevData (centeredCube z' 1 one_pos)).1 : SpatialCoordinates d → ℝ)) +
            (2 * Cp * Rs * Kf + d * Cφ))) ^ 2 *
          volume.real (aux_prop_growth_holder_macro_campanato_cell z' j k) := by
  intro j hjP hjn k hk
  have hR : (0 : ℝ) < 3 ^ n := by positivity
  have hfinc : ∀ L' : ℕ, ∃ cFin : ℝ, 0 < cFin ∧
      ∀ᵐ y ∂volume.restrict (centeredCube z' 1 one_pos : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M' (fun om'' => infraredPartialSum om'' L') om' n z'
            one_pos).val y =
          cFin * (Sreg'.cutoffOn (n + L') (aux_aux_macro_energy_recurrence_relabel n om')
            ((3 : ℝ) ^ n • z') (3 ^ n) hR).val ((3 : ℝ) ^ n • y) := by
    intro L'
    obtain ⟨cFin, hcF, hae⟩ := aux_prop_growth_macro_energy_finite_identity Sreg' om' n L' z'
      one_pos (by positivity)
    refine ⟨cFin, hcF, ?_⟩
    filter_upwards [hae] with y hy
    rw [hy]
    congr 1
    exact aux_aux_macro_energy_recurrence_cutoffOn_congr Sreg' (n + L') rfl
      (by rw [zpow_natCast]) (by rw [zpow_natCast, mul_one]) _ _ (by rw [zpow_natCast])
  obtain ⟨lam, Λ, hlam, hlamA, -⟩ :=
    aux_aux_macro_energy_recurrence_cutoffCoefficient_bounds M' H' om' n z' one_pos
  have hcore := aux_prop_growth_holder_macro_campanato_core_osc hd Cp hCp hFO M' Sreg' alphaM hδC
    hα H' om' n z' one_pos hR lam Rs hlam hlamA hRs
    (fun L' => cutoffPositiveCoefficient M' (fun om'' => infraredPartialSum om'' L') om' n z'
      one_pos)
    hfinc (aux_prop_growth_macro_energy_finite_tendsto M' H' om' hom' n z' one_pos) P0 hpre
    F Kf hKf hFm hFb φ Cφ hφ hCφ b v hb hv j hjn hjP k hk
  refine hcore.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ?_ ?_ 2)
    (aux_prop_growth_holder_macro_campanato_cell_volume_pos z' j k).le)
  · have hCφ0 : 0 ≤ Cφ := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ φ).trans hCφ
    have hRs0 : 0 ≤ Rs := (Real.exp_pos _).le.trans (hRs z' (Metric.mem_closedBall_self (by norm_num)))
    have := Sreg'.C_pos
    have := Real.rpow_nonneg (aux_prop_growth_holder_macro_campanato_side_pos j).le alphaM
    positivity
  · have hsle : aux_prop_growth_holder_macro_campanato_side j ^ alphaM ≤
        aux_prop_growth_holder_macro_campanato_side j ^ alpha :=
      Real.rpow_le_rpow_of_exponent_ge (aux_prop_growth_holder_macro_campanato_side_pos j)
        (aux_prop_growth_holder_macro_campanato_side_le_one j) hαα
    have hCφ0 : 0 ≤ Cφ := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ φ).trans hCφ
    have hRs0 : 0 ≤ Rs := (Real.exp_pos _).le.trans (hRs z' (Metric.mem_closedBall_self (by norm_num)))
    have hX : 0 ≤ Real.sqrt (aux_prop_growth_holder_macro_campanato_var
        (centeredCube z' 1 one_pos : Set (SpatialCoordinates d))
        ((v : SobolevData (centeredCube z' 1 one_pos)).1 : SpatialCoordinates d → ℝ)) +
          (2 * Cp * Rs * Kf + d * Cφ) := by positivity
    have := Sreg'.C_pos
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsle (by positivity)) hX

/-- The coefficient floor on the residual unit cube. -/
theorem aux_prop_growth_holder_macro_campanato_unit_floor (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (aQ : PositiveCoefficient (centeredCube z r hr))
    (aT : PositiveCoefficient (centeredCube (r⁻¹ • z) 1 one_pos)) (c Mx : ℝ)
    (hcoef : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      aQ.val x = c * aT.val (r⁻¹ • x))
    (hfloor : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      1 ≤ Mx * aQ.val x) :
    ∀ᵐ y ∂volume.restrict (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)),
      1 ≤ (c * Mx) * aT.val y := by
  have h : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      1 ≤ (c * Mx) * aT.val (r⁻¹ • x) := by
    filter_upwards [hcoef, hfloor] with x h1 h2
    rw [h1] at h2; linarith
  have h2 := aux_aux_macro_energy_recurrence_ae_pull hr
    (centeredCube (r⁻¹ • z) 1 one_pos).isOpen.measurableSet
    (centeredCube z r hr).isOpen.measurableSet
    (aux_prop_growth_macro_energy_cube_eq_smul z hr one_pos) h
  filter_upwards [h2] with y hy
  rwa [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at hy

/-- **The wavelength input** on the residual unit cube: the micro `pathwise` estimate with the
transferred floor and the transferred macro energy. -/
theorem aux_prop_growth_holder_macro_campanato_unit_H2 (CPw : ℝ) (hCPw : 0 ≤ CPw)
    (hPoinc : ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
      (v : meanZeroSobolevGraph (centeredCube c s hs)),
      ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).1 y) ^ 2 ≤
        CPw * s ^ 2 * ∑ i : Fin d, ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).2 i y) ^ 2)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (aQ : PositiveCoefficient (centeredCube z r hr))
    (aT : PositiveCoefficient (centeredCube (r⁻¹ • z) 1 one_pos)) (c Mx : ℝ) (hc : 0 < c)
    (hMx : 0 ≤ Mx)
    (hcoef : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      aQ.val x = c * aT.val (r⁻¹ • x))
    (hfloor : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      1 ≤ Mx * aQ.val x)
    (u : weakSobolevGraph (centeredCube z r hr))
    (v : weakSobolevGraph (centeredCube (r⁻¹ • z) 1 one_pos))
    (hloc : ∀ (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) (hrS : MeasurableSet (r⁻¹ • S)),
      localGradientEnergy aT hrS (sobolevGradient (v : SobolevData (centeredCube (r⁻¹ • z) 1 one_pos))) =
        c⁻¹ * (r⁻¹) ^ d * r ^ 2 *
          localGradientEnergy aQ hS (sobolevGradient (u : SobolevData (centeredCube z r hr))))
    (ρ : ℝ) (hρ : 0 < ρ) (Eb0 : ℝ)
    (hen : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      localGradientEnergy aQ (s := Metric.ball x (r * ρ) ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
        (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤ Eb0)
    (p : SpatialCoordinates d)
    (hp : p ∈ (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))) :
    aux_prop_growth_holder_macro_campanato_var
        (ball p ρ ∩ (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)))
        ((v : SobolevData (centeredCube (r⁻¹ • z) 1 one_pos)).1 : SpatialCoordinates d → ℝ) ≤
      4 * CPw * ρ ^ 2 * (Mx * ((r⁻¹) ^ d * r ^ 2 * Eb0)) := by
  have hri : 0 < r⁻¹ := inv_pos.2 hr
  have hTQ := aux_prop_growth_macro_energy_cube_eq_inv_smul z hr one_pos
  have hlow := aux_prop_growth_holder_macro_campanato_unit_floor z hr aQ aT c Mx hcoef hfloor
  have hEb : ∀ c' ∈ (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)),
      localGradientEnergy aT (s := Metric.ball c' ρ ∩
          (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube (r⁻¹ • z) 1 one_pos).isOpen.measurableSet)
        (sobolevGradient (v : SobolevData (centeredCube (r⁻¹ • z) 1 one_pos))) ≤
      c⁻¹ * (r⁻¹) ^ d * r ^ 2 * Eb0 := by
    intro c' hc'
    have hS : MeasurableSet (Metric.ball (r • c') (r * ρ) ∩
        (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet
    have hset : r⁻¹ • (Metric.ball (r • c') (r * ρ) ∩
        (centeredCube z r hr : Set (SpatialCoordinates d))) =
        Metric.ball c' ρ ∩ (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)) := by
      rw [aux_aux_macro_energy_recurrence_ball_inter_smul _ _ _ hri, ← hTQ, smul_smul,
        inv_mul_cancel₀ hr.ne', one_smul, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
    have hrS : MeasurableSet (r⁻¹ • (Metric.ball (r • c') (r * ρ) ∩
        (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
      rw [hset]
      exact isOpen_ball.measurableSet.inter (centeredCube (r⁻¹ • z) 1 one_pos).isOpen.measurableSet
    have hl := hloc _ hS hrS
    rw [aux_aux_macro_energy_recurrence_localEnergy_congr aT hset hrS
      (isOpen_ball.measurableSet.inter (centeredCube (r⁻¹ • z) 1 one_pos).isOpen.measurableSet)] at hl
    rw [hl]
    have hmem : r • c' ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      rw [aux_prop_growth_macro_energy_cube_eq_smul z hr one_pos]
      exact Set.smul_mem_smul_set hc'
    exact mul_le_mul_of_nonneg_left (hen (r • c') hmem) (by positivity)
  have hpw := aux_prop_growth_holder_micro_campanato_pathwise CPw hCPw hPoinc (r⁻¹ • z) one_pos aT
    (c * Mx) (by positivity) hlow v ρ _ hρ hEb p hp
  have hbr := aux_prop_growth_holder_macro_campanato_target_eq
    (Ω := centeredCube (r⁻¹ • z) 1 one_pos)
    (S := Metric.ball p ρ ∩ (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)))
    (isOpen_ball.measurableSet.inter (centeredCube (r⁻¹ • z) 1 one_pos).isOpen.measurableSet)
    (Set.inter_subset_right) (v : SobolevData (centeredCube (r⁻¹ • z) 1 one_pos)).1
  rw [hbr] at hpw
  refine hpw.trans (le_of_eq ?_)
  field_simp

/-- The root variance by the coarse Poincaré inequality of `in_poincare`. -/
theorem aux_prop_growth_holder_macro_campanato_root_var {hd : 2 ≤ d} {E : in_J d}
    (P : in_poincare d hd E) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (u : weakSobolevGraph (centeredCube z r hr))
    (Λ form : ℝ) (hΛ : (E.lam z r hr a z r 1 1)⁻¹ ≤ Λ)
    (hform : sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
      (u : SobolevData (centeredCube z r hr)) ≤ form) :
    aux_prop_growth_holder_macro_campanato_var (centeredCube z r hr : Set (SpatialCoordinates d))
        ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) ≤
      (P.C * r) ^ 2 * Λ * form := by
  obtain ⟨w, hw1, hw2⟩ := P.centered_representative z r hr u
  have hP := P.poincare_meanZero_all_radii z r hr a w
  set Q := (centeredCube z r hr : Set (SpatialCoordinates d)) with hQ
  have hVQ : 0 < volume.real Q := centeredCube_volume_pos z hr
  have hlam : 0 < E.lam z r hr a z r 1 1 := E.lam_pos _ _ _ _ _ _ _ _
  have hvar : aux_prop_growth_holder_macro_campanato_var Q
      ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =
      ‖(w : SobolevData (centeredCube z r hr)).1‖ ^ 2 := by
    rw [aux_prop_growth_holder_micro_campanato_norm_sq]
    unfold aux_prop_growth_holder_macro_campanato_var
    rw [← aux_prop_growth_holder_macro_campanato_setAverage_eq
      (centeredCube z r hr).isOpen.measurableSet subset_rfl]
    apply integral_congr_ae
    filter_upwards [hw1] with y hy
    rw [hy]
  have hE0 : 0 ≤ localGradientEnergy a (centeredCube z r hr).isOpen.measurableSet
      (sobolevGradient (u : SobolevData (centeredCube z r hr))) := localGradientEnergy_nonneg _ _ _
  have hEform : localGradientEnergy a (centeredCube z r hr).isOpen.measurableSet
      (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤ form :=
    (localGradientEnergy_le _ _ _).trans hform
  rw [hw2] at hP
  unfold normalizedEnergyNorm at hP
  have hn0 : 0 ≤ ‖(w : SobolevData (centeredCube z r hr)).1‖ / Real.sqrt (volume.real Q) := by
    positivity
  have hsq := pow_le_pow_left₀ hn0 hP 2
  have hrp : (E.lam z r hr a z r 1 1 ^ (-(1 / 2) : ℝ)) ^ 2 = (E.lam z r hr a z r 1 1)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    norm_num
    rw [Real.rpow_neg_one]
  rw [div_pow, Real.sq_sqrt hVQ.le, mul_pow, mul_pow, hrp,
    Real.sq_sqrt (div_nonneg hE0 hVQ.le)] at hsq
  have hPC0 : 0 ≤ (P.C * r) ^ 2 := sq_nonneg _
  have hlam0 : 0 ≤ (E.lam z r hr a z r 1 1)⁻¹ := (inv_pos.2 hlam).le
  rw [hvar]
  have key : ‖(w : SobolevData (centeredCube z r hr)).1‖ ^ 2 ≤
      (P.C * r) ^ 2 * (E.lam z r hr a z r 1 1)⁻¹ *
        localGradientEnergy a (centeredCube z r hr).isOpen.measurableSet
          (sobolevGradient (u : SobolevData (centeredCube z r hr))) := by
    have h := mul_le_mul_of_nonneg_left hsq hVQ.le
    rw [mul_div_cancel₀ _ hVQ.ne'] at h
    calc _ ≤ _ := h
      _ = _ := by field_simp
  calc _ ≤ _ := key
    _ ≤ (P.C * r) ^ 2 * Λ * form := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hΛ hPC0) hEform hE0
        exact mul_nonneg hPC0 (hlam0.trans hΛ)

/-- Transport of the ball variance and volume from the residual unit cube. -/
theorem aux_prop_growth_holder_macro_campanato_transport (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (uf vf : SpatialCoordinates d → ℝ)
    (hv : vf =ᵐ[volume.restrict (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))]
      fun y => uf (r • y))
    (x : SpatialCoordinates d) (rad : ℝ) :
    aux_prop_growth_holder_macro_campanato_var
        (ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) uf =
      r ^ d * aux_prop_growth_holder_macro_campanato_var
        (ball (r⁻¹ • x) (rad / r) ∩ (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))) vf ∧
    volume.real (ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) =
      r ^ d * volume.real
        (ball (r⁻¹ • x) (rad / r) ∩ (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))) := by
  have hQT := aux_prop_growth_macro_energy_cube_eq_smul z hr one_pos
  have hset : r • (ball (r⁻¹ • x) (rad / r) ∩
      (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))) =
      ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [aux_aux_macro_energy_recurrence_ball_inter_smul _ _ _ hr, ← hQT, smul_smul,
      mul_inv_cancel₀ hr.ne', one_smul, mul_div_cancel₀ _ hr.ne']
  have hm : MeasurableSet (ball (r⁻¹ • x) (rad / r) ∩
      (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))) :=
    measurableSet_ball.inter (centeredCube (r⁻¹ • z) 1 one_pos).isOpen.measurableSet
  have hpush := aux_aux_macro_energy_recurrence_ae_push hr
    (centeredCube (r⁻¹ • z) 1 one_pos).isOpen.measurableSet
    (centeredCube z r hr).isOpen.measurableSet hQT hv
  have hU : ∀ᵐ y ∂volume.restrict (r • (ball (r⁻¹ • x) (rad / r) ∩
      (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)))), uf y = vf (r⁻¹ • y) := by
    rw [hset]
    refine ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right ?_
    filter_upwards [hpush] with y hy
    rw [hy, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  refine ⟨?_, ?_⟩
  · rw [← aux_prop_growth_holder_macro_campanato_var_smul hr _ hm vf uf hU, hset]
  · rw [← hset, aux_aux_macro_energy_recurrence_volume_real_smul hr]

/-- The wavelength arithmetic: the pathwise bound in Campanato form. -/
theorem aux_prop_growth_holder_macro_campanato_wave_arith (d : ℕ) {CPw Mx Kmac K r ρ sn e t1 alpha V : ℝ}
    (hCPw : 0 ≤ CPw) (hMx : 0 ≤ Mx) (hKmac : 0 ≤ Kmac) (hr : 0 < r) (hρ : 0 < ρ)
    (hρsn : ρ ≤ sn) (he : 0 < e) (hexp : 2 + t1 = 2 * alpha + d + e) (hV : ρ ^ d ≤ V) :
    4 * CPw * ρ ^ 2 * (Mx * ((r⁻¹) ^ d * r ^ 2 * (Kmac * K ^ 2 * (r * ρ) ^ t1))) ≤
      ((CPw * (r⁻¹) ^ d * r ^ 2 * r ^ t1 * sn ^ e * Mx + Kmac) * K) ^ 2 * ρ ^ (2 * alpha) * V := by
  have hsn : 0 < sn := hρ.trans_le hρsn
  have hρt : (r * ρ) ^ t1 = r ^ t1 * ρ ^ t1 := Real.mul_rpow hr.le hρ.le
  have hsplit : ρ ^ 2 * ρ ^ t1 = ρ ^ (2 * alpha) * ρ ^ d * ρ ^ e := by
    have h1 : ρ ^ 2 * ρ ^ t1 = ρ ^ ((2 : ℝ) + t1) := by
      rw [Real.rpow_add hρ, Real.rpow_two]
    rw [h1, hexp, Real.rpow_add hρ, Real.rpow_add hρ, Real.rpow_natCast]
  have hρe : ρ ^ e ≤ sn ^ e := Real.rpow_le_rpow hρ.le hρsn he.le
  set a := CPw * (r⁻¹) ^ d * r ^ 2 * r ^ t1 * sn ^ e * Mx with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have h4 : 4 * a * Kmac ≤ (a + Kmac) ^ 2 := by nlinarith [sq_nonneg (a - Kmac)]
  have hA : 0 ≤ ρ ^ (2 * alpha) := Real.rpow_nonneg hρ.le _
  have hV0 : 0 ≤ V := (pow_nonneg hρ.le d).trans hV
  calc 4 * CPw * ρ ^ 2 * (Mx * ((r⁻¹) ^ d * r ^ 2 * (Kmac * K ^ 2 * (r * ρ) ^ t1)))
      = 4 * (CPw * (r⁻¹) ^ d * r ^ 2 * r ^ t1 * Mx) * Kmac * K ^ 2 * (ρ ^ 2 * ρ ^ t1) := by
        rw [hρt]; ring
    _ = 4 * (CPw * (r⁻¹) ^ d * r ^ 2 * r ^ t1 * Mx) * Kmac * K ^ 2 *
        (ρ ^ (2 * alpha) * ρ ^ d * ρ ^ e) := by rw [hsplit]
    _ ≤ 4 * (CPw * (r⁻¹) ^ d * r ^ 2 * r ^ t1 * Mx) * Kmac * K ^ 2 *
        (ρ ^ (2 * alpha) * V * sn ^ e) := by
        gcongr
    _ = 4 * a * Kmac * (K ^ 2 * ρ ^ (2 * alpha) * V) := by rw [ha]; ring
    _ ≤ (a + Kmac) ^ 2 * (K ^ 2 * ρ ^ (2 * alpha) * V) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = _ := by ring

/-- The root oscillation of the transferred solution. -/
theorem aux_prop_growth_holder_macro_campanato_root_arith {r PC Λ Kg K varQ varU : ℝ} (hr : 0 < r)
    (hΛ : 0 ≤ Λ) (hKg : 0 ≤ Kg) (hK : 0 ≤ K)
    (hvarQ : varQ ≤ (PC * r) ^ 2 * Λ * (Kg * K ^ 2)) (hvarU : varQ = r ^ d * varU) :
    Real.sqrt varU ≤ Real.sqrt ((r⁻¹) ^ d * (PC * r) ^ 2) * (Λ + Kg) * K := by
  have hrd : 0 < r ^ d := pow_pos hr d
  have hU : varU ≤ (r⁻¹) ^ d * (PC * r) ^ 2 * (Λ * Kg) * K ^ 2 := by
    have : varU = (r⁻¹) ^ d * varQ := by
      rw [hvarU, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, one_mul]
    rw [this]
    calc (r⁻¹) ^ d * varQ ≤ (r⁻¹) ^ d * ((PC * r) ^ 2 * Λ * (Kg * K ^ 2)) :=
          mul_le_mul_of_nonneg_left hvarQ (by positivity)
      _ = _ := by ring
  have hsq : Real.sqrt (Λ * Kg) ≤ Λ + Kg := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [mul_nonneg hΛ hKg]
  calc Real.sqrt varU ≤ Real.sqrt ((r⁻¹) ^ d * (PC * r) ^ 2 * (Λ * Kg) * K ^ 2) :=
        Real.sqrt_le_sqrt hU
    _ = Real.sqrt ((r⁻¹) ^ d * (PC * r) ^ 2) * Real.sqrt (Λ * Kg) * K := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hK]
    _ ≤ Real.sqrt ((r⁻¹) ^ d * (PC * r) ^ 2) * (Λ + Kg) * K := by
        gcongr

/-- Transport of the root variance. -/
theorem aux_prop_growth_holder_macro_campanato_transport_root (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (uf vf : SpatialCoordinates d → ℝ)
    (hv : vf =ᵐ[volume.restrict (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))]
      fun y => uf (r • y)) :
    aux_prop_growth_holder_macro_campanato_var (centeredCube z r hr : Set (SpatialCoordinates d)) uf =
      r ^ d * aux_prop_growth_holder_macro_campanato_var
        (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)) vf := by
  have hQT := aux_prop_growth_macro_energy_cube_eq_smul z hr one_pos
  have hpush := aux_aux_macro_energy_recurrence_ae_push hr
    (centeredCube (r⁻¹ • z) 1 one_pos).isOpen.measurableSet
    (centeredCube z r hr).isOpen.measurableSet hQT hv
  have hU : ∀ᵐ y ∂volume.restrict (r • (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))),
      uf y = vf (r⁻¹ • y) := by
    rw [← hQT]
    filter_upwards [hpush] with y hy
    rw [hy, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  rw [← aux_prop_growth_holder_macro_campanato_var_smul hr _
    (centeredCube (r⁻¹ • z) 1 one_pos).isOpen.measurableSet vf uf hU, ← hQT]

/-- The middle-scale majorant. -/
def aux_prop_growth_holder_macro_campanato_Kmid (d : ℕ) (Kd CS Cp alpha t1 r e cQ CPw : ℝ)
    (n P0 : ℕ) (Λ Kg Rs Ec Mx Kmac : ℝ) : ℝ :=
  r ^ (-alpha) * Kd * (2 * CS * (cQ * (Λ + Kg) + 2 * Cp * Rs * Ec + 3 * d) +
    (CPw * (r⁻¹) ^ d * r ^ 2 * r ^ t1 * aux_prop_growth_holder_macro_campanato_side n ^ e * Mx +
      Kmac) +
    (2 : ℝ) ^ (alpha + (d : ℝ) / 2) * (3 : ℝ) ^ (t1 * (P0 : ℝ)) * (cQ * (Λ + Kg)))

/-- `(2·3^{P0})^{α+d/2} ≤ 2^{α+d/2} 3^{t1 P0}` when `α + d/2 ≤ t1`. -/
theorem aux_prop_growth_holder_macro_campanato_Y_le (alpha t1 : ℝ) (P0 : ℕ)
    (_hα : 0 ≤ alpha + (d : ℝ) / 2) (ht : alpha + (d : ℝ) / 2 ≤ t1) :
    ((2 : ℝ) * 3 ^ P0) ^ (alpha + (d : ℝ) / 2) ≤
      (2 : ℝ) ^ (alpha + (d : ℝ) / 2) * (3 : ℝ) ^ (t1 * (P0 : ℝ)) := by
  rw [Real.mul_rpow (by norm_num) (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have : (0 : ℝ) ≤ P0 := Nat.cast_nonneg _
  nlinarith

/-- The closing arithmetic of the middle scales. -/
theorem aux_prop_growth_holder_macro_campanato_middle_arith {r rad Kd CS X W Y X0 Xt Wt Yt Ot K
    V Vu varT varU alpha : ℝ} (hr : 0 < r) (hrad : 0 < rad) (hKd : 0 ≤ Kd) (hCS : 0 ≤ CS)
    (hX0 : 0 ≤ X) (hW0 : 0 ≤ W) (hY0 : 0 ≤ Y) (hX00 : 0 ≤ X0) (_hK : 0 ≤ K)
    (hX : X ≤ Xt * K) (hW : W ≤ Wt * K) (hYX0 : Y * X0 ≤ Yt * Ot * K)
    (hunit : varU ≤ (Kd * (2 * CS * X + W + Y * X0)) ^ 2 * (rad / r) ^ (2 * alpha) * Vu)
    (hvar : varT = r ^ d * varU) (hvol : V = r ^ d * Vu) (hVu : 0 ≤ Vu) :
    varT ≤ (r ^ (-alpha) * Kd * (2 * CS * Xt + Wt + Yt * Ot) * K) ^ 2 * rad ^ (2 * alpha) * V := by
  have hrd : 0 ≤ r ^ d := pow_nonneg hr.le d
  have hsum : 2 * CS * X + W + Y * X0 ≤ (2 * CS * Xt + Wt + Yt * Ot) * K := by
    have := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ 2 * CS)
    nlinarith
  have hsum0 : 0 ≤ 2 * CS * X + W + Y * X0 := by positivity
  have hsq : (Kd * (2 * CS * X + W + Y * X0)) ^ 2 ≤ (Kd * ((2 * CS * Xt + Wt + Yt * Ot) * K)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hsum hKd) 2
  have hρ : (rad / r) ^ (2 * alpha) = (r ^ (-alpha)) ^ 2 * rad ^ (2 * alpha) := by
    have h1 : (r ^ (-alpha)) ^ 2 = (r ^ (2 * alpha))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le, ← Real.rpow_neg hr.le]
      congr 1; push_cast; ring
    rw [Real.div_rpow hrad.le hr.le, h1, div_eq_mul_inv, mul_comm]
  have hρ0 : 0 ≤ (rad / r) ^ (2 * alpha) := Real.rpow_nonneg (div_nonneg hrad.le hr.le) _
  rw [hvar, hvol]
  calc r ^ d * varU ≤ r ^ d * ((Kd * (2 * CS * X + W + Y * X0)) ^ 2 * (rad / r) ^ (2 * alpha) * Vu) :=
        mul_le_mul_of_nonneg_left hunit hrd
    _ ≤ r ^ d * ((Kd * ((2 * CS * Xt + Wt + Yt * Ot) * K)) ^ 2 * (rad / r) ^ (2 * alpha) * Vu) := by
        gcongr
    _ = _ := by rw [hρ]; ring

/-- The unit-cube assembly property for one constant `Kd`. -/
def aux_prop_growth_holder_macro_campanato_UnitProp (d : ℕ) (alpha Kd : ℝ) : Prop :=
  ∀ (z : SpatialCoordinates d) (v : SpatialCoordinates d → ℝ),
      MemLp v 2 (volume.restrict (ball z (1 / 2))) →
      ∀ (n P0 : ℕ) (Cg X W X0 ρmin : ℝ), 0 ≤ Cg → 0 ≤ X → 0 ≤ W → 0 ≤ X0 → 0 < ρmin →
      ρmin ≤ aux_prop_growth_holder_macro_campanato_side n →
      (∀ j : ℕ, P0 ≤ j → j ≤ n → ∀ k : Fin d → ℤ,
        aux_prop_growth_holder_macro_campanato_Adm j k →
        aux_prop_growth_holder_macro_campanato_var (aux_prop_growth_holder_macro_campanato_cell z j k) v ≤
          (Cg * aux_prop_growth_holder_macro_campanato_side j ^ alpha * X) ^ 2 *
            volume.real (aux_prop_growth_holder_macro_campanato_cell z j k)) →
      (∀ p ∈ ball z (1 / 2), ∀ ρ : ℝ, ρmin ≤ ρ → ρ ≤ aux_prop_growth_holder_macro_campanato_side n →
        aux_prop_growth_holder_macro_campanato_var (ball p ρ ∩ ball z (1 / 2)) v ≤
          W ^ 2 * ρ ^ (2 * alpha) * volume.real (ball p ρ ∩ ball z (1 / 2))) →
      aux_prop_growth_holder_macro_campanato_var (ball z (1 / 2)) v ≤ X0 ^ 2 →
      ∀ x ∈ ball z (1 / 2), ∀ ρ : ℝ, ρmin ≤ ρ → ρ ≤ 1 →
        aux_prop_growth_holder_macro_campanato_var (ball x ρ ∩ ball z (1 / 2)) v ≤
          (Kd * (Cg * X + W + ((2 : ℝ) * 3 ^ P0) ^ (alpha + (d : ℝ) / 2) * X0)) ^ 2 *
            ρ ^ (2 * alpha) * volume.real (ball x ρ ∩ ball z (1 / 2))

theorem aux_prop_growth_holder_macro_campanato_unit' (alpha : ℝ) (hα0 : 0 < alpha)
    (hα1 : alpha ≤ 1) :
    ∃ Kd : ℝ, 1 ≤ Kd ∧ aux_prop_growth_holder_macro_campanato_UnitProp d alpha Kd :=
  aux_prop_growth_holder_macro_campanato_unit alpha hα0 hα1

/-- The lower unit radius `3^{-N}/r` is below the residual wavelength. -/
theorem aux_prop_growth_holder_macro_campanato_rho_min_le {r : ℝ} (hr : 0 < r) (kk n : ℕ)
    (hrk1 : 1 ≤ r * (3 : ℝ) ^ kk) :
    (3 : ℝ) ^ (-((n + kk : ℕ) : ℤ)) / r ≤ aux_prop_growth_holder_macro_campanato_side n := by
  rw [div_le_iff₀ hr]
  unfold aux_prop_growth_holder_macro_campanato_side
  rw [zpow_neg, zpow_natCast, pow_add, mul_inv]
  have h3 : (0 : ℝ) < ((3 : ℝ) ^ n)⁻¹ := by positivity
  have hk : ((3 : ℝ) ^ kk)⁻¹ ≤ r := by
    rw [inv_le_iff_one_le_mul₀ (by positivity)]; linarith [hrk1]
  calc ((3 : ℝ) ^ n)⁻¹ * ((3 : ℝ) ^ kk)⁻¹ ≤ ((3 : ℝ) ^ n)⁻¹ * r :=
        mul_le_mul_of_nonneg_left hk h3.le
    _ = _ := rfl

/-- The wavelength input in the form used by the unit assembly. -/
theorem aux_prop_growth_holder_macro_campanato_middle_H2 (CPw : ℝ) (hCPw : 0 ≤ CPw)
    (hPoinc : ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
      (v : meanZeroSobolevGraph (centeredCube c s hs)),
      ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).1 y) ^ 2 ≤
        CPw * s ^ 2 * ∑ i : Fin d, ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).2 i y) ^ 2)
    (alpha t1 e : ℝ) (he : 0 < e) (hexp : 2 + t1 = 2 * alpha + d + e)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (N n : ℕ)
    (aQ : PositiveCoefficient (centeredCube z r hr))
    (aT : PositiveCoefficient (centeredCube (r⁻¹ • z) 1 one_pos)) (c Mx Kmac K : ℝ) (hc : 0 < c)
    (hMx : 0 ≤ Mx) (hKmac : 0 ≤ Kmac)
    (hcoef : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      aQ.val x = c * aT.val (r⁻¹ • x))
    (hfloor : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      1 ≤ Mx * aQ.val x)
    (u : weakSobolevGraph (centeredCube z r hr))
    (v : weakSobolevGraph (centeredCube (r⁻¹ • z) 1 one_pos))
    (hloc : ∀ (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) (hrS : MeasurableSet (r⁻¹ • S)),
      localGradientEnergy aT hrS (sobolevGradient (v : SobolevData (centeredCube (r⁻¹ • z) 1 one_pos))) =
        c⁻¹ * (r⁻¹) ^ d * r ^ 2 *
          localGradientEnergy aQ hS (sobolevGradient (u : SobolevData (centeredCube z r hr))))
    (hmac : ∀ (x : SpatialCoordinates d) (rad : ℝ),
      x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 → (3 : ℝ) ^ (-(N : ℤ)) ≤ rad →
      localGradientEnergy aQ
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
        Kmac * K ^ 2 * rad ^ t1) :
    ∀ p ∈ ball (r⁻¹ • z) (1 / 2), ∀ ρ : ℝ, (3 : ℝ) ^ (-(N : ℤ)) / r ≤ ρ →
      ρ ≤ aux_prop_growth_holder_macro_campanato_side n →
      aux_prop_growth_holder_macro_campanato_var (ball p ρ ∩ ball (r⁻¹ • z) (1 / 2))
          ((v : SobolevData (centeredCube (r⁻¹ • z) 1 one_pos)).1 : SpatialCoordinates d → ℝ) ≤
        ((CPw * (r⁻¹) ^ d * r ^ 2 * r ^ t1 * aux_prop_growth_holder_macro_campanato_side n ^ e * Mx +
          Kmac) * K) ^ 2 * ρ ^ (2 * alpha) * volume.real (ball p ρ ∩ ball (r⁻¹ • z) (1 / 2)) := by
  intro p hp ρ hρ1 hρ2
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hρ1
  have hsn1 : aux_prop_growth_holder_macro_campanato_side n ≤ 1 :=
    aux_prop_growth_holder_macro_campanato_side_le_one n
  have hrρ1 : r * ρ ≤ 1 := by nlinarith
  have hrρN : (3 : ℝ) ^ (-(N : ℤ)) ≤ r * ρ := by
    rw [div_le_iff₀ hr] at hρ1; linarith
  have hw := aux_prop_growth_holder_macro_campanato_unit_H2 CPw hCPw hPoinc z hr aQ aT c Mx hc hMx
    hcoef hfloor u v hloc ρ hρ0 (Kmac * K ^ 2 * (r * ρ) ^ t1)
    (fun x hx => hmac x (r * ρ) hx (by positivity) hrρ1 hrρN) p hp
  have hV := aux_prop_growth_holder_micro_campanato_volume_ge (r⁻¹ • z) p (R := 1 / 2) hρ0
    (by linarith) hp
  exact hw.trans (aux_prop_growth_holder_macro_campanato_wave_arith d hCPw hMx hKmac hr hρ0 hρ2 he
    hexp hV)

/-- The grid constant `X` of the middle scales. -/
theorem aux_prop_growth_holder_macro_campanato_middle_X (d : ℕ) {O cQ Λ Kg Cp Rs c r Kf Cphi Ec : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hc : 0 < c) (hCp : 0 ≤ Cp) (hRs : 0 ≤ Rs) (hKf : 0 ≤ Kf)
    (hCphi : 0 ≤ Cphi) (hcE' : c⁻¹ ≤ Ec) (hO : O ≤ cQ * (Λ + Kg) * (Kf + Cphi)) :
    O + (2 * Cp * Rs * (c⁻¹ * r ^ 2 * Kf) + d * (3 * Cphi)) ≤
      (cQ * (Λ + Kg) + 2 * Cp * Rs * Ec + 3 * d) * (Kf + Cphi) := by
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hci : 0 < c⁻¹ := inv_pos.2 hc
  have hEc0 : 0 ≤ Ec := hci.le.trans hcE'
  have ha : c⁻¹ * r ^ 2 ≤ Ec := by
    calc c⁻¹ * r ^ 2 ≤ c⁻¹ * 1 := mul_le_mul_of_nonneg_left hr2 hci.le
      _ ≤ Ec := by linarith
  have h1 : c⁻¹ * r ^ 2 * Kf ≤ Ec * (Kf + Cphi) := by
    calc c⁻¹ * r ^ 2 * Kf ≤ Ec * Kf := mul_le_mul_of_nonneg_right ha hKf
      _ ≤ Ec * (Kf + Cphi) := mul_le_mul_of_nonneg_left (by linarith) hEc0
  have h2 : (d : ℝ) * (3 * Cphi) ≤ 3 * d * (Kf + Cphi) := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  have h3 : 2 * Cp * Rs * (c⁻¹ * r ^ 2 * Kf) ≤ 2 * Cp * Rs * (Ec * (Kf + Cphi)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith

/-- **The middle scales for one sample**: `3^{-N} ≤ rad ≤ r`, `N = n + k`, through the
residual unit cube. -/
theorem aux_prop_growth_holder_macro_campanato_middle (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {E : in_J d} (P : in_poincare d hd E)
    (Cp : ℝ) (hCp : 0 ≤ Cp) (hFO : aux_prop_growth_holder_macro_campanato_FO (d := d) Cp)
    (CPw : ℝ) (hCPw : 0 ≤ CPw)
    (hPoinc : ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
      (v : meanZeroSobolevGraph (centeredCube c s hs)),
      ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).1 y) ^ 2 ≤
        CPw * s ^ 2 * ∑ i : Fin d, ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).2 i y) ^ 2)
    (alpha : ℝ) (hα0 : 0 < alpha) (Kd : ℝ) (hKd0 : 0 ≤ Kd)
    (hKd : aux_prop_growth_holder_macro_campanato_UnitProp d alpha Kd)
    (M M' : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg' : in_6_16 d M') (alphaM : ℝ)
    (hδC : M'.delta ≤ Sreg'.C⁻¹) (hαM : alphaM ∈ Sreg'.alphaRange) (hαα : alpha ≤ alphaM)
    (t1 e : ℝ) (he : 0 < e) (hexp : 2 + t1 = 2 * alpha + d + e)
    (ht1Y : alpha + (d : ℝ) / 2 ≤ t1)
    (H H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (om om' : BilateralField d)
    (hom' : Filter.Tendsto (infraredPartialSum om') Filter.atTop (nhds (H' om')))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (kk n : ℕ)
    (hrk1 : 1 ≤ r * (3 : ℝ) ^ kk)
    (c Ec : ℝ) (hc : 0 < c) (hcE' : c⁻¹ ≤ Ec)
    (hcoefid : ∀ x : SpatialCoordinates d,
      cutoffCoefficient M H om (n + kk) (r • x) = c * cutoffCoefficient M' H' om' n x)
    (P0 : ℕ)
    (hpre : ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧
      Sreg'.prefixLen (n + L') alphaM n ((3 : ℝ) ^ n • (r⁻¹ • z))
        (aux_aux_macro_energy_recurrence_relabel n om') ≤ P0)
    (Rs : ℝ) (hRs : ∀ x ∈ (closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)),
      Real.exp (|H' om' x|) ≤ Rs)
    (Λ Kg Mx Kmac : ℝ) (hΛ0 : 0 ≤ Λ) (hKg0 : 0 ≤ Kg) (hKmac0 : 0 ≤ Kmac)
    (hΛ : (E.lam z r hr (cutoffPositiveCoefficient M H om (n + kk) z hr) z r 1 1)⁻¹ ≤ Λ)
    (hMx : 0 < Mx)
    (hfl : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      Mx⁻¹ ≤ cutoffCoefficient M H om (n + kk) x)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ) (hphi : ContDiff ℝ 2 phi)
    (hCphi : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi)
    (b u : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (hu : SolvesDirichlet (cutoffPositiveCoefficient M H om (n + kk) z hr) F b u)
    (hglob : sobolevCoefficientForm (cutoffPositiveCoefficient M H om (n + kk) z hr)
        (u : SobolevData (centeredCube z r hr)) (u : SobolevData (centeredCube z r hr)) ≤
      Kg * (Kf + Cphi) ^ 2)
    (hmac : ∀ (x : SpatialCoordinates d) (rad : ℝ),
      x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 → (3 : ℝ) ^ (-((n + kk : ℕ) : ℤ)) ≤ rad →
      localGradientEnergy (cutoffPositiveCoefficient M H om (n + kk) z hr)
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
        Kmac * (Kf + Cphi) ^ 2 * rad ^ t1)
    (x : SpatialCoordinates d) (hx : x ∈ centeredCube z r hr) (rad : ℝ)
    (hradN : (3 : ℝ) ^ (-((n + kk : ℕ) : ℤ)) ≤ rad) (hradr : rad ≤ r) :
    ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
        ((u : SobolevData (centeredCube z r hr)).1 y - setAverage
          (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (u : SobolevData (centeredCube z r hr)).1) ^ 2
        ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
      (aux_prop_growth_holder_macro_campanato_Kmid d Kd Sreg'.C Cp alpha t1 r e
          (Real.sqrt ((r⁻¹) ^ d * (P.C * r) ^ 2)) CPw n P0 Λ Kg Rs Ec Mx Kmac * (Kf + Cphi)) ^ 2 *
        rad ^ (2 * alpha) *
        volume.real (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hQT := aux_prop_growth_macro_energy_cube_eq_smul z hr one_pos
  have hTQ := aux_prop_growth_macro_energy_cube_eq_inv_smul z hr one_pos
  have hcoef := aux_prop_growth_macro_energy_coef_rel M M' H H' om om' z hr kk n c hcoefid
  obtain ⟨F', b', v, hF'm, hF'b, hb', hsol', hloc, hvrel⟩ :=
    aux_prop_growth_holder_macro_campanato_transfer hr hc hQT hTQ _ _ hcoef F Kf hFm hFb phi b u
      hb hu
  have hphi' : ContDiff ℝ 2 (fun y : SpatialCoordinates d => phi (r • y)) :=
    hphi.comp (contDiff_id.const_smul r)
  have hCphi' := aux_prop_growth_macro_energy_c2Norm_dilate z hr hr1 one_pos phi hphi Cphi hCphi
  have hCphi0 : 0 ≤ Cphi := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ phi).trans hCphi
  have hKf' : 0 ≤ c⁻¹ * r ^ 2 * Kf := by positivity
  have hK : 0 ≤ Kf + Cphi := by positivity
  have H1 := aux_prop_growth_holder_macro_campanato_unit_H1 hd Cp hCp hFO M' Sreg' alphaM alpha hδC
    hαM hαα H' om' hom' (r⁻¹ • z) n P0 hpre Rs hRs F' (c⁻¹ * r ^ 2 * Kf) hKf' hF'm hF'b
    (fun y => phi (r • y)) (3 * Cphi) hphi' hCphi' b' v hb' hsol'
  have hfloor : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      1 ≤ Mx * (cutoffPositiveCoefficient M H om (n + kk) z hr).val y := by
    filter_upwards [aux_prop_growth_holder_micro_campanato_coeff_ae M H om (n + kk) z hr,
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with y hy hyQ
    rw [hy]
    have hlo := hfl y (centeredCube_subset_closedCube z hr hyQ)
    calc (1 : ℝ) = Mx * Mx⁻¹ := (mul_inv_cancel₀ hMx.ne').symm
      _ ≤ Mx * cutoffCoefficient M H om (n + kk) y := mul_le_mul_of_nonneg_left hlo hMx.le
  have H2 := aux_prop_growth_holder_macro_campanato_middle_H2 CPw hCPw hPoinc alpha t1 e he hexp z
    hr hr1 (n + kk) n _ (cutoffPositiveCoefficient M' H' om' n (r⁻¹ • z) one_pos) c Mx Kmac
    (Kf + Cphi) hc hMx.le hKmac0 hcoef hfloor u v hloc hmac
  have hvarQ := aux_prop_growth_holder_macro_campanato_root_var P z hr
    (cutoffPositiveCoefficient M H om (n + kk) z hr) u Λ (Kg * (Kf + Cphi) ^ 2) hΛ hglob
  have hroot := aux_prop_growth_holder_macro_campanato_transport_root z hr _ _ hvrel
  have hO := aux_prop_growth_holder_macro_campanato_root_arith hr hΛ0 hKg0 hK hvarQ hroot
  have hO0 := Real.sqrt_nonneg (aux_prop_growth_holder_macro_campanato_var
    (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))
    ((v : SobolevData (centeredCube (r⁻¹ • z) 1 one_pos)).1 : SpatialCoordinates d → ℝ))
  have H3 : aux_prop_growth_holder_macro_campanato_var (ball (r⁻¹ • z) (1 / 2))
      ((v : SobolevData (centeredCube (r⁻¹ • z) 1 one_pos)).1 : SpatialCoordinates d → ℝ) ≤
      (Real.sqrt (aux_prop_growth_holder_macro_campanato_var
        (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))
        ((v : SobolevData (centeredCube (r⁻¹ • z) 1 one_pos)).1 : SpatialCoordinates d → ℝ))) ^ 2 :=
    le_of_eq (Real.sq_sqrt (aux_prop_growth_holder_macro_campanato_var_nonneg _ _)).symm
  have hRs0 : 0 ≤ Rs :=
    (Real.exp_pos _).le.trans (hRs (r⁻¹ • z) (Metric.mem_closedBall_self (by norm_num)))
  have hx' : r⁻¹ • x ∈ ball (r⁻¹ • z) (1 / 2) := by
    change r⁻¹ • x ∈ (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))
    rw [hTQ]; exact Set.smul_mem_smul_set hx
  have hrad0 : 0 < rad := lt_of_lt_of_le (by positivity) hradN
  have hCS : 0 ≤ 2 * Sreg'.C := by have := Sreg'.C_pos; linarith
  have hXnn : 0 ≤ Real.sqrt (aux_prop_growth_holder_macro_campanato_var
      (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))
      ((v : SobolevData (centeredCube (r⁻¹ • z) 1 one_pos)).1 : SpatialCoordinates d → ℝ)) +
      (2 * Cp * Rs * (c⁻¹ * r ^ 2 * Kf) + d * (3 * Cphi)) := by positivity
  have hWnn : 0 ≤ (CPw * (r⁻¹) ^ d * r ^ 2 * r ^ t1 * aux_prop_growth_holder_macro_campanato_side n ^ e *
      Mx + Kmac) * (Kf + Cphi) := by
    have := (aux_prop_growth_holder_macro_campanato_side_pos n).le
    have := hMx.le
    positivity
  have hunit := hKd (r⁻¹ • z) _ (Lp.memLp _) n P0 (2 * Sreg'.C) _ _ _
    ((3 : ℝ) ^ (-((n + kk : ℕ) : ℤ)) / r) hCS hXnn hWnn hO0 (by positivity)
    (aux_prop_growth_holder_macro_campanato_rho_min_le hr kk n hrk1) H1 H2 H3 (r⁻¹ • x) hx'
    (rad / r) (div_le_div_of_nonneg_right hradN hr.le) ((div_le_one hr).2 hradr)
  obtain ⟨hvarT, hvolT⟩ := aux_prop_growth_holder_macro_campanato_transport z hr _ _ hvrel x rad
  rw [aux_prop_growth_holder_macro_campanato_target_eq
    (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
    Set.inter_subset_right]
  unfold aux_prop_growth_holder_macro_campanato_Kmid
  have hY := aux_prop_growth_holder_macro_campanato_Y_le (d := d) alpha t1 P0 (by positivity) ht1Y
  have hX := aux_prop_growth_holder_macro_campanato_middle_X d hr hr1 hc hCp hRs0 hKf hCphi0 hcE' hO
  have hYO := mul_le_mul hY hO hO0 (by positivity)
  have hY0 : 0 ≤ ((2 : ℝ) * 3 ^ P0) ^ (alpha + (d : ℝ) / 2) := by positivity
  exact aux_prop_growth_holder_macro_campanato_middle_arith hr hrad0 hKd0
    Sreg'.C_pos.le hXnn hWnn hY0 hO0 hK hX
    le_rfl (le_of_le_of_eq hYO (by ring)) hunit hvarT hvolT measureReal_nonneg

end Paper

-- ===== MCFinal =====
/-!
# The macro Campanato child: majorant, almost-sure bound, moments
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators Pointwise ContDiff
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- The early cutoffs `N < k`: only `rad = r` occurs, and the root variance suffices. -/
theorem aux_prop_growth_holder_macro_campanato_global {hd : 2 ≤ d} {E : in_J d}
    (P : in_poincare d hd E) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (u : weakSobolevGraph (centeredCube z r hr))
    (Λ Kg K : ℝ) (hΛ0 : 0 ≤ Λ) (hKg0 : 0 ≤ Kg) (_hK : 0 ≤ K)
    (hΛ : (E.lam z r hr a z r 1 1)⁻¹ ≤ Λ)
    (hform : sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
      (u : SobolevData (centeredCube z r hr)) ≤ Kg * K ^ 2)
    (x : SpatialCoordinates d) (hx : x ∈ centeredCube z r hr) (alpha : ℝ) (_hα0 : 0 ≤ alpha) :
    ∫ y in Metric.ball x r ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
        ((u : SobolevData (centeredCube z r hr)).1 y - setAverage
          (Metric.ball x r ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (u : SobolevData (centeredCube z r hr)).1) ^ 2
        ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
      (P.C * r * (r ^ (alpha + (d : ℝ) / 2))⁻¹ * (Λ + Kg) * K) ^ 2 * r ^ (2 * alpha) *
        volume.real (Metric.ball x r ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  rw [aux_prop_growth_holder_macro_campanato_target_eq
    (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
    Set.inter_subset_right]
  set Q := (centeredCube z r hr : Set (SpatialCoordinates d))
  have hQfin : volume Q ≠ ⊤ := measure_ball_lt_top.ne
  have hS0pos : 0 < volume.real (Metric.ball x r ∩ Q) := by
    have hpos : 0 < volume (Metric.ball x r ∩ Q) :=
      (isOpen_ball.inter (centeredCube z r hr).isOpen).measure_pos volume ⟨x, mem_ball_self hr, hx⟩
    exact ENNReal.toReal_pos hpos.ne' ((measure_mono Set.inter_subset_left).trans_lt
      measure_ball_lt_top).ne
  have hvS0 : MemLp ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) 2
      (volume.restrict (Metric.ball x r ∩ Q)) :=
    aux_prop_growth_holder_macro_campanato_memLp_sub Set.inter_subset_right _
  have h1 := aux_prop_growth_holder_macro_campanato_var_le
    ((measure_mono Set.inter_subset_left).trans_lt measure_ball_lt_top).ne hS0pos hvS0
    (aux_prop_growth_holder_macro_campanato_avg Q ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ))
  have h2 := aux_prop_growth_holder_macro_campanato_sq_mono (Set.inter_subset_right :
    Metric.ball x r ∩ Q ⊆ Q) hQfin (Lp.memLp (u : SobolevData (centeredCube z r hr)).1)
    (aux_prop_growth_holder_macro_campanato_avg Q ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ))
  have h3 := aux_prop_growth_holder_macro_campanato_root_var P z hr a u Λ (Kg * K ^ 2) hΛ hform
  have hvol : r ^ d ≤ volume.real (Metric.ball x r ∩ Q) :=
    aux_prop_growth_holder_micro_campanato_volume_ge z x (R := r / 2) hr (by linarith) hx
  have hrp : 0 < r ^ (alpha + (d : ℝ) / 2) := Real.rpow_pos_of_pos hr _
  have hsq : (r ^ (alpha + (d : ℝ) / 2)) ^ 2 = r ^ (2 * alpha) * r ^ d := by
    rw [← Real.rpow_natCast (r ^ (alpha + (d : ℝ) / 2)), ← Real.rpow_mul hr.le,
      ← Real.rpow_natCast r d, ← Real.rpow_add hr]
    congr 1; push_cast; ring
  have hPC := P.C_pos
  have hkey : (P.C * r) ^ 2 * Λ * (Kg * K ^ 2) ≤
      (P.C * r * (r ^ (alpha + (d : ℝ) / 2))⁻¹ * (Λ + Kg) * K) ^ 2 * r ^ (2 * alpha) * r ^ d := by
    have hΛK : Λ * Kg ≤ (Λ + Kg) ^ 2 := by nlinarith [mul_nonneg hΛ0 hKg0]
    calc (P.C * r) ^ 2 * Λ * (Kg * K ^ 2) = (P.C * r) ^ 2 * K ^ 2 * (Λ * Kg) := by ring
      _ ≤ (P.C * r) ^ 2 * K ^ 2 * (Λ + Kg) ^ 2 :=
          mul_le_mul_of_nonneg_left hΛK (by positivity)
      _ = (P.C * r * (r ^ (alpha + (d : ℝ) / 2))⁻¹ * (Λ + Kg) * K) ^ 2 *
            (r ^ (alpha + (d : ℝ) / 2)) ^ 2 := by
          field_simp
      _ = _ := by rw [hsq]; ring
  calc _ ≤ _ := h1.trans (h2.trans h3)
    _ ≤ _ := hkey
    _ ≤ _ := mul_le_mul_of_nonneg_left hvol (by positivity)

/-- **The final majorant.** -/
def aux_prop_growth_holder_macro_campanato_Kosc {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (kk : ℕ) (r t1 e alpha Kd CS Cp cQ CPw PC : ℝ)
    (Lm : ℕ → BilateralField d → ℕ) (Rs : BilateralField d → ℝ)
    (Λ Kg Mx Kmac : ℕ → BilateralField d → ℝ) (N : ℕ) (om : BilateralField d) : ℝ :=
  if kk ≤ N then
    aux_prop_growth_holder_macro_campanato_Kmid d Kd CS Cp alpha t1 r e cQ CPw (N - kk)
      (Lm (N - kk) (MacroAllCube.residualShift r kk om)) (Λ N om) (Kg N om)
      (Rs (MacroAllCube.residualShift r kk om)) (aux_prop_growth_macro_energy_env M kk om)
      (Mx N om) (Kmac N om)
  else PC * r * (r ^ (alpha + (d : ℝ) / 2))⁻¹ * (Λ N om + Kg N om)

/-- For the early cutoffs `N < k` the admissible radius is `r` itself. -/
theorem aux_prop_growth_holder_macro_campanato_early {r rad : ℝ} {N kk : ℕ} (hr : 0 < r)
    (hk3 : r * (3 : ℝ) ^ kk ≤ 3) (hN : ¬ kk ≤ N) (hradN : (3 : ℝ) ^ (-(N : ℤ)) ≤ rad)
    (hradr : rad ≤ r) : rad = r := by
  have hNk : N + 1 ≤ kk := by omega
  have h3 : (3 : ℝ) ^ (N + 1) ≤ 3 ^ kk := pow_le_pow_right₀ (by norm_num) hNk
  have hr3 : r ≤ (3 : ℝ) ^ (-(N : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
    have h3N : (0 : ℝ) < 3 ^ N := by positivity
    have : r * (3 : ℝ) ^ (N + 1) ≤ 3 := le_trans (mul_le_mul_of_nonneg_left h3 hr.le) hk3
    rw [pow_succ] at this
    rw [← one_div, le_div_iff₀ h3N]
    nlinarith
  linarith

/-- **The almost-sure macro Campanato bound** for the final majorant. -/
theorem aux_prop_growth_holder_macro_campanato_ae_bound (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {E : in_J d} (P : in_poincare d hd E)
    (Cp : ℝ) (hCp : 0 ≤ Cp) (hFO : aux_prop_growth_holder_macro_campanato_FO (d := d) Cp)
    (CPw : ℝ) (hCPw : 0 ≤ CPw)
    (hPoinc : ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
      (v : meanZeroSobolevGraph (centeredCube c s hs)),
      ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).1 y) ^ 2 ≤
        CPw * s ^ 2 * ∑ i : Fin d, ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).2 i y) ^ 2)
    (alpha : ℝ) (hα0 : 0 < alpha) (Kd : ℝ) (hKd0 : 0 ≤ Kd)
    (hKd : aux_prop_growth_holder_macro_campanato_UnitProp d alpha Kd)
    (M M' : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg' : in_6_16 d M') (t1 e : ℝ)
    (hδC : M'.delta ≤ Sreg'.C⁻¹) (hαM : 1 - ((d : ℝ) - t1) / 4 ∈ Sreg'.alphaRange)
    (hαα : alpha ≤ 1 - ((d : ℝ) - t1) / 4)
    (he : 0 < e) (hexp : 2 + t1 = 2 * alpha + d + e) (ht1Y : alpha + (d : ℝ) / 2 ≤ t1)
    (H H' : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (hH' : InfraredCharacterization M' H')
    (htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M'.P = SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (kk : ℕ)
    (hk1 : 1 < r * (3 : ℝ) ^ kk) (hk3 : r * (3 : ℝ) ^ kk ≤ 3)
    (hT : MeasurePreserving (MacroAllCube.residualShift (d := d) r kk)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure)
    (hshift : ∀ n om, aux_prop_growth_macro_energy_shiftC M M' kk n om ≤
        aux_prop_growth_macro_energy_env M kk om ∧
      (aux_prop_growth_macro_energy_shiftC M M' kk n om)⁻¹ ≤ aux_prop_growth_macro_energy_env M kk om)
    (Lm : ℕ → BilateralField d → ℕ)
    (hLpre : ∀ᵐ om' ∂(chaosSampleLaw M').toMeasure, ∀ N L0 : ℕ,
      ∃ L' : ℕ, L0 ≤ L' ∧
        Sreg'.prefixLen (N + L') (1 - ((d : ℝ) - t1) / 4) N ((3 : ℝ) ^ N • (r⁻¹ • z))
          (aux_aux_macro_moment_bank_relabel N om') ≤ Lm N om')
    (Rs : BilateralField d → ℝ)
    (hRs : ∀ om', ∀ x ∈ (closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)),
      Real.exp (|H' om' x|) ≤ Rs om')
    (Λ Kg Mx Kmac : ℕ → BilateralField d → ℝ)
    (hΛ0 : ∀ N om, 0 ≤ Λ N om) (hKg0 : ∀ N om, 0 ≤ Kg N om) (hKmac0 : ∀ N om, 0 ≤ Kmac N om)
    (hΛ : ∀ N om, (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r 1 1)⁻¹ ≤ Λ N om)
    (hKgsrc : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
        0 ≤ Kf →
        AEMeasurable F
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
              (u : SobolevData (centeredCube z r hr))
              (u : SobolevData (centeredCube z r hr)) ≤
            Kg N om * (Kf + Cphi) ^ 2)
    (hext : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, 0 < Mx N om ∧
      ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        (Mx N om)⁻¹ ≤ cutoffCoefficient M H om N x)
    (hmacE : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
        0 ≤ Kf →
        AEMeasurable F
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
      ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
        ContDiff ℝ 2 phi →
        c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
      ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
        SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
        ∀ (x : SpatialCoordinates d) (rad : ℝ),
          x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
          (3 : ℝ) ^ (-(N : ℤ)) ≤ rad →
          localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
              (s := Metric.ball x rad ∩
                (centeredCube z r hr : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter
                (centeredCube z r hr).isOpen.measurableSet)
              (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
            Kmac N om * (Kf + Cphi) ^ 2 * rad ^ t1) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
        0 ≤ Kf →
        AEMeasurable F
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
          |F x| ≤ Kf) →
      ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
        ContDiff ℝ 2 phi →
        c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
      ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
        SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
        ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, (3 : ℝ) ^ (-(N : ℤ)) ≤ rad → rad ≤ r →
          ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
              ((u : SobolevData (centeredCube z r hr)).1 y - setAverage
                (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                (u : SobolevData (centeredCube z r hr)).1) ^ 2
              ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
            (aux_prop_growth_holder_macro_campanato_Kosc M kk r t1 e alpha Kd Sreg'.C Cp
                (Real.sqrt ((r⁻¹) ^ d * (P.C * r) ^ 2)) CPw P.C Lm Rs Λ Kg Mx Kmac N om *
              (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
              volume.real (Metric.ball x rad ∩
                (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  filter_upwards [hKgsrc, hmacE, hext,
    aux_prop_growth_macro_energy_coeff_identity M M' htau H H' hH hH' r kk hT,
    hT.quasiMeasurePreserving.ae hLpre] with om hsrc hmac hex hcoef hpre
  intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve x hx rad hradN hradr
  have hglob := hsrc N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
  have hmacN := hmac N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
  obtain ⟨hMx, hfl⟩ := hex N
  have hCphi0 : 0 ≤ Cphi := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ phi).trans hCphi
  unfold aux_prop_growth_holder_macro_campanato_Kosc
  by_cases hN : kk ≤ N
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + kk := ⟨N - kk, by omega⟩
    rw [if_pos hN, Nat.add_sub_cancel]
    exact aux_prop_growth_holder_macro_campanato_middle hd P Cp hCp hFO CPw hCPw hPoinc alpha hα0
      Kd hKd0 hKd M M' Sreg' _ hδC hαM hαα t1 e he hexp ht1Y H H' om
      (MacroAllCube.residualShift r kk om) hcoef.1 z r hr hr1 kk n hk1.le
      (aux_prop_growth_macro_energy_shiftC M M' kk n om) (aux_prop_growth_macro_energy_env M kk om)
      (aux_prop_growth_macro_energy_shiftC_pos M M' kk n om) (hshift n om).2 (hcoef.2 n)
      (Lm n (MacroAllCube.residualShift r kk om)) (hpre n) (Rs (MacroAllCube.residualShift r kk om))
      (hRs _) (Λ (n + kk) om) (Kg (n + kk) om) (Mx (n + kk) om) (Kmac (n + kk) om) (hΛ0 _ _)
      (hKg0 _ _) (hKmac0 _ _) (hΛ _ _) hMx hfl F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
      hglob hmacN x hx rad hradN hradr
  · rw [if_neg hN]
    have hrad := aux_prop_growth_holder_macro_campanato_early hr hk3 hN hradN hradr
    rw [hrad]
    exact aux_prop_growth_holder_macro_campanato_global P z hr _ u (Λ N om) (Kg N om) (Kf + Cphi)
      (hΛ0 _ _) (hKg0 _ _) (by positivity) (hΛ N om) hglob x hx alpha hα0.le

/-- `L^P` bound of a nonnegative combination with two Hölder products. -/
theorem aux_prop_growth_holder_macro_campanato_moment_combo {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : ℝ) (hP : 1 ≤ P)
    (a0 a1 a2 a3 a4 a5 : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3)
    (ha4 : 0 ≤ a4) (ha5 : 0 ≤ a5)
    (Λ Kg R Ec Mx Km X : Ω → ℝ)
    (hΛm : AEStronglyMeasurable Λ μ) (hKgm : AEStronglyMeasurable Kg μ)
    (hRm : AEStronglyMeasurable R μ) (hEm : AEStronglyMeasurable Ec μ)
    (hMm : AEStronglyMeasurable Mx μ) (hKm : AEStronglyMeasurable Km μ)
    (hXm : AEStronglyMeasurable X μ)
    (BΛ BG BR BE BM BK BX : ℝ≥0∞)
    (hΛ : eLpNorm Λ (ENNReal.ofReal (2 * P)) μ ≤ BΛ) (hKg : eLpNorm Kg (ENNReal.ofReal (2 * P)) μ ≤ BG)
    (hR : eLpNorm R (ENNReal.ofReal (2 * P)) μ ≤ BR) (hE : eLpNorm Ec (ENNReal.ofReal (2 * P)) μ ≤ BE)
    (hM : eLpNorm Mx (ENNReal.ofReal P) μ ≤ BM) (hK : eLpNorm Km (ENNReal.ofReal P) μ ≤ BK)
    (hX : eLpNorm X (ENNReal.ofReal (2 * P)) μ ≤ BX) :
    AEStronglyMeasurable (fun om => a0 + a1 * (Λ om + Kg om) + a2 * (R om * Ec om) + a3 * Mx om +
        a4 * Km om + a5 * (X om * (Λ om + Kg om))) μ ∧
      eLpNorm (fun om => a0 + a1 * (Λ om + Kg om) + a2 * (R om * Ec om) + a3 * Mx om +
        a4 * Km om + a5 * (X om * (Λ om + Kg om))) (ENNReal.ofReal P) μ ≤
      ENNReal.ofReal a0 + ENNReal.ofReal a1 * (BΛ + BG) + ENNReal.ofReal a2 * (BR * BE) +
        ENNReal.ofReal a3 * BM + ENNReal.ofReal a4 * BK + ENNReal.ofReal a5 * (BX * (BΛ + BG)) := by
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal P := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hP
  have hP2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * P) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hle : ENNReal.ofReal P ≤ ENNReal.ofReal (2 * P) := ENNReal.ofReal_le_ofReal (by linarith)
  have hsumm : AEStronglyMeasurable (fun om => Λ om + Kg om) μ := hΛm.add hKgm
  have hsum2 : eLpNorm (fun om => Λ om + Kg om) (ENNReal.ofReal (2 * P)) μ ≤ BΛ + BG :=
    (eLpNorm_add_le hΛm hKgm hP2).trans (add_le_add hΛ hKg)
  have hsumP : eLpNorm (fun om => Λ om + Kg om) (ENNReal.ofReal P) μ ≤ BΛ + BG :=
    (eLpNorm_le_eLpNorm_of_exponent_le hle hsumm).trans hsum2
  have hRE : eLpNorm (fun om => R om * Ec om) (ENNReal.ofReal P) μ ≤ BR * BE :=
    (aux_aux_macro_moment_bank_product_moment μ P R Ec hRm hEm).trans (mul_le_mul' hR hE)
  have hXS : eLpNorm (fun om => X om * (Λ om + Kg om)) (ENNReal.ofReal P) μ ≤ BX * (BΛ + BG) :=
    (aux_aux_macro_moment_bank_product_moment μ P X _ hXm hsumm).trans (mul_le_mul' hX hsum2)
  have hsmul : ∀ (a : ℝ) (f : Ω → ℝ) (B : ℝ≥0∞), 0 ≤ a →
      eLpNorm f (ENNReal.ofReal P) μ ≤ B →
      eLpNorm (fun om => a * f om) (ENNReal.ofReal P) μ ≤ ENNReal.ofReal a * B := by
    intro a f B ha hf
    have h := eLpNorm_const_smul_le (c := a) (f := f) (p := ENNReal.ofReal P) (μ := μ)
    rw [Real.enorm_of_nonneg ha] at h
    exact h.trans (mul_le_mul_right hf _)
  have hc0 : eLpNorm (fun _ : Ω => a0) (ENNReal.ofReal P) μ ≤ ENNReal.ofReal a0 := by
    rw [eLpNorm_const _ (by positivity) (IsProbabilityMeasure.ne_zero μ), measure_univ,
      ENNReal.one_rpow, mul_one, Real.enorm_of_nonneg ha0]
  have m0 : AEStronglyMeasurable (fun _ : Ω => a0) μ := aestronglyMeasurable_const
  have m1 : AEStronglyMeasurable (fun om => a1 * (Λ om + Kg om)) μ := hsumm.const_mul a1
  have m2 : AEStronglyMeasurable (fun om => a2 * (R om * Ec om)) μ := (hRm.mul hEm).const_mul a2
  have m3 : AEStronglyMeasurable (fun om => a3 * Mx om) μ := hMm.const_mul a3
  have m4 : AEStronglyMeasurable (fun om => a4 * Km om) μ := hKm.const_mul a4
  have m5 : AEStronglyMeasurable (fun om => a5 * (X om * (Λ om + Kg om))) μ :=
    (hXm.mul hsumm).const_mul a5
  refine ⟨((((m0.add m1).add m2).add m3).add m4).add m5, ?_⟩
  refine (eLpNorm_add_le ((((m0.add m1).add m2).add m3).add m4) m5 hP1).trans (add_le_add ?_
    (hsmul a5 _ _ ha5 hXS))
  refine (eLpNorm_add_le (((m0.add m1).add m2).add m3) m4 hP1).trans (add_le_add ?_
    (hsmul a4 _ _ ha4 hK))
  refine (eLpNorm_add_le ((m0.add m1).add m2) m3 hP1).trans (add_le_add ?_ (hsmul a3 _ _ ha3 hM))
  refine (eLpNorm_add_le (m0.add m1) m2 hP1).trans (add_le_add ?_ (hsmul a2 _ _ ha2 hRE))
  exact (eLpNorm_add_le m0 m1 hP1).trans (add_le_add hc0 (hsmul a1 _ _ ha1 hsumP))

/-- The factor `3^{-(N-k)e}` absorbs `e^{bN}` for `b ≤ (e/2) log 3`, up to `3^{k e}`. -/
theorem aux_prop_growth_holder_macro_campanato_side_absorb (e b : ℝ) (he : 0 < e)
    (hb : b ≤ (e / 2) * Real.log 3) (N kk : ℕ) :
    aux_prop_growth_holder_macro_campanato_side (N - kk) ^ e * Real.exp (b * N) ≤
      (3 : ℝ) ^ ((kk : ℝ) * e) := by
  have hl : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hside : aux_prop_growth_holder_macro_campanato_side (N - kk) ^ e =
      Real.exp (-(e * ((N - kk : ℕ) : ℝ) * Real.log 3)) := by
    unfold aux_prop_growth_holder_macro_campanato_side
    rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      Real.rpow_def_of_pos (by norm_num), ← Real.exp_neg]
    congr 1; ring
  have h3 : (3 : ℝ) ^ ((kk : ℝ) * e) = Real.exp (Real.log 3 * ((kk : ℝ) * e)) :=
    Real.rpow_def_of_pos (by norm_num) _
  rw [hside, h3, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hm : (N : ℝ) - kk ≤ ((N - kk : ℕ) : ℝ) := by
    rcases le_total kk N with h | h
    · rw [Nat.cast_sub h]
    · rw [Nat.sub_eq_zero_of_le h]; push_cast; linarith [(Nat.cast_le (α := ℝ)).2 h]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hbN : b * N ≤ (e / 2) * Real.log 3 * N := mul_le_mul_of_nonneg_right hb hN0
  have h1 : e * ((N : ℝ) - kk) * Real.log 3 ≤ e * ((N - kk : ℕ) : ℝ) * Real.log 3 := by
    apply mul_le_mul_of_nonneg_right _ hl.le
    exact mul_le_mul_of_nonneg_left hm he.le
  nlinarith [mul_nonneg (mul_nonneg he.le hN0) hl.le]

/-- **Moments of the final majorant**, uniformly in the cutoff. -/
theorem aux_prop_growth_holder_macro_campanato_Kosc_moment {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M M' : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (kk : ℕ) (r t1 e alpha Kd CS Cp cQ CPw PC : ℝ)
    (hr : 0 < r) (hKd : 0 ≤ Kd) (hCS : 0 ≤ CS) (hCp : 0 ≤ Cp) (hcQ : 0 ≤ cQ) (hCPw : 0 ≤ CPw)
    (hPC : 0 ≤ PC) (Pexp : ℝ) (hP : 1 ≤ Pexp)
    (hT : MeasurePreserving (MacroAllCube.residualShift (d := d) r kk)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure)
    (Lm : ℕ → BilateralField d → ℕ) (hLmeas : ∀ n, Measurable (Lm n)) (BX : ℝ≥0∞)
    (hX : ∀ n, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lm n om : ℝ)))
      (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M').toMeasure ≤ BX)
    (Rs : BilateralField d → ℝ) (hRsm : Measurable Rs) (BR : ℝ≥0∞)
    (hR : eLpNorm Rs (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M').toMeasure ≤ BR)
    (BE : ℝ≥0∞) (hE : eLpNorm (aux_prop_growth_macro_energy_env M kk)
      (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤ BE)
    (Λ Kg Mx Kmac : ℕ → BilateralField d → ℝ) (BΛ BG BM BK : ℝ≥0∞)
    (hΛm : ∀ N, AEStronglyMeasurable (Λ N) (chaosSampleLaw M).toMeasure)
    (hΛ : ∀ N, eLpNorm (Λ N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤ BΛ)
    (hKgm : ∀ N, AEStronglyMeasurable (Kg N) (chaosSampleLaw M).toMeasure)
    (hKg : ∀ N, eLpNorm (Kg N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤ BG)
    (hMm : ∀ N, AEStronglyMeasurable (Mx N) (chaosSampleLaw M).toMeasure)
    (hM : ∀ N, eLpNorm (fun om => aux_prop_growth_holder_macro_campanato_side (N - kk) ^ e * Mx N om)
      (ENNReal.ofReal Pexp) (chaosSampleLaw M).toMeasure ≤ BM)
    (hKmm : ∀ N, AEStronglyMeasurable (Kmac N) (chaosSampleLaw M).toMeasure)
    (hK : ∀ N, eLpNorm (Kmac N) (ENNReal.ofReal Pexp) (chaosSampleLaw M).toMeasure ≤ BK)
    (N : ℕ) :
    AEStronglyMeasurable (aux_prop_growth_holder_macro_campanato_Kosc M kk r t1 e alpha Kd CS Cp cQ
        CPw PC Lm Rs Λ Kg Mx Kmac N) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (aux_prop_growth_holder_macro_campanato_Kosc M kk r t1 e alpha Kd CS Cp cQ CPw PC Lm
          Rs Λ Kg Mx Kmac N) (ENNReal.ofReal Pexp) (chaosSampleLaw M).toMeasure ≤
        (ENNReal.ofReal (r ^ (-alpha) * Kd * (2 * CS * (3 * d))) +
            ENNReal.ofReal (r ^ (-alpha) * Kd * (2 * CS * cQ)) * (BΛ + BG) +
            ENNReal.ofReal (r ^ (-alpha) * Kd * (2 * CS * (2 * Cp))) * (BR * BE) +
            ENNReal.ofReal (r ^ (-alpha) * Kd * (CPw * (r⁻¹) ^ d * r ^ 2 * r ^ t1)) * BM +
            ENNReal.ofReal (r ^ (-alpha) * Kd) * BK +
            ENNReal.ofReal (r ^ (-alpha) * Kd * ((2 : ℝ) ^ (alpha + (d : ℝ) / 2) * cQ)) *
              (BX * (BΛ + BG))) +
          ENNReal.ofReal (PC * r * (r ^ (alpha + (d : ℝ) / 2))⁻¹) * (BΛ + BG) := by
  set μ := (chaosSampleLaw M).toMeasure with hμ
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal Pexp := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hP
  have hP2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * Pexp) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hle : ENNReal.ofReal Pexp ≤ ENNReal.ofReal (2 * Pexp) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hra : 0 ≤ r ^ (-alpha) := Real.rpow_nonneg hr.le _
  unfold aux_prop_growth_holder_macro_campanato_Kosc
  by_cases hN : kk ≤ N
  · simp only [if_pos hN]
    have hXmeas : Measurable (fun om : BilateralField d => (3 : ℝ) ^ (t1 * (Lm (N - kk) om : ℝ))) :=
      measurable_const.pow (measurable_const.mul
        ((measurable_from_nat (f := fun m : ℕ => (m : ℝ))).comp (hLmeas (N - kk))))
    have hXm : AEStronglyMeasurable
        (fun om => (3 : ℝ) ^ (t1 * (Lm (N - kk) (MacroAllCube.residualShift r kk om) : ℝ))) μ :=
      (hXmeas.comp hT.measurable).aestronglyMeasurable
    have hXT : eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lm (N - kk) (MacroAllCube.residualShift r kk om) : ℝ)))
        (ENNReal.ofReal (2 * Pexp)) μ ≤ BX := by
      have h := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal (2 * Pexp))
        hXmeas.aestronglyMeasurable hT
      exact (le_of_eq h).trans (hX (N - kk))
    have hRTm : AEStronglyMeasurable (fun om => Rs (MacroAllCube.residualShift r kk om)) μ :=
      (hRsm.comp hT.measurable).aestronglyMeasurable
    have hRT : eLpNorm (fun om => Rs (MacroAllCube.residualShift r kk om))
        (ENNReal.ofReal (2 * Pexp)) μ ≤ BR := by
      have h := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal (2 * Pexp))
        hRsm.aestronglyMeasurable hT
      exact (le_of_eq h).trans hR
    have hEm : AEStronglyMeasurable (aux_prop_growth_macro_energy_env M kk) μ :=
      (aux_prop_growth_macro_energy_measurable_env M kk).aestronglyMeasurable
    have hMm' : AEStronglyMeasurable
        (fun om => aux_prop_growth_holder_macro_campanato_side (N - kk) ^ e * Mx N om) μ :=
      (hMm N).const_mul _
    have hcombo := aux_prop_growth_holder_macro_campanato_moment_combo μ Pexp hP
      (r ^ (-alpha) * Kd * (2 * CS * (3 * d))) (r ^ (-alpha) * Kd * (2 * CS * cQ))
      (r ^ (-alpha) * Kd * (2 * CS * (2 * Cp))) (r ^ (-alpha) * Kd * (CPw * (r⁻¹) ^ d * r ^ 2 * r ^ t1))
      (r ^ (-alpha) * Kd) (r ^ (-alpha) * Kd * ((2 : ℝ) ^ (alpha + (d : ℝ) / 2) * cQ))
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
      (Λ N) (Kg N) _ _ _ (Kmac N) _ (hΛm N) (hKgm N) hRTm hEm hMm' (hKmm N) hXm
      BΛ BG BR BE BM BK BX (hΛ N) (hKg N) hRT hE (hM N) (hK N) hXT
    have hfun : (fun om => aux_prop_growth_holder_macro_campanato_Kmid d Kd CS Cp alpha t1 r e cQ CPw
        (N - kk) (Lm (N - kk) (MacroAllCube.residualShift r kk om)) (Λ N om) (Kg N om)
        (Rs (MacroAllCube.residualShift r kk om)) (aux_prop_growth_macro_energy_env M kk om)
        (Mx N om) (Kmac N om)) =
      (fun om => r ^ (-alpha) * Kd * (2 * CS * (3 * d)) +
        r ^ (-alpha) * Kd * (2 * CS * cQ) * (Λ N om + Kg N om) +
        r ^ (-alpha) * Kd * (2 * CS * (2 * Cp)) *
          (Rs (MacroAllCube.residualShift r kk om) * aux_prop_growth_macro_energy_env M kk om) +
        r ^ (-alpha) * Kd * (CPw * (r⁻¹) ^ d * r ^ 2 * r ^ t1) *
          (aux_prop_growth_holder_macro_campanato_side (N - kk) ^ e * Mx N om) +
        r ^ (-alpha) * Kd * Kmac N om +
        r ^ (-alpha) * Kd * ((2 : ℝ) ^ (alpha + (d : ℝ) / 2) * cQ) *
          ((3 : ℝ) ^ (t1 * (Lm (N - kk) (MacroAllCube.residualShift r kk om) : ℝ)) *
            (Λ N om + Kg N om))) := by
      funext om
      unfold aux_prop_growth_holder_macro_campanato_Kmid
      ring
    rw [hfun]
    exact ⟨hcombo.1, hcombo.2.trans le_self_add⟩
  · simp only [if_neg hN]
    have hsumm : AEStronglyMeasurable (fun om => Λ N om + Kg N om) μ := (hΛm N).add (hKgm N)
    have hc : 0 ≤ PC * r * (r ^ (alpha + (d : ℝ) / 2))⁻¹ := by positivity
    refine ⟨hsumm.const_mul _, ?_⟩
    have hsum2 : eLpNorm (fun om => Λ N om + Kg N om) (ENNReal.ofReal Pexp) μ ≤ BΛ + BG :=
      (eLpNorm_le_eLpNorm_of_exponent_le hle hsumm).trans
        ((eLpNorm_add_le (hΛm N) (hKgm N) hP2).trans (add_le_add (hΛ N) (hKg N)))
    have h := eLpNorm_const_smul_le (c := PC * r * (r ^ (alpha + (d : ℝ) / 2))⁻¹)
      (f := fun om => Λ N om + Kg N om) (p := ENNReal.ofReal Pexp) (μ := μ)
    rw [Real.enorm_of_nonneg hc] at h
    exact (h.trans (mul_le_mul_right hsum2 _)).trans le_add_self

end Paper

-- ===== MCChild =====
/-!
# `prop_growth_holder_macro_campanato`: the exact child of the Hölder reduction
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators Pointwise ContDiff
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The energy exponent `t₁`: strictly between `d - 1` and `d`, with `α ≤ α_M = 1-(d-t₁)/4`,
positive excess `2 + t₁ - 2α - d`, and `α + d/2 ≤ t₁`. -/
theorem aux_prop_growth_holder_macro_campanato_params (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ)
    (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∃ t1 : ℝ, (d : ℝ) - 1 < t1 ∧ t1 < d ∧ 0 ≤ t1 ∧ alpha ≤ 1 - ((d : ℝ) - t1) / 4 ∧
      0 < 2 + t1 - 2 * alpha - d ∧ alpha + (d : ℝ) / 2 ≤ t1 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set m0 := max (max ((d : ℝ) - 1) ((d : ℝ) - 4 * (1 - alpha)))
    (max ((d : ℝ) - 2 + 2 * alpha) (alpha + (d : ℝ) / 2)) with hm0
  have h1 := le_max_left (max ((d : ℝ) - 1) ((d : ℝ) - 4 * (1 - alpha)))
    (max ((d : ℝ) - 2 + 2 * alpha) (alpha + (d : ℝ) / 2))
  have h2 := le_max_right (max ((d : ℝ) - 1) ((d : ℝ) - 4 * (1 - alpha)))
    (max ((d : ℝ) - 2 + 2 * alpha) (alpha + (d : ℝ) / 2))
  have h11 := le_max_left ((d : ℝ) - 1) ((d : ℝ) - 4 * (1 - alpha))
  have h12 := le_max_right ((d : ℝ) - 1) ((d : ℝ) - 4 * (1 - alpha))
  have h21 := le_max_left ((d : ℝ) - 2 + 2 * alpha) (alpha + (d : ℝ) / 2)
  have h22 := le_max_right ((d : ℝ) - 2 + 2 * alpha) (alpha + (d : ℝ) / 2)
  have hm0d : m0 < d := by
    rw [hm0]
    refine max_lt (max_lt (by linarith) (by linarith)) (max_lt (by linarith) (by linarith))
  refine ⟨(m0 + d) / 2, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith⟩

/-- The floor moments absorbed by the residual wavelength factor. -/
theorem aux_prop_growth_holder_macro_campanato_mx_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ≥0∞) (Mx : Ω → ℝ) (e b CE : ℝ) (he : 0 < e)
    (hb : b ≤ (e / 2) * Real.log 3) (hCE : 0 ≤ CE) (N kk : ℕ)
    (hM : eLpNorm Mx p μ ≤ ENNReal.ofReal (CE * Real.exp (b * N))) :
    eLpNorm (fun om => aux_prop_growth_holder_macro_campanato_side (N - kk) ^ e * Mx om) p μ ≤
      ENNReal.ofReal ((3 : ℝ) ^ ((kk : ℝ) * e) * CE) := by
  have hs0 : 0 ≤ aux_prop_growth_holder_macro_campanato_side (N - kk) ^ e :=
    Real.rpow_nonneg (aux_prop_growth_holder_macro_campanato_side_pos _).le _
  have h := eLpNorm_const_smul_le (c := aux_prop_growth_holder_macro_campanato_side (N - kk) ^ e)
    (f := Mx) (p := p) (μ := μ)
  rw [Real.enorm_of_nonneg hs0] at h
  refine (h.trans (mul_le_mul_right hM _)).trans ?_
  rw [← ENNReal.ofReal_mul hs0]
  apply ENNReal.ofReal_le_ofReal
  have habs := aux_prop_growth_holder_macro_campanato_side_absorb e b he hb N kk
  calc aux_prop_growth_holder_macro_campanato_side (N - kk) ^ e * (CE * Real.exp (b * N))
      = CE * (aux_prop_growth_holder_macro_campanato_side (N - kk) ^ e * Real.exp (b * N)) := by ring
    _ ≤ CE * (3 : ℝ) ^ ((kk : ℝ) * e) := mul_le_mul_of_nonneg_left habs hCE
    _ = _ := by ring

/-- Nonnegativity of the final majorant. -/
theorem aux_prop_growth_holder_macro_campanato_Kosc_nonneg {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (kk : ℕ) (r t1 e alpha Kd CS Cp cQ CPw PC : ℝ)
    (Lm : ℕ → BilateralField d → ℕ) (Rs : BilateralField d → ℝ)
    (Λ Kg Mx Kmac : ℕ → BilateralField d → ℝ) (hr : 0 < r) (hKd : 0 ≤ Kd) (hCS : 0 ≤ CS)
    (hCp : 0 ≤ Cp) (hcQ : 0 ≤ cQ) (hCPw : 0 ≤ CPw) (hPC : 0 ≤ PC) (hRs : ∀ om, 0 ≤ Rs om)
    (hΛ : ∀ N om, 0 ≤ Λ N om) (hKg : ∀ N om, 0 ≤ Kg N om) (hMx : ∀ N om, 0 ≤ Mx N om)
    (hKmac : ∀ N om, 0 ≤ Kmac N om) (N : ℕ) (om : BilateralField d) :
    0 ≤ aux_prop_growth_holder_macro_campanato_Kosc M kk r t1 e alpha Kd CS Cp cQ CPw PC Lm Rs Λ Kg
      Mx Kmac N om := by
  unfold aux_prop_growth_holder_macro_campanato_Kosc
  have hΛ' := hΛ N om
  have hKg' := hKg N om
  split_ifs
  · unfold aux_prop_growth_holder_macro_campanato_Kmid
    have hE1 := aux_prop_growth_macro_energy_one_le_env M kk om
    have hMx' := hMx N om
    have hKm := hKmac N om
    have hRs' := hRs (MacroAllCube.residualShift r kk om)
    have hs := (aux_prop_growth_holder_macro_campanato_side_pos (N - kk)).le
    have hE0 : 0 ≤ aux_prop_growth_macro_energy_env M kk om := by linarith
    positivity
  · positivity

/-- The moment conjuncts from one uniform bound. -/
theorem aux_prop_growth_holder_macro_campanato_moment_conj {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} (ps : Fin k → ℝ) (Pexp : ℝ)
    (hpsP : ∀ i, ps i ≤ Pexp) (K : ℕ → Ω → ℝ) (Btot : ℝ≥0∞) (hfin : Btot ≠ ⊤)
    (hmom : ∀ N, AEStronglyMeasurable (K N) μ ∧ eLpNorm (K N) (ENNReal.ofReal Pexp) μ ≤ Btot) :
    (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) μ) ∧
      (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) μ ≤ ENNReal.ofReal ((fun _ : Fin k => Btot.toReal) i)) := by
  refine ⟨fun i N => ?_, fun i N => ?_⟩
  · obtain ⟨hm, hb⟩ := hmom N
    exact ⟨hm, lt_of_le_of_lt ((eLpNorm_le_eLpNorm_of_exponent_le
      (ENNReal.ofReal_le_ofReal (hpsP i)) hm).trans hb) (lt_top_iff_ne_top.2 hfin)⟩
  · obtain ⟨hm, hb⟩ := hmom N
    change _ ≤ ENNReal.ofReal Btot.toReal
    rw [ENNReal.ofReal_toReal hfin]
    exact (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (hpsP i)) hm).trans hb

/-- **The final assembly for one model and one root**, from explicit supplier outputs. -/
theorem aux_prop_growth_holder_macro_campanato_assemble {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {E : in_J d} (P : in_poincare d hd E)
    (Cp : ℝ) (hCp : 0 < Cp) (hFO : aux_prop_growth_holder_macro_campanato_FO (d := d) Cp)
    (CPw : ℝ) (hCPw : 0 ≤ CPw)
    (hPoinc : ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
      (v : meanZeroSobolevGraph (centeredCube c s hs)),
      ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).1 y) ^ 2 ≤
        CPw * s ^ 2 * ∑ i : Fin d, ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).2 i y) ^ 2)
    (alpha : ℝ) (ha0 : 0 < alpha) (Kd : ℝ) (hKd1 : 1 ≤ Kd)
    (hKd : aux_prop_growth_holder_macro_campanato_UnitProp d alpha Kd)
    {k : ℕ} (ps : Fin k → ℝ) (Pexp : ℝ) (hP1 : 1 ≤ Pexp) (hpsP : ∀ i, ps i ≤ Pexp)
    (M M' : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H H' : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (hH' : InfraredCharacterization M' H')
    (htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M'.P = SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
    (t1 e : ℝ) (ht10 : 0 ≤ t1)
    (hδC : M'.delta ≤ (aux_prop_growth_macro_energy_nativeSreg M').C⁻¹)
    (hα' : 1 - ((d : ℝ) - t1) / 4 ∈ (aux_prop_growth_macro_energy_nativeSreg M').alphaRange)
    (hαM : alpha ≤ 1 - ((d : ℝ) - t1) / 4)
    (he : 0 < e) (hexp : 2 + t1 = 2 * alpha + d + e) (ht1Y : alpha + (d : ℝ) / 2 ≤ t1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (kk : ℕ)
    (hk1 : 1 < r * (3 : ℝ) ^ kk) (hk3 : r * (3 : ℝ) ^ kk ≤ 3)
    (hT : MeasurePreserving (MacroAllCube.residualShift (d := d) r kk)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure)
    (hshift : ∀ n om, aux_prop_growth_macro_energy_shiftC M M' kk n om ≤
        aux_prop_growth_macro_energy_env M kk om ∧
      (aux_prop_growth_macro_energy_shiftC M M' kk n om)⁻¹ ≤ aux_prop_growth_macro_energy_env M kk om)
    (Lm : ℕ → BilateralField d → ℕ) (hLmeas : ∀ n, Measurable (Lm n))
    (hLpre : ∀ᵐ om' ∂(chaosSampleLaw M').toMeasure, ∀ N L0 : ℕ,
      ∃ L' : ℕ, L0 ≤ L' ∧
        (aux_prop_growth_macro_energy_nativeSreg M').prefixLen (N + L') (1 - ((d : ℝ) - t1) / 4) N
          ((3 : ℝ) ^ N • (r⁻¹ • z)) (aux_aux_macro_moment_bank_relabel N om') ≤ Lm N om')
    (BX : ℝ≥0∞) (hBX : BX ≠ ⊤)
    (hX : ∀ n, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lm n om : ℝ)))
      (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M').toMeasure ≤ BX)
    (hRmeas : Measurable fun om' => Real.exp ‖(H' om').restrict
      ((closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)))‖)
    (hRdom : ∀ om', ∀ x ∈ (closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)),
      Real.exp |H' om' x| ≤ Real.exp ‖(H' om').restrict
        ((closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)))‖)
    (hRmem : MemLp (fun om' => Real.exp ‖(H' om').restrict
      ((closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)))‖)
      (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M').toMeasure)
    (Kmac : ℕ → BilateralField d → ℝ) (BK : ℝ) (hKmac0 : ∀ N om, 0 ≤ Kmac N om)
    (hKmacmem : ∀ N, AEStronglyMeasurable (Kmac N) (chaosSampleLaw M).toMeasure)
    (hKmacnorm : ∀ N, eLpNorm (Kmac N) (ENNReal.ofReal Pexp) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal BK)
    (hmacE : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
        0 ≤ Kf →
        AEMeasurable F
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
      ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
        ContDiff ℝ 2 phi →
        c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
      ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
        SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
        ∀ (x : SpatialCoordinates d) (rad : ℝ),
          x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
          (3 : ℝ) ^ (-(N : ℤ)) ≤ rad →
          localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
              (s := Metric.ball x rad ∩
                (centeredCube z r hr : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter
                (centeredCube z r hr).isOpen.measurableSet)
              (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
            Kmac N om * (Kf + Cphi) ^ 2 * rad ^ t1)
    (Lg : ℕ → BilateralField d → ℕ) (Kg : ℕ → BilateralField d → ℝ) (BG : ℝ)
    (hKg0 : ∀ N om, 0 ≤ Kg N om)
    (hKgmem : ∀ N, AEStronglyMeasurable (Kg N) (chaosSampleLaw M).toMeasure)
    (hKgnorm : ∀ N, eLpNorm (Kg N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal BG)
    (hKgsrc : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
        0 ≤ Kf →
        AEMeasurable F
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          (3 : ℝ) ^ (t1 * (Lg N om : ℝ)) *
            sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
              (u : SobolevData (centeredCube z r hr))
              (u : SobolevData (centeredCube z r hr)) ≤
            Kg N om * (Kf + Cphi) ^ 2)
    (BL : ℝ)
    (hLmem : ∀ N, AEStronglyMeasurable (fun om : BilateralField d =>
      (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r (1 / 8) 1)⁻¹)
      (chaosSampleLaw M).toMeasure)
    (hLnorm : ∀ N, eLpNorm (fun om : BilateralField d =>
      (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r (1 / 8) 1)⁻¹)
      (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal BL)
    (Mx : ℕ → BilateralField d → ℝ) (BM : ℝ) (hMx0 : ∀ N om, 0 ≤ Mx N om)
    (hMxm : ∀ N, AEStronglyMeasurable (Mx N) (chaosSampleLaw M).toMeasure)
    (hMb : ∀ N, eLpNorm (fun om => aux_prop_growth_holder_macro_campanato_side (N - kk) ^ e * Mx N om)
      (ENNReal.ofReal Pexp) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal BM)
    (hext : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, 0 < Mx N om ∧
      ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        (Mx N om)⁻¹ ≤ cutoffCoefficient M H om N x) :
    ∃ (Kosc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kosc N om) ∧
        (∀ i N, MemLp (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, (3 : ℝ) ^ (-(N : ℤ)) ≤ rad → rad ≤ r →
            ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
                ((u : SobolevData (centeredCube z r hr)).1 y - setAverage
                  (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (u : SobolevData (centeredCube z r hr)).1) ^ 2
                ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
              (Kosc N om * (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
                volume.real (Metric.ball x rad ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hKgsrc' : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
        0 ≤ Kf →
        AEMeasurable F
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
              (u : SobolevData (centeredCube z r hr))
              (u : SobolevData (centeredCube z r hr)) ≤
            Kg N om * (Kf + Cphi) ^ 2 := by
    filter_upwards [hKgsrc] with om hom
    intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    have h := hom N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    have h3 : 1 ≤ (3 : ℝ) ^ (t1 * (Lg N om : ℝ)) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg ht10 (Nat.cast_nonneg _))
    exact (le_mul_of_one_le_left (sobolevCoefficientForm_nonneg _ _) h3).trans h
  have hΛle : ∀ N om, (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r 1 1)⁻¹ ≤
      (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r (1 / 8) 1)⁻¹ := fun N om =>
    inv_anti₀ (E.lam_pos _ _ _ _ _ _ _ _) (E.lam_mono _ _ _ _ _ _ _ _ _ (by norm_num))
  have hΛ0 : ∀ N om,
      0 ≤ (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r (1 / 8) 1)⁻¹ :=
    fun N om => (inv_pos.2 (E.lam_pos _ _ _ _ _ _ _ _)).le
  have hEmem := aux_prop_growth_macro_energy_memLp_env_pow M kk 1 (2 * Pexp) (by linarith)
  have henv1 : (fun om => aux_prop_growth_macro_energy_env M kk om ^ 1) =
      aux_prop_growth_macro_energy_env M kk := by funext om; rw [pow_one]
  rw [henv1] at hEmem
  have hmom := fun N => aux_prop_growth_holder_macro_campanato_Kosc_moment M M' kk r t1 e alpha Kd
    (aux_prop_growth_macro_energy_nativeSreg M').C Cp (Real.sqrt ((r⁻¹) ^ d * (P.C * r) ^ 2)) CPw P.C
    hr (le_trans zero_le_one hKd1) (aux_prop_growth_macro_energy_nativeSreg M').C_pos.le hCp.le
    (Real.sqrt_nonneg _) hCPw P.C_pos.le Pexp hP1 hT Lm hLmeas BX hX _ hRmeas _ le_rfl _ le_rfl
    (fun N om => (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r (1 / 8) 1)⁻¹) Kg Mx
    Kmac (ENNReal.ofReal BL) (ENNReal.ofReal BG) (ENNReal.ofReal BM) (ENNReal.ofReal BK)
    hLmem hLnorm hKgmem hKgnorm hMxm hMb hKmacmem hKmacnorm N
  set Btot := (ENNReal.ofReal (r ^ (-alpha) * Kd * (2 * (aux_prop_growth_macro_energy_nativeSreg M').C *
            (3 * d))) +
          ENNReal.ofReal (r ^ (-alpha) * Kd * (2 * (aux_prop_growth_macro_energy_nativeSreg M').C *
            Real.sqrt ((r⁻¹) ^ d * (P.C * r) ^ 2))) * (ENNReal.ofReal BL + ENNReal.ofReal BG) +
          ENNReal.ofReal (r ^ (-alpha) * Kd * (2 * (aux_prop_growth_macro_energy_nativeSreg M').C *
            (2 * Cp))) *
            (eLpNorm (fun om' => Real.exp ‖(H' om').restrict
                ((closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)))‖)
                (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M').toMeasure *
              eLpNorm (aux_prop_growth_macro_energy_env M kk) (ENNReal.ofReal (2 * Pexp))
                (chaosSampleLaw M).toMeasure) +
          ENNReal.ofReal (r ^ (-alpha) * Kd * (CPw * (r⁻¹) ^ d * r ^ 2 * r ^ t1)) *
            ENNReal.ofReal BM +
          ENNReal.ofReal (r ^ (-alpha) * Kd) * ENNReal.ofReal BK +
          ENNReal.ofReal (r ^ (-alpha) * Kd * ((2 : ℝ) ^ (alpha + (d : ℝ) / 2) *
            Real.sqrt ((r⁻¹) ^ d * (P.C * r) ^ 2))) *
            (BX * (ENNReal.ofReal BL + ENNReal.ofReal BG))) +
        ENNReal.ofReal (P.C * r * (r ^ (alpha + (d : ℝ) / 2))⁻¹) *
          (ENNReal.ofReal BL + ENNReal.ofReal BG) with hBtot
  have hfin : Btot ≠ ⊤ := by
    have hR := hRmem.2.ne
    have hE := hEmem.2.ne
    rw [hBtot]
    simp only [ne_eq, ENNReal.add_eq_top, ENNReal.mul_eq_top, ENNReal.ofReal_ne_top, hR, hE, hBX,
      false_and, and_false, or_self, not_false_eq_true]
  obtain ⟨hmem1, hmem2⟩ := aux_prop_growth_holder_macro_campanato_moment_conj
    (chaosSampleLaw M).toMeasure ps Pexp hpsP _ Btot hfin hmom
  exact ⟨_, _, aux_prop_growth_holder_macro_campanato_Kosc_nonneg M kk r t1 e alpha Kd _ Cp _ CPw
      P.C Lm _ _ Kg Mx Kmac hr (le_trans zero_le_one hKd1)
      (aux_prop_growth_macro_energy_nativeSreg M').C_pos.le hCp.le (Real.sqrt_nonneg _) hCPw
      P.C_pos.le (fun _ => (Real.exp_pos _).le) hΛ0 hKg0 hMx0 hKmac0, hmem1, hmem2,
    aux_prop_growth_holder_macro_campanato_ae_bound hd P Cp hCp.le hFO CPw hCPw hPoinc alpha
      ha0 Kd (le_trans zero_le_one hKd1) hKd M M' (aux_prop_growth_macro_energy_nativeSreg M') t1 e
      hδC hα' hαM he hexp ht1Y H H' hH hH' htau z r hr hr1 kk hk1 hk3 hT hshift Lm hLpre _ hRdom _
      Kg Mx Kmac hΛ0 hKg0 hKmac0 hΛle hKgsrc' hext hmacE⟩



theorem prop_growth_holder_macro_campanato :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E) (_X : in_extension d hd E)
    (_S : SobolevFoundationalInput d hd) (alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (Kosc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kosc N om) ∧
        (∀ i N, MemLp (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, (3 : ℝ) ^ (-(N : ℤ)) ≤ rad → rad ≤ r →
            ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
                ((u : SobolevData (centeredCube z r hr)).1 y - setAverage
                  (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (u : SobolevData (centeredCube z r hr)).1) ^ 2
                ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
              (Kosc N om * (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
                volume.real (Metric.ball x rad ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  intro d hd _ _ E P X S alpha k ps ha0 ha1 hps
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  -- one exponent for all listed orders
  obtain ⟨Pexp, hPdef⟩ : ∃ Pexp : ℝ, Pexp = 1 + ∑ i, ps i := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg fun i _ => by linarith [hps i]
  have hP1 : 1 ≤ Pexp := by rw [hPdef]; linarith
  have hpsP : ∀ i, ps i ≤ Pexp := by
    intro i
    rw [hPdef]
    have := Finset.single_le_sum (f := ps) (fun j _ => by linarith [hps j]) (Finset.mem_univ i)
    linarith
  -- the energy exponent and the excess
  obtain ⟨t1, ht1, ht2, ht10, hαM, he0, ht1Y⟩ :=
    aux_prop_growth_holder_macro_campanato_params d hd alpha ha0 ha1
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = 2 + t1 - 2 * alpha - d := ⟨_, rfl⟩
  have he : 0 < e := by rw [hedef]; exact he0
  have hexp : 2 + t1 = 2 * alpha + d + e := by rw [hedef]; ring
  -- suppliers, all fixed before the model
  obtain ⟨dMac, hdMac, hmacro⟩ := prop_growth_macro_energy d hd E P X S t1 1 (fun _ => Pexp)
    ht1 ht2 (fun _ => hP1)
  obtain ⟨dB, hdB, hbank⟩ := aux_macro_moment_bank d hd E P X S t1 1
    (fun _ => 2 * (2 * Pexp)) ht1 ht2 (fun _ => by linarith)
  obtain ⟨dA, hdA, hthr⟩ := aux_aux_macro_moment_bank_threshold (d := d) t1 (2 * Pexp) ht1 ht2
    ht10 (by linarith)
  obtain ⟨dLf, hdLf, hlamM⟩ := lane4_lambda_inv_moments d hd E (1 / 8)
    ⟨by norm_num, by norm_num⟩
  obtain ⟨Cpe, Cd, cd, hCpe, hCd, hcd, hroot⟩ :=
    aux_prop_growth_energy_assembly_root_extremes d hd Pexp hP1
  obtain ⟨CPw, hCPw0, hPoinc⟩ := aux_prop_growth_holder_micro_campanato_scaled_poincare d (by omega)
  obtain ⟨Cp, hCp, hFO⟩ := aux_prop_growth_holder_macro_campanato_FO_exists (d := d) hd
  obtain ⟨Kd, hKd1, hKd⟩ := aux_prop_growth_holder_macro_campanato_unit' (d := d) alpha ha0 ha1.le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hD0 := ResidualModel.residualDisorderFactor_pos d
  have hdL := hdLf (2 * Pexp) (by linarith)
  obtain ⟨dabs, hdabs⟩ : ∃ s : ℝ, s = min 1 ((e / 2) * Real.log 3 / (Cd + Cpe)) := ⟨_, rfl⟩
  have hdabs0 : 0 < dabs := by
    rw [hdabs]
    exact lt_min one_pos (div_pos (mul_pos (half_pos he) hlog3) (add_pos hCd hCpe))
  refine ⟨min dMac (min dB (min (dA / ResidualModel.residualDisorderFactor d)
    (min (2 * ResidualModel.residualDisorderFactor d)⁻¹ (min (dLf (2 * Pexp))
      (min (cd / (2 * Pexp)) dabs))))),
    lt_min hdMac (lt_min hdB (lt_min (div_pos hdA hD0) (lt_min (by positivity)
      (lt_min hdL (lt_min (div_pos hcd (by linarith)) hdabs0))))), ?_⟩
  intro M Rm Sreg It H hH hδ z r hr hr1
  have hδMac : M.delta ≤ dMac := hδ.trans (min_le_left _ _)
  have hδB : M.delta ≤ dB := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδA : M.delta ≤ dA / ResidualModel.residualDisorderFactor d :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδD : M.delta ≤ (2 * ResidualModel.residualDisorderFactor d)⁻¹ :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _))))
  have hδL : M.delta ≤ dLf (2 * Pexp) :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))))
  have hδc : M.delta ≤ cd / (2 * Pexp) :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
  have hδabs : M.delta ≤ dabs :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))))
  have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hrate : Cd * M.delta + Cpe * M.delta ^ 2 ≤ (e / 2) * Real.log 3 :=
    aux_prop_growth_holder_micro_campanato_rate Cd Cpe e M.delta hCd hCpe hdpos (hδabs.trans_eq hdabs)
  -- the residual scale and the bounded-dilation model `M_s`
  obtain ⟨kk, hk1, hk3⟩ := MacroAllCube.exists_residual_scale hr hr1
  obtain ⟨M', hM'⟩ : ∃ M' : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      M' = ResidualModel.residualModel M hk1.le hk3 hδD := ⟨_, rfl⟩
  have hT : MeasurePreserving (MacroAllCube.residualShift (d := d) r kk)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure := by
    rw [hM']; exact ResidualModel.measurePreserving_residualModel M r kk hk1.le hk3 hδD
  have htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M'.P = SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
    rw [hM']; exact ResidualModel.residualModel_tauSq M hk1.le hk3 hδD
  have hshift : ∀ n om, aux_prop_growth_macro_energy_shiftC M M' kk n om ≤
        aux_prop_growth_macro_energy_env M kk om ∧
      (aux_prop_growth_macro_energy_shiftC M M' kk n om)⁻¹ ≤
        aux_prop_growth_macro_energy_env M kk om := by
    intro n om; rw [hM']; exact aux_prop_growth_macro_energy_shiftC_bounds M hk1.le hk3 hδD kk n om
  have hδ' : M'.delta ≤ dA := by
    rw [hM', ResidualModel.residualModel_delta]
    rw [le_div_iff₀ hD0] at hδA
    linarith
  obtain ⟨hδC', hα', hκ'⟩ := hthr M' (aux_prop_growth_macro_energy_nativeSreg M') hδ'
  obtain ⟨H', hH'⟩ := exists_infraredCharacterization hd M'
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (1 - (1 - ((d : ℝ) - t1) / 4)) ^ 2 /
      ((aux_prop_growth_macro_energy_nativeSreg M').C * M'.delta ^ 2 * |Real.log M'.delta|) :=
    ⟨_, rfl⟩
  rw [← hκ] at hκ'
  have hlam : 0 ≤ 2 * (2 * Pexp) * t1 * Real.log 3 := by
    have : (0 : ℝ) ≤ Pexp := by linarith
    positivity
  have hκ0 : 0 < κ := lt_of_le_of_lt hlam hκ'
  obtain ⟨Lm, hLmeas, hLtail, hLpre⟩ := aux_aux_macro_moment_bank_prefix M'
    (aux_prop_growth_macro_energy_nativeSreg M') (1 - ((d : ℝ) - t1) / 4) κ hδC' hα' hκ hκ0
    (r⁻¹ • z)
  have hA1 : 1 ≤ (aux_prop_growth_macro_energy_nativeSreg M').C *
      Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) := by
    have h1 : 1 ≤ (aux_prop_growth_macro_energy_nativeSreg M').C :=
      (aux_prop_growth_macro_energy_nativeSreg M').C_ge_one
    have h2 : 1 ≤ Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) :=
      Real.one_le_exp (mul_nonneg hκ0.le (by linarith))
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hX4 : ∀ n, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lm n om : ℝ)))
      (ENNReal.ofReal (2 * (2 * Pexp))) (chaosSampleLaw M').toMeasure ≤
      ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M').C *
          Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) * Real.exp κ *
        (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^ (1 / (2 * (2 * Pexp))) :=
    fun n => aux_aux_macro_moment_bank_eLpNorm_rpow_three_le _ (Lm n) t1 (2 * (2 * Pexp))
      (by linarith) _ (aux_aux_macro_moment_bank_lintegral_exp_le (chaosSampleLaw M').toMeasure
        (Lm n) (hLmeas n) _ κ _ hA1 hlam hκ' (hLtail n))
  have hle24 : ENNReal.ofReal (2 * Pexp) ≤ ENNReal.ofReal (2 * (2 * Pexp)) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hX : ∀ n, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lm n om : ℝ)))
      (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M').toMeasure ≤
      ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M').C *
          Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) * Real.exp κ *
        (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^ (1 / (2 * (2 * Pexp))) := by
    intro n
    have hXmeas : Measurable (fun om : BilateralField d => (3 : ℝ) ^ (t1 * (Lm n om : ℝ))) :=
      measurable_const.pow (measurable_const.mul
        ((measurable_from_nat (f := fun m : ℕ => (m : ℝ))).comp (hLmeas n)))
    exact (eLpNorm_le_eLpNorm_of_exponent_le hle24 hXmeas.aestronglyMeasurable).trans (hX4 n)
  -- the macro energy of the actual problem
  obtain ⟨Kmac, CbK, hKmac0, hKmacmem, hKmacnorm, hmacE⟩ :=
    hmacro M Rm Sreg It H hH hδMac z r hr hr1
  -- the global energy
  obtain ⟨Lg, Kg, Cg, hKg0, hKgmem, hKgnorm, -, hKgsrc, -⟩ :=
    hbank M Rm Sreg It H hH hδB z r hr hr1
  -- the coarse ellipticity of the root
  obtain ⟨CbL, hLmem, hLnorm⟩ := hlamM M Rm H hH z r hr hr1 (2 * Pexp) (by linarith) hδL
  -- the coefficient floor
  obtain ⟨D, Mx, CE, hCE, hDMx0, hext, hmem, -, hMxmom⟩ := hroot M H hH hδc z r hr hr1
  -- the residual reference factor
  obtain ⟨hRmeas, hRdom, hRmem⟩ := aux_aux_macro_moment_bank_reference hd M' H' hH'
    (closedCube (r⁻¹ • z) 1 one_pos) (2 * Pexp) (by linarith)
  exact aux_prop_growth_holder_macro_campanato_assemble hd P Cp hCp hFO CPw hCPw0 hPoinc alpha ha0 Kd
    hKd1 hKd ps Pexp hP1 hpsP M M' H H' hH hH' htau t1 e ht10 hδC' hα' hαM he hexp ht1Y z r hr hr1 kk
    hk1 hk3 hT hshift Lm hLmeas hLpre _
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top) hX hRmeas hRdom hRmem
    Kmac (CbK 0) hKmac0 (fun N => (hKmacmem 0 N).1) (fun N => hKmacnorm 0 N) hmacE Lg Kg (Cg 0) hKg0
    (fun N => (hKgmem 0 N).1)
    (fun N => (eLpNorm_le_eLpNorm_of_exponent_le hle24 (hKgmem 0 N).1).trans (hKgnorm 0 N)) hKgsrc
    CbL (fun N => (hLmem N).1) hLnorm Mx _ (fun N om => (hDMx0 N om).2) (fun N => (hmem N).2.1)
    (fun N => aux_prop_growth_holder_macro_campanato_mx_moment _ _ (Mx N) e _ CE he hrate hCE N kk
      (hMxmom N))
    (by
      filter_upwards [hext] with om h
      intro N
      exact ⟨(h N).1, fun x hx => ((h N).2.1 x hx).1⟩)

end Paper
