module

public import SubdiffusiveProcess.Paper.lem_19_smooth_density_one_step_dilation
public import SubdiffusiveProcess.Lane2.ExternalInputs
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import SubdiffusiveProcess.Sobolev.FractionalRepresentatives

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace Paper

lemma aux_lem_19_smooth_density_one_step_mollification_mapsTo
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    Set.MapsTo (fun x : SpatialCoordinates d => z + r • x)
      (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d))
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  intro x hx
  change x ∈ Metric.ball 0 (1 / 2) at hx
  change z + r • x ∈ Metric.ball z (r / 2)
  rw [Metric.mem_ball, dist_eq_norm]
  have hx' : ‖x‖ < (1 / 2 : ℝ) := by
    simpa [Metric.mem_ball, dist_zero_right] using hx
  simpa [norm_smul, abs_of_pos hr, abs_of_nonneg (le_of_lt hr), div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using (by nlinarith : r * ‖x‖ < r * (1 / 2 : ℝ))

lemma aux_lem_19_smooth_density_one_step_mollification_quasi
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    Measure.QuasiMeasurePreserving (fun x : SpatialCoordinates d => z + r • x)
      (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)))
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hs : Measure.QuasiMeasurePreserving (fun x : SpatialCoordinates d => r • x)
      volume volume := Measure.quasiMeasurePreserving_smul (μ := volume) hr.ne'
  have ha : Measure.QuasiMeasurePreserving (fun x : SpatialCoordinates d => z + x)
      volume volume := MeasureTheory.quasiMeasurePreserving_add_left volume z
  have hcomp := ha.comp hs
  exact hcomp.restrict (aux_lem_19_smooth_density_one_step_mollification_mapsTo z hr)

lemma aux_lem_19_smooth_density_one_step_mollification_preimage
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    (fun x : SpatialCoordinates d => z + r • x) ⁻¹'
        (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)) := by
  ext x
  change z + r • x ∈ Metric.ball z (r / 2) ↔ x ∈ Metric.ball 0 (1 / 2)
  rw [Metric.mem_ball, Metric.mem_ball, dist_eq_norm, dist_zero_right]
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  constructor
  · intro h
    exact lt_of_mul_lt_mul_left (by simpa [div_eq_mul_inv, mul_comm] using h) hr.le
  · intro h
    have h' : r * ‖x‖ < r * (1 / 2 : ℝ) := by
      exact mul_lt_mul_of_pos_left h hr
    simpa [div_eq_mul_inv, mul_comm] using h'

lemma aux_lem_19_smooth_density_one_step_mollification_map
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    Measure.map (fun x : SpatialCoordinates d => z + r • x)
        (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d))) =
      ENNReal.ofReal ((r ^ d)⁻¹) •
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  let T : SpatialCoordinates d → SpatialCoordinates d := fun x => z + r • x
  have hglobal : Measure.map T volume = ENNReal.ofReal ((r ^ d)⁻¹) • volume := by
    have hcomp : T = (fun y : SpatialCoordinates d => z + y) ∘ (fun x => r • x) := by
      funext x
      rfl
    rw [hcomp, ← Measure.map_map (measurable_const_add z) (measurable_const_smul r)]
    rw [Measure.map_addHaar_smul volume hr.ne']
    rw [Measure.map_smul _ (show Measurable (fun y : SpatialCoordinates d => z + y) from by simpa using! measurable_const_add z).aemeasurable]
    rw [(inferInstance : Measure.IsAddLeftInvariant (volume : Measure (SpatialCoordinates d))).map_add_left_eq_self]
    have hp : 0 < (r ^ d)⁻¹ := inv_pos.mpr (pow_pos hr d)
    rw [Module.finrank_fin_fun, abs_of_pos hp]
  have hU : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have hcompT : T = (fun y : SpatialCoordinates d => z + y) ∘
      (fun x => r • x) := by
    funext x
    rfl
  have hcompT' : (fun y : SpatialCoordinates d => z + y) ∘
      (fun x => r • x) = (fun x : SpatialCoordinates d => z + r • x) := by
    rfl
  calc
    Measure.map T (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d))) =
        (Measure.map T volume).restrict (centeredCube z r hr : Set (SpatialCoordinates d)) := by
          rw [hcompT]
          rw [Measure.restrict_map
            ((measurable_const_add z).comp (measurable_const_smul r)) hU]
          rw [hcompT']
          rw [aux_lem_19_smooth_density_one_step_mollification_preimage z hr]
    _ = ENNReal.ofReal ((r ^ d)⁻¹) • volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d)) := by
          rw [hglobal, Measure.restrict_smul]

lemma aux_lem_19_smooth_density_one_step_mollification_inv_preimage
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    (fun x : SpatialCoordinates d => r⁻¹ • (x - z)) ⁻¹'
        (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)) =
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  ext x
  change r⁻¹ • (x - z) ∈ Metric.ball 0 (1 / 2) ↔
    x ∈ Metric.ball z (r / 2)
  rw [Metric.mem_ball, Metric.mem_ball, dist_zero_right, dist_eq_norm]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  constructor
  · intro h
    have h' := mul_lt_mul_of_pos_left h hr
    simpa [div_eq_mul_inv, mul_assoc, hr.ne'] using h'
  · intro h
    have h' := mul_lt_mul_of_pos_left h (inv_pos.mpr hr)
    simpa [div_eq_mul_inv, mul_assoc, hr.ne'] using h'

lemma aux_lem_19_smooth_density_one_step_mollification_inv_map
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    Measure.map (fun x : SpatialCoordinates d => r⁻¹ • (x - z))
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) =
      ENNReal.ofReal (r ^ d) •
        volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)) := by
  let S : SpatialCoordinates d → SpatialCoordinates d := fun x => r⁻¹ • (x - z)
  have hsub : Measurable (fun x : SpatialCoordinates d => x - z) := by
    fun_prop
  have hglobal : Measure.map S volume = ENNReal.ofReal (r ^ d) • volume := by
    have hcomp : S = (fun y : SpatialCoordinates d => r⁻¹ • y) ∘
        (fun x => x - z) := by
      funext x
      rfl
    rw [hcomp, ← Measure.map_map (measurable_const_smul r⁻¹) hsub]
    have hsub' : (fun x : SpatialCoordinates d => x - z) =
        (fun x => x + (-z)) := by
      funext x
      simp [sub_eq_add_neg]
    rw [hsub']
    rw [(inferInstance : Measure.IsAddRightInvariant (volume : Measure (SpatialCoordinates d))).map_add_right_eq_self]
    rw [Measure.map_addHaar_smul volume (inv_ne_zero hr.ne')]
    have hp : 0 < r ^ d := pow_pos hr d
    rw [Module.finrank_fin_fun]
    have heq : |(r⁻¹ ^ d)⁻¹| = r ^ d := by
      rw [inv_pow, inv_inv, abs_of_pos hp]
    rw [heq]
  have hU : MeasurableSet (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)) :=
    (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)).isOpen.measurableSet
  have hcompS : S = (fun y : SpatialCoordinates d => r⁻¹ • y) ∘
      (fun x => x - z) := by
    funext x
    rfl
  have hcompS' : (fun y : SpatialCoordinates d => r⁻¹ • y) ∘
      (fun x => x - z) = (fun x : SpatialCoordinates d => r⁻¹ • (x - z)) := by
    rfl
  calc
    Measure.map S (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) =
        (Measure.map S volume).restrict
        (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)) := by
          rw [hcompS]
          rw [hcompS']
          rw [Measure.restrict_map
            (f := fun x : SpatialCoordinates d => r⁻¹ • (x - z))
            ((measurable_const_smul r⁻¹).comp hsub) hU]
          rw [aux_lem_19_smooth_density_one_step_mollification_inv_preimage z hr]
    _ = ENNReal.ofReal (r ^ d) •
        volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)) := by
          rw [hglobal, Measure.restrict_smul]

lemma aux_lem_19_smooth_density_one_step_mollification_double_integral
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (H : (SpatialCoordinates d × SpatialCoordinates d) → ℝ≥0∞) :
    (∫⁻ x in (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)),
        H (z + r • x, z + r • y)) =
      (ENNReal.ofReal ((r ^ d)⁻¹)) ^ 2 *
        (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)), H (x, y)) := by
  let U₀ : Set (SpatialCoordinates d) :=
    centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  let μ₀ : Measure (SpatialCoordinates d) := volume.restrict U₀
  let μ : Measure (SpatialCoordinates d) := volume.restrict U
  let T : SpatialCoordinates d → SpatialCoordinates d := fun x => z + r • x
  let e : SpatialCoordinates d ≃ᵐ SpatialCoordinates d :=
    ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft z)).toMeasurableEquiv
  have he : (e : SpatialCoordinates d → SpatialCoordinates d) = T := by
    funext x
    simp [e, T, Homeomorph.trans_apply]
  have hemb : MeasurableEmbedding T := by
    rw [← he]
    exact e.measurableEmbedding
  have hmap : Measure.map T μ₀ = ENNReal.ofReal ((r ^ d)⁻¹) • μ := by
    simpa only [μ₀, μ, U₀, U, T] using
      aux_lem_19_smooth_density_one_step_mollification_map z hr
  let c : ℝ≥0∞ := ENNReal.ofReal ((r ^ d)⁻¹)
  have hc : c ≠ (⊤ : ℝ≥0∞) := by
    dsimp [c]
    exact ENNReal.ofReal_ne_top
  have hinner (x : SpatialCoordinates d) :
      (∫⁻ y, H (T x, T y) ∂μ₀) =
        c * (∫⁻ y, H (T x, y) ∂μ) := by
    calc
      (∫⁻ y, H (T x, T y) ∂μ₀) =
          ∫⁻ y, H (T x, y) ∂Measure.map T μ₀ := by
            symm
            exact hemb.lintegral_map (fun y => H (T x, y))
      _ = ∫⁻ y, H (T x, y) ∂(c • μ) := by rw [hmap]
      _ = c * (∫⁻ y, H (T x, y) ∂μ) := by
        rw [lintegral_smul_measure]
        rfl
  have houter :
      (∫⁻ x, ∫⁻ y, H (T x, T y) ∂μ₀ ∂μ₀) =
        c ^ 2 * (∫⁻ x, ∫⁻ y, H (x, y) ∂μ ∂μ) := by
    calc
      (∫⁻ x, ∫⁻ y, H (T x, T y) ∂μ₀ ∂μ₀) =
          ∫⁻ x, c * (∫⁻ y, H (T x, y) ∂μ) ∂μ₀ := by
            apply lintegral_congr
            exact fun x => hinner x
      _ = c * (∫⁻ x, (∫⁻ y, H (T x, y) ∂μ) ∂μ₀) := by
            simpa using (lintegral_const_mul' c
              (fun x => ∫⁻ y, H (T x, y) ∂μ) hc)
      _ = c * (∫⁻ x, (∫⁻ y, H (x, y) ∂μ) ∂Measure.map T μ₀) := by
            congr 1
            symm
            exact hemb.lintegral_map (fun x => ∫⁻ y, H (x, y) ∂μ)
      _ = c * (∫⁻ x, (∫⁻ y, H (x, y) ∂μ) ∂(c • μ)) := by
            rw [hmap]
      _ = c * (c * (∫⁻ x, ∫⁻ y, H (x, y) ∂μ ∂μ)) := by
            rw [lintegral_smul_measure]
            rfl
      _ = c ^ 2 * (∫⁻ x, ∫⁻ y, H (x, y) ∂μ ∂μ) := by ring
  simpa only [U₀, U, μ₀, μ, T, c, Measure.restrict_apply_univ] using houter

lemma aux_lem_19_smooth_density_one_step_mollification_distance_scale
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (x y : SpatialCoordinates d) :
    Real.sqrt (∑ j : Fin d, ((z + r • x) j - (z + r • y) j) ^ 2) =
      r * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
  have hsum : (∑ j : Fin d, ((z + r • x) j - (z + r • y) j) ^ 2) =
      r ^ 2 * (∑ j : Fin d, (x j - y j) ^ 2) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      (∑ j : Fin d, (z j + r * x j - (z j + r * y j)) ^ 2) =
          ∑ j : Fin d, (r * (x j - y j)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            congr 1
            ring
      _ = r ^ 2 * (∑ j : Fin d, (x j - y j) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
  rw [hsum, Real.sqrt_mul (sq_nonneg r)]
  rw [Real.sqrt_sq (le_of_lt hr)]

lemma aux_lem_19_smooth_density_one_step_mollification_integrand_scale
    {d k : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1) (G : Fin k → SpatialCoordinates d → ℝ)
    (x y : SpatialCoordinates d) :
    ENNReal.ofReal (∑ i : Fin k,
        (G i (z + r • x) - G i (z + r • y)) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
          ((z + r • x) j - (z + r • y) j) ^ 2)) ^
            ((d : ℝ) + 2 * (s : ℝ))) =
      (ENNReal.ofReal r) ^ (-((d : ℝ) + 2 * (s : ℝ))) *
        (ENNReal.ofReal (∑ i : Fin k,
          (G i (z + r • x) - G i (z + r • y)) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
            (x j - y j) ^ 2)) ^ ((d : ℝ) + 2 * (s : ℝ)))) := by
  let q : ℝ := (d : ℝ) + 2 * (s : ℝ)
  have hq : 0 < q := by
    dsimp [q]
    have hspos : 0 < (s : ℝ) := s.2.1
    nlinarith
  have hq0 : 0 ≤ q := hq.le
  let A : ℝ≥0∞ := ENNReal.ofReal (∑ i : Fin k,
      (G i (z + r • x) - G i (z + r • y)) ^ 2)
  let D₀ : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
      (x j - y j) ^ 2))
  let D : ℝ≥0∞ := D₀ ^ q
  let B : ℝ≥0∞ := ENNReal.ofReal r ^ q
  have hB0 : B ≠ 0 := by
    dsimp [B]
    exact (ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hr)
      ENNReal.ofReal_ne_top))
  have hBt : B ≠ ⊤ := by
    dsimp [B]
    exact ne_of_lt (ENNReal.rpow_lt_top_of_nonneg hq0 ENNReal.ofReal_ne_top)
  by_cases hD0 : D = 0
  · have hxy : x = y := by
      have hD₀ : D₀ = 0 := by
        rcases (ENNReal.rpow_eq_zero_iff.mp hD0) with h | h
        · exact h.1
        · exfalso
          linarith [hq]
      dsimp [D₀] at hD₀
      have hsqrt : Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) = 0 := by
        apply le_antisymm (ENNReal.ofReal_eq_zero.mp hD₀)
        exact Real.sqrt_nonneg _
      have hs : ∑ j : Fin d, (x j - y j) ^ 2 = 0 := by
        apply (Real.sqrt_eq_zero (Finset.sum_nonneg fun j _ => sq_nonneg (x j - y j))).mp
        exact hsqrt
      have hall : ∀ j : Fin d, x j - y j = 0 := by
        intro j
        have hj := (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => sq_nonneg (x i - y i))).mp hs j (Finset.mem_univ j)
        exact sq_eq_zero_iff.mp hj
      funext j
      linarith [hall j]
    subst y
    simp
  · have hDpos : 0 < D := (bot_lt_iff_ne_bot).mpr hD0
    have hDt : D ≠ ⊤ := by
      dsimp [D]
      exact ENNReal.rpow_ne_top_of_nonneg hq0 ENNReal.ofReal_ne_top
    have hden :
        ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
          ((z + r • x) j - (z + r • y) j) ^ 2)) ^ q = B * D := by
      rw [aux_lem_19_smooth_density_one_step_mollification_distance_scale z hr]
      dsimp [B, D]
      rw [ENNReal.ofReal_mul hr.le, ENNReal.mul_rpow_of_nonneg _ _ hq0]
    rw [show ((d : ℝ) + 2 * (s : ℝ)) = q by rfl]
    rw [hden]
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
    rw [ENNReal.mul_inv (Or.inl hB0) (Or.inl hBt)]
    rw [ENNReal.rpow_neg]
    dsimp [D, D₀, B]
    ac_rfl

lemma aux_lem_19_smooth_density_one_step_mollification_integrand_scale_back
    {d k : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1) (G : Fin k → SpatialCoordinates d → ℝ)
    (x y : SpatialCoordinates d) :
    ENNReal.ofReal (∑ i : Fin k,
        (G i (z + r • x) - G i (z + r • y)) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
          (x j - y j) ^ 2)) ^ ((d : ℝ) + 2 * (s : ℝ))) =
      (ENNReal.ofReal r) ^ ((d : ℝ) + 2 * (s : ℝ)) *
        (ENNReal.ofReal (∑ i : Fin k,
          (G i (z + r • x) - G i (z + r • y)) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
            ((z + r • x) j - (z + r • y) j) ^ 2)) ^
              ((d : ℝ) + 2 * (s : ℝ)))) := by
  let q : ℝ := (d : ℝ) + 2 * (s : ℝ)
  have hq : 0 < q := by
    dsimp [q]
    have hspos : 0 < (s : ℝ) := s.2.1
    nlinarith
  have hq0 : 0 ≤ q := hq.le
  let A : ℝ≥0∞ := ENNReal.ofReal (∑ i : Fin k,
      (G i (z + r • x) - G i (z + r • y)) ^ 2)
  let D₀ : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
      (x j - y j) ^ 2))
  let D : ℝ≥0∞ := D₀ ^ q
  let B : ℝ≥0∞ := ENNReal.ofReal r ^ q
  have hB0 : B ≠ 0 := by
    dsimp [B]
    exact (ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hr)
      ENNReal.ofReal_ne_top))
  have hBt : B ≠ ⊤ := by
    dsimp [B]
    exact ne_of_lt (ENNReal.rpow_lt_top_of_nonneg hq0 ENNReal.ofReal_ne_top)
  by_cases hD0 : D = 0
  · have hxy : x = y := by
      have hD₀ : D₀ = 0 := by
        rcases (ENNReal.rpow_eq_zero_iff.mp hD0) with h | h
        · exact h.1
        · exfalso
          linarith [hq]
      dsimp [D₀] at hD₀
      have hsqrt : Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) = 0 := by
        apply le_antisymm (ENNReal.ofReal_eq_zero.mp hD₀)
        exact Real.sqrt_nonneg _
      have hs : ∑ j : Fin d, (x j - y j) ^ 2 = 0 := by
        apply (Real.sqrt_eq_zero (Finset.sum_nonneg fun j _ => sq_nonneg (x j - y j))).mp
        exact hsqrt
      have hall : ∀ j : Fin d, x j - y j = 0 := by
        intro j
        have hj := (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => sq_nonneg (x i - y i))).mp hs j (Finset.mem_univ j)
        exact sq_eq_zero_iff.mp hj
      funext j
      linarith [hall j]
    subst y
    simp
  · have hDpos : 0 < D := (bot_lt_iff_ne_bot).mpr hD0
    have hDt : D ≠ ⊤ := by
      dsimp [D]
      exact ENNReal.rpow_ne_top_of_nonneg hq0 ENNReal.ofReal_ne_top
    have hden :
        ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
          ((z + r • x) j - (z + r • y) j) ^ 2)) ^ q = B * D := by
      rw [aux_lem_19_smooth_density_one_step_mollification_distance_scale z hr]
      dsimp [B, D]
      rw [ENNReal.ofReal_mul hr.le, ENNReal.mul_rpow_of_nonneg _ _ hq0]
    rw [show ((d : ℝ) + 2 * (s : ℝ)) = q by rfl]
    rw [hden]
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
    have hcancel : B * (B * D)⁻¹ = D⁻¹ := by
      rw [ENNReal.mul_inv (Or.inl hB0) (Or.inl hBt)]
      rw [← mul_assoc, ENNReal.mul_inv_cancel hB0 hBt]
      ac_rfl
    calc
      D⁻¹ * A = (B * (B * D)⁻¹) * A := by rw [hcancel]
      _ = B * ((B * D)⁻¹ * A) := by ac_rfl

lemma aux_lem_19_smooth_density_one_step_mollification_raw_seminorm_scale
    {d k : ℕ} (_hd : 2 ≤ d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1) (F : Fin k → SpatialCoordinates d → ℝ) :
    (((ENNReal.ofReal (s : ℝ) /
        volume (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d))) *
      ∫⁻ x in (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)),
          ENNReal.ofReal (∑ i : Fin k,
            (F i (z + r • x) - F i (z + r • y)) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
              (x j - y j) ^ 2))) ^ ((d : ℝ) + 2 * (s : ℝ))) ^ (1 / 2 : ℝ)) =
      (ENNReal.ofReal r) ^ (s : ℝ) *
        (((ENNReal.ofReal (s : ℝ) /
            volume (centeredCube z r hr : Set (SpatialCoordinates d))) *
          ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
              ENNReal.ofReal (∑ i : Fin k,
                (F i x - F i y) ^ 2) /
                (ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
                  (x j - y j) ^ 2))) ^ ((d : ℝ) + 2 * (s : ℝ))) ^
              (1 / 2 : ℝ)) := by
  let q : ℝ := (d : ℝ) + 2 * (s : ℝ)
  let U₀ : Set (SpatialCoordinates d) :=
    centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  let T : SpatialCoordinates d → SpatialCoordinates d := fun x => z + r • x
  let H : (SpatialCoordinates d × SpatialCoordinates d) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (∑ i : Fin k, (F i p.1 - F i p.2) ^ 2) /
      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (p.1 j - p.2 j) ^ 2))) ^ q
  let H₀ : (SpatialCoordinates d × SpatialCoordinates d) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (∑ i : Fin k,
      (F i (T p.1) - F i (T p.2)) ^ 2) /
      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
        (p.1 j - p.2 j) ^ 2))) ^ q
  let B : ℝ≥0∞ := ENNReal.ofReal r ^ q
  let c : ℝ≥0∞ := ENNReal.ofReal ((r ^ d)⁻¹)
  have hBtop : B ≠ (⊤ : ℝ≥0∞) := by
    dsimp [B]
    exact ENNReal.rpow_ne_top_of_nonneg (by
      dsimp [q]
      have hspos : 0 < (s : ℝ) := s.2.1
      nlinarith) ENNReal.ofReal_ne_top
  have hI :
      (∫⁻ x in U₀, ∫⁻ y in U₀, H₀ (x, y)) =
        B * c ^ 2 * (∫⁻ x in U, ∫⁻ y in U, H (x, y)) := by
    calc
      (∫⁻ x in U₀, ∫⁻ y in U₀, H₀ (x, y)) =
          ∫⁻ x in U₀, ∫⁻ y in U₀, B * H (T x, T y) := by
            apply lintegral_congr
            intro x
            apply lintegral_congr
            intro y
            exact aux_lem_19_smooth_density_one_step_mollification_integrand_scale_back
              z hr s F x y
      _ = ∫⁻ x in U₀, B * (∫⁻ y in U₀, H (T x, T y)) := by
            apply lintegral_congr
            intro x
            rw [lintegral_const_mul' B _ hBtop]
      _ = B * (∫⁻ x in U₀, ∫⁻ y in U₀, H (T x, T y)) := by
            rw [lintegral_const_mul' B _ hBtop]
      _ = B * (c ^ 2 * (∫⁻ x in U, ∫⁻ y in U, H (x, y))) := by
            rw [aux_lem_19_smooth_density_one_step_mollification_double_integral z hr H]
      _ = B * c ^ 2 * (∫⁻ x in U, ∫⁻ y in U, H (x, y)) := by ring
  let R : ℝ≥0∞ := ENNReal.ofReal r
  have hR0 : R ≠ 0 := by
    dsimp [R]
    exact (ENNReal.ofReal_pos.mpr hr).ne'
  have hRt : R ≠ ⊤ := by
    dsimp [R]
    exact ENNReal.ofReal_ne_top
  have hrd : 0 < r ^ d := pow_pos hr d
  have hRd : ENNReal.ofReal (r ^ d) = R ^ d := by
    dsimp [R]
    rw [ENNReal.ofReal_pow hr.le]
  have hqsplit : R ^ q = R ^ d * R ^ (2 * (s : ℝ)) := by
    rw [show q = (d : ℝ) + 2 * (s : ℝ) by rfl]
    rw [ENNReal.rpow_add _ _ hR0 hRt, ENNReal.rpow_natCast]
  have hRd0 : R ^ d ≠ 0 := pow_ne_zero d hR0
  have hRdt : R ^ d ≠ ⊤ := by
    exact ENNReal.pow_ne_top hRt
  have hscale : B * c ^ 2 = R ^ (2 * (s : ℝ)) / ENNReal.ofReal (r ^ d) := by
    calc
      B * c ^ 2 = R ^ q * (R ^ d)⁻¹ ^ 2 := by
        dsimp [B, c, R]
        rw [ENNReal.ofReal_inv_of_pos hrd, hRd]
      _ = (R ^ d * R ^ (2 * (s : ℝ))) * (R ^ d)⁻¹ ^ 2 := by rw [hqsplit]
      _ = R ^ (2 * (s : ℝ)) * (R ^ d)⁻¹ := by
        rw [pow_two]
        rw [show R ^ d * R ^ (2 * (s : ℝ)) *
            ((R ^ d)⁻¹ * (R ^ d)⁻¹) =
          (R ^ d * (R ^ d)⁻¹) *
            (R ^ (2 * (s : ℝ)) * (R ^ d)⁻¹) by ac_rfl]
        rw [ENNReal.mul_inv_cancel hRd0 hRdt]
        simp
      _ = R ^ (2 * (s : ℝ)) /
          ENNReal.ofReal (r ^ d) := by
        rw [hRd, ENNReal.div_eq_inv_mul]
        ac_rfl
  have hbase :
      (ENNReal.ofReal (s : ℝ) /
          volume (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d))) *
          (∫⁻ x in U₀, ∫⁻ y in U₀, H₀ (x, y)) =
        R ^ (2 * (s : ℝ)) *
          ((ENNReal.ofReal (s : ℝ) /
            volume (centeredCube z r hr : Set (SpatialCoordinates d))) *
            (∫⁻ x in U, ∫⁻ y in U, H (x, y))) := by
    rw [hI, hscale]
    simp only [U, centeredCube_volume]
    simp only [ENNReal.ofReal_one, one_pow]
    simp
    simp only [ENNReal.div_eq_inv_mul]
    ac_rfl
  have hsqrt :
      ((ENNReal.ofReal (s : ℝ) /
          volume (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d))) *
          (∫⁻ x in U₀, ∫⁻ y in U₀, H₀ (x, y))) ^ (1 / 2 : ℝ) =
        R ^ (s : ℝ) *
          (((ENNReal.ofReal (s : ℝ) /
            volume (centeredCube z r hr : Set (SpatialCoordinates d))) *
            (∫⁻ x in U, ∫⁻ y in U, H (x, y))) ^ (1 / 2 : ℝ)) := by
    rw [hbase, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    rw [← ENNReal.rpow_mul]
    congr 1
    rw [show (2 * (s : ℝ)) * (1 / 2 : ℝ) = (s : ℝ) by ring]
  simpa only [U₀, U, T, H₀, H, q, R] using hsqrt

lemma aux_lem_19_smooth_density_one_step_mollification_seminorm_eq_raw
    {d k : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1)
    (f : Fin k → DomainL2 (centeredCube z r hr))
    (g : Fin k → SpatialCoordinates d → ℝ)
    (hfg : ∀ i, (f i : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g i) :
    cubeFractionalL2Seminorm hd z r hr s f =
      (((ENNReal.ofReal (s : ℝ) /
        volume (centeredCube z r hr : Set (SpatialCoordinates d))) *
      ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal (∑ i : Fin k, (g i x - g i y) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
              (x j - y j) ^ 2))) ^ ((d : ℝ) + 2 * (s : ℝ))) ^ (1 / 2 : ℝ)) := by
  unfold cubeFractionalL2Seminorm
  rw [fractional_square_integral_congr_ae
    (fun i x => (f i : SpatialCoordinates d → ℝ) x) g hfg (s : ℝ)]

lemma aux_lem_19_smooth_density_one_step_mollification_norm_smul_measure
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ)
    (hg : MemLp g (2 : ℝ≥0∞) μ) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    ‖(hg.smul_measure hc).toLp g‖ =
      (c ^ (1 / (2 : ℝ≥0∞)).toReal).toReal * ‖hg.toLp g‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  rw [eLpNorm_smul_measure_of_ne_top (p := (2 : ℝ≥0∞)) (by norm_num) g c hg.aestronglyMeasurable]
  simp only [smul_eq_mul, ENNReal.toReal_mul]

/-- Enlarged-cube mollification step in the smooth-density construction,
paper 1934–1939.
Carried-input tick list:
- SOURCE: dimension `d ≥ 2`, arbitrary centre `z`, positive side `r`, the
  half-fractional class `v`, and an inward factor `λ ∈ (0,1)`.
- DEPENDENCY: `lem_19_smooth_density_one_step_dilation` supplies the class
  `u` representing the inwardly dilated datum on the original cube.
- SOURCE: a positive mollification tolerance `η`.
- CONCLUDED HERE: an ambient smooth `f`, its actual fractional class `a`,
  and a class `mollErr` representing `u - a`, with error below `η`.
The enlarged-cube extension, Jensen estimate, and translation continuity are
the construction in the cited paper step, not carried hypotheses. -/
theorem lem_19_smooth_density_one_step_mollification
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r)
    (v : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder)
    (lam : Set.Ioo (0 : ℝ) 1)
    (u : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder)
    (hu : (u.val 0 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        (v.val 0 : SpatialCoordinates d → ℝ) ∘
        (fun x : SpatialCoordinates d => z + (lam : ℝ) • (x - z)))
    {η : ℝ} (hη : 0 < η) :
    ∃ (a : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder)
      (f : SpatialCoordinates d → ℝ)
      (mollErr : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder),
      ContDiff ℝ ∞ f ∧
      ((a.val 0 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f) ∧
      mollErr.val 0 = u.val 0 - a.val 0 ∧
      cubeFractionalL2Norm hd z r hr halfFractionalOrder mollErr < η := by
  have _ := hu
  let U₀ : Set (SpatialCoordinates d) :=
    centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  let μ₀ : Measure (SpatialCoordinates d) := volume.restrict U₀
  let μ : Measure (SpatialCoordinates d) := volume.restrict U
  let T : SpatialCoordinates d → SpatialCoordinates d := fun x => z + r • x
  let S : SpatialCoordinates d → SpatialCoordinates d := fun x => r⁻¹ • (x - z)
  let c : ℝ≥0∞ := ENNReal.ofReal ((r ^ d)⁻¹)
  let c' : ℝ≥0∞ := ENNReal.ofReal (r ^ d)
  have hTpres : MeasurePreserving T μ₀ (c • μ) := by
    refine ⟨by fun_prop, ?_⟩
    simpa only [T, μ₀, μ, c] using
      aux_lem_19_smooth_density_one_step_mollification_map z hr
  have hSpres : MeasurePreserving S μ (c' • μ₀) := by
    refine ⟨by fun_prop, ?_⟩
    simpa only [S, μ₀, μ, c'] using
      aux_lem_19_smooth_density_one_step_mollification_inv_map z hr
  have hc_top : c ≠ (⊤ : ℝ≥0∞) := by
    dsimp [c]
    exact ENNReal.ofReal_ne_top
  have hc'_top : c' ≠ (⊤ : ℝ≥0∞) := by
    dsimp [c']
    exact ENNReal.ofReal_ne_top
  have huc : MemLp (u.val 0) (2 : ℝ≥0∞) (c • μ) :=
    (Lp.memLp (u.val 0)).smul_measure hc_top
  let u₀ : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)) :=
    Lp.compMeasurePreserving T hTpres (huc.toLp (u.val 0))
  have hu₀ae : (u₀ : SpatialCoordinates d → ℝ) =ᵐ[μ₀]
      (u.val 0 : SpatialCoordinates d → ℝ) ∘ T := by
    dsimp [u₀]
    exact (Lp.coeFn_compMeasurePreserving (huc.toLp (u.val 0)) hTpres).trans
      (hTpres.quasiMeasurePreserving.ae_eq (huc.coeFn_toLp))
  have hu₀semi_raw :=
    aux_lem_19_smooth_density_one_step_mollification_seminorm_eq_raw
      (k := 1) hd (0 : SpatialCoordinates d) 1 (by norm_num) halfFractionalOrder
      (fun _ : Fin 1 => u₀) (fun _ : Fin 1 => (u.val 0 : SpatialCoordinates d → ℝ) ∘ T)
      (by intro i; fin_cases i; simpa [U₀, μ₀] using hu₀ae)
  have hu_semi_raw :=
    aux_lem_19_smooth_density_one_step_mollification_seminorm_eq_raw
      (k := 1) hd z r hr halfFractionalOrder u.val
      (fun _ : Fin 1 => (u.val 0 : SpatialCoordinates d → ℝ))
      (by intro i; fin_cases i; exact Filter.Eventually.of_forall (fun _ => rfl))
  have hu₀finite : cubeFractionalL2Seminorm hd 0 1 (by norm_num)
      halfFractionalOrder (fun _ : Fin 1 => u₀) < ⊤ := by
    rw [hu₀semi_raw]
    have hscale := aux_lem_19_smooth_density_one_step_mollification_raw_seminorm_scale
      hd z (r := r) hr halfFractionalOrder
        (fun _ : Fin 1 => (u.val 0 : SpatialCoordinates d → ℝ))
    simp only [T, Function.comp_apply] at hscale ⊢
    rw [hscale]
    have hsemi : cubeFractionalL2Seminorm hd z r hr halfFractionalOrder u.val < ⊤ := u.property
    rw [hu_semi_raw] at hsemi
    have hRpowtop : ENNReal.ofReal r ^ (halfFractionalOrder : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (le_of_lt halfFractionalOrder.2.1)
        ENNReal.ofReal_ne_top
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hRpowtop) hsemi
  let Q₀ : Homogenization.TriadicCube d := Homogenization.originCube d 0
  have hcenter : Homogenization.cubeCenter Q₀ = 0 := by
    funext i
    simp [Q₀, Homogenization.cubeCenter, Homogenization.originCube,
      Homogenization.cubeScaleFactor]
  have hscaleQ : Homogenization.cubeScaleFactor Q₀ = 1 := by
    simp [Q₀, Homogenization.originCube, Homogenization.cubeScaleFactor]
  let hQ₀ : 0 < Homogenization.cubeScaleFactor Q₀ := by
    dsimp [Q₀]
    simp
  have hcube : centeredCube (Homogenization.cubeCenter Q₀)
      (Homogenization.cubeScaleFactor Q₀) hQ₀ =
        centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) := by
    simp [hcenter, hscaleQ]
  have hset : (centeredCube (Homogenization.cubeCenter Q₀)
      (Homogenization.cubeScaleFactor Q₀) hQ₀ : Set (SpatialCoordinates d)) =
        (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
          Set (SpatialCoordinates d)) := congrArg (fun O : Opens (SpatialCoordinates d) =>
            (O : Set (SpatialCoordinates d))) hcube
  let μQ : Measure (SpatialCoordinates d) :=
    volume.restrict (centeredCube (Homogenization.cubeCenter Q₀)
      (Homogenization.cubeScaleFactor Q₀) hQ₀ : Set (SpatialCoordinates d))
  have hμQ : μQ = μ₀ := by
    dsimp [μQ, μ₀]
    rw [hset]
  have hTpresQ : MeasurePreserving T μQ (c • μ) := by
    rw [hμQ]
    exact hTpres
  have hSpresQ : MeasurePreserving S μ (c' • μQ) := by
    rw [hμQ]
    exact hSpres
  let uQ : DomainL2 (centeredCube (Homogenization.cubeCenter Q₀)
      (Homogenization.cubeScaleFactor Q₀) hQ₀) :=
    Lp.compMeasurePreserving T hTpresQ (huc.toLp (u.val 0))
  have huQae : (uQ : SpatialCoordinates d → ℝ) =ᵐ[μQ]
      (u.val 0 : SpatialCoordinates d → ℝ) ∘ T := by
    dsimp [uQ]
    exact (Lp.coeFn_compMeasurePreserving (huc.toLp (u.val 0)) hTpresQ).trans
      (hTpresQ.quasiMeasurePreserving.ae_eq (huc.coeFn_toLp))
  have huQsemi_raw :=
    aux_lem_19_smooth_density_one_step_mollification_seminorm_eq_raw
      (k := 1) hd (Homogenization.cubeCenter Q₀)
      (Homogenization.cubeScaleFactor Q₀) hQ₀ halfFractionalOrder
      (fun _ : Fin 1 => uQ) (fun _ : Fin 1 => (u.val 0 : SpatialCoordinates d → ℝ) ∘ T)
      (by intro i; fin_cases i; exact huQae)
  let δ : ℝ := η * r ^ (halfFractionalOrder : ℝ)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have huQfinite : cubeFractionalL2Seminorm hd
      (Homogenization.cubeCenter Q₀) (Homogenization.cubeScaleFactor Q₀) hQ₀
      halfFractionalOrder (fun _ : Fin 1 => uQ) < ⊤ := by
    rw [huQsemi_raw]
    have hscale := aux_lem_19_smooth_density_one_step_mollification_raw_seminorm_scale
      hd z (r := r) hr halfFractionalOrder
        (fun _ : Fin 1 => (u.val 0 : SpatialCoordinates d → ℝ))
    simp only [hcenter, hscaleQ] at hscale ⊢
    simp only [T, Function.comp_apply] at hscale ⊢
    rw [hscale]
    have hsemi : cubeFractionalL2Seminorm hd z r hr halfFractionalOrder u.val < ⊤ := u.property
    rw [hu_semi_raw] at hsemi
    have hRpowtop : ENNReal.ofReal r ^ (halfFractionalOrder : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (le_of_lt halfFractionalOrder.2.1)
        ENNReal.ofReal_ne_top
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hRpowtop) hsemi
  let uQ' : CubeFractionalL2 (k := 1) hd
      (Homogenization.cubeCenter Q₀) (Homogenization.cubeScaleFactor Q₀) hQ₀
      halfFractionalOrder := ⟨fun _ : Fin 1 => uQ, huQfinite⟩
  obtain ⟨aQ, happrox, eQ⟩ :=
    SubdiffusiveProcess.exists_scalarCubeFractionalL2_globalSmooth_sub_norm_lt
      hd Q₀ hQ₀ halfFractionalOrder uQ' hδ
  obtain ⟨f₀, hf₀, haQ⟩ := happrox
  obtain ⟨eQ, heQ, heQnorm⟩ := eQ
  let pushLp (g : DomainL2 (centeredCube (Homogenization.cubeCenter Q₀)
      (Homogenization.cubeScaleFactor Q₀) hQ₀)) :
    DomainL2 (centeredCube z r hr) :=
    Lp.compMeasurePreserving S hSpresQ
      (((Lp.memLp g).smul_measure hc'_top).toLp
        (g : SpatialCoordinates d → ℝ)
      )
  have hpushae (g : DomainL2 (centeredCube (Homogenization.cubeCenter Q₀)
      (Homogenization.cubeScaleFactor Q₀) hQ₀)) :
      (pushLp g : SpatialCoordinates d → ℝ) =ᵐ[μ]
        (g : SpatialCoordinates d → ℝ) ∘ S := by
    dsimp [pushLp]
    exact (Lp.coeFn_compMeasurePreserving
      (((Lp.memLp g).smul_measure hc'_top).toLp
        (g : SpatialCoordinates d → ℝ)) hSpresQ).trans
      (hSpresQ.quasiMeasurePreserving.ae_eq
        (((Lp.memLp g).smul_measure hc'_top).coeFn_toLp))
  have hpush_semirel (g : DomainL2 (centeredCube (Homogenization.cubeCenter Q₀)
      (Homogenization.cubeScaleFactor Q₀) hQ₀)) :
      cubeFractionalL2Seminorm hd z r hr halfFractionalOrder
          (fun _ : Fin 1 => pushLp g) =
        (ENNReal.ofReal r) ^ (-(halfFractionalOrder : ℝ)) *
          cubeFractionalL2Seminorm hd (Homogenization.cubeCenter Q₀)
            (Homogenization.cubeScaleFactor Q₀) hQ₀ halfFractionalOrder
              (fun _ : Fin 1 => g) := by
    let F : Fin 1 → SpatialCoordinates d → ℝ :=
      fun _ => (g : SpatialCoordinates d → ℝ) ∘ S
    have hST (x : SpatialCoordinates d) : S (T x) = x := by
      dsimp [S, T]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply]
      field_simp [hr.ne']
      ring
    have hFT (i : Fin 1) (x : SpatialCoordinates d) :
        F i (z + r • x) = (g : SpatialCoordinates d → ℝ) x := by
      dsimp [F]
      change (g : SpatialCoordinates d → ℝ) (S (T x)) = _
      rw [hST]
    have htarget_raw :=
      aux_lem_19_smooth_density_one_step_mollification_seminorm_eq_raw
        (k := 1) hd z r hr halfFractionalOrder
        (fun _ : Fin 1 => pushLp g) F
        (by intro i; fin_cases i; exact hpushae g)
    have hsource_raw :=
      aux_lem_19_smooth_density_one_step_mollification_seminorm_eq_raw
        (k := 1) hd (Homogenization.cubeCenter Q₀)
        (Homogenization.cubeScaleFactor Q₀) hQ₀ halfFractionalOrder
        (fun _ : Fin 1 => g)
        (fun _ : Fin 1 => (g : SpatialCoordinates d → ℝ))
        (by intro i; fin_cases i; exact Filter.Eventually.of_forall (fun _ => rfl))
    have hscale :=
      aux_lem_19_smooth_density_one_step_mollification_raw_seminorm_scale
        hd z (r := r) hr halfFractionalOrder F
    simp only [hcenter, hscaleQ] at hscale hsource_raw
    simp_rw [hFT] at hscale
    have hR0 : ENNReal.ofReal r ≠ 0 := ENNReal.ofReal_pos.mpr hr |>.ne'
    have hRt : ENNReal.ofReal r ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
    have hp0 : (ENNReal.ofReal r) ^ (halfFractionalOrder : ℝ) ≠ 0 :=
      (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hr) hRt).ne'
    have hpt : (ENNReal.ofReal r) ^ (halfFractionalOrder : ℝ) ≠ (⊤ : ℝ≥0∞) :=
      ENNReal.rpow_ne_top_of_nonneg halfFractionalOrder.2.1.le hRt
    have hinv : (ENNReal.ofReal r) ^ (-(halfFractionalOrder : ℝ)) *
        (ENNReal.ofReal r) ^ (halfFractionalOrder : ℝ) = 1 := by
      rw [ENNReal.rpow_neg]
      exact ENNReal.inv_mul_cancel hp0 hpt
    rw [htarget_raw, hsource_raw]
    rw [hscale]
    rw [← mul_assoc, hinv, one_mul]
  have hpush_normrel (g : DomainL2 (centeredCube (Homogenization.cubeCenter Q₀)
      (Homogenization.cubeScaleFactor Q₀) hQ₀)) :
      ‖pushLp g‖ /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) =
        ‖g‖ /
          Real.sqrt (volume.real (centeredCube (Homogenization.cubeCenter Q₀)
            (Homogenization.cubeScaleFactor Q₀) hQ₀ : Set (SpatialCoordinates d))) := by
    have hnorm : ‖pushLp g‖ =
        (c' ^ (1 / (2 : ℝ≥0∞)).toReal).toReal * ‖g‖ := by
      dsimp [pushLp]
      rw [Lp.norm_compMeasurePreserving]
      rw [aux_lem_19_smooth_density_one_step_mollification_norm_smul_measure
        μQ (g : SpatialCoordinates d → ℝ) (Lp.memLp g) hc'_top]
      rw [Lp.norm_toLp]
      rfl
    have hc'pow :
        (c' ^ (1 / (2 : ℝ≥0∞)).toReal).toReal = Real.sqrt (r ^ d) := by
      dsimp [c']
      rw [← ENNReal.toReal_rpow]
      rw [ENNReal.toReal_ofReal (pow_nonneg hr.le d)]
      norm_num [Real.sqrt_eq_rpow]
    have hvol : volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) = r ^ d :=
      centeredCube_volume_real z hr
    have hvolQ : volume.real (centeredCube (Homogenization.cubeCenter Q₀)
        (Homogenization.cubeScaleFactor Q₀) hQ₀ : Set (SpatialCoordinates d)) = 1 := by
      let h1 : (0 : ℝ) < (1 : ℝ) := by norm_num
      have hset' : (centeredCube (Homogenization.cubeCenter Q₀)
          (Homogenization.cubeScaleFactor Q₀) hQ₀ : Set (SpatialCoordinates d)) =
          (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) := by
        simpa using hset
      rw [hset']
      have hvol1 : volume.real (centeredCube (0 : SpatialCoordinates d) 1 h1 :
          Set (SpatialCoordinates d)) = (1 : ℝ) ^ d :=
        centeredCube_volume_real (0 : SpatialCoordinates d) h1
      simpa using hvol1
    rw [hnorm, hc'pow, hvol, hvolQ]
    rw [Real.sqrt_one]
    have hsqrt : Real.sqrt (r ^ d) ≠ 0 :=
      (Real.sqrt_pos.2 (pow_pos hr d)).ne'
    field_simp [hsqrt]
  have haQsemi : cubeFractionalL2Seminorm hd z r hr halfFractionalOrder
      (fun _ : Fin 1 => pushLp (aQ.val 0)) < ⊤ := by
    rw [hpush_semirel]
    have hbase0 : ENNReal.ofReal r ≠ 0 := ENNReal.ofReal_pos.mpr hr |>.ne'
    have hpowtop : (ENNReal.ofReal r) ^ (-(halfFractionalOrder : ℝ)) ≠ ⊤ := by
      intro h
      rw [ENNReal.rpow_eq_top_iff] at h
      rcases h with h | h
      · exact hbase0 h.1
      · exact ENNReal.ofReal_ne_top h.1
    exact ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr hpowtop) aQ.property
  have heQsemi : cubeFractionalL2Seminorm hd z r hr halfFractionalOrder
      (fun _ : Fin 1 => pushLp (eQ.val 0)) < ⊤ := by
    rw [hpush_semirel]
    have hbase0 : ENNReal.ofReal r ≠ 0 := ENNReal.ofReal_pos.mpr hr |>.ne'
    have hpowtop : (ENNReal.ofReal r) ^ (-(halfFractionalOrder : ℝ)) ≠ ⊤ := by
      intro h
      rw [ENNReal.rpow_eq_top_iff] at h
      rcases h with h | h
      · exact hbase0 h.1
      · exact ENNReal.ofReal_ne_top h.1
    exact ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr hpowtop) eQ.property
  let a : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder :=
    ⟨fun _ : Fin 1 => pushLp (aQ.val 0), haQsemi⟩
  let mollErr : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder :=
    ⟨fun _ : Fin 1 => pushLp (eQ.val 0), heQsemi⟩
  have hc'0 : c' ≠ 0 := by
    dsimp [c']
    exact (ENNReal.ofReal_pos.mpr (pow_pos hr d)).ne'
  have hcoeff : ((ENNReal.ofReal r) ^ (-(halfFractionalOrder : ℝ))).toReal =
      r ^ (-(halfFractionalOrder : ℝ)) := by
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hr.le]
  have hsemi_toReal :
      (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder mollErr.val).toReal =
        r ^ (-(halfFractionalOrder : ℝ)) *
          (cubeFractionalL2Seminorm hd (Homogenization.cubeCenter Q₀)
            (Homogenization.cubeScaleFactor Q₀) hQ₀ halfFractionalOrder eQ.val).toReal := by
    rw [hpush_semirel]
    rw [ENNReal.toReal_mul, hcoeff]
    rfl
  have hfull : cubeFractionalL2Norm hd z r hr halfFractionalOrder mollErr =
      r ^ (-(halfFractionalOrder : ℝ)) *
        cubeFractionalL2Norm hd (Homogenization.cubeCenter Q₀)
          (Homogenization.cubeScaleFactor Q₀) hQ₀ halfFractionalOrder eQ := by
    dsimp [mollErr]
    unfold cubeFractionalL2Norm
    rw [hsemi_toReal]
    simp only [Fin.sum_univ_one]
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
    rw [hpush_normrel]
    simp only [hscaleQ]
    norm_num
    ring
  have hTS (x : SpatialCoordinates d) : T (S x) = x := by
    dsimp [T, S]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    field_simp [hr.ne']
    ring
  have hSsmooth : ContDiff ℝ ∞ S := by
    dsimp [S]
    fun_prop
  let f : SpatialCoordinates d → ℝ := f₀ ∘ S
  have hf : ContDiff ℝ ∞ f := by
    dsimp [f]
    exact hf₀.comp hSsmooth
  have haQμ : (aQ.val 0 : SpatialCoordinates d → ℝ) =ᵐ[μQ] f₀ := by
    simpa only [μQ] using haQ
  have haQpush :
      (aQ.val 0 : SpatialCoordinates d → ℝ) ∘ S =ᵐ[μ]
        f₀ ∘ S := by
    have haQscaled := Measure.ae_smul_measure haQμ c'
    exact hSpresQ.quasiMeasurePreserving.ae_eq haQscaled
  have ha_ae : (a.val 0 : SpatialCoordinates d → ℝ) =ᵐ[μ] f := by
    have hapush := hpushae (aQ.val 0)
    filter_upwards [hapush, haQpush] with x h₁ h₂
    exact h₁.trans h₂
  have heQae : (eQ.val 0 : SpatialCoordinates d → ℝ) =ᵐ[μQ]
      (uQ : SpatialCoordinates d → ℝ) - (aQ.val 0 : SpatialCoordinates d → ℝ) := by
    rw [heQ]
    exact Lp.coeFn_sub _ _
  have heQpush :
      (eQ.val 0 : SpatialCoordinates d → ℝ) ∘ S =ᵐ[μ]
        ((uQ : SpatialCoordinates d → ℝ) - (aQ.val 0 : SpatialCoordinates d → ℝ)) ∘ S := by
    have heQscaled := Measure.ae_smul_measure heQae c'
    exact hSpresQ.quasiMeasurePreserving.ae_eq heQscaled
  have huQμ : (uQ : SpatialCoordinates d → ℝ) =ᵐ[μQ]
      (u.val 0 : SpatialCoordinates d → ℝ) ∘ T := by
    simpa only [μQ] using huQae
  have huQpush : (uQ : SpatialCoordinates d → ℝ) ∘ S =ᵐ[μ]
      (u.val 0 : SpatialCoordinates d → ℝ) := by
    have huQscaled := Measure.ae_smul_measure huQμ c'
    have hcomp := hSpresQ.quasiMeasurePreserving.ae_eq huQscaled
    filter_upwards [hcomp] with x hx
    simpa only [Function.comp_apply, hTS] using hx
  have haQpush_to_a : (aQ.val 0 : SpatialCoordinates d → ℝ) ∘ S =ᵐ[μ]
      (a.val 0 : SpatialCoordinates d → ℝ) := (hpushae (aQ.val 0)).symm
  have hmoll_ae : (mollErr.val 0 : SpatialCoordinates d → ℝ) =ᵐ[μ]
      (u.val 0 : SpatialCoordinates d → ℝ) - (a.val 0 : SpatialCoordinates d → ℝ) := by
    dsimp [mollErr]
    have hempush := hpushae (eQ.val 0)
    filter_upwards [hempush, heQpush, huQpush, haQpush_to_a] with x h₁ h₂ h₃ h₄
    simp only [Function.comp_apply, Pi.sub_apply] at h₂
    have h₃' : (uQ : SpatialCoordinates d → ℝ) (S x) =
        (u.val 0 : SpatialCoordinates d → ℝ) x := by
      simpa only [Function.comp_apply] using h₃
    have h₄' : (aQ.val 0 : SpatialCoordinates d → ℝ) (S x) =
        (a.val 0 : SpatialCoordinates d → ℝ) x := by
      simpa only [Function.comp_apply] using h₄
    calc
      (pushLp (eQ.val 0) : SpatialCoordinates d → ℝ) x =
          ((eQ.val 0 : SpatialCoordinates d → ℝ) ∘ S) x := h₁
      _ = (uQ : SpatialCoordinates d → ℝ) (S x) -
          (aQ.val 0 : SpatialCoordinates d → ℝ) (S x) := h₂
      _ = (u.val 0 : SpatialCoordinates d → ℝ) x -
          (a.val 0 : SpatialCoordinates d → ℝ) x := by rw [h₃', h₄']
  have hmoll_eq : mollErr.val 0 = u.val 0 - a.val 0 := by
    apply Lp.ext
    filter_upwards [hmoll_ae, Lp.coeFn_sub (u.val 0) (a.val 0)] with x hx hsub
    exact hx.trans hsub.symm
  have hrpow : 0 < r ^ (halfFractionalOrder : ℝ) :=
    Real.rpow_pos_of_pos hr _
  have hnorm_lt : cubeFractionalL2Norm hd z r hr halfFractionalOrder mollErr < η := by
    calc
      cubeFractionalL2Norm hd z r hr halfFractionalOrder mollErr =
          r ^ (-(halfFractionalOrder : ℝ)) *
            cubeFractionalL2Norm hd (Homogenization.cubeCenter Q₀)
              (Homogenization.cubeScaleFactor Q₀) hQ₀ halfFractionalOrder eQ := hfull
      _ < r ^ (-(halfFractionalOrder : ℝ)) * δ := by
        exact mul_lt_mul_of_pos_left heQnorm
          (Real.rpow_pos_of_pos hr _)
      _ = η := by
        dsimp [δ]
        calc
          r ^ (-(halfFractionalOrder : ℝ)) *
              (η * r ^ (halfFractionalOrder : ℝ)) =
              η * ((r ^ (halfFractionalOrder : ℝ))⁻¹ *
                r ^ (halfFractionalOrder : ℝ)) := by
                rw [Real.rpow_neg hr.le]
                ring
          _ = η := by rw [inv_mul_cancel₀ hrpow.ne', mul_one]
  exact ⟨a, f, mollErr, hf, ha_ae, hmoll_eq, hnorm_lt⟩

end Paper
