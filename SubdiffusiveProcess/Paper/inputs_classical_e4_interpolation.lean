import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Lane4.CubeDilation
import SubdiffusiveProcess.Paper.lane4_gagliardo_dilation_scaling
import SubdiffusiveProcess.Paper.classical_unit_cube_fractional_interpolation

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_inputs_classical_e4_interpolation_memLp {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (v : DomainL2 (centeredCube z r hr)) :
    MemLp ((v : SpatialCoordinates d → ℝ) ∘ cubeDilation z (0 : SpatialCoordinates d) r) 2
      (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) := by
  have h1 : MemLp (v : SpatialCoordinates d → ℝ) 2
      (Measure.map (cubeDilation z (0 : SpatialCoordinates d) r)
        (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))) := by
    rw [map_cubeDilation_restrict z 0 hr one_pos]
    exact (Lp.memLp v).smul_measure ENNReal.ofReal_ne_top
  exact h1.comp_of_map (continuous_cubeDilation z 0 r).measurable.aemeasurable

/-- Pull an `L²` class of the cube of side `r` back to the unit cube along the dilation. -/
def aux_inputs_classical_e4_interpolation_pull {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (v : DomainL2 (centeredCube z r hr)) : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos) :=
  (aux_inputs_classical_e4_interpolation_memLp z hr v).toLp
      ((v : SpatialCoordinates d → ℝ) ∘ cubeDilation z (0 : SpatialCoordinates d) r)

theorem aux_inputs_classical_e4_interpolation_pull_ae {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (v : DomainL2 (centeredCube z r hr)) :
    ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      (aux_inputs_classical_e4_interpolation_pull z hr v : SpatialCoordinates d → ℝ) x =
        (v : SpatialCoordinates d → ℝ) (cubeDilation z (0 : SpatialCoordinates d) r x) := by
  unfold aux_inputs_classical_e4_interpolation_pull
  exact (aux_inputs_classical_e4_interpolation_memLp z hr v).coeFn_toLp

/-- Real form of the scaling of the normalised Gagliardo seminorm and of the normalised `L²` norm. -/
theorem aux_inputs_classical_e4_interpolation_scale {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1) (v : DomainL2 (centeredCube z r hr)) :
    (cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v) < ⊤ ↔
      cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s
        (fun _ : Fin 1 => aux_inputs_classical_e4_interpolation_pull z hr v) < ⊤) ∧
    (cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v)).toReal =
      r ^ (-(s : ℝ)) * (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s
        (fun _ : Fin 1 => aux_inputs_classical_e4_interpolation_pull z hr v)).toReal ∧
    ‖v‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) =
      ‖aux_inputs_classical_e4_interpolation_pull z hr v‖ /
        Real.sqrt (volume.real (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) := by
  have h := lane4_gagliardo_dilation_scaling d 1 hd z 0 r hr one_pos s (fun _ => v)
    (fun _ => aux_inputs_classical_e4_interpolation_pull z hr v)
    (fun _ => aux_inputs_classical_e4_interpolation_pull_ae z hr v)
  obtain ⟨h1, h2⟩ := h
  set Sr := cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v) with hSr
  set S1 := cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s
    (fun _ : Fin 1 => aux_inputs_classical_e4_interpolation_pull z hr v) with hS1
  have hc0 : ENNReal.ofReal (r ^ (-(2 * (s : ℝ)))) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hct : ENNReal.ofReal (r ^ (-(2 * (s : ℝ)))) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfin : Sr < ⊤ ↔ S1 < ⊤ := by
    constructor
    · intro h
      by_contra hcon
      have hS1top : S1 = ⊤ := not_lt_top_iff.1 hcon
      rw [hS1top] at h1
      have h3 : Sr ^ (2 : ℕ) = ⊤ := by
        rw [h1, ENNReal.top_pow (by norm_num), ENNReal.mul_top hc0]
      exact (ne_of_lt (ENNReal.pow_lt_top h)) h3
    · intro h
      have h3 : Sr ^ (2 : ℕ) < ⊤ := by
        rw [h1]; exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hct) (ENNReal.pow_lt_top h)
      by_contra hcon
      have hs : Sr = ⊤ := not_lt_top_iff.1 hcon
      rw [hs, ENNReal.top_pow (by norm_num)] at h3
      exact lt_irrefl _ h3
  refine ⟨hfin, ?_, ?_⟩
  · by_cases hS : S1 < ⊤
    · have hSr' : Sr ≠ ⊤ := (hfin.2 hS).ne
      have h1' : (Sr.toReal) ^ 2 = (r ^ (-(2 * (s : ℝ)))) * (S1.toReal) ^ 2 := by
        have := congrArg ENNReal.toReal h1
        rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofReal (by positivity)] at this
        exact this
      have hpos : 0 ≤ r ^ (-(s : ℝ)) * S1.toReal := by positivity
      have hr2 : (r ^ (-(s : ℝ))) ^ 2 = r ^ (-(2 * (s : ℝ))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
        congr 1; push_cast; ring
      have hsq : (r ^ (-(s : ℝ)) * S1.toReal) ^ 2 = (r ^ (-(2 * (s : ℝ)))) * (S1.toReal) ^ 2 := by
        rw [mul_pow, hr2]
      have h4 := h1'.trans hsq.symm
      have h5 := (sq_eq_sq_iff_abs_eq_abs _ _).1 h4
      rwa [abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg hpos] at h5
    · have hS1 : S1 = ⊤ := not_lt_top_iff.1 hS
      have hSr : Sr = ⊤ := by
        by_contra hne
        have hlt : Sr < ⊤ := lt_top_iff_ne_top.2 hne
        exact hS (hfin.1 hlt)
      simp [hS1, hSr]
  · have h2' := h2
    simp only [Finset.univ_unique, Finset.sum_singleton] at h2'
    have e1 : ‖v‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) =
        Real.sqrt (‖v‖ ^ 2 / volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) := by
      rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    have e2 : ‖aux_inputs_classical_e4_interpolation_pull z hr v‖ /
        Real.sqrt (volume.real (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) =
        Real.sqrt (‖aux_inputs_classical_e4_interpolation_pull z hr v‖ ^ 2 /
          volume.real (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) := by
      rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    rw [e1, e2, h2']

/-- The unit-cube leaf in sum form: with `Sem` the normalised Gagliardo seminorm and `a` the normalised `L²` norm,
`Sem_t + a ≤ C a^{1-t/s}(Sem_s + a)^{t/s}`. -/
theorem aux_inputs_classical_e4_interpolation_unit_sum {d : ℕ} (hd : 2 ≤ d) (s t : Set.Ioo (0 : ℝ) 1)
    (hts : (t : ℝ) < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => v) < ⊤ →
      cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos t (fun _ : Fin 1 => v) < ⊤ ∧
      (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos t (fun _ : Fin 1 => v)).toReal +
          ‖v‖ / Real.sqrt (volume.real
            (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) ≤
        C * (‖v‖ / Real.sqrt (volume.real
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))) ^
            (1 - (t : ℝ) / s) *
          ((cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => v)).toReal +
            ‖v‖ / Real.sqrt (volume.real
              (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))) ^ ((t : ℝ) / s) := by
  obtain ⟨C0, hC0, hC⟩ := classical_unit_cube_fractional_interpolation d hd s t hts
  refine ⟨Real.sqrt 2 * C0, by positivity, ?_⟩
  intro v hv
  obtain ⟨ht, hb⟩ := hC v hv
  refine ⟨ht, ?_⟩
  set a : ℝ := ‖v‖ / Real.sqrt (volume.real
    (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) with ha
  set bt : ℝ := (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos t (fun _ : Fin 1 => v)).toReal with hbt
  set bs : ℝ := (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => v)).toReal with hbs
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hbt0 : 0 ≤ bt := ENNReal.toReal_nonneg
  have hbs0 : 0 ≤ bs := ENNReal.toReal_nonneg
  have hθ0 : 0 ≤ (t : ℝ) / s := div_nonneg t.2.1.le s.2.1.le
  have hnorm : ∀ σ : Set.Ioo (0 : ℝ) 1, cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos σ v =
      (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos σ (fun _ : Fin 1 => v)).toReal ^ 2 + a ^ 2 := by
    intro σ
    unfold cubeFractionalSqNorm cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [ha, div_pow, Real.sq_sqrt (by positivity)]
  rw [hnorm t] at hb
  rw [hnorm s] at hb
  have h1 : bt + a ≤ Real.sqrt 2 * Real.sqrt (bt ^ 2 + a ^ 2) := by
    rw [← Real.sqrt_mul (by norm_num)]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (bt - a)]
  have h2 : Real.sqrt (bs ^ 2 + a ^ 2) ≤ bs + a := by
    apply Real.sqrt_le_iff.2
    exact ⟨by positivity, by nlinarith [mul_nonneg hbs0 ha0]⟩
  have h3 : Real.sqrt (bs ^ 2 + a ^ 2) ^ ((t : ℝ) / s) ≤ (bs + a) ^ ((t : ℝ) / s) :=
    Real.rpow_le_rpow (Real.sqrt_nonneg _) h2 hθ0
  calc bt + a ≤ Real.sqrt 2 * Real.sqrt (bt ^ 2 + a ^ 2) := h1
    _ ≤ Real.sqrt 2 * (C0 * a ^ (1 - (t : ℝ) / s) * Real.sqrt (bs ^ 2 + a ^ 2) ^ ((t : ℝ) / s)) := by
        apply mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt 2 * (C0 * a ^ (1 - (t : ℝ) / s) * (bs + a) ^ ((t : ℝ) / s)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        apply mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

/-- **Scale-covariant interpolation on every cube** (`r > 0`, cube-independent constant): in the norms
`Norm_σ = Sem_σ + r^{-σ}·a` (`a` the normalised `L²` norm), `Norm_t ≤ C a^{1-t/s} Norm_s^{t/s}`. Proved from the
unit-cube leaf by the dilation; the factor `r^{-t}` cancels. -/
theorem aux_inputs_classical_e4_interpolation_all_sum {d : ℕ} (hd : 2 ≤ d) (s t : Set.Ioo (0 : ℝ) 1)
    (hts : (t : ℝ) < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (v : DomainL2 (centeredCube z r hr)),
      cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v) < ⊤ →
      cubeFractionalL2Seminorm hd z r hr t (fun _ : Fin 1 => v) < ⊤ ∧
      (cubeFractionalL2Seminorm hd z r hr t (fun _ : Fin 1 => v)).toReal +
          r ^ (-(t : ℝ)) * (‖v‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ≤
        C * (‖v‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ^
            (1 - (t : ℝ) / s) *
          ((cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v)).toReal +
            r ^ (-(s : ℝ)) * (‖v‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))) ^
              ((t : ℝ) / s) := by
  obtain ⟨C, hC, hU⟩ := aux_inputs_classical_e4_interpolation_unit_sum hd s t hts
  refine ⟨C, hC, ?_⟩
  intro z r hr v hv
  set w := aux_inputs_classical_e4_interpolation_pull z hr v with hw
  obtain ⟨hfs, hSs, hAs⟩ := aux_inputs_classical_e4_interpolation_scale hd z hr s v
  obtain ⟨hft, hSt, hAt⟩ := aux_inputs_classical_e4_interpolation_scale hd z hr t v
  have hvw : cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => w) < ⊤ :=
    hfs.1 hv
  obtain ⟨hwt, hbound⟩ := hU w hvw
  refine ⟨hft.2 hwt, ?_⟩
  set a : ℝ := ‖v‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) with ha
  have haw : a = ‖w‖ / Real.sqrt (volume.real
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) := hAs
  rw [← haw] at hbound
  rw [hSt, hSs]
  set bt : ℝ := (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos t (fun _ : Fin 1 => w)).toReal
  set bs : ℝ := (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => w)).toReal
  have hbs0 : 0 ≤ bs := ENNReal.toReal_nonneg
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hθ : (t : ℝ) / s ≥ 0 := div_nonneg t.2.1.le s.2.1.le
  have hrs : 0 ≤ r ^ (-(s : ℝ)) := by positivity
  have hrt : r ^ (-(t : ℝ)) = (r ^ (-(s : ℝ))) ^ ((t : ℝ) / s) := by
    rw [← Real.rpow_mul hr.le]
    congr 1
    field_simp [s.2.1.ne']
  have hrhs : (r ^ (-(s : ℝ)) * bs + r ^ (-(s : ℝ)) * a) ^ ((t : ℝ) / s) =
      r ^ (-(t : ℝ)) * (bs + a) ^ ((t : ℝ) / s) := by
    rw [← mul_add, Real.mul_rpow hrs (by positivity), hrt]
  calc r ^ (-(t : ℝ)) * bt + r ^ (-(t : ℝ)) * a = r ^ (-(t : ℝ)) * (bt + a) := by ring
    _ ≤ r ^ (-(t : ℝ)) * (C * a ^ (1 - (t : ℝ) / s) * (bs + a) ^ ((t : ℝ) / s)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = C * a ^ (1 - (t : ℝ) / s) * (r ^ (-(s : ℝ)) * bs + r ^ (-(s : ℝ)) * a) ^ ((t : ℝ) / s) := by
        rw [hrhs]; ring



/-- The constant `L²` class. -/
def aux_inputs_classical_e4_interpolation_const {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (m : ℝ) :
    DomainL2 (centeredCube z r hr) :=
  (memLp_const m).toLp (fun _ => m)

theorem aux_inputs_classical_e4_interpolation_const_ae {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (m : ℝ) :
    (aux_inputs_classical_e4_interpolation_const z hr m : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun _ => m := MemLp.coeFn_toLp _

/-- Jensen: `|f x − mean f|² ≤ ∫ |f x − f y|² dμ(y)` for a probability measure. -/
theorem aux_inputs_classical_e4_interpolation_jensen_pointwise {d : ℕ} (μ : Measure (SpatialCoordinates d)) [IsProbabilityMeasure μ]
    (f : SpatialCoordinates d → ℝ) (hf : MemLp f 2 μ) (x : SpatialCoordinates d) :
    ENNReal.ofReal ((f x - ∫ y, f y ∂μ) ^ 2) ≤ ∫⁻ y, ENNReal.ofReal ((f x - f y) ^ 2) ∂μ := by
  have hint : Integrable f μ := hf.integrable one_le_two
  have hg : MemLp (fun y => f x - f y) 2 μ := (memLp_const (f x)).sub hf
  have hsq : Integrable (fun y => (f x - f y) ^ 2) μ := hg.integrable_sq
  have hgi : Integrable (fun y => f x - f y) μ := (integrable_const _).sub hint
  have hJ := (Even.convexOn_pow (𝕜 := ℝ) (n := 2) even_two).map_integral_le (continuousOn_pow 2)
    isClosed_univ (Filter.Eventually.of_forall fun _ => mem_univ _) hgi (by simpa [Function.comp] using hsq)
  have hm : ∫ y, (f x - f y) ∂μ = f x - ∫ y, f y ∂μ := by
    rw [integral_sub (integrable_const _) hint]; simp
  rw [hm] at hJ
  calc ENNReal.ofReal ((f x - ∫ y, f y ∂μ) ^ 2) ≤ ENNReal.ofReal (∫ y, (f x - f y) ^ 2 ∂μ) :=
        ENNReal.ofReal_le_ofReal hJ
    _ = ∫⁻ y, ENNReal.ofReal ((f x - f y) ^ 2) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hsq (Filter.Eventually.of_forall fun _ => sq_nonneg _)

theorem aux_inputs_classical_e4_interpolation_cube1_dist {d : ℕ} (x y : SpatialCoordinates d)
    (hx : x ∈ (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
    (hy : y ∈ (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d := by
  rw [centeredCube_eq_pi] at hx hy
  apply Real.sqrt_le_sqrt
  calc ∑ j : Fin d, (x j - y j) ^ 2 ≤ ∑ _j : Fin d, (1 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 := hx j (mem_univ j)
        have h2 := hy j (mem_univ j)
        rw [mem_Ioo] at h1 h2
        simp only [Pi.zero_apply, zero_sub, zero_add] at h1 h2
        nlinarith [h1.1, h1.2, h2.1, h2.2]
    _ = d := by simp

/-- **Fractional Poincaré on the unit cube**: `‖u − mean u‖² ≤ (√d)^{d+2s}/s · Sem_s(u)²`. -/
theorem aux_inputs_classical_e4_interpolation_pointwise (a ρ σ p : ℝ) (ha : 0 ≤ a) (hρ : 0 ≤ ρ) (hρσ : ρ ≤ σ) (hp : 0 < p) (hσ : 0 < σ) :
    ENNReal.ofReal a ≤ ENNReal.ofReal (σ ^ p) * (ENNReal.ofReal a / ENNReal.ofReal ρ ^ p) := by
  rcases hρ.eq_or_lt with h0 | hpos
  · subst h0
    by_cases ha0 : a = 0
    · simp [ha0]
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      rw [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hp, ENNReal.div_zero (ENNReal.ofReal_pos.2 hapos).ne']
      have : 0 < ENNReal.ofReal (σ ^ p) := ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hσ p)
      simp [ENNReal.mul_top this.ne']
  · rw [ENNReal.ofReal_rpow_of_nonneg hpos.le hp.le, ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hpos p),
      ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hσ p).le]
    apply ENNReal.ofReal_le_ofReal
    have h1 : ρ ^ p ≤ σ ^ p := Real.rpow_le_rpow hpos.le hρσ hp.le
    have h2 : 0 < ρ ^ p := Real.rpow_pos_of_pos hpos p
    rw [← mul_div_assoc, le_div_iff₀ h2]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha]

theorem aux_inputs_classical_e4_interpolation_poincare_aux {d : ℕ} (hd : 2 ≤ d) (s : Set.Ioo (0 : ℝ) 1)
    (u : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (hu : cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => u) < ⊤) :
    ‖u - aux_inputs_classical_e4_interpolation_const (0 : SpatialCoordinates d) one_pos
        (∫ x, (u : SpatialCoordinates d → ℝ) x ∂(volume.restrict
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))))‖ ^ 2 ≤
      (Real.sqrt d ^ ((d : ℝ) + 2 * s) / s) *
        (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => u)).toReal ^ 2 := by
  classical
  set Q : Set (SpatialCoordinates d) := (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) with hQ
  set μ := volume.restrict Q with hμ
  have hvol : volume Q = 1 := by rw [hQ, centeredCube_volume]; simp
  haveI : IsProbabilityMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ, hvol]⟩
  set U : SpatialCoordinates d → ℝ := (u : SpatialCoordinates d → ℝ) with hU
  have hUL2 : MemLp U 2 μ := Lp.memLp u
  set m := ∫ x, U x ∂μ with hm
  set w := u - aux_inputs_classical_e4_interpolation_const (0 : SpatialCoordinates d) one_pos m with hw
  have hwae : (w : SpatialCoordinates d → ℝ) =ᵐ[μ] fun x => U x - m := by
    filter_upwards [Lp.coeFn_sub u (aux_inputs_classical_e4_interpolation_const (0 : SpatialCoordinates d) one_pos m),
      aux_inputs_classical_e4_interpolation_const_ae (0 : SpatialCoordinates d) one_pos m] with x h1 h2
    rw [h1]; simp only [Pi.sub_apply, h2]; rfl
  have hnorm : ‖w‖ ^ 2 = ∫ x, (U x - m) ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hwae] with x hx
    simp [hx, sq]
  have hint : Integrable (fun x => (U x - m) ^ 2) μ := (hUL2.sub (memLp_const m)).integrable_sq
  have h1 : ENNReal.ofReal (‖w‖ ^ 2) = ∫⁻ x, ENNReal.ofReal ((U x - m) ^ 2) ∂μ := by
    rw [hnorm]
    exact ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)
  have h2 : ∫⁻ x, ENNReal.ofReal ((U x - m) ^ 2) ∂μ ≤
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((U x - U y) ^ 2) ∂μ ∂μ :=
    lintegral_mono fun x => aux_inputs_classical_e4_interpolation_jensen_pointwise μ U hUL2 x
  set pp : ℝ := (d : ℝ) + 2 * s with hpp
  have hpp0 : 0 < pp := by rw [hpp]; have := s.2.1; positivity
  have hσ : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < d))
  set I : ℝ≥0∞ := ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal ((U x - U y) ^ 2) /
    ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ pp with hI
  have hSem : cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => u) =
      (ENNReal.ofReal s / volume Q * I) ^ (1 / 2 : ℝ) := by
    unfold cubeFractionalL2Seminorm
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rfl
  have h3 : ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((U x - U y) ^ 2) ∂μ ∂μ ≤ ENNReal.ofReal (Real.sqrt d ^ pp) * I := by
    rw [hI, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem (μ := volume) (s := Q) (by rw [hQ]; exact (centeredCube _ _ one_pos).isOpen.measurableSet)]
      with x hx
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem (μ := volume) (s := Q) (by rw [hQ]; exact (centeredCube _ _ one_pos).isOpen.measurableSet)]
      with y hy
    have hxy := aux_inputs_classical_e4_interpolation_cube1_dist x y hx hy
    have := aux_inputs_classical_e4_interpolation_pointwise ((U x - U y) ^ 2) (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) (Real.sqrt d) pp
      (sq_nonneg _) (Real.sqrt_nonneg _) hxy hpp0 hσ
    exact this
  have hIfin : I < ⊤ := by
    have h4 : (ENNReal.ofReal s / volume Q * I) ^ (1 / 2 : ℝ) < ⊤ := hSem ▸ hu
    have h5 : ENNReal.ofReal s / volume Q * I < ⊤ := (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h4
    rw [hvol] at h5
    have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.2 s.2.1).ne'
    rw [div_one] at h5
    exact lt_top_iff_ne_top.2 (ENNReal.lt_top_of_mul_ne_top_right h5.ne hs0).ne
  have hSreal : (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => u)).toReal ^ 2 =
      s * I.toReal := by
    rw [hSem, ← ENNReal.toReal_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg, hvol,
      div_one, ENNReal.toReal_mul, ENNReal.toReal_ofReal s.2.1.le]
    norm_num
  have hbound : ENNReal.ofReal (‖w‖ ^ 2) ≤ ENNReal.ofReal (Real.sqrt d ^ pp) * I := h1 ▸ h2.trans h3
  have hfinR : ENNReal.ofReal (Real.sqrt d ^ pp) * I ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIfin.ne
  have hreal : ‖w‖ ^ 2 ≤ Real.sqrt d ^ pp * I.toReal := by
    have := (ENNReal.toReal_mono hfinR hbound)
    rwa [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.rpow_pos_of_pos hσ pp).le] at this
  rw [hSreal]
  calc ‖w‖ ^ 2 ≤ Real.sqrt d ^ pp * I.toReal := hreal
    _ = Real.sqrt d ^ pp / s * (s * I.toReal) := by field_simp [s.2.1.ne']

/-- **Fractional Poincaré on the unit cube**: `‖u − mean u‖² ≤ (√d)^{d+2s}/s · Sem_s(u)²`. -/
theorem aux_inputs_classical_e4_interpolation_poincare {d : ℕ} (hd : 2 ≤ d) (s : Set.Ioo (0 : ℝ) 1)
    (u : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (hu : cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => u) < ⊤) :
    ‖u - aux_inputs_classical_e4_interpolation_const (0 : SpatialCoordinates d) one_pos
        (∫ x, (u : SpatialCoordinates d → ℝ) x ∂(volume.restrict
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))))‖ ^ 2 ≤
      (Real.sqrt d ^ ((d : ℝ) + 2 * s) / s) *
        (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => u)).toReal ^ 2 :=
  aux_inputs_classical_e4_interpolation_poincare_aux hd s u hu

/-- `‖f‖² = ∫ f²` for a real `L²` class. -/
theorem aux_inputs_classical_e4_interpolation_norm_sq {d : ℕ} {Ω : Opens (SpatialCoordinates d)} (f : DomainL2 Ω) :
    ‖f‖ ^ 2 = ∫ x, ((f : SpatialCoordinates d → ℝ) x) ^ 2 ∂(volume.restrict (Ω : Set (SpatialCoordinates d))) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  simp [sq]

/-- The norm of a constant on the unit cube. -/
theorem aux_inputs_classical_e4_interpolation_norm_const {d : ℕ} (m : ℝ) :
    ‖aux_inputs_classical_e4_interpolation_const (0 : SpatialCoordinates d) one_pos m‖ = |m| := by
  have hvol : volume (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) = 1 := by
    rw [centeredCube_volume]; simp
  haveI : IsProbabilityMeasure (volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) :=
    ⟨by rw [Measure.restrict_apply_univ, hvol]⟩
  have h := aux_inputs_classical_e4_interpolation_norm_sq (aux_inputs_classical_e4_interpolation_const (0 : SpatialCoordinates d) one_pos m)
  have h2 : ∫ x, ((aux_inputs_classical_e4_interpolation_const (0 : SpatialCoordinates d) one_pos m : SpatialCoordinates d → ℝ) x) ^ 2
      ∂(volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) = m ^ 2 := by
    rw [integral_congr_ae ((aux_inputs_classical_e4_interpolation_const_ae (0 : SpatialCoordinates d) one_pos m).mono fun x hx => by rw [hx])]
    simp
  rw [h2] at h
  have := abs_nonneg m
  nlinarith [norm_nonneg (aux_inputs_classical_e4_interpolation_const (0 : SpatialCoordinates d) one_pos m), sq_abs m, sq_nonneg (‖aux_inputs_classical_e4_interpolation_const (0 : SpatialCoordinates d) one_pos m‖ - |m|), sq_nonneg (‖aux_inputs_classical_e4_interpolation_const (0 : SpatialCoordinates d) one_pos m‖ + |m|)]

/-- `|mean u| ≤ ‖u‖` on the unit cube. -/
theorem aux_inputs_classical_e4_interpolation_abs_mean_le {d : ℕ} (u : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) :
    |∫ x, (u : SpatialCoordinates d → ℝ) x ∂(volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))| ≤ ‖u‖ := by
  have hvol : volume (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) = 1 := by
    rw [centeredCube_volume]; simp
  haveI : IsProbabilityMeasure (volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) :=
    ⟨by rw [Measure.restrict_apply_univ, hvol]⟩
  set μ := volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
  have hUL2 : MemLp (u : SpatialCoordinates d → ℝ) 2 μ := Lp.memLp u
  have hint : Integrable (u : SpatialCoordinates d → ℝ) μ := hUL2.integrable one_le_two
  have hsq : Integrable (fun x => ((u : SpatialCoordinates d → ℝ) x) ^ 2) μ := hUL2.integrable_sq
  have hJ := (Even.convexOn_pow (𝕜 := ℝ) (n := 2) even_two).map_integral_le (continuousOn_pow 2)
    isClosed_univ (Filter.Eventually.of_forall fun _ => mem_univ _) hint (by simpa [Function.comp] using hsq)
  have h2 := aux_inputs_classical_e4_interpolation_norm_sq u
  simp only at hJ
  have : (∫ x, (u : SpatialCoordinates d → ℝ) x ∂μ) ^ 2 ≤ ‖u‖ ^ 2 := by rw [h2]; exact hJ
  exact abs_le_of_sq_le_sq' this (norm_nonneg _) |>.2 |> fun h => by
    rw [abs_le]; exact ⟨(abs_le_of_sq_le_sq' this (norm_nonneg _)).1, h⟩

/-- Subtracting a constant does not change the seminorm. -/
theorem aux_inputs_classical_e4_interpolation_semi_sub_const {d : ℕ} (hd : 2 ≤ d) (s : Set.Ioo (0 : ℝ) 1)
    (u : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) (m : ℝ) :
    cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s
        (fun _ : Fin 1 => u - aux_inputs_classical_e4_interpolation_const (0 : SpatialCoordinates d) one_pos m) =
      cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => u) := by
  have hw : (↑(u - aux_inputs_classical_e4_interpolation_const (0 : SpatialCoordinates d) one_pos m) : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))]
      fun x => (u : SpatialCoordinates d → ℝ) x - m := by
    filter_upwards [Lp.coeFn_sub u (aux_inputs_classical_e4_interpolation_const (0 : SpatialCoordinates d) one_pos m),
      aux_inputs_classical_e4_interpolation_const_ae (0 : SpatialCoordinates d) one_pos m] with x h1 h2
    rw [h1]; simp only [Pi.sub_apply, h2]
  unfold cubeFractionalL2Seminorm
  congr 2
  refine lintegral_congr_ae ?_
  filter_upwards [hw] with x hx
  refine lintegral_congr_ae ?_
  filter_upwards [hw] with y hy
  simp only [Finset.univ_unique, Finset.sum_singleton, hx, hy]
  congr 2
  ring

/-- Unit-cube homogeneous interpolation: `Sem_t(u) ≤ K ‖u‖^{1-t/s} Sem_s(u)^{t/s}` (no `L²` term on the right seminorm). -/
theorem aux_inputs_classical_e4_interpolation_unit_hom {d : ℕ} (hd : 2 ≤ d) (s t : Set.Ioo (0 : ℝ) 1) (hts : (t : ℝ) < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => u) < ⊤ →
      cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos t (fun _ : Fin 1 => u) < ⊤ ∧
      (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos t (fun _ : Fin 1 => u)).toReal ≤
        K * ‖u‖ ^ (1 - (t : ℝ) / s) *
          (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => u)).toReal ^
            ((t : ℝ) / s) := by
  obtain ⟨C, hC, hU⟩ := aux_inputs_classical_e4_interpolation_unit_sum hd s t hts
  set P : ℝ := Real.sqrt d ^ ((d : ℝ) + 2 * s) / s with hP
  have hP0 : 0 ≤ P := by
    rw [hP]; have := s.2.1; positivity
  refine ⟨2 * C * (1 + Real.sqrt P), by positivity, ?_⟩
  intro u hu
  set m := ∫ x, (u : SpatialCoordinates d → ℝ) x ∂(volume.restrict
    (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) with hm
  set w := u - aux_inputs_classical_e4_interpolation_const (0 : SpatialCoordinates d) one_pos m with hw
  have hSs : cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => w) =
      cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => u) :=
    aux_inputs_classical_e4_interpolation_semi_sub_const hd s u m
  have hSt : cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos t (fun _ : Fin 1 => w) =
      cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos t (fun _ : Fin 1 => u) :=
    aux_inputs_classical_e4_interpolation_semi_sub_const hd t u m
  have hwfin : cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => w) < ⊤ := by
    rw [hSs]; exact hu
  obtain ⟨hwt, hb⟩ := hU w hwfin
  rw [hSt] at hwt
  refine ⟨hwt, ?_⟩
  rw [hSs, hSt] at hb
  have hvr : volume.real (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) = 1 := by
    rw [centeredCube_volume_real]; simp
  rw [hvr, Real.sqrt_one, div_one] at hb
  set bt := (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos t (fun _ : Fin 1 => u)).toReal
  set bs := (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => u)).toReal
  have hbt0 : 0 ≤ bt := ENNReal.toReal_nonneg
  have hbs0 : 0 ≤ bs := ENNReal.toReal_nonneg
  have hθ0 : 0 ≤ (t : ℝ) / s := div_nonneg t.2.1.le s.2.1.le
  have hθ1 : (t : ℝ) / s ≤ 1 := (div_le_one s.2.1).2 hts.le
  have hθ1' : 0 < 1 - (t : ℝ) / s := by
    have : (t : ℝ) / s < 1 := (div_lt_one s.2.1).2 hts
    linarith
  -- bounds on ‖w‖
  have hpoin := aux_inputs_classical_e4_interpolation_poincare hd s u hu
  rw [← hm, ← hw] at hpoin
  have hwP : ‖w‖ ≤ Real.sqrt P * bs := by
    have hsq : ‖w‖ ^ 2 ≤ (Real.sqrt P * bs) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hP0]; exact hpoin
    exact abs_le_of_sq_le_sq' hsq (by positivity) |>.2
  have hwu : ‖w‖ ≤ 2 * ‖u‖ := by
    have h1 : ‖w‖ ≤ ‖u‖ + ‖aux_inputs_classical_e4_interpolation_const (0 : SpatialCoordinates d) one_pos m‖ := by
      rw [hw]; exact norm_sub_le _ _
    rw [aux_inputs_classical_e4_interpolation_norm_const] at h1
    have := aux_inputs_classical_e4_interpolation_abs_mean_le u
    linarith
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have hstep : bt ≤ C * ‖w‖ ^ (1 - (t : ℝ) / s) * (bs + ‖w‖) ^ ((t : ℝ) / s) := by linarith
  have h1 : ‖w‖ ^ (1 - (t : ℝ) / s) ≤ 2 * ‖u‖ ^ (1 - (t : ℝ) / s) := by
    calc ‖w‖ ^ (1 - (t : ℝ) / s) ≤ (2 * ‖u‖) ^ (1 - (t : ℝ) / s) :=
          Real.rpow_le_rpow hw0 hwu hθ1'.le
      _ = 2 ^ (1 - (t : ℝ) / s) * ‖u‖ ^ (1 - (t : ℝ) / s) := Real.mul_rpow (by norm_num) hu0
      _ ≤ 2 * ‖u‖ ^ (1 - (t : ℝ) / s) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc (2 : ℝ) ^ (1 - (t : ℝ) / s) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 2 := Real.rpow_one 2
  have h2 : (bs + ‖w‖) ^ ((t : ℝ) / s) ≤ (1 + Real.sqrt P) * bs ^ ((t : ℝ) / s) := by
    calc (bs + ‖w‖) ^ ((t : ℝ) / s) ≤ ((1 + Real.sqrt P) * bs) ^ ((t : ℝ) / s) := by
          apply Real.rpow_le_rpow (by positivity) _ hθ0
          nlinarith
      _ = (1 + Real.sqrt P) ^ ((t : ℝ) / s) * bs ^ ((t : ℝ) / s) := Real.mul_rpow (by positivity) hbs0
      _ ≤ (1 + Real.sqrt P) * bs ^ ((t : ℝ) / s) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc (1 + Real.sqrt P) ^ ((t : ℝ) / s) ≤ (1 + Real.sqrt P) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith [Real.sqrt_nonneg P]) hθ1
            _ = 1 + Real.sqrt P := Real.rpow_one _
  calc bt ≤ C * ‖w‖ ^ (1 - (t : ℝ) / s) * (bs + ‖w‖) ^ ((t : ℝ) / s) := hstep
    _ ≤ C * (2 * ‖u‖ ^ (1 - (t : ℝ) / s)) * ((1 + Real.sqrt P) * bs ^ ((t : ℝ) / s)) := by
        apply mul_le_mul _ h2 (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left h1 hC.le
    _ = 2 * C * (1 + Real.sqrt P) * ‖u‖ ^ (1 - (t : ℝ) / s) * bs ^ ((t : ℝ) / s) := by ring


/-- **Homogeneous scale-covariant interpolation on every cube**: `Sem_t(v) ≤ K a^{1-t/s} Sem_s(v)^{t/s}`, `a` the
normalised `L²` norm; from the unit-cube homogeneous form by the dilation (the factor `r^{-t}` cancels). -/
theorem aux_inputs_classical_e4_interpolation_all_hom {d : ℕ} (hd : 2 ≤ d) (s t : Set.Ioo (0 : ℝ) 1)
    (hts : (t : ℝ) < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (v : DomainL2 (centeredCube z r hr)),
      cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v) < ⊤ →
      cubeFractionalL2Seminorm hd z r hr t (fun _ : Fin 1 => v) < ⊤ ∧
      (cubeFractionalL2Seminorm hd z r hr t (fun _ : Fin 1 => v)).toReal ≤
        K * (‖v‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ^
            (1 - (t : ℝ) / s) *
          (cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v)).toReal ^ ((t : ℝ) / s) := by
  obtain ⟨K, hK, hU⟩ := aux_inputs_classical_e4_interpolation_unit_hom hd s t hts
  refine ⟨K, hK, ?_⟩
  intro z r hr v hv
  set w := aux_inputs_classical_e4_interpolation_pull z hr v with hw
  obtain ⟨hfs, hSs, hAs⟩ := aux_inputs_classical_e4_interpolation_scale hd z hr s v
  obtain ⟨hft, hSt, hAt⟩ := aux_inputs_classical_e4_interpolation_scale hd z hr t v
  obtain ⟨hwt, hbound⟩ := hU w (hfs.1 hv)
  refine ⟨hft.2 hwt, ?_⟩
  have hvr : volume.real (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) = 1 := by
    rw [centeredCube_volume_real]; simp
  have ha : ‖v‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) = ‖w‖ := by
    rw [hAs, hvr, Real.sqrt_one, div_one]
  rw [ha, hSt, hSs]
  set bt := (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos t (fun _ : Fin 1 => w)).toReal
  set bs := (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => w)).toReal
  have hbs0 : 0 ≤ bs := ENNReal.toReal_nonneg
  have hθ0 : 0 ≤ (t : ℝ) / s := div_nonneg t.2.1.le s.2.1.le
  have hrs : 0 ≤ r ^ (-(s : ℝ)) := by positivity
  have hrt : r ^ (-(t : ℝ)) = (r ^ (-(s : ℝ))) ^ ((t : ℝ) / s) := by
    rw [← Real.rpow_mul hr.le]
    congr 1
    field_simp [s.2.1.ne']
  calc r ^ (-(t : ℝ)) * bt ≤ r ^ (-(t : ℝ)) * (K * ‖w‖ ^ (1 - (t : ℝ) / s) * bs ^ ((t : ℝ) / s)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = K * ‖w‖ ^ (1 - (t : ℝ) / s) * (r ^ (-(s : ℝ)) * bs) ^ ((t : ℝ) / s) := by
        rw [Real.mul_rpow hrs hbs0, hrt]; ring

/-- E4: fractional interpolation on cubes, in normalized Gagliardo norms.  PROVED from the unit-cube leaf
`classical_unit_cube_fractional_interpolation` (the statement is unchanged; the hypothesis `r ≤ 1` is not needed). -/
theorem inputs_classical_e4_interpolation (d : ℕ) (hd : 2 ≤ d)
    (s t : Set.Ioo (0 : ℝ) 1) (hts : (t : ℝ) < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ v : DomainL2 (centeredCube z r hr),
        cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v) < ⊤ →
        cubeFractionalL2Seminorm hd z r hr t (fun _ : Fin 1 => v) < ⊤ ∧
        Real.sqrt (cubeFractionalSqNorm hd z r hr t v) ≤
          C * (‖v‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ^
            (1 - (t : ℝ) / s) *
          Real.sqrt (cubeFractionalSqNorm hd z r hr s v) ^ ((t : ℝ) / s) := by
  obtain ⟨K, hK, hall⟩ := aux_inputs_classical_e4_interpolation_all_hom hd s t hts
  refine ⟨K + 1, by positivity, ?_⟩
  intro z r hr _ v hv
  obtain ⟨ht, hb⟩ := hall z r hr v hv
  refine ⟨ht, ?_⟩
  set a : ℝ := ‖v‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) with ha
  set bt : ℝ := (cubeFractionalL2Seminorm hd z r hr t (fun _ : Fin 1 => v)).toReal with hbt
  set bs : ℝ := (cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v)).toReal with hbs
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hbt0 : 0 ≤ bt := ENNReal.toReal_nonneg
  have hbs0 : 0 ≤ bs := ENNReal.toReal_nonneg
  have hθ0 : 0 ≤ (t : ℝ) / s := div_nonneg t.2.1.le s.2.1.le
  have hθ1 : (t : ℝ) / s < 1 := (div_lt_one s.2.1).2 hts
  have hnorm : ∀ σ : Set.Ioo (0 : ℝ) 1, cubeFractionalSqNorm hd z r hr σ v =
      (cubeFractionalL2Seminorm hd z r hr σ (fun _ : Fin 1 => v)).toReal ^ 2 + a ^ 2 := by
    intro σ
    unfold cubeFractionalSqNorm cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [ha, div_pow, Real.sq_sqrt (by positivity)]
  rw [hnorm t, hnorm s]
  have hNs : bs ≤ Real.sqrt (bs ^ 2 + a ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg a])
  have hNa : a ≤ Real.sqrt (bs ^ 2 + a ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg bs])
  have hNt : Real.sqrt (bt ^ 2 + a ^ 2) ≤ bt + a := by
    apply Real.sqrt_le_iff.2
    exact ⟨by positivity, by nlinarith [mul_nonneg hbt0 ha0]⟩
  have h1 : bs ^ ((t : ℝ) / s) ≤ Real.sqrt (bs ^ 2 + a ^ 2) ^ ((t : ℝ) / s) :=
    Real.rpow_le_rpow hbs0 hNs hθ0
  have h2 : a ≤ a ^ (1 - (t : ℝ) / s) * Real.sqrt (bs ^ 2 + a ^ 2) ^ ((t : ℝ) / s) := by
    calc a = a ^ (1 - (t : ℝ) / s) * a ^ ((t : ℝ) / s) := by
          rw [← Real.rpow_add' ha0 (by linarith)]; simp
      _ ≤ a ^ (1 - (t : ℝ) / s) * Real.sqrt (bs ^ 2 + a ^ 2) ^ ((t : ℝ) / s) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha0 hNa hθ0) (by positivity)
  calc Real.sqrt (bt ^ 2 + a ^ 2) ≤ bt + a := hNt
    _ ≤ K * a ^ (1 - (t : ℝ) / s) * bs ^ ((t : ℝ) / s) + a := by linarith
    _ ≤ K * a ^ (1 - (t : ℝ) / s) * Real.sqrt (bs ^ 2 + a ^ 2) ^ ((t : ℝ) / s) +
          a ^ (1 - (t : ℝ) / s) * Real.sqrt (bs ^ 2 + a ^ 2) ^ ((t : ℝ) / s) := by
        apply add_le_add _ h2
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (K + 1) * a ^ (1 - (t : ℝ) / s) * Real.sqrt (bs ^ 2 + a ^ 2) ^ ((t : ℝ) / s) := by ring

end Paper

