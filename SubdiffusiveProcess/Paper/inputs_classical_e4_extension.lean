module

public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import SubdiffusiveProcess.Paper.inputs_classical_e4_interpolation
public import SubdiffusiveProcess.Paper.classical_unit_cube_fractional_extension

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Change of variables on the whole space under the dilation, for an arbitrary `ℝ≥0∞`-valued integrand. -/
theorem aux_inputs_classical_e4_extension_lintegral {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (g : SpatialCoordinates d → ℝ≥0∞) :
    ∫⁻ x, g x = ENNReal.ofReal (r ^ d) * ∫⁻ x, g (cubeDilation z (0 : SpatialCoordinates d) r x) := by
  have hcoe : ⇑(cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne') = cubeDilation z 0 r := rfl
  have h := lintegral_map_equiv (μ := (volume : Measure (SpatialCoordinates d))) g
    (cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne')
  rw [hcoe, map_cubeDilation_volume z 0 hr.ne', lintegral_smul_measure, smul_eq_mul] at h
  rw [← h, ← mul_assoc]
  have : ENNReal.ofReal (r ^ d) * ENNReal.ofReal |(r ^ d)⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity : (0 : ℝ) < (r ^ d)⁻¹),
      mul_inv_cancel₀ (by positivity : (r : ℝ) ^ d ≠ 0)]
    simp
  rw [this, one_mul]

/-- Change of variables on `ℝ^d × ℝ^d` under the product of the dilation with itself. -/
theorem aux_inputs_classical_e4_extension_lintegral_prod {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (h : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞) :
    ∫⁻ q, h q = ENNReal.ofReal (r ^ d) ^ 2 *
      ∫⁻ q : SpatialCoordinates d × SpatialCoordinates d,
        h (cubeDilation z (0 : SpatialCoordinates d) r q.1, cubeDilation z (0 : SpatialCoordinates d) r q.2) := by
  set e := cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne' with he
  have hmap : Measure.map (Prod.map e e) ((volume : Measure (SpatialCoordinates d)).prod volume) =
      (ENNReal.ofReal |(r ^ d)⁻¹|) ^ 2 • ((volume : Measure (SpatialCoordinates d)).prod volume) := by
    rw [← Measure.map_prod_map _ _ e.measurable e.measurable]
    have h1 : Measure.map e (volume : Measure (SpatialCoordinates d)) = ENNReal.ofReal |(r ^ d)⁻¹| • volume := by
      have := map_cubeDilation_volume z (0 : SpatialCoordinates d) hr.ne'
      exact this
    rw [h1, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, sq]
  have h2 := lintegral_map_equiv (μ := (volume : Measure (SpatialCoordinates d)).prod volume) h (e.prodCongr e)
  have hcoe : ⇑(e.prodCongr e) = Prod.map e e := rfl
  have h3 : Measure.map (e.prodCongr e) ((volume : Measure (SpatialCoordinates d)).prod volume) =
      (ENNReal.ofReal |(r ^ d)⁻¹|) ^ 2 • ((volume : Measure (SpatialCoordinates d)).prod volume) := by
    rw [hcoe]; exact hmap
  rw [h3, lintegral_smul_measure, smul_eq_mul] at h2
  have h4 : ENNReal.ofReal |(r ^ d)⁻¹| ^ 2 * ∫⁻ q : SpatialCoordinates d × SpatialCoordinates d, h q
        ∂((volume : Measure (SpatialCoordinates d)).prod volume) =
      ∫⁻ q : SpatialCoordinates d × SpatialCoordinates d,
        h (cubeDilation z (0 : SpatialCoordinates d) r q.1, cubeDilation z (0 : SpatialCoordinates d) r q.2)
        ∂((volume : Measure (SpatialCoordinates d)).prod volume) := h2
  have hprod : (volume : Measure (SpatialCoordinates d × SpatialCoordinates d)) =
      (volume : Measure (SpatialCoordinates d)).prod volume := rfl
  rw [hprod, ← h4, ← mul_assoc]
  have : ENNReal.ofReal (r ^ d) ^ 2 * ENNReal.ofReal |(r ^ d)⁻¹| ^ 2 = 1 := by
    rw [← mul_pow, ← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity : (0 : ℝ) < (r ^ d)⁻¹),
      mul_inv_cancel₀ (by positivity : (r : ℝ) ^ d ≠ 0)]
    simp
  rw [this, one_mul]

/-- Pushing an extension forward along the dilation does not increase the global Gagliardo norm (`r ≤ 1`, `d ≥ 2s`). -/
theorem aux_inputs_classical_e4_extension_global_le {d : ℕ} (hd : 2 ≤ d) (s : Set.Ioo (0 : ℝ) 1)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (V' : SpatialCoordinates d → ℝ) :
    globalFractionalSqNorm (s : ℝ) (fun x => V' (cubeDilation (0 : SpatialCoordinates d) z r⁻¹ x)) ≤
      globalFractionalSqNorm (s : ℝ) V' := by
  set V : SpatialCoordinates d → ℝ := fun x => V' (cubeDilation (0 : SpatialCoordinates d) z r⁻¹ x) with hVdef
  have hV : ∀ x', V (cubeDilation z (0 : SpatialCoordinates d) r x') = V' x' := by
    intro x'
    show V' ((cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne').symm
      ((cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne') x')) = V' x'
    rw [MeasurableEquiv.symm_apply_apply]
  have hs := s.2
  have hpp0 : 0 < (d : ℝ) + 2 * (s : ℝ) := by have := hs.1; positivity
  have hrp : 0 < ENNReal.ofReal r ^ ((d : ℝ) + 2 * (s : ℝ)) := ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hr) ENNReal.ofReal_ne_top
  have hrpt : ENNReal.ofReal r ^ ((d : ℝ) + 2 * (s : ℝ)) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hpp0.le ENNReal.ofReal_ne_top
  unfold globalFractionalSqNorm
  rw [aux_inputs_classical_e4_extension_lintegral z hr, aux_inputs_classical_e4_extension_lintegral_prod z hr]
  simp only [hV, sqrt_sum_sq_cubeDilation z (0 : SpatialCoordinates d) hr]
  have hint : ∀ q : SpatialCoordinates d × SpatialCoordinates d,
      ENNReal.ofReal ((V' q.1 - V' q.2) ^ 2) /
        ENNReal.ofReal (r * Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2)) ^ ((d : ℝ) + 2 * (s : ℝ)) =
      (ENNReal.ofReal r ^ ((d : ℝ) + 2 * (s : ℝ)))⁻¹ * (ENNReal.ofReal ((V' q.1 - V' q.2) ^ 2) /
        ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2)) ^ ((d : ℝ) + 2 * (s : ℝ))) := by
    intro q
    rw [ENNReal.ofReal_mul hr.le, ENNReal.mul_rpow_of_nonneg _ _ hpp0.le, div_eq_mul_inv, div_eq_mul_inv,
      ENNReal.mul_inv (Or.inl hrp.ne') (Or.inl hrpt)]
    ring
  simp_rw [hint]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hrp.ne')]
  have hc1 : ENNReal.ofReal (r ^ d) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (pow_le_one₀ hr.le hr1)
  have hc2 : ENNReal.ofReal (r ^ d) ^ 2 * (ENNReal.ofReal r ^ ((d : ℝ) + 2 * (s : ℝ)))⁻¹ ≤ 1 := by
    rw [ENNReal.ofReal_rpow_of_nonneg hr.le hpp0.le, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hr ((d : ℝ) + 2 * (s : ℝ))), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have h1 : r ^ ((d : ℝ) + 2 * (s : ℝ)) ≥ (r ^ d) ^ 2 := by
      rw [← pow_mul, ← Real.rpow_natCast, show ((d * 2 : ℕ) : ℝ) = 2 * (d : ℝ) by push_cast; ring]
      apply Real.rpow_le_rpow_of_exponent_ge hr hr1
      have := hs.2; have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    rw [← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hr ((d : ℝ) + 2 * (s : ℝ)))]
    exact h1
  rw [← mul_assoc]
  exact add_le_add (mul_le_of_le_one_left (zero_le) hc1) (mul_le_of_le_one_left (zero_le) hc2)

/-- `cubeFractionalSqNorm` as `Sem² + a²`. -/
theorem aux_inputs_classical_e4_extension_sqnorm {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (σ : Set.Ioo (0 : ℝ) 1) (v : DomainL2 (centeredCube z r hr)) :
    cubeFractionalSqNorm hd z r hr σ v =
      (cubeFractionalL2Seminorm hd z r hr σ (fun _ : Fin 1 => v)).toReal ^ 2 +
        (‖v‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ^ 2 := by
  unfold cubeFractionalSqNorm cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [div_pow, Real.sq_sqrt (by positivity)]

/-- E4: bounded extension from a cube, with finite extended seminorm.  PROVED from the unit-cube leaf
`classical_unit_cube_fractional_extension` (statement unchanged): extend the pull-back to the unit cube and push the
extension forward along the dilation; for `r ≤ 1` the global norm does not increase (`d ≥ 2s`), and the cube-normalised
norm of `v` dominates that of the pull-back. -/
theorem inputs_classical_e4_extension (d : ℕ) (hd : 2 ≤ d) (s : Set.Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ v : DomainL2 (centeredCube z r hr),
        cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v) < ⊤ →
        ∃ V : SpatialCoordinates d → ℝ,
          ((v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] V) ∧
          globalFractionalSqNorm s V ≤ ENNReal.ofReal (C * cubeFractionalSqNorm hd z r hr s v) := by
  obtain ⟨C, hC, hext⟩ := classical_unit_cube_fractional_extension d hd s
  refine ⟨C, hC, ?_⟩
  intro z r hr hr1 v hv
  set w := aux_inputs_classical_e4_interpolation_pull z hr v with hw
  obtain ⟨hfs, hSs, hAs⟩ := aux_inputs_classical_e4_interpolation_scale hd z hr s v
  obtain ⟨V', hV'ae, hV'⟩ := hext w (hfs.1 hv)
  refine ⟨fun x => V' (cubeDilation (0 : SpatialCoordinates d) z r⁻¹ x), ?_, ?_⟩
  · -- a.e. equality on the cube of side `r`
    have hpull := aux_inputs_classical_e4_interpolation_pull_ae z hr v
    have hkey : ∀ᵐ x' ∂(volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))),
        (v : SpatialCoordinates d → ℝ) (cubeDilation z (0 : SpatialCoordinates d) r x') = V' x' := by
      filter_upwards [hpull, hV'ae] with x' h1 h2
      rw [← h1, h2]
    have hcoe : ⇑(cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne') = cubeDilation z 0 r := rfl
    set N : Set (SpatialCoordinates d) := {x | ¬ ((v : SpatialCoordinates d → ℝ) x =
      V' (cubeDilation (0 : SpatialCoordinates d) z r⁻¹ x))} with hN
    have hnull : (Measure.map (cubeDilation z (0 : SpatialCoordinates d) r) (volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))) N = 0 := by
      rw [← hcoe, MeasurableEquiv.map_apply]
      refine measure_mono_null ?_ (ae_iff.1 hkey)
      intro x' hx'
      simp only [Set.mem_preimage, hN, Set.mem_ofPred_eq] at hx' ⊢
      intro h
      apply hx'
      rw [hcoe]
      have hinv : cubeDilation (0 : SpatialCoordinates d) z r⁻¹ (cubeDilation z (0 : SpatialCoordinates d) r x') = x' := by
        have := MeasurableEquiv.symm_apply_apply (cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne') x'
        exact this
      rw [hinv]; exact h
    rw [map_cubeDilation_restrict z 0 hr one_pos, Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hnull
    rcases hnull with h0 | h0
    · exfalso
      rw [ENNReal.ofReal_eq_zero] at h0
      have : 0 < |(r ^ d)⁻¹| := abs_pos.2 (inv_ne_zero (pow_ne_zero _ hr.ne'))
      linarith
    · exact ae_iff.2 h0
  · calc globalFractionalSqNorm (s : ℝ) (fun x => V' (cubeDilation (0 : SpatialCoordinates d) z r⁻¹ x))
        ≤ globalFractionalSqNorm (s : ℝ) V' :=
          aux_inputs_classical_e4_extension_global_le hd s z hr hr1 V'
      _ ≤ ENNReal.ofReal (C * cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos s w) := hV'
      _ ≤ ENNReal.ofReal (C * cubeFractionalSqNorm hd z r hr s v) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left _ hC.le
          rw [aux_inputs_classical_e4_extension_sqnorm hd z hr s v,
            aux_inputs_classical_e4_extension_sqnorm hd (0 : SpatialCoordinates d) one_pos s w, ← hAs, hSs]
          have hs0 := s.2.1
          have hrs : 1 ≤ r ^ (-(s : ℝ)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by linarith)
          have hb0 : 0 ≤ (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s
              (fun _ : Fin 1 => w)).toReal := ENNReal.toReal_nonneg
          have : (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => w)).toReal ≤
              r ^ (-(s : ℝ)) * (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s
                (fun _ : Fin 1 => w)).toReal := by nlinarith
          nlinarith [this, sq_nonneg (‖v‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))]

end SubdiffusiveProcess.Paper

