import SubdiffusiveProcess.Paper.lem_19_smooth_density_one_step_dilation
import SubdiffusiveProcess.Paper.lem_19_smooth_density_one_step_mollification
import SubdiffusiveProcess.Lane2.ExternalInputs
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace Paper

theorem aux_lem_19_smooth_density_one_step_error_assembly_kernel_square
    (t : ℝ) (b : ℝ≥0∞) (q : ℝ) :
    ENNReal.ofReal (t ^ 2) / b ^ q =
      (ENNReal.ofReal |t| / b ^ (q / 2)) ^ 2 := by
  rw [← sq_abs t, ENNReal.ofReal_pow (abs_nonneg t) 2]
  conv_rhs => rw [ENNReal.div_eq_inv_mul]
  rw [mul_pow]
  rw [← ENNReal.inv_pow]
  rw [ENNReal.div_eq_inv_mul]
  rw [← ENNReal.rpow_natCast (b ^ (q / 2)) 2, ← ENNReal.rpow_mul]
  congr 1
  ring_nf

theorem aux_lem_19_smooth_density_one_step_error_assembly_fractional_add
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r)
    (f g : Fin 1 → DomainL2 (centeredCube z r hr))
    (hf : cubeFractionalL2Seminorm hd z r hr halfFractionalOrder f < ⊤)
    (hg : cubeFractionalL2Seminorm hd z r hr halfFractionalOrder g < ⊤) :
    cubeFractionalL2Seminorm hd z r hr halfFractionalOrder (fun i => f i + g i) < ⊤ ∧
      (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder (fun i => f i + g i)).toReal ≤
        (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder f).toReal +
          (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder g).toReal := by
  classical
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  let μ : Measure (SpatialCoordinates d) := volume.restrict U
  let a : ℝ≥0∞ := ENNReal.ofReal (halfFractionalOrder : ℝ) / volume U
  let q : ℝ := (d : ℝ) + 2 * (halfFractionalOrder : ℝ)
  let If : ℝ≥0∞ := ∫⁻ x, ∫⁻ y,
      ENNReal.ofReal (∑ i : Fin 1, (f i x - f i y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ q ∂μ ∂μ
  let Ig : ℝ≥0∞ := ∫⁻ x, ∫⁻ y,
      ENNReal.ofReal (∑ i : Fin 1, (g i x - g i y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ q ∂μ ∂μ
  let Ip : ℝ≥0∞ := ∫⁻ x, ∫⁻ y,
      ENNReal.ofReal (((f 0 x + g 0 x) - (f 0 y + g 0 y)) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ q ∂μ ∂μ
  have hvoltop : volume U ≠ ⊤ := by
    simp only [U, centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  have hvolpos : 0 < volume U := by
    simp only [U, centeredCube_volume]
    exact ENNReal.ofReal_pos.mpr (pow_pos hr _)
  have ha0 : a ≠ 0 := by
    apply ENNReal.div_ne_zero.mpr
    exact ⟨(ENNReal.ofReal_pos.mpr halfFractionalOrder.2.1).ne', hvoltop⟩
  have hfa : (a * If) ^ (1 / 2 : ℝ) < ⊤ := by
    simpa only [a, If, U, μ, q, cubeFractionalL2Seminorm] using hf
  have hga : (a * Ig) ^ (1 / 2 : ℝ) < ⊤ := by
    simpa only [a, Ig, U, μ, q, cubeFractionalL2Seminorm] using hg
  have hIf : If < ⊤ := by
    have hprod : a * If < ⊤ := by
      by_contra h
      have heq : a * If = ⊤ := top_unique (le_of_not_gt h)
      exact (ne_of_lt hfa) (by rw [heq, ENNReal.top_rpow_of_pos (by norm_num)])
    rcases (ENNReal.mul_lt_top_iff.mp hprod) with h | h | h
    · exact h.2
    · exact (ha0 h).elim
    · simp [h]
  have hIg : Ig < ⊤ := by
    have hprod : a * Ig < ⊤ := by
      by_contra h
      have heq : a * Ig = ⊤ := top_unique (le_of_not_gt h)
      exact (ne_of_lt hga) (by rw [heq, ENNReal.top_rpow_of_pos (by norm_num)])
    rcases (ENNReal.mul_lt_top_iff.mp hprod) with h | h | h
    · exact h.2
    · exact (ha0 h).elim
    · simp [h]
  have hfi (i : Fin 1) : AEStronglyMeasurable (fun x => (f i x : ℝ)) μ := by
    simpa only [μ] using (Lp.aestronglyMeasurable (f i))
  have hgi (i : Fin 1) : AEStronglyMeasurable (fun x => (g i x : ℝ)) μ := by
    simpa only [μ] using (Lp.aestronglyMeasurable (g i))
  let Hf : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun xy =>
    ENNReal.ofReal |(f 0 xy.1 : ℝ) - (f 0 xy.2 : ℝ)| /
      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (xy.1 j - xy.2 j) ^ 2))) ^ (q / 2)
  let Hg : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun xy =>
    ENNReal.ofReal |(g 0 xy.1 : ℝ) - (g 0 xy.2 : ℝ)| /
      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (xy.1 j - xy.2 j) ^ 2))) ^ (q / 2)
  let Hp : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun xy =>
    ENNReal.ofReal |((f 0 xy.1 : ℝ) + (g 0 xy.1 : ℝ)) -
        ((f 0 xy.2 : ℝ) + (g 0 xy.2 : ℝ))| /
      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (xy.1 j - xy.2 j) ^ 2))) ^ (q / 2)
  have hbase : Measurable
      (fun xy : SpatialCoordinates d × SpatialCoordinates d =>
        ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (xy.1 j - xy.2 j) ^ 2))) := by
    apply Measurable.ennreal_ofReal
    apply Measurable.sqrt
    exact Finset.measurable_sum Finset.univ fun j _ =>
      (((measurable_pi_apply j).comp measurable_fst).sub
        ((measurable_pi_apply j).comp measurable_snd)).pow_const 2
  have hden : Measurable
      (fun xy : SpatialCoordinates d × SpatialCoordinates d =>
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (xy.1 j - xy.2 j) ^ 2))) ^ (q / 2)) := by
    exact hbase.pow measurable_const
  have hnumf : AEMeasurable
      (fun xy : SpatialCoordinates d × SpatialCoordinates d =>
        |(f 0 xy.1 : ℝ) - (f 0 xy.2 : ℝ)|) (μ.prod μ) := by
    exact (((hfi 0).aemeasurable.comp_fst).sub
      ((hfi 0).aemeasurable.comp_snd)).abs
  have hnumg : AEMeasurable
      (fun xy : SpatialCoordinates d × SpatialCoordinates d =>
        |(g 0 xy.1 : ℝ) - (g 0 xy.2 : ℝ)|) (μ.prod μ) := by
    exact (((hgi 0).aemeasurable.comp_fst).sub
      ((hgi 0).aemeasurable.comp_snd)).abs
  have hHf : AEMeasurable Hf (μ.prod μ) := by
    exact hnumf.ennreal_ofReal.div hden.aemeasurable
  have hHg : AEMeasurable Hg (μ.prod μ) := by
    exact hnumg.ennreal_ofReal.div hden.aemeasurable
  have hnump : AEMeasurable
      (fun xy : SpatialCoordinates d × SpatialCoordinates d =>
        |((f 0 xy.1 : ℝ) + (g 0 xy.1 : ℝ)) -
          ((f 0 xy.2 : ℝ) + (g 0 xy.2 : ℝ))|) (μ.prod μ) := by
    exact ((((hfi 0).aemeasurable.comp_fst).add
      ((hgi 0).aemeasurable.comp_fst)).sub
        (((hfi 0).aemeasurable.comp_snd).add
          ((hgi 0).aemeasurable.comp_snd))).abs
  have hHp : AEMeasurable Hp (μ.prod μ) := by
    exact hnump.ennreal_ofReal.div hden.aemeasurable
  have hpoint (xy : SpatialCoordinates d × SpatialCoordinates d) :
      Hp xy ≤ Hf xy + Hg xy := by
    dsimp [Hp, Hf, Hg]
    have habs :
        |((f 0 xy.1 : ℝ) + (g 0 xy.1 : ℝ)) -
            ((f 0 xy.2 : ℝ) + (g 0 xy.2 : ℝ))| ≤
          |(f 0 xy.1 : ℝ) - (f 0 xy.2 : ℝ)| +
            |(g 0 xy.1 : ℝ) - (g 0 xy.2 : ℝ)| := by
      calc
        _ = |((f 0 xy.1 : ℝ) - (f 0 xy.2 : ℝ)) +
            ((g 0 xy.1 : ℝ) - (g 0 xy.2 : ℝ))| := by congr 1 <;> ring
        _ ≤ _ := abs_add_le _ _
    calc
      _ ≤ ENNReal.ofReal (|(f 0 xy.1 : ℝ) - (f 0 xy.2 : ℝ)| +
            |(g 0 xy.1 : ℝ) - (g 0 xy.2 : ℝ)|) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (xy.1 j - xy.2 j) ^ 2))) ^ (q / 2) :=
        ENNReal.div_le_div (ENNReal.ofReal_le_ofReal habs) (le_refl _)
      _ = Hf xy + Hg xy := by
        rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), ENNReal.add_div]
  have hIf_eq : If = ∫⁻ xy, Hf xy ^ (2 : ℝ) ∂(μ.prod μ) := by
    calc
      If = ∫⁻ x, ∫⁻ y, Hf (x, y) ^ (2 : ℝ) ∂μ ∂μ := by
        apply lintegral_congr_ae
        filter_upwards with x
        apply lintegral_congr_ae
        filter_upwards with y
        have hkernel :=
          aux_lem_19_smooth_density_one_step_error_assembly_kernel_square
            ((f 0 x : ℝ) - (f 0 y : ℝ))
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) q
        have hsquare :
            (ENNReal.ofReal |(f 0 x : ℝ) - (f 0 y : ℝ)| /
                (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ (q / 2)) ^
                (2 : ℕ) =
              (ENNReal.ofReal |(f 0 x : ℝ) - (f 0 y : ℝ)| /
                (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ (q / 2)) ^
                (2 : ℝ) := (ENNReal.rpow_natCast _ 2).symm
        simpa only [Hf, q, Fin.sum_univ_succ, Fin.sum_univ_zero, zero_add, add_zero] using
          hkernel.trans hsquare
      _ = ∫⁻ xy, Hf xy ^ (2 : ℝ) ∂(μ.prod μ) := by
        symm
        exact lintegral_prod _ (hHf.pow_const 2)
  have hIg_eq : Ig = ∫⁻ xy, Hg xy ^ (2 : ℝ) ∂(μ.prod μ) := by
    calc
      Ig = ∫⁻ x, ∫⁻ y, Hg (x, y) ^ (2 : ℝ) ∂μ ∂μ := by
        apply lintegral_congr_ae
        filter_upwards with x
        apply lintegral_congr_ae
        filter_upwards with y
        have hkernel :=
          aux_lem_19_smooth_density_one_step_error_assembly_kernel_square
            ((g 0 x : ℝ) - (g 0 y : ℝ))
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) q
        have hsquare :
            (ENNReal.ofReal |(g 0 x : ℝ) - (g 0 y : ℝ)| /
                (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ (q / 2)) ^
                (2 : ℕ) =
              (ENNReal.ofReal |(g 0 x : ℝ) - (g 0 y : ℝ)| /
                (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ (q / 2)) ^
                (2 : ℝ) := (ENNReal.rpow_natCast _ 2).symm
        simpa only [Hg, q, Fin.sum_univ_succ, Fin.sum_univ_zero, zero_add, add_zero] using
          hkernel.trans hsquare
      _ = ∫⁻ xy, Hg xy ^ (2 : ℝ) ∂(μ.prod μ) := by
        symm
        exact lintegral_prod _ (hHg.pow_const 2)
  have hplus_ae : ∀ᵐ x ∂μ, ∀ i : Fin 1,
      ((f i + g i) x : ℝ) = (f i x : ℝ) + (g i x : ℝ) := by
    exact ae_all_iff.mpr fun i => Lp.coeFn_add (f i) (g i)
  have hIp_eq : Ip = ∫⁻ xy, Hp xy ^ (2 : ℝ) ∂(μ.prod μ) := by
    calc
      Ip = ∫⁻ x, ∫⁻ y, Hp (x, y) ^ (2 : ℝ) ∂μ ∂μ := by
        apply lintegral_congr_ae
        filter_upwards with x
        apply lintegral_congr_ae
        filter_upwards with y
        have hkernel :=
          aux_lem_19_smooth_density_one_step_error_assembly_kernel_square
            (((f 0 x : ℝ) + (g 0 x : ℝ)) - ((f 0 y : ℝ) + (g 0 y : ℝ)))
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) q
        have hsquare :
            (ENNReal.ofReal |((f 0 x : ℝ) + (g 0 x : ℝ)) -
                ((f 0 y : ℝ) + (g 0 y : ℝ))| /
                (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ (q / 2)) ^
                (2 : ℕ) =
              (ENNReal.ofReal |((f 0 x : ℝ) + (g 0 x : ℝ)) -
                ((f 0 y : ℝ) + (g 0 y : ℝ))| /
                (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ (q / 2)) ^
                (2 : ℝ) := (ENNReal.rpow_natCast _ 2).symm
        simpa only [Hp, q] using hkernel.trans hsquare
      _ = ∫⁻ xy, Hp xy ^ (2 : ℝ) ∂(μ.prod μ) := by
        symm
        exact lintegral_prod _ (hHp.pow_const 2)
  have hsemi_f :
      cubeFractionalL2Seminorm hd z r hr halfFractionalOrder f =
        (a * If) ^ (1 / 2 : ℝ) := by
    simpa only [a, If, U, μ, q, cubeFractionalL2Seminorm]
  have hsemi_g :
      cubeFractionalL2Seminorm hd z r hr halfFractionalOrder g =
        (a * Ig) ^ (1 / 2 : ℝ) := by
    simpa only [a, Ig, U, μ, q, cubeFractionalL2Seminorm]
  have hsemi_p :
      cubeFractionalL2Seminorm hd z r hr halfFractionalOrder (fun i => f i + g i) =
        (a * Ip) ^ (1 / 2 : ℝ) := by
    unfold cubeFractionalL2Seminorm
    rw [show (∫⁻ x in U, ∫⁻ y in U,
        ENNReal.ofReal (∑ i : Fin 1, ((f i + g i) x - (f i + g i) y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ q) = Ip by
      dsimp [Ip, U, μ]
      apply lintegral_congr_ae
      filter_upwards [hplus_ae] with x hx
      apply lintegral_congr_ae
      filter_upwards [hplus_ae] with y hy
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, zero_add, add_zero]
      change ENNReal.ofReal ((((f 0 + g 0) x : ℝ) - ((f 0 + g 0) y : ℝ)) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ q = _
      rw [hx 0, hy 0]
      ]
  have hmink := ENNReal.lintegral_Lp_add_le hHf hHg (by norm_num : (1 : ℝ) ≤ 2)
  have hroot : Ip ^ (1 / 2 : ℝ) ≤ If ^ (1 / 2 : ℝ) + Ig ^ (1 / 2 : ℝ) := by
    rw [hIp_eq, hIf_eq, hIg_eq]
    calc
      (∫⁻ xy, Hp xy ^ (2 : ℝ) ∂(μ.prod μ)) ^ (1 / 2 : ℝ) ≤
          (∫⁻ xy, (Hf xy + Hg xy) ^ (2 : ℝ) ∂(μ.prod μ)) ^ (1 / 2 : ℝ) := by
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        exact lintegral_mono fun xy =>
          ENNReal.rpow_le_rpow (hpoint xy) (by norm_num)
      _ ≤ _ := hmink
  have hroot' : (a * Ip) ^ (1 / 2 : ℝ) ≤
      (a * If) ^ (1 / 2 : ℝ) + (a * Ig) ^ (1 / 2 : ℝ) := by
    calc
      (a * Ip) ^ (1 / 2 : ℝ) = a ^ (1 / 2 : ℝ) * Ip ^ (1 / 2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ ≤ a ^ (1 / 2 : ℝ) * (If ^ (1 / 2 : ℝ) + Ig ^ (1 / 2 : ℝ)) :=
        mul_le_mul_left' hroot _
      _ = (a * If) ^ (1 / 2 : ℝ) + (a * Ig) ^ (1 / 2 : ℝ) := by
        rw [mul_add, ← ENNReal.mul_rpow_of_nonneg a If (by norm_num),
          ← ENNReal.mul_rpow_of_nonneg a Ig (by norm_num)]
  constructor
  · rw [hsemi_p]
    exact lt_of_le_of_lt hroot' (ENNReal.add_lt_top.mpr ⟨hfa, hga⟩)
  · have hroot_top : (a * If) ^ (1 / 2 : ℝ) + (a * Ig) ^ (1 / 2 : ℝ) ≠ ⊤ :=
      (ENNReal.add_lt_top.mpr ⟨hfa, hga⟩).ne
    have hto := ENNReal.toReal_mono hroot_top hroot'
    calc
      (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder (fun i => f i + g i)).toReal =
          ((a * Ip) ^ (1 / 2 : ℝ)).toReal := by rw [hsemi_p]
      _ ≤ ((a * If) ^ (1 / 2 : ℝ) + (a * Ig) ^ (1 / 2 : ℝ)).toReal := hto
      _ = (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder f).toReal +
          (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder g).toReal := by
        rw [ENNReal.toReal_add hfa.ne hga.ne, ← hsemi_f, ← hsemi_g]

/-- Final error assembly in the smooth-density construction, paper 1936–1939.
Carried-input tick list:
- SOURCE: the dimension, cube, classes `v`, `u`, `a`, and the positive
  tolerance `ε`.
- DEPENDENCY: `lem_19_smooth_density_one_step_dilation` supplies the first
  difference identity and its half-error bound.
- DEPENDENCY: `lem_19_smooth_density_one_step_mollification` supplies the
  second difference identity and its half-error bound.
- CONCLUDED HERE: an admissible class representing `v-a` with total error
  below `ε`.
The class addition and triangle estimate are the final assembly of the two
paper errors, not extra hypotheses on the source data. -/
theorem lem_19_smooth_density_one_step_error_assembly
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r)
    (v u a dilErr mollErr :
      CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder)
    (hdil : dilErr.val 0 = v.val 0 - u.val 0)
    (hmoll : mollErr.val 0 = u.val 0 - a.val 0)
    {ε : ℝ} (hε : 0 < ε)
    (hdilErr : cubeFractionalL2Norm hd z r hr halfFractionalOrder dilErr < ε / 2)
    (hmollErr : cubeFractionalL2Norm hd z r hr halfFractionalOrder mollErr < ε / 2) :
    ∃ diff : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
      diff.val 0 = v.val 0 - a.val 0 ∧
      cubeFractionalL2Norm hd z r hr halfFractionalOrder diff < ε := by
  have hsemi :=
    aux_lem_19_smooth_density_one_step_error_assembly_fractional_add
      hd z r hr (fun i => dilErr.val i) (fun i => mollErr.val i)
      dilErr.property mollErr.property
  let diff : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder :=
    ⟨fun i => dilErr.val i + mollErr.val i, hsemi.1⟩
  have hdiff_val : diff.val 0 = v.val 0 - a.val 0 := by
    dsimp [diff]
    rw [hdil, hmoll]
    abel
  have hsqrt :
      Real.sqrt (∑ i : Fin 1, ‖dilErr.val i + mollErr.val i‖ ^ 2) ≤
        Real.sqrt (∑ i : Fin 1, ‖dilErr.val i‖ ^ 2) +
          Real.sqrt (∑ i : Fin 1, ‖mollErr.val i‖ ^ 2) := by
    simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, zero_add, add_zero,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      (norm_add_le (dilErr.val 0) (mollErr.val 0))
  have hnormle :
      cubeFractionalL2Norm hd z r hr halfFractionalOrder diff ≤
        cubeFractionalL2Norm hd z r hr halfFractionalOrder dilErr +
          cubeFractionalL2Norm hd z r hr halfFractionalOrder mollErr := by
    unfold cubeFractionalL2Norm
    dsimp [diff]
    have hcoef : 0 ≤ r ^ (-(halfFractionalOrder : ℝ)) :=
      Real.rpow_nonneg (le_of_lt hr) _
    have hden : 0 ≤ Real.sqrt (volume.real
        (centeredCube z r hr : Set (SpatialCoordinates d))) := Real.sqrt_nonneg _
    have hdiv :
        Real.sqrt (∑ i : Fin 1, ‖dilErr.val i + mollErr.val i‖ ^ 2) /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
          Real.sqrt (∑ i : Fin 1, ‖dilErr.val i‖ ^ 2) /
              Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) +
            Real.sqrt (∑ i : Fin 1, ‖mollErr.val i‖ ^ 2) /
              Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) := by
      calc
        _ ≤ (Real.sqrt (∑ i : Fin 1, ‖dilErr.val i‖ ^ 2) +
            Real.sqrt (∑ i : Fin 1, ‖mollErr.val i‖ ^ 2)) /
              Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) :=
          div_le_div_of_nonneg_right hsqrt hden
        _ = _ := add_div _ _ _
    calc
      (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder
          (fun i => dilErr.val i + mollErr.val i)).toReal +
          r ^ (-(halfFractionalOrder : ℝ)) *
            (Real.sqrt (∑ i : Fin 1, ‖dilErr.val i + mollErr.val i‖ ^ 2) /
              Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))
          ≤ ((cubeFractionalL2Seminorm hd z r hr halfFractionalOrder
              (fun i => dilErr.val i)).toReal +
              (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder
                (fun i => mollErr.val i)).toReal) +
            r ^ (-(halfFractionalOrder : ℝ)) *
              ((Real.sqrt (∑ i : Fin 1, ‖dilErr.val i‖ ^ 2) /
                  Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) +
                (Real.sqrt (∑ i : Fin 1, ‖mollErr.val i‖ ^ 2) /
                  Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))) := by
        exact add_le_add hsemi.2
          (mul_le_mul_of_nonneg_left
            hdiv hcoef)
      _ = cubeFractionalL2Norm hd z r hr halfFractionalOrder dilErr +
          cubeFractionalL2Norm hd z r hr halfFractionalOrder mollErr := by
        unfold cubeFractionalL2Norm
        ring
  refine ⟨diff, hdiff_val, ?_⟩
  exact lt_of_le_of_lt hnormle (by linarith)

end Paper
