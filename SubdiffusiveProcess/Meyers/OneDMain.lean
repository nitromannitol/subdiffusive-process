import SubdiffusiveProcess.Meyers.OneDBridge
import SubdiffusiveProcess.Meyers.PoincareBridge
import SubdiffusiveProcess.Meyers.Glue

/-! `d = 1`: the derived form `E2Body 1 p (1/2) 12`. -/

open MeasureTheory Set Filter Topology
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

namespace SubdiffusiveProcess.Meyers

/-- Cauchy–Schwarz: `∫ G ≤ |Q|^{1/2} ‖G‖₂` for `G ≥ 0`. -/
theorem integral_le_sqrt_mul_L2 {S : Set (Vec 1)} (hS : volume S < ⊤) {G : Vec 1 → ℝ}
    (hG : ∀ x, 0 ≤ G x) (hG2 : MemLp G 2 (volume.restrict S)) :
    ∫ x in S, G x ≤ (volume.real S) ^ (1 / 2 : ℝ) * (eLpNorm G 2 (volume.restrict S)).toReal := by
  haveI : IsFiniteMeasure (volume.restrict S) := ⟨by rw [Measure.restrict_apply_univ]; exact hS⟩
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict S) (f := G)
    (p := 1) (q := 2) (by norm_num) hG2.1
  have hint : Integrable G (volume.restrict S) := hG2.integrable (by norm_num)
  have e1 : ∫ x in S, G x = (eLpNorm G 1 (volume.restrict S)).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm hG2.1]
    congr 1; funext x
    exact (Real.norm_of_nonneg (hG x)).symm
  rw [e1]
  have hne : eLpNorm G 2 (volume.restrict S) ≠ ⊤ := hG2.eLpNorm_ne_top
  have h2 : (eLpNorm G 1 (volume.restrict S)).toReal ≤
      (eLpNorm G 2 (volume.restrict S) * (volume.restrict S) univ ^
        (1 / ENNReal.toReal 1 - 1 / ENNReal.toReal 2)).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top hne (ENNReal.rpow_ne_top_of_nonneg
      (by norm_num) (measure_ne_top _ _))) h1
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at h2
  have e2 : (1 / ENNReal.toReal 1 - 1 / ENNReal.toReal 2 : ℝ) = 1 / 2 := by
    norm_num
  rw [e2, Measure.restrict_apply_univ] at h2
  calc (eLpNorm G 1 (volume.restrict S)).toReal
      ≤ (eLpNorm G 2 (volume.restrict S)).toReal * ((volume S).toReal) ^ (1 / 2 : ℝ) := h2
    _ = (volume.real S) ^ (1 / 2 : ℝ) * (eLpNorm G 2 (volume.restrict S)).toReal := by
        rw [Measure.real]; ring

theorem oneD_sup_bound {x0 : Vec 1} {l : ℝ} (hl : 0 < l) {a : Vec 1 → ℝ} {a0 : ℝ} (ha0 : 0 < a0)
    (haM : AEMeasurable a (volume.restrict (Metric.ball x0 (2 * l))))
    (hnear : ∀ᵐ x ∂volume.restrict (Metric.ball x0 (2 * l)), |a x - a0| ≤ 1 / 2 * a0)
    {F : Vec 1 → ℝ} {Kf : ℝ} (hKf : 0 ≤ Kf)
    (hFb : ∀ᵐ x ∂volume.restrict (Metric.ball x0 (2 * l)), |F x| ≤ Kf)
    (u : H1Function (Metric.ball x0 (2 * l)))
    (heq : ∀ phi : H10Function (Metric.ball x0 (2 * l)),
      (∫ x in Metric.ball x0 (2 * l), a x * (∑ i : Fin 1, u.grad x i * phi.toH1Function.grad x i)) =
        ∫ x in Metric.ball x0 (2 * l), F x * phi.toH1Function.toFun x) :
    ∀ᵐ x ∂volume.restrict (Metric.ball x0 l),
      |u.grad x 0| ≤ 12 * ((eLpNorm (fun x => Real.sqrt (∑ i : Fin 1, (u.grad x i) ^ 2)) 2
          (volume.restrict (Metric.ball x0 (2 * l)))).toReal /
        (volume.real (Metric.ball x0 (2 * l))) ^ (1 / 2 : ℝ)) + 8 * l * a0⁻¹ * Kf := by
  have hpos : (0 : ℝ) < 2 * l := by positivity
  have hQ := ball_eq_preimage x0 hpos
  have hQ1 := ball_eq_preimage x0 hl
  have hvolQ : volume (Metric.ball x0 (2 * l)) < ⊤ := measure_ball_lt_top
  haveI hfinQ : IsFiniteMeasure (volume.restrict (Metric.ball x0 (2 * l))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hvolQ⟩
  have hgL2 : MemLp (fun x => u.grad x 0) 2 (volume.restrict (Metric.ball x0 (2 * l))) := u.gradMemL2 0
  have hgint : Integrable (fun x => u.grad x 0) (volume.restrict (Metric.ball x0 (2 * l))) :=
    hgL2.integrable (by norm_num)
  have habound : ∀ᵐ x ∂volume.restrict (Metric.ball x0 (2 * l)), ‖a x‖ ≤ 3 / 2 * a0 := by
    filter_upwards [hnear] with x hx
    rw [Real.norm_eq_abs]
    have := abs_le.mp hx
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]
  have hlow : ∀ᵐ x ∂volume.restrict (Metric.ball x0 (2 * l)), a0 / 2 ≤ |a x| := by
    filter_upwards [hnear] with x hx
    have := abs_le.mp hx
    rw [abs_of_nonneg (by linarith [this.1, this.2])]
    linarith [this.1]
  have hWint : Integrable (fun x => a x * u.grad x 0) (volume.restrict (Metric.ball x0 (2 * l))) :=
    hgint.bdd_mul haM.aestronglyMeasurable habound
  obtain ⟨wR, hwR⟩ : ∃ wR : ℝ → ℝ, wR = fun t => a (fun _ => t) * u.grad (fun _ => t) 0 := ⟨_, rfl⟩
  have hWeq : ∀ x : Vec 1, a x * u.grad x 0 = wR (x 0) := by
    intro x
    rw [hwR]
    show a x * u.grad x 0 = a (fun _ => x 0) * u.grad (fun _ => x 0) 0
    rw [← vec1_eq_const x]
  have hfun : (fun x : Vec 1 => wR (x 0)) = fun x => a x * u.grad x 0 := funext (fun x => (hWeq x).symm)
  have hw : IntegrableOn wR (Ioo (x0 0 - 2 * l) (x0 0 + 2 * l)) := by
    refine (integrableOn_transport wR).mp ?_
    rw [← hQ, hfun]
    exact hWint
  have hFae : ∀ᵐ t ∂volume.restrict (Ioo (x0 0 - 2 * l) (x0 0 + 2 * l)), |F (fun _ => t)| ≤ Kf := by
    rw [ae_transport (fun t => |F (fun _ => t)| ≤ Kf), ← hQ]
    filter_upwards [hFb] with x hx
    show |F (fun _ => x 0)| ≤ Kf
    rw [← vec1_eq_const x]
    exact hx
  have hreal := oneD_real_equation hl a F u heq
  have hreal' : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (x0 0 - 2 * l) (x0 0 + 2 * l) →
      ∫ t in Ioo (x0 0 - 2 * l) (x0 0 + 2 * l), wR t * deriv φ t =
        ∫ t in Ioo (x0 0 - 2 * l) (x0 0 + 2 * l), (fun t => F (fun _ => t)) t * φ t := by
    intro φ h1 h2 h3
    rw [hwR]
    exact hreal φ h1 h2 h3
  have hsup := real_line_sup_bound (c := x0 0) (F := fun t => F (fun _ => t)) hl hKf hw hFae hreal'
  have hsup' : ∀ᵐ x ∂volume.restrict (Metric.ball x0 l),
      |wR (x 0)| ≤ (1 / l) * (∫ s in Ioo (x0 0 - 2 * l) (x0 0 + 2 * l), |wR s|) + Kf * (4 * l) := by
    rw [hQ1]
    exact (ae_transport (fun t => |wR t| ≤ (1 / l) *
      (∫ s in Ioo (x0 0 - 2 * l) (x0 0 + 2 * l), |wR s|) + Kf * (4 * l))).mp hsup
  -- the integral of |w|
  obtain ⟨A2, hA2⟩ : ∃ A2 : ℝ, A2 = (eLpNorm (fun x => Real.sqrt (∑ i : Fin 1, (u.grad x i) ^ 2)) 2
      (volume.restrict (Metric.ball x0 (2 * l)))).toReal := ⟨_, rfl⟩
  rw [← hA2]
  have hGeq : ∀ x : Vec 1, Real.sqrt (∑ i : Fin 1, (u.grad x i) ^ 2) = |u.grad x 0| := by
    intro x
    simp [Real.sqrt_sq_eq_abs]
  have hI : (∫ s in Ioo (x0 0 - 2 * l) (x0 0 + 2 * l), |wR s|) ≤
      3 / 2 * a0 * ((volume.real (Metric.ball x0 (2 * l))) ^ (1 / 2 : ℝ) * A2) := by
    have e1 : (∫ s in Ioo (x0 0 - 2 * l) (x0 0 + 2 * l), |wR s|) =
        ∫ x in Metric.ball x0 (2 * l), |a x * u.grad x 0| := by
      rw [setIntegral_congr_set hQ.eventuallyEq,
        ← integral_transport (J := Ioo (x0 0 - 2 * l) (x0 0 + 2 * l)) (fun s => |wR s|)]
      congr 1; funext x; rw [hWeq x]
    rw [e1]
    calc ∫ x in Metric.ball x0 (2 * l), |a x * u.grad x 0|
        ≤ ∫ x in Metric.ball x0 (2 * l), (3 / 2 * a0) * |u.grad x 0| := by
          apply integral_mono_ae hWint.abs (hgint.abs.const_mul _)
          filter_upwards [habound] with x hx
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (by rwa [Real.norm_eq_abs] at hx) (abs_nonneg _)
      _ = (3 / 2 * a0) * ∫ x in Metric.ball x0 (2 * l), |u.grad x 0| := integral_const_mul _ _
      _ ≤ (3 / 2 * a0) * ((volume.real (Metric.ball x0 (2 * l))) ^ (1 / 2 : ℝ) * A2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := integral_le_sqrt_mul_L2 hvolQ
            (G := fun x => Real.sqrt (∑ i : Fin 1, (u.grad x i) ^ 2))
            (fun x => Real.sqrt_nonneg _) (memLp_two_gradNorm u)
          have e2 : ∫ x in Metric.ball x0 (2 * l), |u.grad x 0| =
              ∫ x in Metric.ball x0 (2 * l), Real.sqrt (∑ i : Fin 1, (u.grad x i) ^ 2) := by
            congr 1; funext x; exact (hGeq x).symm
          rw [e2, hA2]
          exact this
  have hV : volume.real (Metric.ball x0 (2 * l)) = 4 * l := by
    rw [volume_real_ball x0 hpos]; ring
  obtain ⟨sq, hsq⟩ : ∃ sq : ℝ, sq = (volume.real (Metric.ball x0 (2 * l))) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  rw [← hsq] at hI ⊢
  have hsq_pos : 0 < sq := by rw [hsq, hV]; positivity
  have hsq2 : sq * sq = 4 * l := by
    rw [hsq, ← Real.sqrt_eq_rpow, hV]
    exact Real.mul_self_sqrt (by positivity)
  have hA2nn : 0 ≤ A2 := by rw [hA2]; exact ENNReal.toReal_nonneg
  filter_upwards [hsup', ae_restrict_of_ae_restrict_of_subset
    (Metric.ball_subset_ball (by linarith : l ≤ 2 * l)) hlow] with x hx1 hx2
  have h1 : |u.grad x 0| * (a0 / 2) ≤ |wR (x 0)| := by
    rw [← hWeq x, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hx2 (abs_nonneg _)
  have h3 : |wR (x 0)| ≤ (1 / l) * (3 / 2 * a0 * (sq * A2)) + Kf * (4 * l) :=
    hx1.trans (add_le_add (mul_le_mul_of_nonneg_left hI (by positivity)) le_rfl)
  have heqT : (12 * (A2 / sq) + 8 * l * a0⁻¹ * Kf) * (a0 / 2) =
      (1 / l) * (3 / 2 * a0 * (sq * A2)) + Kf * (4 * l) := by
    field_simp
    linear_combination (-3 * A2 * a0) * hsq2
  have : |u.grad x 0| * (a0 / 2) ≤ (12 * (A2 / sq) + 8 * l * a0⁻¹ * Kf) * (a0 / 2) := by
    rw [heqT]; exact h1.trans h3
  exact le_of_mul_le_mul_right this (by positivity)

theorem e2_dim_one (p : ℝ) (hp : 2 ≤ p) : E2Body 1 p (1 / 2) 12 := by
  intro x0 l hl a a0 ha0 haM hnear F Kf hFM hKf hFb u heq
  have hp0 : 0 < p := by linarith
  have hsup := oneD_sup_bound hl ha0 haM hnear hKf hFb u heq
  have hvolQ : volume (Metric.ball x0 (2 * l)) < ⊤ := measure_ball_lt_top
  have hvolQ1 : volume (Metric.ball x0 l) < ⊤ := measure_ball_lt_top
  haveI hfin1 : IsFiniteMeasure (volume.restrict (Metric.ball x0 l)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hvolQ1⟩
  obtain ⟨A2, hA2⟩ : ∃ A2 : ℝ, A2 = (eLpNorm (fun x => Real.sqrt (∑ i : Fin 1, (u.grad x i) ^ 2)) 2
      (volume.restrict (Metric.ball x0 (2 * l)))).toReal := ⟨_, rfl⟩
  rw [← hA2] at hsup ⊢
  have hV : volume.real (Metric.ball x0 (2 * l)) = 4 * l := by
    rw [volume_real_ball x0 (by positivity)]; ring
  have hV1 : volume.real (Metric.ball x0 l) = 2 * l := by
    rw [volume_real_ball x0 hl]; ring
  have hs : 0 < (volume.real (Metric.ball x0 (2 * l))) ^ (1 / 2 : ℝ) := by
    rw [hV]; positivity
  have hA2nn : 0 ≤ A2 := by rw [hA2]; exact ENNReal.toReal_nonneg
  have hGeq : ∀ x : Vec 1, Real.sqrt (∑ i : Fin 1, (u.grad x i) ^ 2) = |u.grad x 0| := by
    intro x
    simp [Real.sqrt_sq_eq_abs]
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 12 * (A2 / (volume.real (Metric.ball x0 (2 * l))) ^ (1 / 2 : ℝ)) +
      8 * l * a0⁻¹ * Kf := ⟨_, rfl⟩
  rw [← hM] at hsup
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hG : ∀ᵐ x ∂volume.restrict (Metric.ball x0 l),
      |Real.sqrt (∑ i : Fin 1, (u.grad x i) ^ 2)| ≤ M := by
    filter_upwards [hsup] with x hx
    rw [hGeq x, abs_abs]
    exact hx
  have hmeas : AEStronglyMeasurable (fun x => Real.sqrt (∑ i : Fin 1, (u.grad x i) ^ 2))
      (volume.restrict (Metric.ball x0 l)) :=
    (memLp_two_gradNorm u).1.mono_measure (Measure.restrict_mono
      (Metric.ball_subset_ball (by linarith : l ≤ 2 * l)) le_rfl)
  refine ⟨MemLp.of_bound hmeas M (by filter_upwards [hG] with x hx; simpa [Real.norm_eq_abs] using hx), ?_⟩
  have h1 := toReal_eLpNorm_bounded_le (μ := volume.restrict (Metric.ball x0 l))
    (f := fun x => Real.sqrt (∑ i : Fin 1, (u.grad x i) ^ 2)) hM0 hG hp0
  rw [Measure.restrict_apply_univ] at h1
  have hV1' : ((volume (Metric.ball x0 l)).toReal) = 2 * l := by
    rw [← Measure.real, hV1]
  rw [hV1'] at h1
  have hpos : 0 < (2 * l) ^ (1 / p) := by positivity
  rw [hV1, div_le_iff₀ hpos]
  · calc (eLpNorm (fun x => Real.sqrt (∑ i : Fin 1, (u.grad x i) ^ 2)) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x0 l))).toReal
        ≤ M * (2 * l) ^ (1 / p) := h1
      _ ≤ (12 * (A2 / (volume.real (Metric.ball x0 (2 * l))) ^ (1 / 2 : ℝ)) +
            12 * l * a0⁻¹ * Kf) * (2 * l) ^ (1 / p) := by
          apply mul_le_mul_of_nonneg_right _ hpos.le
          rw [hM]
          have : 0 ≤ l * a0⁻¹ * Kf := by positivity
          nlinarith [this]

end SubdiffusiveProcess.Meyers
