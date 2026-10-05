module

public import SubdiffusiveProcess.FractionalEmbedding.Endpoint
public import SubdiffusiveProcess.FractionalEmbedding.RealLp

@[expose] public section

open MeasureTheory Set
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.FractionalEmbedding

/-- Transfer the endpoint inequality through the almost-everywhere real L2 carrier. -/
theorem domainL2_raw_moment {d : ℕ} (hd : 2 ≤ d) (s : Set.Ioo (0 : ℝ) 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (v : DomainL2 (centeredCube z r hr))
    (hE : scalarGagliardoEnergy z r hr s v < ⊤) :
    (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ENNReal.ofReal (|v x| ^ criticalPower d s)) < ⊤ ∧
    (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ENNReal.ofReal (|v x| ^ criticalPower d s)).toReal ^ criticalRoot d s ≤
      rawEmbeddingConstant d s r * (‖v‖ ^ 2 + (scalarGagliardoEnergy z r hr s v).toReal) := by
  let μ := volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
  obtain ⟨hβ, _, hq, _, _⟩ := critical_exponents hd s
  by_cases hv : ‖v‖ = 0
  · have hvzero : v = 0 := norm_eq_zero.mp hv
    have hvAE : (v : SpatialCoordinates d → ℝ) =ᵐ[μ] 0 := by
      simpa only [hvzero] using (Lp.coeFn_zero ℝ 2 μ)
    have hmoment : (∫⁻ x, ENNReal.ofReal (|v x| ^ criticalPower d s) ∂μ) = 0 := by
      calc
        _ = ∫⁻ _x, (0 : ℝ≥0∞) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [hvAE] with x hx
          simp only [hx, Pi.zero_apply, abs_zero, Real.zero_rpow hq.ne', ENNReal.ofReal_zero]
        _ = 0 := lintegral_zero
    change (_ : ℝ≥0∞) < ⊤ ∧ _
    rw [hmoment]
    simp only [ENNReal.toReal_zero, Real.zero_rpow hβ.ne']
    exact ⟨ENNReal.zero_lt_top, mul_nonneg (rawEmbeddingConstant_pos d s r).le
      (add_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)⟩
  · let g := (Lp.aestronglyMeasurable v).mk v
    let f := fun x => |g x|
    have hg : Measurable g := (Lp.aestronglyMeasurable v).stronglyMeasurable_mk.measurable
    have hf : Measurable f := by
      simpa only [Real.norm_eq_abs] using hg.norm
    have hf0 (x : SpatialCoordinates d) : 0 ≤ f x := abs_nonneg _
    have hgv : g =ᵐ[μ] (v : SpatialCoordinates d → ℝ) :=
      (Lp.aestronglyMeasurable v).ae_eq_mk.symm
    have hL2eq : (∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ) = ENNReal.ofReal (‖v‖ ^ 2) := by
      calc
        _ = ∫⁻ x, ENNReal.ofReal ((v x) ^ 2) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [hgv] with x hx
          dsimp only [f]
          rw [hx, sq_abs]
        _ = _ := squaredMoment_eq_L2 z r hr v
    have hEF : scalarGagliardoEnergy z r hr s f ≤ scalarGagliardoEnergy z r hr s v :=
      (scalarGagliardoEnergy_abs_le z r hr s g).trans_eq
        (scalarGagliardoEnergy_congr_ae z r hr s hgv)
    have hnorm : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    have hM : 0 < (∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ).toReal := by
      rw [hL2eq, ENNReal.toReal_ofReal (sq_nonneg _)]
      exact pow_pos hnorm 2
    obtain ⟨hfinite, hbound⟩ := cube_fractional_moment_bound hd z r hr s f hf hf0
      (by rw [hL2eq]; exact ENNReal.ofReal_lt_top) hM (hEF.trans_lt hE)
    have hmoment : (∫⁻ x, ENNReal.ofReal (|v x| ^ criticalPower d s) ∂μ) =
        ∫⁻ x, ENNReal.ofReal ((f x) ^ criticalPower d s) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hgv] with x hx
      dsimp only [f]
      rw [hx]
    change (_ : ℝ≥0∞) < ⊤ ∧ _
    rw [hmoment]
    refine ⟨hfinite, ?_⟩
    rw [hL2eq, ENNReal.toReal_ofReal (sq_nonneg _)] at hbound
    have hER := ENNReal.toReal_mono hE.ne hEF
    have hscaled := mul_le_mul_of_nonneg_left hER (rawEmbeddingConstant_pos d s r).le
    linarith only [hbound, hscaled]

/-- Fractional Sobolev embedding with the exact project's volume-normalized norm. -/
theorem cube_sobolev_embedding
    (d : ℕ) (hd : 2 ≤ d) (s : Set.Ioo (0 : ℝ) 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : DomainL2 (centeredCube z r hr),
      cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v) < ⊤ →
      MemLp (v : SpatialCoordinates d → ℝ) (ENNReal.ofReal (criticalPower d s))
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            |v x| ^ criticalPower d s) ^ criticalRoot d s ≤
          C * cubeFractionalSqNorm hd z r hr s v := by
  let C := rawEmbeddingConstant d (s : ℝ) r
  let V := volume.real (centeredCube z r hr : Set (SpatialCoordinates d))
  have hC : 0 < C := rawEmbeddingConstant_pos d s r
  have hV : 0 < V := centeredCube_volume_pos z hr
  have hs : 0 < (s : ℝ) := s.2.1
  refine ⟨C * V / (s : ℝ), div_pos (mul_pos hC hV) hs, ?_⟩
  intro v hv
  have hE := (scalarSeminorm_lt_top_iff hd z r hr s v).mp hv
  obtain ⟨hfinite, hbound⟩ := domainL2_raw_moment hd s z r hr v hE
  have hq := (critical_exponents hd s).2.2.1
  refine ⟨memLp_of_abs_moment _ v (Lp.aestronglyMeasurable v) hq hfinite, ?_⟩
  rw [absMoment_integral _ v (Lp.aestronglyMeasurable v) (criticalPower d s)]
  calc
    _ ≤ C * (‖v‖ ^ 2 + (scalarGagliardoEnergy z r hr s v).toReal) := hbound
    _ ≤ (C / (s : ℝ)) * (‖v‖ ^ 2 + (s : ℝ) *
        (scalarGagliardoEnergy z r hr s v).toReal) := by
      have hcoeff : C ≤ C / (s : ℝ) := by
        apply (le_div_iff₀ hs).mpr
        nlinarith only [mul_nonneg hC.le (sub_nonneg.mpr s.2.2.le)]
      have hscaled := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg ‖v‖)
      have hcancel : (C / (s : ℝ)) * (‖v‖ ^ 2 + (s : ℝ) *
          (scalarGagliardoEnergy z r hr s v).toReal) =
          (C / (s : ℝ)) * ‖v‖ ^ 2 + C * (scalarGagliardoEnergy z r hr s v).toReal := by
        field_simp
      rw [hcancel]
      nlinarith only [hscaled]
    _ = (C * V / (s : ℝ)) * cubeFractionalSqNorm hd z r hr s v := by
      rw [cubeFractionalSqNorm_eq_raw]
      change (C / (s : ℝ)) * (‖v‖ ^ 2 + (s : ℝ) *
        (scalarGagliardoEnergy z r hr s v).toReal) =
        (C * V / (s : ℝ)) * (((s : ℝ) *
          (scalarGagliardoEnergy z r hr s v).toReal + ‖v‖ ^ 2) / V)
      field_simp
      ring

end SubdiffusiveProcess.FractionalEmbedding
