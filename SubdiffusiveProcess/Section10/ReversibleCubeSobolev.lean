import SubdiffusiveProcess.CoarseGrainingVocab.Section11.CubeH10Embedding
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledStrongContinuity

/-! Deterministic weighted cube Sobolev estimates from the native zero-trace
embedding and actual local coefficient bounds. No caller's energy inequality
or probabilistic regularity certificate is introduced. -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledStrongContinuity
open SubdiffusiveProcess.CoarseGrainingVocab.Section11
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

/-- An arbitrary finite Sobolev conjugate cube embedding transports to the
actual positive weight and scalar coefficient energy. -/
theorem exists_weighted_h10_cube_energy_bound {d : ℕ} [NeZero d]
    (p q : FiniteLpExponent) (hp : p.exponent ≤ 2)
    (hpd : p.exponent.toReal < d)
    (hpq : q.exponent.toReal⁻¹ = p.exponent.toReal⁻¹ - (d : ℝ)⁻¹)
    (z : Vec d) (L : ℝ) (hL : 0 < L) (c rho : Vec d → ℝ)
    (hc : CoefficientOn (axisCube z L) c) (hr : CoefficientOn (axisCube z L) rho) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : H10Function (axisCube z L),
      eLpNorm u.toH1Function.toFun q.exponent
          ((weightedMeasure rho).restrict (axisCube z L)) ^ 2 ≤
        ENNReal.ofReal K * ENNReal.ofReal (energy c (axisCube z L) u.toH1Function) := by
  obtain ⟨C, hC, hbound⟩ := h10_cube_embedding_sq p hp hpd
  obtain ⟨lo, hi, hlo, hcb⟩ := hc.2
  obtain ⟨rlo, rhi, _hrlo, hrb⟩ := hr.2
  let H := |rhi| + 1
  have hH : 0 < H := by dsimp only [H]; positivity
  let J := H ^ (1 / q.exponent.toReal)
  have hJ : 0 < J := Real.rpow_pos_of_pos hH _
  let D := C * (volume (axisCube z L)).toReal ^
    (2 * (1 / p.exponent.toReal - 1 / 2))
  have hD : 0 < D := mul_pos hC (Real.rpow_pos_of_pos (volume_axisCube_toReal_pos z hL) _)
  have hmu := weightedMeasure_restrict_le_smul_volume_restrict
    (isOpen_axisCube z L).measurableSet H (hrb.mono fun x hx ↦
      hx.2.trans ((le_abs_self rhi).trans (le_add_of_nonneg_right zero_le_one)))
  have hc1 : CoefficientOn (axisCube z L) (fun _ ↦ (1 : ℝ)) :=
    ⟨aestronglyMeasurable_const, 1, 1, zero_lt_one,
      Filter.Eventually.of_forall fun _ ↦ ⟨le_rfl, le_rfl⟩⟩
  refine ⟨J ^ 2 * D / lo, by positivity, fun u ↦ ?_⟩
  have hnorm : eLpNorm u.toH1Function.toFun q.exponent
      ((weightedMeasure rho).restrict (axisCube z L)) ≤
        ENNReal.ofReal J * eLpNorm u.toH1Function.toFun q.exponent
          (volume.restrict (axisCube z L)) := by
    have hh := eLpNorm_mono_measure (p := q.exponent) u.toH1Function.toFun hmu
    rw [eLpNorm_smul_measure_of_ne_top q.lt_top.ne,
      smul_eq_mul, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.ofReal_rpow_of_pos hH] at hh
    exact hh
  have h1int : IntegrableOn
      (fun x ↦ (1 : ℝ) * vecDot (u.grad x) (u.grad x)) (axisCube z L) := by
    simpa only [vecDot_smul_left] using
      integrableOn_energy_pairing hc1 u.toH1Function.grad_memVectorL2
        u.toH1Function.grad_memVectorL2
  have hcint : IntegrableOn
      (fun x ↦ c x * vecDot (u.grad x) (u.grad x)) (axisCube z L) := by
    simpa only [vecDot_smul_left] using
      integrableOn_energy_pairing hc u.toH1Function.grad_memVectorL2
        u.toH1Function.grad_memVectorL2
  have henergy : lo * energy (fun _ ↦ (1 : ℝ)) (axisCube z L) u.toH1Function ≤
      energy c (axisCube z L) u.toH1Function := by
    rw [energy, energy, ← integral_const_mul]
    apply integral_mono_ae (h1int.const_mul lo) hcint
    filter_upwards [hcb] with x hx
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hx.1 (vecNormSq_nonneg (u.grad x))
  have hen : energy (fun _ ↦ (1 : ℝ)) (axisCube z L) u.toH1Function ≤
      energy c (axisCube z L) u.toH1Function / lo := by
    apply (le_div_iff₀ hlo).mpr
    simpa only [mul_comm] using henergy
  calc
    _ ≤ (ENNReal.ofReal J * eLpNorm u.toH1Function.toFun q.exponent
          (volume.restrict (axisCube z L))) ^ 2 := pow_le_pow_left₀ (zero_le _) hnorm 2
    _ = ENNReal.ofReal (J ^ 2) *
        eLpNorm u.toH1Function.toFun q.exponent (volume.restrict (axisCube z L)) ^ 2 := by
      rw [mul_pow, ← ENNReal.ofReal_pow hJ.le]
    _ ≤ ENNReal.ofReal (J ^ 2) * (ENNReal.ofReal D *
        ENNReal.ofReal (energy (fun _ ↦ 1) (axisCube z L) u.toH1Function)) :=
      mul_le_mul' le_rfl (hbound q hpq z L hL u)
    _ ≤ ENNReal.ofReal (J ^ 2) * (ENNReal.ofReal D *
        ENNReal.ofReal (energy c (axisCube z L) u.toH1Function / lo)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hen))
    _ = _ := by
      rw [← ENNReal.ofReal_mul hD.le, ← ENNReal.ofReal_mul (sq_nonneg J),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ J ^ 2 * D / lo)]
      congr 1
      ring

end SubdiffusiveProcess.Section10
