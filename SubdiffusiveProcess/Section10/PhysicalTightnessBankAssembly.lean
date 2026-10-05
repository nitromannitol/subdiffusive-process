module

public import SubdiffusiveProcess.Section10.PhysicalTightnessActualExitBank

@[expose] public section




open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section11
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness
open PhysicalLocalTransport

/-- Read the real Dirichlet energy from the literal lower-integral bound. -/
theorem energy_le_of_lintegral_le {d : ℕ} (a : Vec d → ℝ) (ha : ∀ x, 0 ≤ a x)
    (U : Set (Vec d)) (v : H1Function U) (D : ℝ) (hD : 0 ≤ D)
    (hbound : (∫⁻ x in U, ENNReal.ofReal (a x * vecDot (v.grad x) (v.grad x))) ≤
      ENNReal.ofReal D) : energy a U v ≤ D := by
  by_cases hi : Integrable (fun x => a x * vecDot (v.grad x) (v.grad x)) (volume.restrict U)
  · have heq : ENNReal.ofReal (energy a U v) =
        ∫⁻ x in U, ENNReal.ofReal (a x * vecDot (v.grad x) (v.grad x)) :=
      ofReal_integral_eq_lintegral_ofReal hi
        (ae_of_all _ fun x => mul_nonneg (ha x) (vecNormSq_nonneg _))
    exact (ENNReal.ofReal_le_ofReal_iff hD).mp (heq.trans_le hbound)
  · simpa only [energy, integral_undef hi] using hD

/-- The moment-two cost of one constant controlling both actual analytic
clauses is `2*D^2*Ccut+2*Cmoser`. The inputs remain analytic propositions,
and the source application supplies them from the fixed static theorem. -/
theorem local_analytic_bank_of_cutoff_and_moser {d : ℕ} (M : GMCModel d)
    (D Ccut Cmoser : ℝ) (hD : 0 ≤ D) (hCcut : 0 ≤ Ccut) (hCmoser : 0 ≤ Cmoser)
    (hcut : ∀ (L : WithTop ℕ) (m : ℕ) (z : Vec d),
      ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
        (∫⁻ omega, ENNReal.ofReal (K omega ^ (2 : ℝ))
          ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤ ENNReal.ofReal Ccut ∧
        ∀ᵐ omega ∂(PhysicalAttachment.physicalLaw M).toMeasure,
          ∃ chi : H10Function (Metric.ball (0 : Vec d) (1 / 2)),
            (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
            (∀ x ∈ Metric.ball (0 : Vec d) (1 / 6), chi.toFun x = 1) ∧
            energy (localCoefficient M L m z omega) (Metric.ball (0 : Vec d) (1 / 2))
              chi.toH1Function ≤ D * K omega)
    (hmoser : ∀ (L : WithTop ℕ) (m : ℕ) (z : Vec d),
      ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
        (∫⁻ omega, ENNReal.ofReal (K omega ^ (2 : ℝ))
          ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤ ENNReal.ofReal Cmoser ∧
        ∀ᵐ omega ∂(PhysicalAttachment.physicalLaw M).toMeasure,
          ∀ w : H1Function (Metric.ball (0 : Vec d) (1 / 6)),
            (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Vec d) (1 / 6)), 0 ≤ w.toFun x) →
            (∃ Mw : ℝ, ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Vec d) (1 / 6)), w.toFun x ≤ Mw) →
            IsWeakSubSolutionOn (localCoefficient M L m z omega) (Metric.ball (0 : Vec d) (1 / 6)) w →
            ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Vec d) (1 / 18)),
              ENNReal.ofReal (w.toFun x) ≤ ENNReal.ofReal (K omega) *
                (∫⁻ y in Metric.ball (0 : Vec d) (1 / 6),
                  ENNReal.ofReal (w.toFun y ^ 2 * localSpeed M L m z omega y)) ^ (1 / 2 : ℝ)) :
    ∀ (L : WithTop ℕ) (m : ℕ) (z : Vec d),
      ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
        (∫⁻ omega, ENNReal.ofReal (K omega ^ (2 : ℝ))
          ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤ ENNReal.ofReal (2 * D ^ 2 * Ccut + 2 * Cmoser) ∧
        ∀ᵐ omega ∂(PhysicalAttachment.physicalLaw M).toMeasure,
          LocalExitCertificate (localCoefficient M L m z omega) (localSpeed M L m z omega) (K omega) := by
  intro L m z
  obtain ⟨Kc, hKc, hKcone, hKcint, hKcbound⟩ := hcut L m z
  obtain ⟨Km, hKm, hKmone, hKmint, hKmbound⟩ := hmoser L m z
  let K : AnchoredC11Sample d → ℝ := fun omega => D * Kc omega + Km omega
  have hKc0 : ∀ omega, 0 ≤ Kc omega := fun omega => zero_le_one.trans (hKcone omega)
  have hKm0 : ∀ omega, 0 ≤ Km omega := fun omega => zero_le_one.trans (hKmone omega)
  have hKcone' : ∀ omega, D * Kc omega ≤ K omega := fun omega =>
    le_add_of_nonneg_right (hKm0 omega)
  have hKmone' : ∀ omega, Km omega ≤ K omega := fun omega =>
    le_add_of_nonneg_left (mul_nonneg hD (hKc0 omega))
  refine ⟨K, (measurable_const.mul hKc).add hKm,
    fun omega => (hKmone omega).trans (hKmone' omega), ?_, ?_⟩
  · have hpoint : ∀ omega, ENNReal.ofReal (K omega ^ (2 : ℝ)) ≤
        ENNReal.ofReal (2 * D ^ 2) * ENNReal.ofReal (Kc omega ^ (2 : ℝ)) +
          ENNReal.ofReal 2 * ENNReal.ofReal (Km omega ^ (2 : ℝ)) := by
      intro omega
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * D ^ 2),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_add
          (mul_nonneg (by positivity) (Real.rpow_nonneg (hKc0 omega) _))
          (mul_nonneg (by norm_num) (Real.rpow_nonneg (hKm0 omega) _))]
      apply ENNReal.ofReal_le_ofReal
      simp only [Real.rpow_two, K]
      nlinarith only [sq_nonneg (D * Kc omega - Km omega)]
    have hleft : Measurable (fun omega =>
        ENNReal.ofReal (2 * D ^ 2) * ENNReal.ofReal (Kc omega ^ (2 : ℝ))) :=
      measurable_const.mul (ENNReal.measurable_ofReal.comp (hKc.pow_const (2 : ℝ)))
    calc
      _ ≤ ∫⁻ omega, ENNReal.ofReal (2 * D ^ 2) * ENNReal.ofReal (Kc omega ^ (2 : ℝ)) +
          ENNReal.ofReal 2 * ENNReal.ofReal (Km omega ^ (2 : ℝ))
            ∂(PhysicalAttachment.physicalLaw M).toMeasure := lintegral_mono hpoint
      _ = ENNReal.ofReal (2 * D ^ 2) *
          (∫⁻ omega, ENNReal.ofReal (Kc omega ^ (2 : ℝ)) ∂(PhysicalAttachment.physicalLaw M).toMeasure) +
          ENNReal.ofReal 2 *
          (∫⁻ omega, ENNReal.ofReal (Km omega ^ (2 : ℝ)) ∂(PhysicalAttachment.physicalLaw M).toMeasure) := by
        rw [lintegral_add_left hleft,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (2 * D ^ 2) * ENNReal.ofReal Ccut +
          ENNReal.ofReal 2 * ENNReal.ofReal Cmoser := add_le_add
            (mul_le_mul' le_rfl hKcint) (mul_le_mul' le_rfl hKmint)
      _ = ENNReal.ofReal (2 * D ^ 2 * Ccut + 2 * Cmoser) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * D ^ 2),
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
  · filter_upwards [hKcbound, hKmbound] with omega hc hm
    obtain ⟨chi, hchi01, hchi1, henergy⟩ := hc
    refine ⟨chi, hchi01, hchi1, henergy.trans (hKcone' omega), ?_⟩
    intro w hw0 hwM hsub
    filter_upwards [hm w hw0 hwM hsub] with x hx
    exact hx.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (hKmone' omega)) le_rfl)

end SubdiffusiveProcess.Section10.PhysicalTightness
