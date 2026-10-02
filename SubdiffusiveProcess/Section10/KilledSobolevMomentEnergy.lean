import SubdiffusiveProcess.Section10.KilledSobolevMoment
import SubdiffusiveProcess.Section10.KilledSobolevEnergy

/-! A deterministic Sobolev certificate on the actual native killed domain,
and its transfer to a moment bank. The conditional adapter is an internal
library theorem; model suppliers must discharge its analytic premise. -/

open MeasureTheory Homogenization SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- All native zero-boundary tests, with both literal lower and real energies. -/
def KilledSobolevBound {d : ℕ} (U : Set (SpatialCoordinates d))
    (b A : SpatialCoordinates d → ℝ) (k : ℝ) : Prop :=
  ∀ v : H10Function U,
    MemLp v.toFun (ENNReal.ofReal (killedSobolevExponent d)) ((weightedMeasure b).restrict U) ∧
    eLpNorm v.toFun (ENNReal.ofReal (killedSobolevExponent d))
        ((weightedMeasure b).restrict U) ^ 2 ≤
      ENNReal.ofReal k * killedCoefficientEnergy A v.toH1Function ∧
    lpSq b U (killedSobolevExponent d) v.toFun ≤
      ENNReal.ofReal (k * energy A U v.toH1Function) ∧
    (eLpNorm v.toFun (ENNReal.ofReal (killedSobolevExponent d))
        ((weightedMeasure b).restrict U)).toReal ^ 2 ≤
      k * energy A U v.toH1Function

lemma killedSobolevBound_of_lower {d : ℕ} {U : Set (SpatialCoordinates d)}
    {b A : SpatialCoordinates d → ℝ} {k : ℝ} (hA : CoefficientOn U A) (hk : 0 ≤ k)
    (h : ∀ v : H10Function U,
      eLpNorm v.toFun (ENNReal.ofReal (killedSobolevExponent d))
          ((weightedMeasure b).restrict U) ^ 2 ≤
        ENNReal.ofReal k * killedCoefficientEnergy A v.toH1Function) :
    KilledSobolevBound U b A k := by
  intro v
  have hr := killed_sobolev_real_of_bound (weightedMeasure b)
    (withDensity_absolutelyContinuous _ _) hA v hk (h v)
  exact ⟨hr.1, h v, killed_lpSq_le_of_bound hA v hk (h v), hr.2⟩

lemma KilledSobolevBound.mono {d : ℕ} {U : Set (SpatialCoordinates d)}
    {b A : SpatialCoordinates d → ℝ} {k k' : ℝ}
    (h : KilledSobolevBound U b A k) (hA : CoefficientOn U A) (hkk : k ≤ k') :
    KilledSobolevBound U b A k' := by
  intro v
  have hv := h v
  have he := killed_energy_nonneg hA v.toH1Function
  exact ⟨hv.1, hv.2.1.trans (mul_le_mul_left
      (ENNReal.ofReal_le_ofReal hkk) _),
    hv.2.2.1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hkk he)),
    hv.2.2.2.trans (mul_le_mul_of_nonneg_right hkk he)⟩

/-- Generic deterministic-to-moment-bank adapter. The law, coefficients,
native domain, and real energy are unchanged. -/
theorem killedSobolev_moment_bank_of_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (U : Set (SpatialCoordinates d))
    (b A : Ω → SpatialCoordinates d → ℝ) (K : Ω → ℝ) (D C q : ℝ)
    (hK : Measurable K) (hKone : ∀ ω, 1 ≤ K ω) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hmoment : (∫⁻ ω, ENNReal.ofReal (K ω ^ killedSobolevMomentOrder q) ∂P) ≤
      ENNReal.ofReal C)
    (hA : ∀ ω, CoefficientOn U (A ω))
    (hbound : ∀ᵐ ω ∂P, KilledSobolevBound U (b ω) (A ω) (D * K ω ^ 2)) :
    ∃ Ksob : Ω → ℝ, Measurable Ksob ∧ (∀ ω, 1 ≤ Ksob ω) ∧
      (∫⁻ ω, ENNReal.ofReal (Ksob ω ^ q) ∂P) ≤
        ENNReal.ofReal (if 0 < q then 1 + D ^ q * C else 1) ∧
      (∀ ω, Ksob ω = max 1 (D * K ω ^ 2)) ∧
      ∀ᵐ ω ∂P, KilledSobolevBound U (b ω) (A ω) (Ksob ω) := by
  refine ⟨fun ω => killedSobolevBankConstant D (K ω),
    measurable_killedSobolevBankConstant hK D,
    fun ω => killedSobolevBankConstant_ge_one D (K ω),
    killedSobolevBankConstant_moment P hK hKone hD hC hmoment, fun _ => rfl, ?_⟩
  filter_upwards [hbound] with ω hω
  exact hω.mono (hA ω) (mul_sq_le_killedSobolevBankConstant D (K ω))

end SubdiffusiveProcess.Section10
