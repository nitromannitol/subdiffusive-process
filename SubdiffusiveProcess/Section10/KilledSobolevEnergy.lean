module

public import SubdiffusiveProcess.Section10.KilledSobolev
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledStrongContinuity

@[expose] public section

/-! Real-energy and weighted-Lp consumers of the deterministic killed estimate.
These use the actual `Section9SupportInput.energy` and `lpSq` definitions. -/

open MeasureTheory Set Homogenization SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- Local coefficient bounds make every native H1 energy integrable and nonnegative. -/
theorem killedCoefficientEnergy_eq_ofReal_energy {d : ℕ}
    {U : Set (SpatialCoordinates d)} {A : SpatialCoordinates d → ℝ}
    (hA : CoefficientOn U A) (v : H1Function U) :
    killedCoefficientEnergy A v = ENNReal.ofReal (energy A U v) := by
  have hint : IntegrableOn (fun x => A x * vecDot (v.grad x) (v.grad x)) U := by
    simpa only [vecDot_smul_left] using
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledStrongContinuity.integrableOn_energy_pairing
        hA v.grad_memVectorL2 v.grad_memVectorL2
  obtain ⟨lo, hi, hlo, hb⟩ := hA.2
  have hnn : 0 ≤ᵐ[volume.restrict U] fun x => A x * vecDot (v.grad x) (v.grad x) := by
    filter_upwards [hb] with x hx
    exact mul_nonneg (hlo.le.trans hx.1) (vecNormSq_nonneg (v.grad x))
  exact (ofReal_integral_eq_lintegral_ofReal hint hnn).symm

lemma killed_energy_nonneg {d : ℕ} {U : Set (SpatialCoordinates d)}
    {A : SpatialCoordinates d → ℝ} (hA : CoefficientOn U A) (v : H1Function U) :
    0 ≤ energy A U v := by
  obtain ⟨lo, hi, hlo, hb⟩ := hA.2
  apply integral_nonneg_of_ae
  filter_upwards [hb] with x hx
  exact mul_nonneg (hlo.le.trans hx.1) (vecNormSq_nonneg (v.grad x))

/-- A finite extended estimate yields genuine weighted MemLp and the real
Dirichlet-energy estimate, so a real integral cannot silently default to zero. -/
theorem killed_sobolev_real_of_bound {d : ℕ}
    {U : Set (SpatialCoordinates d)} (μ : Measure (SpatialCoordinates d))
    (hμ : μ ≪ volume) {A : SpatialCoordinates d → ℝ} (hA : CoefficientOn U A)
    (v : H10Function U) {p K : ℝ} (hK : 0 ≤ K)
    (hbound : eLpNorm v.toFun (ENNReal.ofReal p) (μ.restrict U) ^ 2 ≤
      ENNReal.ofReal K * killedCoefficientEnergy A v.toH1Function) :
    MemLp v.toFun (ENNReal.ofReal p) (μ.restrict U) ∧
      (eLpNorm v.toFun (ENNReal.ofReal p) (μ.restrict U)).toReal ^ 2 ≤
        K * energy A U v.toH1Function := by
  have hE := killedCoefficientEnergy_eq_ofReal_energy hA v.toH1Function
  rw [hE, ← ENNReal.ofReal_mul hK] at hbound
  have hpow : eLpNorm v.toFun (ENNReal.ofReal p) (μ.restrict U) ^ 2 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hnorm : eLpNorm v.toFun (ENNReal.ofReal p) (μ.restrict U) ≠ ⊤ := by
    rcases ENNReal.pow_ne_top_iff.mp hpow with h | h
    · exact h
    · norm_num at h
  refine ⟨hnorm.lt_top, ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal
    (mul_nonneg hK (killed_energy_nonneg hA v.toH1Function))] at hreal
  exact hreal

/-- Exact `lpSq` vocabulary consumed by weighted torsion and killed Nash. -/
theorem killed_lpSq_le_of_bound {d : ℕ}
    {U : Set (SpatialCoordinates d)} {b A : SpatialCoordinates d → ℝ}
    (hA : CoefficientOn U A) (v : H10Function U) {p K : ℝ} (hK : 0 ≤ K)
    (hbound : eLpNorm v.toFun (ENNReal.ofReal p) ((weightedMeasure b).restrict U) ^ 2 ≤
      ENNReal.ofReal K * killedCoefficientEnergy A v.toH1Function) :
    lpSq b U p v.toFun ≤ ENNReal.ofReal (K * energy A U v.toH1Function) := by
  rw [lpSq]
  exact ((ENNReal.pow_le_pow_left (n := 2) (SubdiffusiveProcess.RawLp.eLpNorm_le_guarded _ _ _)).trans hbound).trans_eq (by
    rw [killedCoefficientEnergy_eq_ofReal_energy hA, ← ENNReal.ofReal_mul hK])



end SubdiffusiveProcess.Section10
