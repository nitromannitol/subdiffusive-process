import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.VariationalLevelBound

/-! The unit-forcing specialization of the existing scalar iteration.
No new iteration or integrability promise for the unknown solution is used. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal
namespace SubdiffusiveProcess.Section10

/-- The source's constant depends only on p. -/
def torsionConstant (p : ℝ) : ℝ := stampacchiaConstant p

lemma torsionConstant_pos (p : ℝ) : 0 < torsionConstant p := stampacchiaConstant_pos p

/-- Positive-level estimates with unit forcing give exactly the torsion mass power. -/
theorem torsion_ae_le_of_level_estimates {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {p Ksob : ℝ}
    (hp : 2 < p) (hKsob : 0 < Ksob) (hM : 0 < (μ Set.univ).toReal)
    {u : X → ℝ} (hu : MemLp u 2 μ)
    (hLevel : ∀ h : ℝ, 0 ≤ h →
      (eLpNorm (fun x => max (u x - h) 0) (ENNReal.ofReal p) μ) ^ 2 ≤
      ENNReal.ofReal Ksob * ∫⁻ x, ENNReal.ofReal (max (u x - h) 0) ∂μ) :
    ∀ᵐ x ∂μ, u x ≤ torsionConstant p * Ksob * (μ Set.univ).toReal ^ (1 - 2 / p) := by
  let q : ℝ := 2 / (1 - 2 / p)
  obtain ⟨_, hq2, _, _⟩ := stampacchia_exponents hp
  have hq0 : 0 < q := by dsimp only [q]; linarith
  have hf : MemLp (fun _ : X => (1 : ℝ)) (ENNReal.ofReal q) μ := memLp_const 1
  have hN : (eLpNorm (fun _ : X => (1 : ℝ)) (ENNReal.ofReal q) μ).toReal =
      (μ Set.univ).toReal ^ (1 / q) := by
    rw [eLpNorm_const' 1 (ne_of_gt (ENNReal.ofReal_pos.mpr hq0)) ENNReal.ofReal_ne_top]
    simp only [enorm_one, one_mul, ENNReal.toReal_rpow, ENNReal.toReal_ofReal hq0.le]
  have hLevel' : ∀ h : ℝ, 0 ≤ h →
      (eLpNorm (fun x => max (u x - h) 0) (ENNReal.ofReal p) μ) ^ 2 ≤
      ENNReal.ofReal Ksob * ∫⁻ x, ENNReal.ofReal (|(1 : ℝ)| * max (u x - h) 0) ∂μ := by
    simpa only [abs_one, one_mul] using hLevel
  have h := variational_ae_le_of_level_estimates μ hp hKsob hM hu hf hLevel'
  have hq : 1 / q + 1 / q = 1 - 2 / p := by dsimp only [q]; field_simp; ring
  have hc : torsionConstant p * Ksob * (μ Set.univ).toReal ^ (1 / q) *
      (μ Set.univ).toReal ^ (1 / q) =
      torsionConstant p * Ksob * (μ Set.univ).toReal ^ (1 - 2 / p) := by
    rw [mul_assoc, ← Real.rpow_add hM, hq]
  change ∀ᵐ x ∂μ, u x ≤ torsionConstant p * Ksob * (μ Set.univ).toReal ^ (1 / q) *
    (eLpNorm (fun _ : X => (1 : ℝ)) (ENNReal.ofReal q) μ).toReal at h
  simpa only [hN, hc] using h

end SubdiffusiveProcess.Section10
