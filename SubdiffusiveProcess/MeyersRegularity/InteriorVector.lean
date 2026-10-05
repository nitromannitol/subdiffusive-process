module

public import SubdiffusiveProcess.MeyersRegularity.LocalStep
public import SubdiffusiveProcess.MeyersRegularity.SpatialIteration

@[expose] public section

/-! Interior Meyers regularity: InteriorVector. -/

open MeasureTheory Filter Set TopologicalSpace
open Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

theorem exists_interior_vector_estimate (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ epsilon C : ℝ, 0 < epsilon ∧ epsilon ≤ 1/2 ∧ 0 < C ∧
      ∀ (a : Vec d → ℝ) (F : Vec d → Vec d),
        AEMeasurable a (volume.restrict (unitBall d (3/2))) →
        (∀ᵐ x ∂volume.restrict (unitBall d (3/2)), |a x-1| ≤ epsilon) →
        MemLp (hilbertifyVecField F) (ENNReal.ofReal p)
          (volume.restrict (unitBall d (3/2))) →
        ∀ u : H1Function (unitBall d (3/2)), VectorEquation a F u →
          MemLp (gradientField u) (ENNReal.ofReal p) (volume.restrict (unitBall d 1)) ∧
            (eLpNorm (gradientField u) (ENNReal.ofReal p)
              (volume.restrict (unitBall d 1))).toReal ≤ C * vectorDataSize p u F := by
  let μO := volume.restrict (unitBall d (3/2))
  have hsub : unitBall d 1 ⊆ unitBall d (3/2) := Meyers.eBall_mono 0 (by norm_num) (by norm_num)
  have hmeasure : volume.restrict (unitBall d 1) ≤ μO := Measure.restrict_mono hsub le_rfl
  by_cases hp2 : p = 2
  · subst p
    refine ⟨1/2, 1, by norm_num, le_rfl, by norm_num, ?_⟩
    intro a F ha hclose hF u heq
    have hf := gradientField_memLp_two u
    have hfr := hf.mono_measure hmeasure
    norm_num only [ENNReal.ofReal_ofNat]
    refine ⟨hfr, ?_⟩
    have hn := ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure (gradientField u) hmeasure)
    simp only [one_mul, vectorDataSize]
    exact hn.trans (le_add_of_nonneg_right ENNReal.toReal_nonneg)
  · have hpgt : 2 < p := lt_of_le_of_ne hp (Ne.symm hp2)
    have hp0 : 0 < p := by linarith only [hpgt]
    let β := spatialPower d p
    have hβ : 0 ≤ β := div_nonneg (mul_nonneg (Nat.cast_nonneg d) (sub_nonneg.mpr hp)) (by norm_num)
    let θ := (4*(2 : ℝ)^β)⁻¹
    have hθ : 0 < θ := by dsimp only [θ]; positivity
    have hθsmall : θ*(2 : ℝ)^β ≤ 1/2 := by
      dsimp only [θ]
      have hpow : (2 : ℝ)^β ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
      field_simp
      norm_num
    obtain ⟨epsilon, A, hepsilon, hepsilonhalf, hA, hlocal⟩ :=
      exists_local_truncated_estimate d hd p θ hpgt hθ
    let c := 2*(4 : ℝ)^β*A
    have hc : 0 < c := by dsimp only [c]; positivity
    let C := c^(p⁻¹)
    have hC : 0 < C := Real.rpow_pos_of_pos hc _
    have hCpow : C^p = c := Real.rpow_inv_rpow hc.le hp0.ne'
    refine ⟨epsilon, C, hepsilon, hepsilonhalf, hC, ?_⟩
    intro a F ha hclose hF u heq
    let D := vectorDataSize p u F
    have hD : 0 ≤ D := by dsimp only [D, vectorDataSize]; positivity
    have hf := gradientField_memLp_two u
    have hfr := hf.mono_measure hmeasure
    apply memLp_and_norm_le_of_truncatedMoment_le hfr hpgt (mul_nonneg hC.le hD)
    intro T hT
    let X : ℝ → ℝ := fun r => (truncatedMoment (volume.restrict (unitBall d r)) (gradientField u) p T).toReal
    have hX : ∀ r ∈ Icc (1 : ℝ) (3/2), 0 ≤ X r ∧
        X r ≤ (truncatedMoment μO (gradientField u) p T).toReal := by
      intro r hr
      refine ⟨ENNReal.toReal_nonneg, ?_⟩
      have hsubr : unitBall d r ⊆ unitBall d (3/2) := Meyers.eBall_mono 0 (by linarith only [hr.1]) hr.2
      exact ENNReal.toReal_mono (truncatedMoment_ne_top hf hpgt hT)
        (truncatedMoment_mono_measure (Measure.restrict_mono hsubr le_rfl) _ _ _)
    have hstep : ∀ r s : ℝ, 1 ≤ r → r < s → s ≤ 3/2 →
        X r ≤ θ*X s+(A*D^p)*(s-r)^(-β) := by
      intro r s hr hrs hs
      have hh := hlocal a F ha hclose hF u heq r s T hr hrs hs hT
      change X r ≤ θ*X s+A*(s-r)^(-β)*D^p at hh
      convert hh using 1 ; ring
    have hh := spatial_iteration hβ (mul_nonneg hA.le (Real.rpow_nonneg hD _))
      (ENNReal.toReal_nonneg : 0 ≤ (truncatedMoment μO (gradientField u) p T).toReal)
      hθ.le hθsmall hX hstep
    have hpower : (C*D)^p = c*D^p := by rw [Real.mul_rpow hC.le hD, hCpow]
    change X 1 ≤ (C*D)^p
    rw [hpower]
    simpa only [c, mul_assoc] using hh


end SubdiffusiveProcess.MeyersRegularity
