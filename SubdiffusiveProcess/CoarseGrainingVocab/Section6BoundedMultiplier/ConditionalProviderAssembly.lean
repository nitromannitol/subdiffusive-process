module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.GlobalRepresentative

@[expose] public section

/-!
# Pathwise interfaces for the bounded-multiplier provider

The Campanato event supplies the final target-local oscillation row directly.
No fixed unit-cell mean is required to decay with the target depth.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model

noncomputable section

private abbrev Sample (d : ℕ) := PotentialSample d

/-- Frozen-shaped pathwise conclusion in the regime `j ≤ m`. -/
def BoundedMultiplierPathwiseEstimate {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) (j : ℕ)
    (B' : Set (Vec d)) (epsilon C c : ℝ) (omega : Sample d) : Prop :=
  ∀ theta : Vec d → ℝ,
    ContinuousOn theta (translatedCube d m z) →
    (∀ x ∈ translatedCube d m z, 0 < theta x) →
    (∃ b > 0, ∀ x ∈ translatedCube d m z,
      |b⁻¹ * theta x - 1| ≤ epsilon) →
    ∀ h : H1Function (translatedCube d m z),
      IsWeaklyHarmonicOn
          (fun x ↦ aCutoff M L omega x * theta x)
          (translatedCube d m z) h →
        ∃ hRep : Vec d → ℝ,
          ContinuousOn hRep (translatedCube d m z) ∧
          hRep =ᵐ[volume.restrict (translatedCube d m z)] h.toFun ∧
          oscillationOn B' hRep ≤
            C * (3 : ℝ) ^ (-c * (j : ℝ)) *
              oscillationOn {x : Vec d | ‖x - z‖ ≤
                3 * (3 : ℝ) ^ m / 8} hRep ∧
          sSup {r : ℝ | ∃ x ∈ B',
            r = |hRep x - averageOn (translatedCube d m z) hRep|} ≤
              C * normalizedL2On (translatedCube d m z)
                (fun x ↦ hRep x -
                  averageOn (translatedCube d m z) hRep)

/-- Split pathwise conclusion for `m < j`.  The first factor is the sub-unit
contraction below scale one and the second is the scale-one Campanato price. -/
def BoundedMultiplierBelowScalePathwiseEstimate {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) (j : ℕ)
    (B' : Set (Vec d)) (epsilon C c : ℝ) (omega : Sample d) : Prop :=
  ∀ theta : Vec d → ℝ,
    ContinuousOn theta (translatedCube d m z) →
    (∀ x ∈ translatedCube d m z, 0 < theta x) →
    (∃ b > 0, ∀ x ∈ translatedCube d m z,
      |b⁻¹ * theta x - 1| ≤ epsilon) →
    ∀ h : H1Function (translatedCube d m z),
      IsWeaklyHarmonicOn
          (fun x ↦ aCutoff M L omega x * theta x)
          (translatedCube d m z) h →
        ∃ hRep : Vec d → ℝ,
          ContinuousOn hRep (translatedCube d m z) ∧
          hRep =ᵐ[volume.restrict (translatedCube d m z)] h.toFun ∧
          oscillationOn B' hRep ≤
            C * (3 : ℝ) ^
                (-(c * ((((j : ℤ) - m : ℤ) : ℝ)))) *
              ((3 : ℝ) ^ (-(c * (m : ℝ))) *
                oscillationOn {x : Vec d | ‖x - z‖ ≤
                  3 * (3 : ℝ) ^ m / 8} hRep) ∧
          sSup {r : ℝ | ∃ x ∈ B',
            r = |hRep x - averageOn (translatedCube d m z) hRep|} ≤
              C * normalizedL2On (translatedCube d m z)
                (fun x ↦ hRep x -
                  averageOn (translatedCube d m z) hRep)

/-- The split below-scale oscillation factors multiply to `3^(-c*j)`. -/
theorem boundedMultiplierPathwiseEstimate_of_belowScale
    {d : ℕ} (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) (j : ℕ)
    (B' : Set (Vec d)) (epsilon C c : ℝ) (omega : Sample d)
    (hbelow : BoundedMultiplierBelowScalePathwiseEstimate
      M L m z j B' epsilon C c omega) :
    BoundedMultiplierPathwiseEstimate
      M L m z j B' epsilon C c omega := by
  intro theta hthetaCont hthetaPos hthetaClose h hharm
  obtain ⟨hRep, hRepCont, hRepAE, hosc, hsup⟩ :=
    hbelow theta hthetaCont hthetaPos hthetaClose h hharm
  refine ⟨hRep, hRepCont, hRepAE, ?_, hsup⟩
  have hexponent :
      -(c * ((((j : ℤ) - m : ℤ) : ℝ))) + -(c * (m : ℝ)) =
        -(c * (j : ℝ)) := by
    norm_num
    ring
  calc
    oscillationOn B' hRep ≤
        C * (3 : ℝ) ^
            (-(c * ((((j : ℤ) - m : ℤ) : ℝ)))) *
          ((3 : ℝ) ^ (-(c * (m : ℝ))) *
            oscillationOn {x : Vec d | ‖x - z‖ ≤
              3 * (3 : ℝ) ^ m / 8} hRep) := hosc
    _ = C *
          ((3 : ℝ) ^ (-(c * ((((j : ℤ) - m : ℤ) : ℝ)))) *
            (3 : ℝ) ^ (-(c * (m : ℝ))) *
          oscillationOn {x : Vec d | ‖x - z‖ ≤
            3 * (3 : ℝ) ^ m / 8} hRep) := by ring
    _ = C * (3 : ℝ) ^ (-c * (j : ℝ)) *
          oscillationOn {x : Vec d | ‖x - z‖ ≤
            3 * (3 : ℝ) ^ m / 8} hRep := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), hexponent]
      simp only [neg_mul]
      ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
