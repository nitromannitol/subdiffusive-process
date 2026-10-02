import SubdiffusiveProcess.Static.HarmonicCellDerivativeMoment
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum

/-! # Uniform physical-cell banks with a selectable geometric moment margin -/

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The microscopic derivative bank on the unit cover of a larger cell. -/
def harmonicMicroscopicDerivativeBank {d : ℕ} (_M : GMCModel d) (j k : ℕ)
    (omega : PotentialSample d) : ℝ :=
  (shellCoverShifts d ((k + 1 : ℕ) : ℤ)).sup'
    (shellCoverShifts_nonempty d ((k + 1 : ℕ) : ℤ))
    (fun p => harmonicMicroscopicDerivativeEnvelope j (physicalShellCoverCenter 0 p) omega)

theorem one_le_harmonicMicroscopicDerivativeBank {d : ℕ} (M : GMCModel d) (j k : ℕ)
    (omega : PotentialSample d) : 1 ≤ harmonicMicroscopicDerivativeBank M j k omega := by
  obtain ⟨p, hp⟩ := shellCoverShifts_nonempty d ((k + 1 : ℕ) : ℤ)
  exact (one_le_harmonicMicroscopicDerivativeEnvelope j (physicalShellCoverCenter 0 p) omega).trans
    (Finset.le_sup' (fun p => harmonicMicroscopicDerivativeEnvelope j (physicalShellCoverCenter 0 p) omega) hp)

theorem measurable_harmonicMicroscopicDerivativeBank {d : ℕ} (M : GMCModel d) (j k : ℕ) :
    Measurable (harmonicMicroscopicDerivativeBank M j k) := by
  let V := (shellCoverShifts d ((k + 1 : ℕ) : ℤ)).sup'
    (shellCoverShifts_nonempty d ((k + 1 : ℕ) : ℤ))
    (fun p => harmonicMicroscopicDerivativeEnvelope j (physicalShellCoverCenter 0 p))
  have hV : Measurable V := Finset.measurable_sup' (shellCoverShifts_nonempty _ _)
    (fun p _ => measurable_harmonicMicroscopicDerivativeEnvelope j (physicalShellCoverCenter 0 p))
  have heq : V = harmonicMicroscopicDerivativeBank M j k := by
    funext omega
    exact Finset.sup'_apply _ _ omega
  rwa [← heq]

/-- High internal moments absorb the covering cardinality. The resulting
derivative price has any positive geometric exponent, uniformly for `j≤k`. -/
theorem exists_harmonicMicroscopicDerivativeBank_moment_bound (d : ℕ) (q eta : ℝ)
    (hq : 1 ≤ q) (heta : 0 < eta) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 → ∀ j k : ℕ, j ≤ k →
        eLpNorm (harmonicMicroscopicDerivativeBank M j k) (ENNReal.ofReal q) M.P.toMeasure ≤
          ENNReal.ofReal (C * (3 : ℝ) ^ (eta * (k : ℝ))) := by
  let S := max (q + 1) (2 * (d : ℝ) / eta + 1)
  have hqS : q ≤ S := (by linarith : q ≤ q + 1).trans (le_max_left _ _)
  have hS1 : 1 < S := (by linarith : 1 < q + 1).trans_le (le_max_left _ _)
  have hS0 : 0 < S := zero_lt_one.trans hS1
  have hdim : (d : ℝ) / S ≤ eta / 2 := by
    have hlow : 2 * (d : ℝ) / eta ≤ S :=
      (by linarith : 2 * (d : ℝ) / eta ≤ 2 * (d : ℝ) / eta + 1).trans (le_max_right _ _)
    have hlow' := (div_le_iff₀ heta).mp hlow
    exact (div_le_iff₀ hS0).mpr (by nlinarith)
  obtain ⟨delta0, C0, hdelta, hC0, hcell⟩ :=
    exists_harmonicMicroscopicDerivativeEnvelope_geometric_moment_bound d S (eta / 2) hS1.le (by positivity)
  let C := C0 * (3 : ℝ) ^ (3 * eta / 2)
  refine ⟨delta0, C, hdelta, by dsimp only [C]; positivity, ?_⟩
  intro M hM j k hjk
  have hhigh := SubdiffusiveProcess.eLpNorm_sup'_le_of_le M.P.toMeasure
    (shellCoverShifts d ((k + 1 : ℕ) : ℤ)) (shellCoverShifts_nonempty _ _)
    (fun p => harmonicMicroscopicDerivativeEnvelope j (physicalShellCoverCenter 0 p))
    (fun p omega => zero_le_one.trans (one_le_harmonicMicroscopicDerivativeEnvelope j (physicalShellCoverCenter 0 p) omega))
    (fun p _ => (measurable_harmonicMicroscopicDerivativeEnvelope j (physicalShellCoverCenter 0 p)).aestronglyMeasurable)
    (C0 * (3 : ℝ) ^ ((eta / 2) * (j : ℝ))) S hS1 (fun p _ => hcell M hM j p)
  have hcard : ((shellCoverShifts d ((k + 1 : ℕ) : ℤ)).card : ℝ) ^ (1 / S) ≤
      (3 : ℝ) ^ ((eta / 2) * ((k : ℝ) + 3)) := by
    have hcard' := card_shellCoverShifts_subunit_le d (k + 1)
    have hcardR : ((shellCoverShifts d ((k + 1 : ℕ) : ℤ)).card : ℝ) ≤
        (3 : ℝ) ^ ((k + 3) * d) := by exact_mod_cast hcard'
    calc
      _ ≤ ((3 : ℝ) ^ ((k + 3) * d)) ^ (1 / S) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hcardR (by positivity)
      _ = (3 : ℝ) ^ (((k : ℝ) + 3) * ((d : ℝ) / S)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1
        push_cast
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by nlinarith only [mul_le_mul_of_nonneg_left hdim (by positivity : 0 ≤ (k : ℝ) + 3)])
  have hnorm := (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hqS)
    (measurable_harmonicMicroscopicDerivativeBank M j k).aestronglyMeasurable).trans hhigh
  refine hnorm.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [max_eq_left (by positivity)]
  have hjkR : (j : ℝ) ≤ k := by exact_mod_cast hjk
  calc
    _ ≤ (3 : ℝ) ^ ((eta / 2) * ((k : ℝ) + 3)) *
        (C0 * (3 : ℝ) ^ ((eta / 2) * (k : ℝ))) := by
      gcongr <;> norm_num
    _ = _ := by
      have hid : (3 : ℝ) ^ ((eta / 2) * ((k : ℝ) + 3)) *
          (3 : ℝ) ^ ((eta / 2) * (k : ℝ)) =
          (3 : ℝ) ^ (3 * eta / 2) * (3 : ℝ) ^ (eta * (k : ℝ)) := by
        rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
        congr 1
        ring
      calc
        _ = C0 * ((3 : ℝ) ^ ((eta / 2) * ((k : ℝ) + 3)) *
            (3 : ℝ) ^ ((eta / 2) * (k : ℝ))) := by ring
        _ = _ := by rw [hid]; dsimp only [C]; ring

end SubdiffusiveProcess.Static
