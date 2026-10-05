module

public import SubdiffusiveProcess.Static.HarmonicCellCoefficientMoment

@[expose] public section

/-! # Uniform physical-cell banks with a selectable geometric moment margin -/

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open _root_.SubdiffusiveProcess.Model
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The microscopic coefficient bank on the unit cover of a larger cell. -/
def harmonicMicroscopicCoefficientBank {d : ℕ} (M : GMCModel d) (j k : ℕ)
    (omega : PotentialSample d) : ℝ :=
  (shellCoverShifts d ((k + 1 : ℕ) : ℤ)).sup'
    (shellCoverShifts_nonempty d ((k + 1 : ℕ) : ℤ))
    (fun p => harmonicMicroscopicCellEnvelope M j p omega)

theorem one_le_harmonicMicroscopicCoefficientBank {d : ℕ} (M : GMCModel d) (j k : ℕ)
    (omega : PotentialSample d) : 1 ≤ harmonicMicroscopicCoefficientBank M j k omega := by
  obtain ⟨p, hp⟩ := shellCoverShifts_nonempty d ((k + 1 : ℕ) : ℤ)
  exact (one_le_harmonicMicroscopicCellEnvelope M j p omega).trans
    (Finset.le_sup' (fun p => harmonicMicroscopicCellEnvelope M j p omega) hp)

theorem measurable_harmonicMicroscopicCoefficientBank {d : ℕ} (M : GMCModel d) (j k : ℕ) :
    Measurable (harmonicMicroscopicCoefficientBank M j k) := by
  let V := (shellCoverShifts d ((k + 1 : ℕ) : ℤ)).sup'
    (shellCoverShifts_nonempty d ((k + 1 : ℕ) : ℤ))
    (fun p => harmonicMicroscopicCellEnvelope M j p)
  have hV : Measurable V := Finset.measurable_sup' (shellCoverShifts_nonempty _ _)
    (fun p _ => measurable_harmonicMicroscopicCellEnvelope M j p)
  have heq : V = harmonicMicroscopicCoefficientBank M j k := by
    funext omega
    exact Finset.sup'_apply _ _ omega
  rwa [← heq]

/-- A two-sided coefficient bound on each physical unit cell. -/
theorem harmonicMicroscopicCellEnvelope_comparison {d : ℕ} (M : GMCModel d) (j : ℕ)
    (p : Fin d → ℤ) (omega : PotentialSample d) {x : Vec d}
    (hx : x - physicalShellCoverCenter 0 p ∈ openCubeSet (originCube d 0)) :
    (ahom M j)⁻¹ * aCutoff M j omega x ≤ harmonicMicroscopicCellEnvelope M j p omega ∧
      ((ahom M j)⁻¹ * aCutoff M j omega x)⁻¹ ≤ harmonicMicroscopicCellEnvelope M j p omega := by
  let T := cutoffShellSum j (-1) x omega -
    (((j : ℝ) + 1) * tauSq M.P + Real.log (ahom M j))
  have hlocal := abs_cutoffShellSum_le_smallCubeBlockEnvelope
    0 j (0 : ℤ) (physicalShellCoverCenter 0 p) (by norm_num) omega hx
  norm_num only [Nat.cast_zero, zero_sub] at hlocal
  have habs : |T| ≤ subunitCellEnvelope j p omega + subunitDrift M j :=
    (abs_sub _ _).trans (add_le_add hlocal (abs_ahomShift_le_subunitDrift M j))
  have hsuffix : 0 ≤ suffixSensitivityRealRepresentative j (j : ℤ) omega := ENNReal.toReal_nonneg
  have hn : (ahom M j)⁻¹ * aCutoff M j omega x = Real.exp T := by
    simp only [aCutoff_eq_exp_absoluteShellSum, T, Real.exp_sub, Real.exp_add,
      Real.exp_log (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M j)]
    field_simp
  rw [hn, ← Real.exp_neg]
  constructor <;> unfold harmonicMicroscopicCellEnvelope <;>
    apply Real.exp_le_exp.mpr
  · have ht := (le_abs_self T).trans habs
    linarith
  · have ht := (neg_le_abs T).trans habs
    linarith

/-- The bank controls both signs at every physical point of the larger cell. -/
theorem harmonicMicroscopicCoefficientBank_comparison {d : ℕ} (M : GMCModel d) (j k : ℕ)
    (omega : PotentialSample d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d ((k + 1 : ℕ) : ℤ))) :
    (ahom M j)⁻¹ * aCutoff M j omega x ≤ harmonicMicroscopicCoefficientBank M j k omega ∧
      ((ahom M j)⁻¹ * aCutoff M j omega x)⁻¹ ≤ harmonicMicroscopicCoefficientBank M j k omega := by
  obtain ⟨p, hp, hpx⟩ := exists_physicalShellCoverCenter_mem 0 ((k + 1 : ℕ) : ℤ) hx
  simp only [Nat.cast_zero, sub_zero] at hp hpx
  have h := harmonicMicroscopicCellEnvelope_comparison M j p omega hpx
  have hb : harmonicMicroscopicCellEnvelope M j p omega ≤
      harmonicMicroscopicCoefficientBank M j k omega :=
    Finset.le_sup' (fun p => harmonicMicroscopicCellEnvelope M j p omega) hp
  exact ⟨h.1.trans hb, h.2.trans hb⟩

/-- High internal moments absorb the covering cardinality. The resulting
coefficient price has any positive geometric exponent, uniformly for `j≤k`. -/
theorem exists_harmonicMicroscopicCoefficientBank_moment_bound (d : ℕ) (q eta : ℝ)
    (hq : 1 ≤ q) (heta : 0 < eta) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 → ∀ j k : ℕ, j ≤ k →
        eLpNorm (harmonicMicroscopicCoefficientBank M j k) (ENNReal.ofReal q) M.P.toMeasure ≤
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
    exists_harmonicMicroscopicCellEnvelope_moment_bound d S (eta / 2) hS1.le (by positivity)
  let C := C0 * (3 : ℝ) ^ (3 * eta / 2)
  refine ⟨delta0, C, hdelta, by dsimp only [C]; positivity, ?_⟩
  intro M hM j k hjk
  have hhigh := SubdiffusiveProcess.eLpNorm_sup'_le_of_le M.P.toMeasure
    (shellCoverShifts d ((k + 1 : ℕ) : ℤ)) (shellCoverShifts_nonempty _ _)
    (harmonicMicroscopicCellEnvelope M j)
    (fun p omega => zero_le_one.trans (one_le_harmonicMicroscopicCellEnvelope M j p omega))
    (fun p _ => (measurable_harmonicMicroscopicCellEnvelope M j p).aestronglyMeasurable)
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
  have hnorm := (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hqS)).trans hhigh
  refine hnorm.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [max_eq_left (by positivity)]
  have hjkR : (j : ℝ) ≤ k := by exact_mod_cast hjk
  calc
    _ ≤ (3 : ℝ) ^ ((eta / 2) * ((k : ℝ) + 3)) *
        (C0 * (3 : ℝ) ^ ((eta / 2) * (k : ℝ))) := by
      gcongr ; norm_num
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
