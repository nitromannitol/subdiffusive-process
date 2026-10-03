module

public import SubdiffusiveProcess.BesovComparison.Constants
public import SubdiffusiveProcess.BesovComparison.ZeroDimension

@[expose] public section

/-! The exact source-facing comparison, including p = 1 and divergent energies. -/
open Homogenization MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.BesovComparison
variable {d : ℕ}

theorem comparison_measurable [NeZero d] (m : ℤ) (s p : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hp : 1 ≤ p) (u : Vec d → ℝ) (humeas : Measurable u)
    (hmem : MemLp u (ENNReal.ofReal p) (normalizedCubeMeasure (originCube d m))) :
    wsp d m s p u ≤ ENNReal.ofReal (comparisonConstant d) *
        besov d m s (ENNReal.ofReal p) (ENNReal.ofReal p) (ENNReal.ofReal p) u ∧
      besov d m s (ENNReal.ofReal p) (ENNReal.ofReal p) (ENNReal.ofReal p) u ≤
        ENNReal.ofReal (comparisonConstant d) * wsp d m s p u := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hpE : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  let order : FractionalOrder := ⟨s,hs,hs1⟩
  let exponent : FiniteExponent := ⟨ENNReal.ofReal p,hpE,ENNReal.ofReal_lt_top⟩
  let P := exactOverlapScalarPParameters order exponent
  let hi := overlapIntegrableOfMemLp _ _ hpE u hmem
  have hPs : P.s = s := rfl
  have hPp : P.p = p := ENNReal.toReal_ofReal hp0.le
  have hPq : P.q = p := ENNReal.toReal_ofReal hp0.le
  have hB := besov_eq_overlap m s p hp0.le P hPs hPp hPq u hi
  have hA := ambientWsp_eq_gagliardo m s p hs hp0 u humeas
  have hBA : besov d m s (ENNReal.ofReal p) (ENNReal.ofReal p) (ENNReal.ofReal p) u ≤
      upperConstant d * ambientWsp d m s p u := by
    rw [hB, hA]
    calc
      _ ≤ ENNReal.ofReal s ^ p⁻¹ * (upperConstant d *
          Gagliardo.cubeGagliardoESeminorm (originCube d m) s (ENNReal.ofReal p) u) :=
        mul_le_mul' le_rfl (overlap_le_upper_mul_gagliardo order exponent _ u hi humeas hmem)
      _ = _ := mul_left_comm _ _ _
  have hAB : ambientWsp d m s p u ≤ Gagliardo.gagliardoBesovLowerConstant d *
      besov d m s (ENNReal.ofReal p) (ENNReal.ofReal p) (ENNReal.ofReal p) u := by
    rw [hB, hA]
    calc
      _ ≤ ENNReal.ofReal s ^ p⁻¹ * (Gagliardo.gagliardoBesovLowerConstant d *
          exactOverlapFiniteSeminorm P (originCube d m) u hi) :=
        mul_le_mul' le_rfl (gagliardo_le_lower_mul_overlap order exponent _ u hi humeas hmem)
      _ = _ := mul_left_comm _ _ _
  constructor
  · exact ((wsp_le_ambient m s p hs hp0 u).trans hAB).trans
      (mul_le_mul' (lowerConstant_le_comparisonConstant d) le_rfl)
  · calc
      _ ≤ upperConstant d * ambientWsp d m s p u := hBA
      _ ≤ upperConstant d * (metricConstant d * wsp d m s p u) :=
        mul_le_mul' le_rfl (ambient_le_metric_mul_wsp m s p hs hs1 hp u)
      _ = (upperConstant d * metricConstant d) * wsp d m s p u := (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul' (upper_metric_le_comparisonConstant d) le_rfl

theorem comparison_all_representatives [NeZero d] (m : ℤ) (s p : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hp : 1 ≤ p) (u : Vec d → ℝ)
    (hmem : MemLp u (ENNReal.ofReal p) (volume.restrict (cube d m))) :
    wsp d m s p u ≤ ENNReal.ofReal (comparisonConstant d) *
        besov d m s (ENNReal.ofReal p) (ENNReal.ofReal p) (ENNReal.ofReal p) u ∧
      besov d m s (ENNReal.ofReal p) (ENNReal.ofReal p) (ENNReal.ofReal p) u ≤
        ENNReal.ofReal (comparisonConstant d) * wsp d m s p u := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hpE : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hu := memLp_normalized_root m _ u hmem
  let v := hu.aestronglyMeasurable.mk u
  have hvmeas : Measurable v := hu.aestronglyMeasurable.measurable_mk
  have huv : u =ᵐ[normalizedCubeMeasure (originCube d m)] v := hu.aestronglyMeasurable.ae_eq_mk
  have hv : MemLp v (ENNReal.ofReal p) (normalizedCubeMeasure (originCube d m)) := hu.ae_eq huv
  let P : ExactOverlapFiniteParameters := ⟨s,p,p,hs,hs1,hp,hp⟩
  have hB := besov_congr_normalized m s p hp0.le P rfl rfl rfl
    (overlapIntegrableOfMemLp _ _ hpE u hu) (overlapIntegrableOfMemLp _ _ hpE v hv) huv
  have hW := wsp_congr_ae m s p (ae_root_of_ae_normalized m huv)
  rw [hB, hW]
  exact comparison_measurable m s p hs hs1 hp v hvmeas hv

theorem source_comparison (d : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (s p : ℝ) (m : ℤ) (u : Vec d → ℝ),
      0 < s → s < 1 → 1 ≤ p → MemLp u (ENNReal.ofReal p) (volume.restrict (cube d m)) →
      ENNReal.ofReal C⁻¹ * wsp d m s p u ≤
          besov d m s (ENNReal.ofReal p) (ENNReal.ofReal p) (ENNReal.ofReal p) u ∧
        besov d m s (ENNReal.ofReal p) (ENNReal.ofReal p) (ENNReal.ofReal p) u ≤
          ENNReal.ofReal C * wsp d m s p u := by
  refine ⟨comparisonConstant d, one_le_comparisonConstant d, ?_⟩
  intro s p m u hs hs1 hp hu
  by_cases hd : d = 0
  · subst d
    rw [besov_zero_dimension m s p hs hs1 hp u hu,
      wsp_zero_dimension m s p (zero_lt_one.trans_le hp) u]
    simp
  letI : NeZero d := ⟨hd⟩
  obtain ⟨hWB,hBW⟩ := comparison_all_representatives m s p hs hs1 hp u hu
  refine ⟨?_,hBW⟩
  have hC : 0 < comparisonConstant d := zero_lt_one.trans_le (one_le_comparisonConstant d)
  rw [ENNReal.ofReal_inv_of_pos hC]
  calc
    _ ≤ (ENNReal.ofReal (comparisonConstant d))⁻¹ *
        (ENNReal.ofReal (comparisonConstant d) *
          besov d m s (ENNReal.ofReal p) (ENNReal.ofReal p) (ENNReal.ofReal p) u) :=
      mul_le_mul' le_rfl hWB
    _ = _ := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hC)
        ENNReal.ofReal_ne_top, one_mul]

end SubdiffusiveProcess.BesovComparison
