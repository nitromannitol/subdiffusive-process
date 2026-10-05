module

public import SubdiffusiveProcess.Besov.SmoothTestNorm

@[expose] public section

namespace SubdiffusiveProcess.Besov
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov
open scoped BigOperators ENNReal ContDiff
noncomputable section

/-- The paper's inhomogeneous negative norm, with globally smooth vector tests. -/
def hHatNorm {d : ℕ} (Q : TriadicCube d) (F : Vec d → Vec d) : ℝ≥0∞ :=
  ⨆ φ : {φ : Vec d → Vec d // ContDiff ℝ ∞ φ},
    ENNReal.ofReal |∫ x, vecDot (F x) (φ.1 x) ∂normalizedCubeMeasure Q| /
      ENNReal.ofReal (smoothTestSize Q φ.1)

theorem hHatNorm_congr_ae {d : ℕ} (Q : TriadicCube d) {F G : Vec d → Vec d}
    (h : F =ᵐ[normalizedCubeMeasure Q] G) : hHatNorm Q F = hHatNorm Q G := by
  unfold hHatNorm
  congr 1
  funext φ
  congr 3
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

/-- Dimension-only constant for the smooth Sobolev-to-Besov test embedding. -/
def hHatBesovConstant (d : ℕ) : ℝ :=
  (3 : ℝ) ^ ((d : ℝ) + 1) * cubeMeanZeroHMinusOneBesovTestConstant d

theorem hHatBesovConstant_pos (d : ℕ) : 0 < hHatBesovConstant d :=
  mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (cubeMeanZeroHMinusOneBesovTestConstant_pos d)

/-- The literal smooth-test norm is controlled by the coordinate circ norms. -/
theorem hHatNorm_le_sum_circ {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (F : Vec d → Vec d) (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q)) :
    hHatNorm Q F ≤ ENNReal.ofReal
      (hHatBesovConstant d * ∑ i : Fin d, cubeBesovCircNorm Q 1 2 1 (fun x => F x i)) := by
  have hcirc : ∀ i : Fin d, 0 ≤ cubeBesovCircNorm Q 1 2 1 (fun x => F x i) := by
    intro i
    exact cubeBesovCircNorm_nonneg Q 1 2 1 _
      (cubeBesovCircNormValueSet_bddAbove_of_memLp Q 1 2 1 _
        (by norm_num) (hF i) (by norm_num) (by norm_num) (by norm_num))
  have hA : 0 ≤ hHatBesovConstant d * ∑ i : Fin d, cubeBesovCircNorm Q 1 2 1 (fun x => F x i) :=
    mul_nonneg (hHatBesovConstant_pos d).le (Finset.sum_nonneg fun i _ => hcirc i)
  unfold hHatNorm
  refine iSup_le fun φ => ENNReal.div_le_of_le_mul ?_
  rw [← ENNReal.ofReal_mul hA]
  apply ENNReal.ofReal_le_ofReal
  have hsize : 0 ≤ smoothTestSize Q φ.1 :=
    add_nonneg (Real.sqrt_nonneg _) (mul_nonneg
      (inv_nonneg.mpr (by unfold cubeScaleFactor; positivity)) (Real.sqrt_nonneg _))
  have h := abs_cubeAverage_vecDot_le_sum_note_constant_mul_of_uniform_component_bounds_two_one_of_nonneg
    Q 1 F φ.1 (fun _ => cubeMeanZeroHMinusOneBesovTestConstant d * smoothTestSize Q φ.1)
    (by norm_num) hF
    (fun _ => mul_nonneg (cubeMeanZeroHMinusOneBesovTestConstant_pos d).le hsize)
    (fun i N => smoothCoordinate_dualTestNorm_le Q φ.1 φ.2 i N)
    (fun i => CubeBesovDualLocalMemLpGlobal.of_memLp_parent (p := (2 : ℝ≥0∞))
      (by
        have hp : cubeBesovConjExponent 2 = 2 := by
          simpa [cubeBesovConjExponent] using
            (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
        simpa only [hp] using smoothCoordinate_memLp Q φ.1 φ.2 i))
  rw [cubeAverage_eq_integral_normalizedCubeMeasure] at h
  refine h.trans_eq ?_
  rw [hHatBesovConstant]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem hHatNorm_toReal_le_sum_circ {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (F : Vec d → Vec d) (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q)) :
    (hHatNorm Q F).toReal ≤
      hHatBesovConstant d * ∑ i : Fin d, cubeBesovCircNorm Q 1 2 1 (fun x => F x i) := by
  have hnonneg : 0 ≤ hHatBesovConstant d * ∑ i : Fin d,
      cubeBesovCircNorm Q 1 2 1 (fun x => F x i) := by
    refine mul_nonneg (hHatBesovConstant_pos d).le (Finset.sum_nonneg ?_)
    intro i _
    exact cubeBesovCircNorm_nonneg Q 1 2 1 _
      (cubeBesovCircNormValueSet_bddAbove_of_memLp Q 1 2 1 _
        (by norm_num) (hF i) (by norm_num) (by norm_num) (by norm_num))
  simpa only [ENNReal.toReal_ofReal hnonneg] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top (hHatNorm_le_sum_circ Q F hF)

end
end SubdiffusiveProcess.Besov
