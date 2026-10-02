import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.WindowSeminorms
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalPoincare

/-!
# Hölder Step 3: window means versus the top supremum

The boundary part of the recurrence contains the Euclidean magnitude of the
gradient average on a truncated window.  Jensen and the literal top-cube
supremum bound it by `vectorSupNormOn`; the Hölder guard supplies the boundedness
needed to use the conditionally complete `sSup` carrier honestly.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open Homogenization hiding Vec

noncomputable section

private theorem euclideanNorm_add_le {d : ℕ} (u v : Vec d) :
    euclideanNorm (u + v) ≤ euclideanNorm u + euclideanNorm v := by
  simp only [euclideanNorm_eq_norm_ofVec]
  simpa only [← HilbertVec.ofVecL_apply, map_add] using
    norm_add_le (HilbertVec.ofVec u) (HilbertVec.ofVec v)

theorem bddAbove_vectorValues_cube_of_memHolder {d : ℕ} [NeZero d]
    {m : ℤ} {f : Vec d → Vec d} (hf : MemHolder (cube d m) (1 / 2) f) :
    BddAbove {r : ℝ | ∃ x ∈ cube d m, r = euclideanNorm (f x)} := by
  obtain ⟨K, hK, hholder⟩ := hf
  let B := K * ((d : ℝ) * (3 : ℝ) ^ m) ^ (1 / 2 : ℝ) + euclideanNorm (f 0)
  refine ⟨B, ?_⟩
  rintro r ⟨x, hx, rfl⟩
  have hzero : (0 : Vec d) ∈ cube d m := zero_mem_cube d m
  have hdist : dist x 0 < (3 : ℝ) ^ m := by
    exact Metric.mem_ball.mp (cube_subset_ball hzero hx)
  have hnorm : euclideanNorm (x - 0) ≤ (d : ℝ) * (3 : ℝ) ^ m := by
    calc
      euclideanNorm (x - 0) ≤ (d : ℝ) * ‖x - 0‖ :=
        Homogenization.euclideanNorm_le_dimension_mul_norm _
      _ = (d : ℝ) * dist x 0 := by rw [dist_eq_norm]
      _ ≤ (d : ℝ) * (3 : ℝ) ^ m :=
        mul_le_mul_of_nonneg_left hdist.le (Nat.cast_nonneg d)
  have hbase0 : 0 ≤ (d : ℝ) * (3 : ℝ) ^ m := by positivity
  have hpow := Real.rpow_le_rpow (euclideanNorm_nonneg _) hnorm (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hdiff := hholder x hx 0 hzero
  have hscaled := mul_le_mul_of_nonneg_left hpow hK
  have htri : euclideanNorm (f x) ≤ euclideanNorm (f x - f 0) + euclideanNorm (f 0) := by
    calc
      euclideanNorm (f x) = euclideanNorm ((f x - f 0) + f 0) := by
        congr 1
        abel
      _ ≤ _ := euclideanNorm_add_le _ _
  dsimp only [B]
  linarith

theorem euclideanNorm_le_vectorSupNormOn_cube {d : ℕ} [NeZero d]
    {m : ℤ} {f : Vec d → Vec d} (hf : MemHolder (cube d m) (1 / 2) f)
    {x : Vec d} (hx : x ∈ cube d m) :
    euclideanNorm (f x) ≤ vectorSupNormOn (cube d m) f := by
  unfold vectorSupNormOn
  exact le_csSup (bddAbove_vectorValues_cube_of_memHolder hf) ⟨x, hx, rfl⟩

theorem vectorSupNormOn_cube_nonneg {d : ℕ} [NeZero d]
    {m : ℤ} {f : Vec d → Vec d} (hf : MemHolder (cube d m) (1 / 2) f) :
    0 ≤ vectorSupNormOn (cube d m) f := by
  exact (euclideanNorm_nonneg (f 0)).trans
    (euclideanNorm_le_vectorSupNormOn_cube hf (zero_mem_cube d m))

/-- The boundary mean in `e.one.step.expanded` is bounded by the exact top
`L∞` carrier printed in `e.delta.j.z.def`. -/
theorem sqrt_vecNormSq_averageVecOn_truncatedCube_le_vectorSupNormOn_cube
    {d : ℕ} [NeZero d] {m j : ℤ} {z : Vec d}
    (h : H1Function (openCubeSet (originCube d m)))
    (hz : z ∈ cube d m) (hjm : j - 1 ≤ m)
    (hh : MemHolder (cube d m) (1 / 2) h.grad) :
    Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m j z) h.grad)) ≤
      vectorSupNormOn (cube d m) h.grad := by
  let W := truncatedCube d m j z
  have hWpos : 0 < (volume W).toReal :=
    volume_toReal_truncatedCube_pos z hz hjm
  have hmem : MemLp (fun x ↦ HilbertVec.ofVec (h.grad x)) 2
      (volume.restrict W) :=
    (memHilbertVectorL2_hilbertifyVecField h.grad_memVectorL2).mono_measure
      (Measure.restrict_mono (truncatedCube_subset_cube d m j z) le_rfl)
  have hmean :=
    Section6HarmonicApproximation.euclideanNorm_averageVecOn_le_vectorNormalizedL2On
      hWpos hmem
  have hsup0 := vectorSupNormOn_cube_nonneg hh
  have hsq : IntegrableOn (fun x ↦ euclideanNorm (h.grad x) ^ 2) W := by
    simpa only [euclideanNorm_eq_norm_ofVec] using hmem.norm.integrable_sq
  have hnorm : vectorNormalizedL2On W h.grad ≤ vectorSupNormOn (cube d m) h.grad := by
    unfold vectorNormalizedL2On
    apply Section6Iteration.normalizedL2On_le_of_abs_le
      (measurableSet_truncatedCube d m j z) hWpos
      (volume_truncatedCube_lt_top d m j z).ne hsup0 hsq
    intro x hx
    rw [abs_of_nonneg (euclideanNorm_nonneg _)]
    exact euclideanNorm_le_vectorSupNormOn_cube hh
      (truncatedCube_subset_cube d m j z hx)
  change euclideanNorm (averageVecOn W h.grad) ≤ _
  exact hmean.trans hnorm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
