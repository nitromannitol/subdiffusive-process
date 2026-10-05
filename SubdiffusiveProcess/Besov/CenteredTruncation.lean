module

public import SubdiffusiveProcess.Besov.TruncationCore
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.TriadicMeanComparison

@[expose] public section

open MeasureTheory MeasureTheory.Measure SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open scoped BigOperators ENNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Besov

/-- The clipped part after subtracting the root mean. -/
def clippedPart {d : ℕ} (Q : TriadicCube d) (n : ℕ) (g : Vec d → ℝ) : Vec d → ℝ :=
  fun x => clip (n + 1) (g x - cubeAverage Q g)

/-- Center the truncation so its root mean is exactly the original root mean. -/
def centeredTruncation {d : ℕ} (Q : TriadicCube d) (n : ℕ) (g : Vec d → ℝ) : Vec d → ℝ :=
  fun x => clippedPart Q n g x + (cubeAverage Q g - cubeAverage Q (clippedPart Q n g))

/-- Probability-space oscillations are invariant under addition of a constant. -/
theorem oscillation_add_const {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (h : α → ℝ) (hh : Integrable h μ) (c : ℝ) :
    eLpNorm (fun x => h x + c - ∫ y, h y + c ∂μ) 1 μ =
      eLpNorm (fun x => h x - ∫ y, h y ∂μ) 1 μ := by
  have hm : (∫ y, h y + c ∂μ) = (∫ y, h y ∂μ) + c := by
    rw [integral_add hh (integrable_const c)]
    simp
  congr 1
  funext x
  rw [hm]
  ring

/-- Integrability of a centered truncation on the root cube. -/
theorem centeredTruncation_integrable {d : ℕ} (Q : TriadicCube d) (n : ℕ)
    (g : Vec d → ℝ) (hg : IntegrableOn g (cubeSet Q)) :
    IntegrableOn (centeredTruncation Q n g) (cubeSet Q) := by
  have hgμ := integrable_normalizedCubeMeasure Q hg
  have hc := integrable_clip (normalizedCubeMeasure Q)
    (hgμ.sub (integrable_const (cubeAverage Q g))) (by positivity : 0 ≤ (n : ℝ) + 1)
  exact integrableOn_of_integrable_normalizedCubeMeasure Q (hc.add (integrable_const _))

/-- Every centered truncation is bounded. -/
theorem centeredTruncation_bound {d : ℕ} (Q : TriadicCube d) (n : ℕ) (g : Vec d → ℝ)
    (x : Vec d) :
    |centeredTruncation Q n g x| ≤
      (n : ℝ) + 1 + |cubeAverage Q g - cubeAverage Q (clippedPart Q n g)| := by
  exact (abs_add_le _ _).trans (add_le_add
    (clip_abs_le_bound (by positivity) _) le_rfl)

/-- The root mean is preserved by centering. -/
theorem centeredTruncation_mean {d : ℕ} (Q : TriadicCube d) (n : ℕ)
    (g : Vec d → ℝ) (hg : IntegrableOn g (cubeSet Q)) :
    cubeAverage Q (centeredTruncation Q n g) = cubeAverage Q g := by
  have hgμ := integrable_normalizedCubeMeasure Q hg
  have hc := integrable_clip (normalizedCubeMeasure Q)
    (hgμ.sub (integrable_const (cubeAverage Q g))) (by positivity : 0 ≤ (n : ℝ) + 1)
  change Integrable (clippedPart Q n g) (normalizedCubeMeasure Q) at hc
  unfold centeredTruncation
  rw [cubeAverage_eq_integral_normalizedCubeMeasure, integral_add hc (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul,
    ← cubeAverage_eq_integral_normalizedCubeMeasure]
  ring

/-- A local cube's normalized measure is a probability measure. -/
theorem translatedCube_normalized_isProbability {d : ℕ} (k : ℤ) (z : Vec d) :
    IsProbabilityMeasure ((volume (translatedCube d k z))⁻¹ • volume.restrict (translatedCube d k z)) := by
  constructor
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel
    (ENNReal.toReal_pos_iff.mp (Section6BoundedMultiplier.volume_translatedCube_toReal_pos k z)).1.ne'
    (Section6BoundedMultiplier.volume_translatedCube_ne_top k z)

/-- On every overlapping local cube, truncation costs at most two in the L1 oscillation. -/
theorem centeredTruncation_local_oscillation_le {d : ℕ} (Q : TriadicCube d) (n : ℕ)
    (g : Vec d → ℝ) (k : ℤ) (z : Vec d)
    (hg : IntegrableOn g (translatedCube d k z)) :
    normalizedLp (translatedCube d k z) 1
      (fun x => centeredTruncation Q n g x - ⨍ y in translatedCube d k z, centeredTruncation Q n g y) ≤
      2 * normalizedLp (translatedCube d k z) 1
        (fun x => g x - ⨍ y in translatedCube d k z, g y) := by
  let μ := (volume (translatedCube d k z))⁻¹ • volume.restrict (translatedCube d k z)
  let : IsProbabilityMeasure μ := translatedCube_normalized_isProbability k z
  have h0 : volume (translatedCube d k z) ≠ 0 :=
    (ENNReal.toReal_pos_iff.mp (Section6BoundedMultiplier.volume_translatedCube_toReal_pos k z)).1.ne'
  have hgμ : Integrable g μ := hg.smul_measure (ENNReal.inv_ne_top.mpr h0)
  have hc := integrable_clip μ (hgμ.sub (integrable_const (cubeAverage Q g)))
    (by positivity : 0 ≤ (n : ℝ) + 1)
  unfold normalizedLp
  rw [setAverage_eq', setAverage_eq']
  change eLpNorm (fun x => clippedPart Q n g x + _ - ∫ y, clippedPart Q n g y + _ ∂μ) 1 μ ≤ _
  rw [oscillation_add_const μ (clippedPart Q n g) hc]
  exact clipped_oscillation_le μ g hgμ (cubeAverage Q g) (n + 1) (by positivity)

end SubdiffusiveProcess.Besov
