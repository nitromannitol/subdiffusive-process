module

public import SubdiffusiveProcess.Analysis.CubeFractionalBounds
public import SubdiffusiveProcess.Compactness.UniformFiniteApproximation

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace Homogenization
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

/-- Fractional Rellich compactness on a fixed cube, proved by cell averages. -/
theorem exists_subseq_of_cubeFractionalSqNorm_bounded (d : ℕ) (hd : 2 ≤ d)
    (s : Set.Ioo (0 : ℝ) 1) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (v : ℕ → DomainL2 (centeredCube z r hr)) (B : ℝ)
    (hfinite : ∀ n, cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v n) < ⊤)
    (hbound : ∀ n, cubeFractionalSqNorm hd z r hr s (v n) ≤ B) :
    ∃ (phi : ℕ → ℕ) (w : DomainL2 (centeredCube z r hr)),
      StrictMono phi ∧ Tendsto (fun n => v (phi n)) atTop (𝓝 w) := by
  let c : ℝ≥0∞ := ENNReal.ofReal (s : ℝ) /
    volume (centeredCube z r hr : Set (SpatialCoordinates d))
  have hc0 : c ≠ 0 := ENNReal.div_ne_zero.mpr
    ⟨ENNReal.ofReal_ne_zero_iff.mpr s.property.1,
      by rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top⟩
  let K : ℝ≥0∞ := ENNReal.ofReal B / c
  have hK : K ≠ ⊤ := ENNReal.div_ne_top ENNReal.ofReal_ne_top hc0
  have henergy (n : ℕ) : cubeGagliardoIntegral z r hr s (v n) ≤ K :=
    cubeGagliardoIntegral_le_of_cubeFractionalSqNorm_le hd z r hr s (v n) B
      (hfinite n) (hbound n)
  let R : ℝ := Real.sqrt (B * volume.real
    (centeredCube z r hr : Set (SpatialCoordinates d)))
  have hR (n : ℕ) : ‖v n‖ ≤ R :=
    norm_le_of_cubeFractionalSqNorm_le hd z r hr s (v n) B (hbound n)
  apply exists_subseq_of_totallyBounded_approximations v
  intro eps heps
  have hlim := tendsto_cubeCellErrorCoefficient_zero (d := d) r hr s s.property.1 K hK
  obtain ⟨m, hm⟩ := (hlim.eventually_lt_const
    (ENNReal.ofReal_pos.mpr (pow_pos heps 2))).exists
  refine ⟨fun n => cubeCellProjection z r hr m (v n),
    totallyBounded_range_cubeCellProjection z r hr m v R hR, ?_⟩
  intro n
  rw [dist_eq_norm]
  apply (sq_lt_sq₀ (norm_nonneg _) heps.le).mp
  apply (ENNReal.ofReal_lt_ofReal_iff (pow_pos heps 2)).mp
  exact ((cubeCellProjection_error_sq_le z r hr s s.property.1 m (v n)).trans
    (mul_le_mul_right (henergy n) _)).trans_lt hm

end SubdiffusiveProcess
