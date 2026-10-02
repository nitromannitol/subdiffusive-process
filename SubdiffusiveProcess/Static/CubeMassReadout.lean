import SubdiffusiveProcess.Static.CubeMassAffine
import SubdiffusiveProcess.Static.MassGrowthNumerics
import SubdiffusiveProcess.Static.LocalEstimateClauses

/-! # Deterministic all-ball readout of the two counted cube tests -/
open MeasureTheory Metric SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions
open Homogenization hiding Vec TriadicCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- A counted cube envelope gives the literal two-sided all-ball mass clause. -/
theorem localMassEstimates_of_cube_envelope {d : ℕ} (M : GMCModel d)
    (j m : ℕ) (z y0 : Vec d) {ρ0 R W : ℝ} (hR : 1 ≤ R) (hρR : ρ0 ≤ R)
    (hW : 1 ≤ W) (ω : PotentialSample d)
    (henv : ∀ n : ℕ, ∀ k ∈ MassGrid.catalogue R n,
      (translatedCutoffAverage M j ((m : ℤ) - n)
        (z + (3 : ℝ) ^ m • (y0 + MassGrid.cc ((3 : ℝ) ^ n)⁻¹ k)) ω)⁻¹ ≤
          W * (3 : ℝ) ^ ((1 / 2 : ℝ) * n) ∧
      translatedCutoffAverage M j ((m : ℤ) - n + 3)
        (z + (3 : ℝ) ^ m • (y0 + MassGrid.cc ((3 : ℝ) ^ n)⁻¹ k)) ω ≤
          W * (3 : ℝ) ^ ((1 / 2 : ℝ) * n)) :
    localMassEstimates (fun x => aCutoff M j ω (z + (3 : ℝ) ^ m • x)) y0 ρ0
      (massGrowthConstant d * W) := by
  intro x r hr hr1 hsub
  have hsub0 : Metric.ball (x - y0) r ⊆ Metric.ball (0 : Vec d) (R / 2) := by
    intro u hu
    have hux : u + y0 ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm] at hu ⊢
      convert hu using 2; abel
    have hup := hsub hux
    rw [Metric.mem_ball, dist_eq_norm] at hup ⊢
    have heq : (u + y0) - y0 = u := by abel
    rw [heq] at hup
    simpa only [sub_zero] using hup.trans_le (by linarith : ρ0 / 2 ≤ R / 2)
  obtain ⟨n, k, hk, hcell, hrh, hhr⟩ := MassGrid.cell_in_ball hR (x - y0) r hr hr1 hsub0
  let h : ℝ := ((3 : ℝ) ^ n)⁻¹
  let c : Vec d := y0 + MassGrid.cc h k
  have hh : 0 < h := by dsimp only [h]; positivity
  have hsmall : Metric.ball c (h / 2) ⊆ Metric.ball x r := by
    intro u hu
    have hu' : u - y0 ∈ MassGrid.cell h k := by
      rw [Metric.mem_ball, dist_eq_norm] at hu
      rw [MassGrid.cell, Metric.mem_ball, dist_eq_norm]
      dsimp only [c] at hu
      convert hu using 2; abel
    have hu'' := hcell hu'
    rw [Metric.mem_ball, dist_eq_norm] at hu'' ⊢
    convert hu'' using 2; abel
  have hcx : c ∈ Metric.ball x r := hsmall (Metric.mem_ball_self (half_pos hh))
  have hlarge : Metric.ball x r ⊆ Metric.ball c (27 * h / 2) := by
    intro u hu
    have hux := Metric.mem_ball.mp hu
    have hxc := Metric.mem_ball.mp hcx
    rw [dist_comm c x] at hxc
    rw [Metric.mem_ball]
    have ht := dist_triangle u x c
    change r < 3 * h at hrh
    linarith
  let a := translatedCutoffAverage M j ((m : ℤ) - n) (z + (3 : ℝ) ^ m • c) ω
  let b := translatedCutoffAverage M j ((m : ℤ) - n + 3) (z + (3 : ℝ) ^ m • c) ω
  obtain ⟨hai, hb⟩ := henv n k hk
  rw [triadic_mesh_weight] at hai hb
  have hnum := mass_growth_numeric (d := d) (by have := M.shellPrefix.dimension; omega)
    hr hh (zero_lt_one.trans_le hW) (translatedCutoffAverage_pos M j _ _ ω)
    hrh.le hhr hai hb
  let μ := volume.withDensity (fun u => ENNReal.ofReal (aCutoff M j ω (z + (3 : ℝ) ^ m • u)))
  have hmass (t : ℕ) : μ (Metric.ball c ((3 : ℝ) ^ ((t : ℤ) - n) / 2)) =
      ENNReal.ofReal ((((3 : ℝ) ^ ((t : ℤ) - n)) ^ d) *
        translatedCutoffAverage M j ((m : ℤ) - n + t) (z + (3 : ℝ) ^ m • c) ω) := by
    rw [show μ = volume.withDensity
      (fun u => ENNReal.ofReal (aCutoff M j ω (z + (3 : ℝ) ^ m • u))) from rfl]
    rw [withDensity_apply _ measurableSet_ball, lintegral_scaled_cutoff_ball,
      ← ENNReal.ofReal_mul (by positivity)]
  have hs : μ (Metric.ball c (h / 2)) = ENNReal.ofReal (h ^ d * a) := by
    simpa only [Nat.cast_zero, zero_sub, zpow_neg, zpow_natCast, add_zero, h, a] using hmass 0
  have hl : μ (Metric.ball c (27 * h / 2)) = ENNReal.ofReal ((27 * h) ^ d * b) := by
    have hp : (3 : ℝ) ^ ((3 : ℤ) - (n : ℤ)) = 27 * h := by
      rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num [h, div_eq_mul_inv]
    have h3 := hmass 3
    norm_num only [Nat.cast_ofNat] at h3
    rw [hp] at h3
    exact h3
  constructor
  · exact (ENNReal.ofReal_le_ofReal hnum.1).trans ((hs.symm.le).trans (measure_mono hsmall))
  · exact (measure_mono hlarge).trans ((hl.le).trans (ENNReal.ofReal_le_ofReal hnum.2))

end SubdiffusiveProcess.Static
