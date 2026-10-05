module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevMassCore
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevMeasure
@[expose] public section

set_option autoImplicit false
open Homogenization MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
theorem weightedSobolev_scaled_mass_root {x M p a : ℝ} (hx : 0 ≤ x)
    (hM : 0 ≤ M) (hp : 1 ≤ p)
    (h : (1 / 8 : ℝ) * (3 : ℝ) ^ (-a * p) * x ^ p ≤ M ^ p) :
    x ≤ 8 * M * (3 : ℝ) ^ a := by
  have hscale : 0 < (3 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 3) a
  have hc : (3 : ℝ) ^ (-a * p) * ((3 : ℝ) ^ a) ^ p = 1 := by
    rw [←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),
        ←Real.rpow_add (by norm_num : (0:ℝ) < 3),
        show (-a * p + a * p : ℝ) = 0 by ring,
        Real.rpow_zero]
  have hbound := mul_le_mul_of_nonneg_right h
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) (Real.rpow_nonneg hscale.le p))
  have hcancel : (1 / 8 : ℝ) * (3 : ℝ) ^ (-a * p) * x ^ p * (8 * ((3 : ℝ) ^ a) ^ p) = x ^ p := by
    calc (1 / 8 : ℝ) * (3 : ℝ) ^ (-a * p) * x ^ p * (8 * ((3 : ℝ) ^ a) ^ p)
        = ((3 : ℝ) ^ (-a * p) * ((3 : ℝ) ^ a) ^ p) * x ^ p := by ring
      _ = x ^ p := by rw [hc, one_mul]
  rw [hcancel] at hbound
  have hfinal : x ^ p ≤ 8 * (M * (3 : ℝ) ^ a) ^ p := by
    rw [Real.mul_rpow hM hscale.le]
    convert hbound using 1 ; ring
  simpa only [mul_assoc] using
    weightedSobolev_mass_root hx (mul_nonneg hM hscale.le) hp hfinal

theorem weightedSobolev_dimension_order {d : ℕ} (hd : 2 ≤ d) :
    1 ≤ 4 * (d : ℝ) := by
  have h : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  linarith

theorem weightedSobolev_growth_ge_one (j : ℕ) :
    1 ≤ (3 : ℝ) ^ ((3 / 8 : ℝ) * (j : ℝ)) :=
  Real.one_le_rpow (by norm_num) (by positivity)

theorem weightedSobolev_density_to_mass {w M z : ℝ} (hz : 1 ≤ z)
    (h : |w - 1| ≤ 8 * M * z) : w ≤ 8 * (1 + M) * z := by
  have h0 := le_abs_self (w - 1)
  have h1 := h0.trans h
  nlinarith [h1, hz]

theorem weightedSobolev_cell_average_bound {d : ℕ} (hd : 2 ≤ d) (m : ℤ)
    (f : Vec d → ℝ) (hf : ExactCircIntegrable (originCube d m) f)
    (M : ℝ) (hM : 0 ≤ M)
    (hmass : ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (m : ℝ))) *
      paperNegativeBesovCircDiagonal (originCube d m) (1 / 8) (4 * (d : ℝ)) f hf ≤
        ENNReal.ofReal M)
    (j : ℕ) (R : TriadicCube d) (hR : R ∈ descendantsAtDepth (originCube d m) j) :
    |cubeAverage R f| ≤ 8 * M * (3 : ℝ) ^ ((3 / 8 : ℝ) * (j : ℝ)) := by
  apply weightedSobolev_scaled_mass_root (a := (3/8)*(j:ℝ))
    (abs_nonneg _) hM (weightedSobolev_dimension_order hd)
  simpa only [neg_mul] using
    weightedSobolev_cell_moment hd m f hf M hM hmass j R hR

theorem weightedSobolev_cell_mass_bound {d : ℕ} (hd : 2 ≤ d) (m : ℤ)
    (b : Vec d → ℝ) (hb : CoefficientOn (openCubeSet (originCube d m)) b)
    (hI : ExactCircIntegrable (originCube d m) (fun x => b x / cubeAverage (originCube d m) b - 1))
    (M : ℝ) (hM : 0 ≤ M)
    (hmass : ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (m : ℝ))) *
      paperNegativeBesovCircDiagonal (originCube d m) (1 / 8) (4 * (d : ℝ))
        (fun x => b x / cubeAverage (originCube d m) b - 1) hI ≤ ENNReal.ofReal M)
    (j : ℕ) (R : TriadicCube d) (hR : R ∈ descendantsAtDepth (originCube d m) j) :
    cubeAverage R b / cubeAverage (originCube d m) b ≤
      8 * (1 + M) * (3 : ℝ) ^ ((3 / 8 : ℝ) * (j : ℝ)) := by
  obtain habs := weightedSobolev_cell_average_bound hd m _ hI M hM hmass j R hR
  have hbR : CoefficientOn (openCubeSet R) b :=
    weightedSobolev_coefficient_mono (openCubeSet_subset_of_mem_descendantsAtDepth hR) hb
  have childIntegrable : Integrable b (normalizedCubeMeasure R) :=
    (weightedSobolev_coefficient_cube_memLp R b hbR 1).integrable le_rfl
  rw [weightedSobolev_average_density _ R b childIntegrable] at habs
  exact weightedSobolev_density_to_mass (weightedSobolev_growth_ge_one j) habs

theorem weightedSobolev_mass_constant_ge_one {M : ℝ} (hM : 1 ≤ M) :
    1 ≤ 8 * (1 + M) := by
  linarith


theorem weightedSobolev_measure_cell_bound {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (b : Vec d → ℝ) (hb : CoefficientOn (openCubeSet Q) b) (hR : R ∈ descendantsAtDepth Q j)
    (K : ℝ) (hK : 0 ≤ K)
    (h : cubeAverage R b / cubeAverage Q b ≤ K * (3 : ℝ)^((3/8:ℝ)*(j:ℝ))) :
    weightedSobolevMeasure Q b (cubeSet R) ≤
      (ENNReal.ofReal K * (3:ℝ≥0∞)^((3/8:ℝ)*(j:ℝ))) / ((descendantsAtDepth Q j).card : ℝ≥0∞) := by
  rw [weightedSobolevMeasure_cubeSet_descendant b hb hR]
  have h1 := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_mul hK] at h1
  rw [←ENNReal.ofReal_rpow_of_pos (by norm_num : (0:ℝ)<3)] at h1
  norm_num only [ENNReal.ofReal_ofNat] at h1
  gcongr

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
