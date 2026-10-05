module

public import Mathlib
public import SubdiffusiveProcess.Paper.calib_h0_large_cell_bounds_of_growth
public import SubdiffusiveProcess.Paper.calib_h0_large_cell_bounds
public import SubdiffusiveProcess.Paper.prop_growth_large_root
public import SubdiffusiveProcess.Paper.prop_conc_mesh_cutoff_family

@[expose] public section

/-! Almost-sure harmonic-cell bounds of the infrared-free coefficient sequence along a represented sequence from the Stage-3
coordinates: almost surely the constants `Kc p (N n) (env n ω)` converge (hence are bounded) and satisfy `GrowthAt` for every `n`
(the environments have the chaos law), so `calib_h0_large_cell_bounds_of_growth` applies on every padded calibration cube. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- **Cell bounds along the represented sequence.** -/
theorem calib_coordinates_cells {d : ℕ} (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (K0 : ℕ) (t alpha : ℝ)
    (ht : 0 ≤ t) (ha : 0 < alpha)
    (Kc : ℕ × OddGridIndex d (triadicHalf 1) → ℕ → BilateralField d → ℝ)
    (hKae : ∀ p : ℕ × OddGridIndex d (triadicHalf 1), ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (r : ℝ) (hr : 0 < r), r = (3 : ℝ) ^ (K0 + p.1) →
        aux_prop_growth_large_root_GrowthAt M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
          (oddGridCenter (0 : SpatialCoordinates d) (3 * (3 : ℝ) ^ (K0 + p.1 + 1) / 3) (triadicHalf 1) p.2) r hr
          t alpha om (fun N => Kc p N om))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (env : ℕ → Ω → BilateralField d)
    (hmp : ∀ n, MeasurePreserving (env n) P (chaosSampleLaw M).toMeasure) (N : ℕ → ℕ)
    (hconv : ∀ᵐ omega ∂P, ∀ p : ℕ × OddGridIndex d (triadicHalf 1), ∃ Z : ℝ,
      Tendsto (fun n => Kc p (N n) (env n omega)) atTop (𝓝 Z)) :
    ∀ᵐ omega ∂P, ∀ k : ℕ,
      calib_h0_large_cell_bounds (0 : SpatialCoordinates d) (3 * (3 : ℝ) ^ (K0 + k + 1) / 3) (by positivity)
        (fun n => cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (env n omega) (N n)) t alpha := by
  have hall : ∀ᵐ omega ∂P, ∀ (n : ℕ) (p : ℕ × OddGridIndex d (triadicHalf 1)),
      ∀ (r : ℝ) (hr : 0 < r), r = (3 : ℝ) ^ (K0 + p.1) →
        aux_prop_growth_large_root_GrowthAt M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
          (oddGridCenter (0 : SpatialCoordinates d) (3 * (3 : ℝ) ^ (K0 + p.1 + 1) / 3) (triadicHalf 1) p.2) r hr
          t alpha (env n omega) (fun N => Kc p N (env n omega)) := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro p
    exact (hmp n).quasiMeasurePreserving.ae (hKae p)
  filter_upwards [hall, hconv] with omega hom hcv
  intro k
  refine calib_h0_large_cell_bounds_of_growth hd 0 (3 * (3 : ℝ) ^ (K0 + k + 1) / 3) (by positivity) _ t alpha ht ha ?_
  intro cidx
  obtain ⟨Z, hZ⟩ := hcv (k, cidx)
  obtain ⟨B, hB⟩ := (hZ.bddAbove_range)
  have hR : (0 : ℝ) < 3 * (3 : ℝ) ^ (K0 + k + 1) / 3 := by positivity
  have hc : (0 : ℝ) < 2 * ((triadicHalf 1 : ℕ) : ℝ) + 1 := by positivity
  have hcr : (0 : ℝ) < (3 * (3 : ℝ) ^ (K0 + k + 1) / 3) / (2 * ((triadicHalf 1 : ℕ) : ℝ) + 1) := div_pos hR hc
  have h3 : (2 * ((triadicHalf 1 : ℕ) : ℝ) + 1) = 3 := by
    have h := two_mul_triadicHalf_add_one 1
    have h' : ((2 * triadicHalf 1 + 1 : ℕ) : ℝ) = ((3 ^ 1 : ℕ) : ℝ) := by rw [h]
    push_cast at h'
    linarith
  have hrj : (3 * (3 : ℝ) ^ (K0 + k + 1) / 3) / (2 * ((triadicHalf 1 : ℕ) : ℝ) + 1) = (3 : ℝ) ^ (K0 + k) := by
    rw [h3, pow_succ]
    field_simp
  refine ⟨fun n => cutoffPositiveCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (env n omega) (N n)
      (oddGridCenter (0 : SpatialCoordinates d) (3 * (3 : ℝ) ^ (K0 + k + 1) / 3) (triadicHalf 1) cidx) hcr,
    fun n => Kc (k, cidx) (N n) (env n omega), B, ?_, ?_, ?_⟩
  · intro n
    exact aux_prop_growth_large_root_cutoffPositiveCoefficient_val_ae M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
      (env n omega) (N n) _ hcr
  · intro n
    exact hB ⟨n, rfl⟩
  · intro n F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    exact hom n (k, cidx) _ hcr hrj (N n) F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve

end
end SubdiffusiveProcess.Paper
