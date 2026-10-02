import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Geometry.TriadicGridScale
import SubdiffusiveProcess.Lane4.CutoffCoefficientRepresentative

/-! This file transfers a uniform absolute-grid coefficient cap to each sufficiently deep root-grid cell; it does not derive the cap premise. -/
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped Topology ENNReal
noncomputable section
namespace Paper
/-- Transports a cutoff coefficient cap across equal center and side charts. -/
theorem aux_goodext_root_grid_coefficient_cap_chart_congr
    {d : ℕ} (I : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (env : ℕ → BilateralField d) (N : ℕ → ℕ)
    (beta eta K : ℝ) {w₁ w₂ : SpatialCoordinates d} {r₁ r₂ : ℝ}
    (n : ℕ) (hw : w₁ = w₂) (hr : r₁ = r₂)
    (hpos₁ : 0 < r₁) (hpos₂ : 0 < r₂)
    (hcap : I.Lam w₁ r₁ hpos₁
      (cutoffPositiveCoefficient M H (env n) (N n) w₁ hpos₁)
      w₁ r₁ ((beta - 1 / 2) / 4) 2 ≤ K * r₁ ^ (-eta)) :
    I.Lam w₂ r₂ hpos₂
      (cutoffPositiveCoefficient M H (env n) (N n) w₂ hpos₂)
      w₂ r₂ ((beta - 1 / 2) / 4) 2 ≤ K * r₂ ^ (-eta) := by
  cases hw
  cases hr
  exact hcap

/-- A guarded absolute-grid coefficient cap holds eventually on every sufficiently deep root-grid cell. -/
theorem goodext_root_grid_coefficient_cap
    {d : ℕ} (I : in_J d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (env : ℕ → BilateralField d) (N : ℕ → ℕ) (hN : StrictMono N)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (ell : ℤ) (hScale : R = (3 : ℝ) ^ ell)
    (beta eta K : ℝ)
    (hCap : ∀ (n k : ℕ) (idx : Fin d → ℤ), k ≤ N n →
      let wc : SpatialCoordinates d := fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * idx i
      let rc : ℝ := (3 : ℝ) ^ (-(k : ℤ))
      ∀ hc : 0 < rc,
      (centeredCube wc rc hc : Set (SpatialCoordinates d)) ⊆
        (centeredCube z R hR : Set (SpatialCoordinates d)) →
      I.Lam wc rc hc (cutoffPositiveCoefficient M H (env n) (N n) wc hc)
        wc rc ((beta - 1 / 2) / 4) 2 +
        (I.lam wc rc hc (cutoffPositiveCoefficient M H (env n) (N n) wc hc)
          wc rc ((beta - 1 / 2) / 4) 2)⁻¹ ≤ K * rc ^ (-eta)) :
    ∀ q : {q : TriadicGridLabel d // ell.toNat ≤ q.1}, ∀ᶠ n in atTop,
      I.Lam (triadicGridCenter z R q.val) (triadicGridSide R q.val) (triadicGridSide_pos hR q.val)
        (cutoffPositiveCoefficient M H (env n) (N n)
          (triadicGridCenter z R q.val) (triadicGridSide_pos hR q.val))
        (triadicGridCenter z R q.val) (triadicGridSide R q.val) ((beta - 1 / 2) / 4) 2 ≤
          K * (triadicGridSide R q.val) ^ (-eta) := by
  have hNtoTop : Tendsto N atTop atTop := hN.tendsto_atTop
  intro q
  obtain ⟨k, hSide, hCenter⟩ :=
    triadicGrid_absolute_level z R ell hScale q.val q.property
  let idx : Fin d → ℤ := fun i =>
    ((q.val.2 i).val : ℤ) - (triadicHalf q.val.1 : ℤ)
  let wc : SpatialCoordinates d := fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * idx i
  let rc : ℝ := (3 : ℝ) ^ (-(k : ℤ))
  have hcenter : triadicGridCenter z R q.val = wc := by
    dsimp only [wc, idx]
    simp only [Int.cast_sub]
    exact hCenter
  have hside : triadicGridSide R q.val = rc := hSide
  have hrc : 0 < rc := by
    rw [← hside]
    exact triadicGridSide_pos hR q.val
  have hcontain : (centeredCube wc rc hrc : Set (SpatialCoordinates d)) ⊆
      centeredCube z R hR := by
    simpa only [triadicGridCell, hcenter, hside] using
      (triadicGridCell_subset z hR q.val)
  filter_upwards [hNtoTop.eventually_ge_atTop k] with n hn
  have hfull := hCap n k idx hn hrc hcontain
  have hInv : 0 ≤
      (I.lam wc rc hrc
        (cutoffPositiveCoefficient M H (env n) (N n) wc hrc)
        wc rc ((beta - 1 / 2) / 4) 2)⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt (I.lam_pos wc rc hrc
      (cutoffPositiveCoefficient M H (env n) (N n) wc hrc)
      wc rc ((beta - 1 / 2) / 4) 2))
  have hbound :
      I.Lam wc rc hrc
        (cutoffPositiveCoefficient M H (env n) (N n) wc hrc)
        wc rc ((beta - 1 / 2) / 4) 2 ≤ K * rc ^ (-eta) := by
    exact (le_add_of_nonneg_right hInv).trans hfull
  exact aux_goodext_root_grid_coefficient_cap_chart_congr
    I M H env N beta eta K n hcenter.symm hside.symm hrc
    (triadicGridSide_pos hR q.val) hbound
