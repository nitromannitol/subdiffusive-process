module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_point_rate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_inverse_point_rate
public import SubdiffusiveProcess.Paper.reference_oscillation_moments
public import SubdiffusiveProcess.Paper.reference_point_moments
public import SubdiffusiveProcess.Paper.reference_mesh_envelope
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open SubdiffusiveProcess
open scoped ENNReal

namespace SubdiffusiveProcess.Paper

/-- Hölder and the triangle inequality assemble the two point moments and
the oscillation moment into a cell factor bound. -/
theorem aux_shallow_cell_factor_norm
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (q : ℝ) (hq : 1 ≤ q) (E s : Ω → ℝ)
    (hE : MemLp E (ENNReal.ofReal (2 * q)) P)
    (hs : MemLp s (ENNReal.ofReal (2 * q)) P)
    (hsi : MemLp (fun ω => (s ω)⁻¹) (ENNReal.ofReal (2 * q)) P)
    (BE Bs Bsi : ℝ≥0∞)
    (hEB : eLpNorm E (ENNReal.ofReal (2 * q)) P ≤ BE)
    (hsB : eLpNorm s (ENNReal.ofReal (2 * q)) P ≤ Bs)
    (hsiB : eLpNorm (fun ω => (s ω)⁻¹) (ENNReal.ofReal (2 * q)) P ≤ Bsi) :
    eLpNorm (fun ω => E ω * (s ω + (s ω)⁻¹))
        (ENNReal.ofReal q) P ≤ BE * (Bs + Bsi) := by
  have hqq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * q) :=
    by simpa using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ 2 * q by linarith)
  have hsum := eLpNorm_add_le
    (f := s) (g := fun ω => (s ω)⁻¹) (μ := P) hqq
  have hsum' := (show eLpNorm (s + fun ω => (s ω)⁻¹)
      (ENNReal.ofReal (2 * q)) P ≤
      eLpNorm s (ENNReal.ofReal (2 * q)) P +
        eLpNorm (fun ω => (s ω)⁻¹) (ENNReal.ofReal (2 * q)) P by
        simpa only [one_mul] using hsum)
  have hsumB : eLpNorm (fun ω => s ω + (s ω)⁻¹)
      (ENNReal.ofReal (2 * q)) P ≤ Bs + Bsi := by
    simpa only [Pi.add_apply] using! hsum'.trans (add_le_add hsB hsiB)
  exact (aux_reference_mesh_envelope_product q (by linarith)
    hE.aestronglyMeasurable
    (hs.aestronglyMeasurable.add hsi.aestronglyMeasurable)).trans
      (mul_le_mul hEB hsumB (zero_le) (zero_le))

/-- Exact shallow-cell moment from the reference oscillation and paired point
moments. All constants are chosen before the model. -/
theorem lem_as_coarse_shallow_grid_cell_moment
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ Cpoint Rpoint Cinv Rinv Cosc : ℝ,
      0 < Cpoint ∧ 0 < Rpoint ∧ 0 < Cinv ∧ 0 < Rinv ∧ 0 < Cosc ∧
      ∀ delta0 : ℝ, 0 < delta0 → delta0 ≤ 1 →
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω x => H ω x + ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x
        let s : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun N k ω x =>
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
              Real.exp (G k ω x - (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k ω y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k),
              v = |G k ω x - G k ω x'|}
        let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω y => sSup (oscSet k ω y)
        ∀ (N k : ℕ), k ≤ N → ∀ y : SpatialCoordinates d,
          (∀ i, 0 ≤ y i ∧ y i ≤ 1) →
          eLpNorm (fun ω => Real.exp (osc k ω y) *
            (s N k ω y + (s N k ω y)⁻¹))
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal Cosc *
            (ENNReal.ofReal ((Cpoint * Real.exp (Rpoint *
              ((2*q)+(2*q)^2) * M.delta^2 * (k : ℝ))) ^ (2*q)⁻¹) +
             ENNReal.ofReal ((Cinv * Real.exp (Rinv *
              ((2*q)+(2*q)^2) * M.delta^2 * (k : ℝ))) ^ (2*q)⁻¹)) := by
  obtain ⟨Cpoint, Rpoint, hCp, hRp, hp⟩ :=
    lem_as_coarse_shallow_grid_point_rate d hd q hq
  obtain ⟨Cinv, Rinv, hCi, hRi, hi⟩ :=
    lem_as_coarse_shallow_grid_inverse_point_rate d hd q hq
  obtain ⟨Cosc, hCo, ho⟩ :=
    reference_oscillation_moments d hd q hq
  obtain ⟨_, _, _, _, hm⟩ := reference_point_moments d hd q hq
  refine ⟨Cpoint, Rpoint, Cinv, Rinv, Cosc,
    hCp, hRp, hCi, hRi, hCo, ?_⟩
  intro delta0 hd0 hd01 M Rm H hH hMd
  dsimp
  intro N k hkn y hy
  have hyK : y ∈ ({x : SpatialCoordinates d | ∀ i, 0 ≤ x i ∧ x i ≤ 1} :
      Set (SpatialCoordinates d)) := hy
  obtain ⟨hEmem, hEB⟩ := ho delta0 hd0 hd01 M H hH hMd k y hyK
  have hq2 : (2*q : ℝ) ∈ Set.Icc 1 (2*q) := ⟨by linarith, le_rfl⟩
  obtain ⟨_, _, hsmem, hsimem⟩ :=
    hm delta0 hd0 hd01 M Rm H hH hMd (2*q) hq2 N k hkn y hyK
  have hpB := hp delta0 hd0 hd01 M Rm H hH hMd N k hkn y hy
  have hiB := hi delta0 hd0 hd01 M Rm H hH hMd N k hkn y hy
  exact aux_shallow_cell_factor_norm (chaosSampleLaw M).toMeasure q hq
    _ _ hEmem hsmem hsimem _ _ _ hEB hpB hiB

end SubdiffusiveProcess.Paper
