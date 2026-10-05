module

public import SubdiffusiveProcess.Paper.reference_mesh_envelope
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Tactic
public import SubdiffusiveProcess.Analysis.RawLp

@[expose] public section

open MeasureTheory ENNReal
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper

private theorem aux_lem_as_coarse_shallow_grid_factor_product_positive
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ) (hq : 0 < q) {X Z : Ω → ℝ}
    (hX : AEStronglyMeasurable X P) (hZ : AEStronglyMeasurable Z P)
    (BX BZ : ℝ≥0∞)
    (hXB : eLpNorm X (ENNReal.ofReal (2 * q)) P ≤ BX)
    (hZB : eLpNorm Z (ENNReal.ofReal (2 * q)) P ≤ BZ) :
    eLpNorm (fun ω => X ω * (1 + Z ω)) (ENNReal.ofReal q) P ≤
      LpAddConst (ENNReal.ofReal q) * (BX * (1 + BZ)) := by
  have hqne : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  have hPne : P ≠ 0 := by
    intro hzero
    have hmass : P Set.univ = 1 := measure_univ
    rw [hzero] at hmass
    norm_num at hmass
  have hprod := aux_reference_mesh_envelope_product q hq hX hZ
  have hprodB : eLpNorm (fun ω => X ω * Z ω) (ENNReal.ofReal q) P ≤ BX * BZ :=
    hprod.trans (mul_le_mul hXB hZB zero_le zero_le)
  have hXq : eLpNorm X (ENNReal.ofReal q) P ≤ BX := by
    calc
      eLpNorm X (ENNReal.ofReal q) P ≤
          eLpNorm X (ENNReal.ofReal (2 * q)) P := by
            apply eLpNorm_le_eLpNorm_of_exponent_le
            exact ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ BX := hXB
  have hsum := eLpNorm_add_le' (f := X) (g := fun ω => X ω * Z ω) (μ := P) (ENNReal.ofReal q)
  have hgoal' : eLpNorm (fun ω => X ω + X ω * Z ω) (ENNReal.ofReal q) P ≤
      LpAddConst (ENNReal.ofReal q) * (BX * (1 + BZ)) := by
    have hsumB : eLpNorm X (ENNReal.ofReal q) P +
        eLpNorm (fun ω => X ω * Z ω) (ENNReal.ofReal q) P ≤ BX * (1 + BZ) := by
      calc
        _ ≤ BX + BX * BZ := add_le_add hXq hprodB
        _ = BX * (1 + BZ) := by rw [mul_add, mul_one]
    calc
      eLpNorm (fun ω => X ω + X ω * Z ω) (ENNReal.ofReal q) P ≤
          LpAddConst (ENNReal.ofReal q) *
            (eLpNorm X (ENNReal.ofReal q) P +
              eLpNorm (fun ω => X ω * Z ω) (ENNReal.ofReal q) P) := by
            simpa only [Pi.add_apply] using! hsum
      _ ≤ LpAddConst (ENNReal.ofReal q) * (BX * (1 + BZ)) := by
            exact mul_le_mul_right hsumB _
  simpa only [show (fun ω => X ω * (1 + Z ω)) =
      (fun ω => X ω + X ω * Z ω) by funext ω; ring] using hgoal'

/-- Hölder and the probability-space monotonicity of moments control the product
of a shallow-cell coarse factor with one plus a limiting response. -/
theorem lem_as_coarse_shallow_grid_factor_product
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ) (hq : 1 ≤ q) {X Z : Ω → ℝ}
    (hX : AEStronglyMeasurable X P) (hZ : AEStronglyMeasurable Z P)
    (BX BZ : ℝ≥0∞)
    (hXB : eLpNorm X (ENNReal.ofReal (2 * q)) P ≤ BX)
    (hZB : eLpNorm Z (ENNReal.ofReal (2 * q)) P ≤ BZ) :
    eLpNorm (fun ω => X ω * (1 + Z ω)) (ENNReal.ofReal q) P ≤ BX * (1 + BZ) := by
  have hmain := aux_lem_as_coarse_shallow_grid_factor_product_positive P q
    (by linarith) hX hZ BX BZ hXB hZB
  rw [LpAddConst_of_one_le (by
    simpa using ENNReal.ofReal_le_ofReal hq)] at hmain
  simpa using hmain



theorem aux_shallow_zero_ir_product_domination
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ) (hq : 0 < q) (F X Z : Ω → ℝ)
    (hX : AEStronglyMeasurable X P)
    (hZ : AEStronglyMeasurable Z P)
    (hdom : ∀ᵐ ω ∂P, |F ω| ≤ |X ω * Z ω|)
    (BX BZ : ℝ≥0∞)
    (hXB : eLpNorm X (ENNReal.ofReal (2 * q)) P ≤ BX)
    (hZB : eLpNorm Z (ENNReal.ofReal (2 * q)) P ≤ BZ) :
    SubdiffusiveProcess.RawLp.eLpNorm F (ENNReal.ofReal q) P ≤ BX * BZ := by
  calc
    SubdiffusiveProcess.RawLp.eLpNorm F (ENNReal.ofReal q) P ≤
        eLpNorm (fun ω => X ω * Z ω) (ENNReal.ofReal q) P :=
      (SubdiffusiveProcess.RawLp.eLpNorm_mono_ae hdom).trans (SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (hX.mul hZ)).le
    _ ≤ eLpNorm X (ENNReal.ofReal (2 * q)) P *
        eLpNorm Z (ENNReal.ofReal (2 * q)) P :=
      aux_reference_mesh_envelope_product q hq hX hZ
    _ ≤ BX * BZ := mul_le_mul hXB hZB zero_le zero_le

/-- Three-factor Hölder bound for an infrared-free shallow factor times a
shifted response. The dominated target need not be measurable. -/
theorem aux_shallow_zero_ir_triple_product_domination
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ) (hq : 1 ≤ q) (F X Y Z : Ω → ℝ)
    (hX : AEStronglyMeasurable X P)
    (hY : AEStronglyMeasurable Y P)
    (hZ : AEStronglyMeasurable Z P)
    (hdom : ∀ᵐ ω ∂P, |F ω| ≤ |X ω * Y ω * (1 + Z ω)|)
    (BX BY BZ : ℝ≥0∞)
    (hXB : eLpNorm X (ENNReal.ofReal (4 * q)) P ≤ BX)
    (hYB : eLpNorm Y (ENNReal.ofReal (4 * q)) P ≤ BY)
    (hZB : eLpNorm Z (ENNReal.ofReal (2 * q)) P ≤ BZ) :
    SubdiffusiveProcess.RawLp.eLpNorm F (ENNReal.ofReal q) P ≤ BX * BY * (1 + BZ) := by
  have hq2 : 0 < 2 * q := by linarith
  have hXYmeas : AEStronglyMeasurable (fun ω => X ω * Y ω) P := hX.mul hY
  have hXYB : eLpNorm (fun ω => X ω * Y ω)
      (ENNReal.ofReal (2 * q)) P ≤ BX * BY := by
    calc
      eLpNorm (fun ω => X ω * Y ω) (ENNReal.ofReal (2 * q)) P ≤
          eLpNorm X (ENNReal.ofReal (4 * q)) P *
            eLpNorm Y (ENNReal.ofReal (4 * q)) P :=
        by simpa only [show 2 * (2 * q) = 4 * q by ring] using
          aux_reference_mesh_envelope_product (2 * q) hq2 hX hY
      _ ≤ BX * BY := mul_le_mul hXB hYB zero_le zero_le
  have hprod := lem_as_coarse_shallow_grid_factor_product P q hq
    hXYmeas hZ (BX * BY) BZ hXYB hZB
  exact ((SubdiffusiveProcess.RawLp.eLpNorm_mono_ae hdom).trans
    (SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (hXYmeas.mul (aestronglyMeasurable_const.add hZ))).le).trans hprod




end SubdiffusiveProcess.Paper
