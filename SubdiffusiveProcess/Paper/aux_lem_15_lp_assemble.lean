module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.Paper

/--
Final moment assembly for `lem_15`.

Scope and inputs:

- the original and resampled responses and four response terms live on
  one probability space;
- the `3p` MemLp bounds and numerical bounds for the growth and response
  factors are explicit inputs, with the moment order fixed before the data;
- the four individual (L^p) bounds are explicit proof-step inputs;
- the finite-sum identity and triangle/Hölder assembly are concluded,
  yielding the exact decay exponent (b/(8\log 3));
- no influence estimate is assumed as a parent hypothesis. -/
theorem aux_lem_15_lp_assemble
    (d : ℕ) (_hd : 2 ≤ d) (t p B delta Cterm : ℝ)
    (ht_lower : (d : ℝ) - 1 < t) (ht_upper : t < (d : ℝ))
    (hp : 2 ≤ p) (_hB : 0 ≤ B) (hdelta : 0 < delta)
    (hCterm : 0 < Cterm)
    (_hb : 0 < t * (t - (d : ℝ) + 1) / (t + 1))
    (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K Y Y' : Ω → ℝ) (D : Fin 4 → Ω → ℝ) (j : ℕ)
    (_hKmeas : AEStronglyMeasurable K μ)
    (_hYmeas : AEStronglyMeasurable Y μ)
    (_hY'meas : AEStronglyMeasurable Y' μ)
    (_hKmem : MemLp K (ENNReal.ofReal (3 * p)) μ)
    (_hYmem : MemLp Y (ENNReal.ofReal (3 * p)) μ)
    (_hY'mem : MemLp Y' (ENNReal.ofReal (3 * p)) μ)
    (_hKbound : eLpNorm K (ENNReal.ofReal (3 * p)) μ ≤ ENNReal.ofReal B)
    (_hYbound : eLpNorm Y (ENNReal.ofReal (3 * p)) μ ≤ ENNReal.ofReal B)
    (_hY'bound : eLpNorm Y' (ENNReal.ofReal (3 * p)) μ ≤ ENNReal.ofReal B)
    (hdecomp : ∀ omega, Y omega - Y' omega = ∑ i : Fin 4, D i omega)
    (hterms : ∀ i : Fin 4,
      AEStronglyMeasurable (D i) μ ∧
      eLpNorm (D i) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal
          (Cterm * delta *
            (3 : ℝ) ^ (-(3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) *
              (j : ℝ)))) :
    ∃ C : ℝ, 0 < C ∧
      eLpNorm (fun omega => Y omega - Y' omega)
          (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal
          (C * delta *
            (3 : ℝ) ^
              (-(t * (t - (d : ℝ) + 1) / (t + 1) /
                  (8 * Real.log 3)) * (j : ℝ)))
    := by
  let a : ℝ := t * (t - (d : ℝ) + 1) / (t + 1)
  let q₁ : ℝ := -(3 * a / 8) * (j : ℝ)
  let q₂ : ℝ := -(a / (8 * Real.log 3)) * (j : ℝ)
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hsum :=
    eLpNorm_sum_le (μ := μ) (p := ENNReal.ofReal p) (f := D)
      (s := Finset.univ) hp1
  have hsum_bound :
      eLpNorm (∑ i : Fin 4, D i) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (4 * (Cterm * delta * (3 : ℝ) ^ q₁)) := by
    calc
      eLpNorm (∑ i : Fin 4, D i) (ENNReal.ofReal p) μ ≤
          ∑ i : Fin 4, eLpNorm (D i) (ENNReal.ofReal p) μ := by
            simpa using hsum
      _ ≤ ∑ i : Fin 4,
          ENNReal.ofReal (Cterm * delta * (3 : ℝ) ^ q₁) := by
            exact Finset.sum_le_sum (fun i _ => by
              simpa [a, q₁] using (hterms i).2)
      _ = ENNReal.ofReal (4 * (Cterm * delta * (3 : ℝ) ^ q₁)) := by
        rw [Fin.sum_univ_four]
        let x : ℝ := Cterm * delta * (3 : ℝ) ^ q₁
        have hx : 0 ≤ x := by
          dsimp [x]
          positivity
        calc
          ENNReal.ofReal x + ENNReal.ofReal x + ENNReal.ofReal x + ENNReal.ofReal x =
              4 • ENNReal.ofReal x := by
                rw [nsmul_eq_mul]
                ring
          _ = ENNReal.ofReal (4 • x) := by
            rw [ENNReal.ofReal_nsmul]
          _ = ENNReal.ofReal (4 * x) := by norm_num [nsmul_eq_mul]
          _ = ENNReal.ofReal (4 * (Cterm * delta * (3 : ℝ) ^ q₁)) := by
            rfl
  have hrpow :
      (3 : ℝ) ^ q₁ = (3 : ℝ) ^ (q₁ - q₂) * (3 : ℝ) ^ q₂ := by
    calc
      (3 : ℝ) ^ q₁ = (3 : ℝ) ^ ((q₁ - q₂) + q₂) := by
        congr 1
        ring
      _ = (3 : ℝ) ^ (q₁ - q₂) * (3 : ℝ) ^ q₂ := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  have hreal :
      4 * (Cterm * delta * (3 : ℝ) ^ q₁) =
        (4 * Cterm * (3 : ℝ) ^ (q₁ - q₂)) * delta * (3 : ℝ) ^ q₂ := by
    rw [hrpow]
    ring
  refine ⟨4 * Cterm * (3 : ℝ) ^ (q₁ - q₂), ?_, ?_⟩
  · positivity
  · change eLpNorm (fun omega => Y omega - Y' omega) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal
        ((4 * Cterm * (3 : ℝ) ^ (q₁ - q₂)) * delta * (3 : ℝ) ^ q₂)
    rw [show (fun omega => Y omega - Y' omega) = ∑ i : Fin 4, D i by
      funext omega
      exact hdecomp omega]
    calc
      eLpNorm (∑ i : Fin 4, D i) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (4 * (Cterm * delta * (3 : ℝ) ^ q₁)) := hsum_bound
      _ = ENNReal.ofReal
          ((4 * Cterm * (3 : ℝ) ^ (q₁ - q₂)) * delta * (3 : ℝ) ^ q₂) := by
            rw [hreal]

end SubdiffusiveProcess.Paper
