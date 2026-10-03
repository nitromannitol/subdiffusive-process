module

public import SubdiffusiveProcess.Probability.MeshEnvelope
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace SubdiffusiveProcess

/-- An explicit exponential Lq-norm growth rate is compensated at the mesh depth before applying the uniform envelope. The finite-moment margin includes q times that growth rate; no independence or model reference-average estimate is assumed as a theorem of M. -/
theorem exists_triadic_mesh_envelope_of_exponential_growth
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (k : ℕ → ℕ) (d b : ℕ) (C η γ : ℝ) (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) (hqt : q ≠ ∞)
    (hgap : (d : ℝ) * Real.log 3 + q.toReal * γ <
      q.toReal * η * Real.log 3)
    (hcard : ∀ n : ℕ, (k n : ℝ) ≤
      C * ((n : ℝ) + 1) ^ b * (3 : ℝ) ^ ((d : ℝ) * n))
    (Z : ∀ n : ℕ, Fin (k n) → Ω → ℝ)
    (hZ : ∀ n i, AEStronglyMeasurable (Z n i) μ)
    (K : ℝ≥0∞) (hKt : K ≠ ∞)
    (hK : ∀ n i, eLpNorm (Z n i) q μ ≤
      K * ENNReal.ofReal (Real.exp (γ * n))) :
    ∃ W : Ω → ℝ, MemLp W p μ ∧
      (∀ᵐ ω ∂μ, 0 ≤ W ω ∧ ∀ n : ℕ, ∀ i : Fin (k n),
        |Z n i ω| ≤ W ω * (3 : ℝ) ^ (η * n)) ∧
      eLpNorm W p μ ≤
        (∑' n : ℕ, ENNReal.ofReal
          (Real.exp (γ * n) * (3 : ℝ) ^ (-η * n)) *
          (k n : ℝ≥0∞) ^ (1 / q.toReal)) * K := by
  classical
  have hlog : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  let η' : ℝ := η - γ / Real.log 3
  let Z' : ∀ n : ℕ, Fin (k n) → Ω → ℝ :=
    fun n i ω => Real.exp (-γ * n) * Z n i ω
  have hgap' : (d : ℝ) < q.toReal * η' := by
    have heta : q.toReal * η' =
        (q.toReal * η * Real.log 3 - q.toReal * γ) / Real.log 3 := by
      dsimp [η']
      field_simp
    rw [heta]
    apply (lt_div_iff₀ hlog).2
    nlinarith
  have hZ' : ∀ n i, AEStronglyMeasurable (Z' n i) μ := by
    intro n i
    exact (hZ n i).const_mul _
  have hK' : ∀ n i, eLpNorm (Z' n i) q μ ≤ K := by
    intro n i
    rw [show Z' n i = (Real.exp (-γ * n)) • Z n i by
      funext ω
      simp [Z']]
    rw [eLpNorm_const_smul]
    rw [Real.enorm_of_nonneg (Real.exp_pos _).le]
    calc
      ENNReal.ofReal (Real.exp (-γ * n)) * eLpNorm (Z n i) q μ ≤
          ENNReal.ofReal (Real.exp (-γ * n)) *
            (K * ENNReal.ofReal (Real.exp (γ * n))) :=
        mul_le_mul_right (hK n i) _
      _ = K := by
        rw [show ENNReal.ofReal (Real.exp (-γ * n)) *
            (K * ENNReal.ofReal (Real.exp (γ * n))) =
            K * (ENNReal.ofReal (Real.exp (-γ * n)) *
              ENNReal.ofReal (Real.exp (γ * n))) by ac_rfl,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        rw [← Real.exp_add]
        have : -γ * (n : ℝ) + γ * n = 0 := by ring
        rw [this]
        simp
  obtain ⟨W, hWmem, hWdom, hWnorm⟩ :=
    exists_triadic_mesh_envelope μ k d b C η' hC hp hpq hqt hgap' hcard Z' hZ' K hKt hK'
  refine ⟨W, hWmem, ?_, ?_⟩
  · filter_upwards [hWdom] with ω hω
    refine ⟨hω.1, fun n i => ?_⟩
    have h := hω.2 n i
    have heq : Real.exp (γ * n) * (3 : ℝ) ^ (η' * n) =
        (3 : ℝ) ^ (η * n) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.exp_add]
      congr 1
      dsimp [η']
      field_simp
      ring
    calc
      |Z n i ω| = Real.exp (γ * n) * |Z' n i ω| := by
        simp only [Z', abs_mul, abs_of_pos (Real.exp_pos _)]
        rw [← mul_assoc, ← Real.exp_add]
        have : γ * (n : ℝ) + -γ * n = 0 := by ring
        rw [this]
        simp
      _ ≤ Real.exp (γ * n) * (W ω * (3 : ℝ) ^ (η' * n)) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = W ω * (Real.exp (γ * n) * (3 : ℝ) ^ (η' * n)) := by ring
      _ = W ω * (3 : ℝ) ^ (η * n) := by rw [heq]
  · calc
      eLpNorm W p μ ≤
          (∑' n : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-η' * n)) *
            (k n : ℝ≥0∞) ^ (1 / q.toReal)) * K := hWnorm
      _ = (∑' n : ℕ, ENNReal.ofReal
          (Real.exp (γ * n) * (3 : ℝ) ^ (-η * n)) *
          (k n : ℝ≥0∞) ^ (1 / q.toReal)) * K := by
        congr 1
        exact tsum_congr fun n => by
          congr 1
          apply congrArg ENNReal.ofReal
          rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
            Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.exp_add]
          congr 1
          dsimp [η']
          field_simp
          ring

end SubdiffusiveProcess
