module

public import SubdiffusiveProcess.ResponseMoments.RelativeResponseSlopes
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# From per-slope concentration to matrix-entry concentration

Let `A, B : Ω → Matrix (Fin d) (Fin d) ℝ` be symmetric matrix-valued random variables and
`c : ℝ`. The entries of `(tr A)⁻¹ • (B - c • A)` are polarization combinations
(`RelSlopes.entry_polarization`) of the three relative responses on the slopes `e_i + e_j`, `e_i`, `e_j`.
Per-slope centered and conditional-expectation `L^q` bounds therefore give entrywise bounds
(`entry_moment`, `entry_band`) and, summed over the `d²` entries, the matrix-norm bounds
`relative_concentration_matrix_bounds` (constant `3 d²`).
-/

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open _root_.SubdiffusiveProcess.ResponseMoments.RelSlopes

namespace SubdiffusiveProcess.ResponseMoments.RelSlopes
noncomputable section

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

theorem ennreal_three_mul (d : ℕ) (X : ℝ) :
    (d : ℝ≥0∞) * ((d : ℝ≥0∞) * (ENNReal.ofReal X + ENNReal.ofReal X + ENNReal.ofReal X)) =
      ENNReal.ofReal (3 * ((d : ℝ) * (d : ℝ)) * X) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  ring

/-- A three-term combination is controlled by the sum of the three `L^q` norms. -/
theorem three_le (P : Measure Ω) (q : ℝ≥0∞) (hq : 1 ≤ q)
    (f1 f2 f3 : Ω → ℝ) (h1 : AEStronglyMeasurable f1 P) (h2 : AEStronglyMeasurable f2 P)
    (h3 : AEStronglyMeasurable f3 P) :
    eLpNorm (fun ω => (f1 ω - f2 ω - f3 ω) / 2) q P ≤
      eLpNorm f1 q P + eLpNorm f2 q P + eLpNorm f3 q P := by
  have hmono : eLpNorm (fun ω => (f1 ω - f2 ω - f3 ω) / 2) q P ≤
      eLpNorm (f1 - f2 - f3) q P := by
    apply eLpNorm_mono (((h1.sub h2).sub h3).div₀ (g := fun _ => (2 : ℝ)) aestronglyMeasurable_const)
    intro ω
    simp only [Real.norm_eq_abs, Pi.div_apply, Pi.sub_apply, abs_div, abs_two]
    have := abs_nonneg (f1 ω - f2 ω - f3 ω)
    linarith
  refine hmono.trans ?_
  calc eLpNorm (f1 - f2 - f3) q P ≤ eLpNorm (f1 - f2) q P + eLpNorm f3 q P :=
        eLpNorm_sub_le hq
    _ ≤ eLpNorm f1 q P + eLpNorm f2 q P + eLpNorm f3 q P := by
        gcongr
        exact eLpNorm_sub_le hq

/-- The double entry sum of absolute values is controlled entrywise. -/
theorem double_sum_le {d : ℕ} (P : Measure Ω) (q : ℝ≥0∞) (hq : 1 ≤ q)
    (F : Fin d → Fin d → Ω → ℝ) (hF : ∀ i j, AEStronglyMeasurable (F i j) P)
    (X : ℝ≥0∞) (hX : ∀ i j, eLpNorm (F i j) q P ≤ X) :
    eLpNorm (fun ω => ∑ i : Fin d, ∑ j : Fin d, |F i j ω|) q P ≤ (d : ℝ≥0∞) * (d * X) := by
  have hrow : ∀ i, AEStronglyMeasurable (fun ω => ∑ j : Fin d, |F i j ω|) P := by
    intro i
    have : (fun ω => ∑ j : Fin d, |F i j ω|) = ∑ j : Fin d, (fun ω => |F i j ω|) := by
      funext ω; simp
    rw [this]
    exact Finset.aestronglyMeasurable_sum _ fun j _ => (hF i j).norm
  have hsum : (fun ω => ∑ i : Fin d, ∑ j : Fin d, |F i j ω|) =
      ∑ i : Fin d, (fun ω => ∑ j : Fin d, |F i j ω|) := by
    funext ω; simp
  rw [hsum]
  refine (eLpNorm_sum_le hq).trans ?_
  have hrowle : ∀ i, eLpNorm (fun ω => ∑ j : Fin d, |F i j ω|) q P ≤ d * X := by
    intro i
    have : (fun ω => ∑ j : Fin d, |F i j ω|) = ∑ j : Fin d, (fun ω => |F i j ω|) := by
      funext ω; simp
    rw [this]
    refine (eLpNorm_sum_le hq).trans ?_
    calc ∑ j : Fin d, eLpNorm (fun ω => |F i j ω|) q P
        ≤ ∑ _j : Fin d, X := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h := eLpNorm_norm (p := q) (μ := P) (F i j) (hF i j)
          simp only [Real.norm_eq_abs] at h
          rw [h]
          exact hX i j
      _ = d * X := by simp
  calc ∑ i : Fin d, eLpNorm (fun ω => ∑ j : Fin d, |F i j ω|) q P
      ≤ ∑ _i : Fin d, (d : ℝ≥0∞) * X := Finset.sum_le_sum fun i _ => hrowle i
    _ = (d : ℝ≥0∞) * (d * X) := by simp

/-- Conditional expectation commutes with the three-term polarization combination. -/
theorem three_condExp (P : Measure Ω) (mB : MeasurableSpace Ω)
    (f1 f2 f3 : Ω → ℝ) (h1 : Integrable f1 P) (h2 : Integrable f2 P)
    (h3 : Integrable f3 P) :
    (fun ω => (f1 ω - f2 ω - f3 ω) / 2 -
        (P[fun ω' => (f1 ω' - f2 ω' - f3 ω') / 2 | mB]) ω) =ᵐ[P]
      fun ω => ((f1 ω - (P[f1 | mB]) ω) - (f2 ω - (P[f2 | mB]) ω) -
        (f3 ω - (P[f3 | mB]) ω)) / 2 := by
  have hfun : (fun ω' => (f1 ω' - f2 ω' - f3 ω') / 2) = (1 / 2 : ℝ) • (f1 - f2 - f3) := by
    funext ω; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have hc : P[fun ω' => (f1 ω' - f2 ω' - f3 ω') / 2 | mB] =ᵐ[P]
      (1 / 2 : ℝ) • (P[f1 | mB] - P[f2 | mB] - P[f3 | mB]) := by
    rw [hfun]
    refine (condExp_smul (1 / 2 : ℝ) (f1 - f2 - f3) mB).trans ?_
    have hs1 := condExp_sub (h1.sub h2) h3 mB
    have hs2 := condExp_sub h1 h2 mB
    filter_upwards [hs1, hs2] with ω e1 e2
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e1 e2 ⊢
    rw [e1, e2]
  filter_upwards [hc] with ω hω
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hω
  rw [hω]
  ring

theorem double_sum_aesStronglyMeasurable (P : Measure Ω)
    (F : Fin d → Fin d → Ω → ℝ) (hF : ∀ i j, AEStronglyMeasurable (F i j) P) :
    AEStronglyMeasurable (fun ω => ∑ i : Fin d, ∑ j : Fin d, |F i j ω|) P := by
  have hsum : (fun ω => ∑ i : Fin d, ∑ j : Fin d, |F i j ω|) =
      ∑ i : Fin d, ∑ j : Fin d, (fun ω => |F i j ω|) := by
    funext ω; simp
  rw [hsum]
  exact Finset.aestronglyMeasurable_sum _ fun i _ =>
    Finset.aestronglyMeasurable_sum _ fun j _ => (hF i j).norm

/-- Per-entry moment bound from the per-slope centred bounds and the mean-zero clause. -/
theorem entry_moment (P : Measure Ω)
    (A B : Ω → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ ω, (A ω).transpose = A ω)
    (hB : ∀ ω, (B ω).transpose = B ω) (c : ℝ) (q : ℝ≥0∞) (hq : 1 ≤ q) (X0 : ℝ)
    (i j : Fin d)
    (hint : ∀ v : Fin d → ℝ, IsAffineSlope v →
      Integrable (fun ω => relativeResponse (A ω) (B ω) c v) P)
    (hmean : ∫ ω, ((Matrix.trace (A ω))⁻¹ • (B ω - c • A ω)) i j ∂P = 0)
    (hbd : ∀ v : Fin d → ℝ, IsAffineSlope v →
      eLpNorm (fun ω => relativeResponse (A ω) (B ω) c v -
          ∫ ω', relativeResponse (A ω') (B ω') c v ∂P) q P ≤ ENNReal.ofReal X0) :
    eLpNorm (fun ω => ((Matrix.trace (A ω))⁻¹ • (B ω - c • A ω)) i j) q P ≤
      ENNReal.ofReal X0 + ENNReal.ofReal X0 + ENNReal.ofReal X0 := by
  have s1 : IsAffineSlope (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) :=
    Or.inr ⟨i, j, rfl⟩
  have s2 : IsAffineSlope (Pi.single i (1 : ℝ)) := Or.inl ⟨i, rfl⟩
  have s3 : IsAffineSlope (Pi.single j (1 : ℝ)) := Or.inl ⟨j, rfl⟩
  set f1 := fun ω => relativeResponse (A ω) (B ω) c (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))
    with hf1
  set f2 := fun ω => relativeResponse (A ω) (B ω) c (Pi.single i (1 : ℝ)) with hf2
  set f3 := fun ω => relativeResponse (A ω) (B ω) c (Pi.single j (1 : ℝ)) with hf3
  have hpol : ∀ ω, ((Matrix.trace (A ω))⁻¹ • (B ω - c • A ω)) i j =
      (f1 ω - f2 ω - f3 ω) / 2 := fun ω => entry_polarization (A ω) (B ω) (hA ω) (hB ω) c i j
  have hI1 := hint _ s1
  have hI2 := hint _ s2
  have hI3 := hint _ s3
  have hmean' : (∫ ω, f1 ω ∂P) - (∫ ω, f2 ω ∂P) - (∫ ω, f3 ω ∂P) = 0 := by
    have h12 : Integrable (fun ω => f1 ω - f2 ω) P := hI1.sub hI2
    have h := hmean
    rw [integral_congr_ae (Filter.Eventually.of_forall hpol), integral_div,
      integral_sub h12 hI3, integral_sub hI1 hI2] at h
    linarith
  have hfun : (fun ω => ((Matrix.trace (A ω))⁻¹ • (B ω - c • A ω)) i j) =
      fun ω => ((f1 ω - ∫ ω', f1 ω' ∂P) - (f2 ω - ∫ ω', f2 ω' ∂P) -
        (f3 ω - ∫ ω', f3 ω' ∂P)) / 2 := by
    funext ω
    rw [hpol ω]
    linarith
  rw [hfun]
  refine (three_le P q hq _ _ _
    (hI1.aestronglyMeasurable.sub aestronglyMeasurable_const)
    (hI2.aestronglyMeasurable.sub aestronglyMeasurable_const)
    (hI3.aestronglyMeasurable.sub aestronglyMeasurable_const)).trans ?_
  gcongr
  · exact hbd _ s1
  · exact hbd _ s2
  · exact hbd _ s3

/-- Per-entry band bound from the per-slope band bounds. -/
theorem entry_band (P : Measure Ω)
    (A B : Ω → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ ω, (A ω).transpose = A ω)
    (hB : ∀ ω, (B ω).transpose = B ω) (c : ℝ) (q : ℝ≥0∞) (hq : 1 ≤ q) (Y : ℝ)
    (mBs : ℕ → MeasurableSpace Ω) (n : ℕ) (i j : Fin d)
    (hint : ∀ v : Fin d → ℝ, IsAffineSlope v →
      Integrable (fun ω => relativeResponse (A ω) (B ω) c v) P)
    (hbd : ∀ v : Fin d → ℝ, IsAffineSlope v →
      eLpNorm (fun ω => relativeResponse (A ω) (B ω) c v -
          (P[fun ω' => relativeResponse (A ω') (B ω') c v | mBs n]) ω) q P ≤
        ENNReal.ofReal Y) :
    eLpNorm (fun ω => ((Matrix.trace (A ω))⁻¹ • (B ω - c • A ω)) i j -
        (P[fun ω' => ((Matrix.trace (A ω'))⁻¹ • (B ω' - c • A ω')) i j | mBs n]) ω) q P ≤
      ENNReal.ofReal Y + ENNReal.ofReal Y + ENNReal.ofReal Y := by
  have s1 : IsAffineSlope (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) :=
    Or.inr ⟨i, j, rfl⟩
  have s2 : IsAffineSlope (Pi.single i (1 : ℝ)) := Or.inl ⟨i, rfl⟩
  have s3 : IsAffineSlope (Pi.single j (1 : ℝ)) := Or.inl ⟨j, rfl⟩
  set f1 := fun ω => relativeResponse (A ω) (B ω) c (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))
    with hf1
  set f2 := fun ω => relativeResponse (A ω) (B ω) c (Pi.single i (1 : ℝ)) with hf2
  set f3 := fun ω => relativeResponse (A ω) (B ω) c (Pi.single j (1 : ℝ)) with hf3
  have hpol : ∀ ω, ((Matrix.trace (A ω))⁻¹ • (B ω - c • A ω)) i j =
      (f1 ω - f2 ω - f3 ω) / 2 := fun ω =>
    entry_polarization (A ω) (B ω) (hA ω) (hB ω) c i j
  have hI1 := hint _ s1
  have hI2 := hint _ s2
  have hI3 := hint _ s3
  simp only [hpol]
  rw [eLpNorm_congr_ae (three_condExp P (mBs n) f1 f2 f3 hI1 hI2 hI3)]
  refine (three_le P q hq _ _ _
    (hI1.aestronglyMeasurable.sub integrable_condExp.aestronglyMeasurable)
    (hI2.aestronglyMeasurable.sub integrable_condExp.aestronglyMeasurable)
    (hI3.aestronglyMeasurable.sub integrable_condExp.aestronglyMeasurable)).trans ?_
  gcongr
  · exact hbd _ s1
  · exact hbd _ s2
  · exact hbd _ s3

/-- Matrix-norm bounds (`L^{q0}`, `q0 ≤ q`, `1 ≤ q`) for `B_c = (tr A)⁻¹ (B - c A)` and for its
deviation from conditional expectations onto σ-fields `mB n`, from the per-slope bounds. -/
theorem relative_concentration_matrix_bounds (P : Measure Ω) [IsProbabilityMeasure P]
    (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hsymAE : ∀ ω, (AE ω).transpose = AE ω) (hsymAF : ∀ ω, (AF ω).transpose = AF ω) (c : ℝ)
    (q q0 : ℝ≥0∞) (hq : 1 ≤ q) (hq0 : q0 ≤ q) (X0 : ℝ) (X : ℕ → ℝ)
    (mB : ℕ → MeasurableSpace Ω)
    (hint : ∀ v : Fin d → ℝ, IsAffineSlope v →
      Integrable (fun ω => relativeResponse (AE ω) (AF ω) c v) P)
    (hmean : ∀ i j : Fin d,
      ∫ ω, ((Matrix.trace (AE ω))⁻¹ • (AF ω - c • AE ω)) i j ∂P = 0)
    (hcent : ∀ v : Fin d → ℝ, IsAffineSlope v →
      eLpNorm (fun ω => relativeResponse (AE ω) (AF ω) c v -
          ∫ ω', relativeResponse (AE ω') (AF ω') c v ∂P) q P ≤ ENNReal.ofReal X0)
    (hband : ∀ v : Fin d → ℝ, IsAffineSlope v → ∀ n : ℕ,
      eLpNorm (fun ω => relativeResponse (AE ω) (AF ω) c v -
          (P[fun ω' => relativeResponse (AE ω') (AF ω') c v | mB n]) ω) q P ≤
        ENNReal.ofReal (X n)) :
    eLpNorm (fun ω => ∑ i : Fin d, ∑ j : Fin d,
        |((Matrix.trace (AE ω))⁻¹ • (AF ω - c • AE ω)) i j|) q0 P ≤
      ENNReal.ofReal (3 * ((d : ℝ) * (d : ℝ)) * X0) ∧
    ∀ n : ℕ, eLpNorm (fun ω => ∑ i : Fin d, ∑ j : Fin d,
        |((Matrix.trace (AE ω))⁻¹ • (AF ω - c • AE ω)) i j -
          (P[fun ω' => ((Matrix.trace (AE ω'))⁻¹ • (AF ω' - c • AE ω')) i j | mB n]) ω|) q0 P ≤
      ENNReal.ofReal (3 * ((d : ℝ) * (d : ℝ)) * X n) := by
  have hBint : ∀ i j : Fin d,
      Integrable (fun ω => ((Matrix.trace (AE ω))⁻¹ • (AF ω - c • AE ω)) i j) P := by
    intro i j
    have h := (((hint _ (Or.inr ⟨i, j, rfl⟩)).sub
      (hint _ (Or.inl ⟨i, rfl⟩))).sub (hint _ (Or.inl ⟨j, rfl⟩))).div_const 2
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply]
    exact (entry_polarization (AE ω) (AF ω) (hsymAE ω) (hsymAF ω) c i j).symm
  constructor
  · have hentry : ∀ i j : Fin d,
        eLpNorm (fun ω => ((Matrix.trace (AE ω))⁻¹ • (AF ω - c • AE ω)) i j) q P ≤
          ENNReal.ofReal X0 + ENNReal.ofReal X0 + ENNReal.ofReal X0 := fun i j =>
      entry_moment P AE AF hsymAE hsymAF c q hq X0 i j hint (hmean i j) hcent
    have hF : ∀ i j : Fin d,
        AEStronglyMeasurable (fun ω => ((Matrix.trace (AE ω))⁻¹ • (AF ω - c • AE ω)) i j) P :=
      fun i j => (hBint i j).aestronglyMeasurable
    refine (eLpNorm_le_eLpNorm_of_exponent_le hq0).trans ?_
    refine (double_sum_le P q hq _ hF _ hentry).trans ?_
    rw [ennreal_three_mul]
  · intro n
    have hentry : ∀ i j : Fin d,
        eLpNorm (fun ω => ((Matrix.trace (AE ω))⁻¹ • (AF ω - c • AE ω)) i j -
          (P[fun ω' => ((Matrix.trace (AE ω'))⁻¹ • (AF ω' - c • AE ω')) i j | mB n]) ω) q P ≤
        ENNReal.ofReal (X n) + ENNReal.ofReal (X n) + ENNReal.ofReal (X n) := fun i j =>
      entry_band P AE AF hsymAE hsymAF c q hq (X n) mB n i j hint (hband · · n)
    have hF : ∀ i j : Fin d,
        AEStronglyMeasurable (fun ω => ((Matrix.trace (AE ω))⁻¹ • (AF ω - c • AE ω)) i j -
          (P[fun ω' => ((Matrix.trace (AE ω'))⁻¹ • (AF ω' - c • AE ω')) i j | mB n]) ω) P :=
      fun i j => (hBint i j).aestronglyMeasurable.sub integrable_condExp.aestronglyMeasurable
    refine (eLpNorm_le_eLpNorm_of_exponent_le hq0).trans ?_
    refine (double_sum_le P q hq _ hF _ hentry).trans ?_
    rw [ennreal_three_mul]

end
end SubdiffusiveProcess.ResponseMoments.RelSlopes
