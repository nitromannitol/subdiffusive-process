module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section11.CubeH10Poincare
public import Homogenization.Sobolev.CubeEmbedding.LimitFiniteP
public import Homogenization.Sobolev.W1p.FiniteMeasureDowngrade

@[expose] public section

/-!
# Finite-exponent Sobolev for zero-trace cube functions

Finite-measure Hölder reduces the input exponent to `2`. Scale-explicit
Dirichlet Poincaré absorbs the value term in the cube embedding. The constants
are chosen before the cube centre, side, and function.
-/

open Homogenization MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section11

open Section9SupportInput Section6Iteration

variable {d : ℕ}

private theorem cube_downgrade {p : FiniteLpExponent} (hp : p.exponent ≤ 2)
    (z : Vec d) {L : ℝ} (hL : 0 < L) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volumeMeasureOn (axisCube z L))) :
    eLpNorm f p.exponent (volumeMeasureOn (axisCube z L)) ≤
      ENNReal.ofReal ((eLpNorm f 2 (volumeMeasureOn (axisCube z L))).toReal *
        (volume (axisCube z L)).toReal ^ (1 / p.exponent.toReal - 1 / 2)) := by
  have hv := volume_axisCube_toReal_pos z hL
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hf.aestronglyMeasurable
  simpa only [volumeMeasureOn, Measure.restrict_apply_univ, ENNReal.toReal_ofNat,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hf.eLpNorm_ne_top,
    ← ENNReal.ofReal_rpow_of_pos hv,
    ENNReal.ofReal_toReal (volume_axisCube_ne_top z L)] using h

/-- A finite-input-exponent zero-trace cube embedding, before its norm is squared. -/
theorem h10_cube_embedding [NeZero d] (p : FiniteLpExponent)
    (hp : p.exponent ≤ 2) (hpd : p.exponent.toReal < d) :
    ∃ A : ℝ, 0 < A ∧ ∀ q : FiniteLpExponent,
      (q.exponent.toReal)⁻¹ = p.exponent.toReal⁻¹ - (d : ℝ)⁻¹ →
      ∀ (z : Vec d) (L : ℝ), 0 < L → ∀ f : H10Function (axisCube z L),
        eLpNorm f.toH1Function.toFun q.exponent (volumeMeasureOn (axisCube z L)) ≤
          ENNReal.ofReal (A *
            (∑ i : Fin d, (eLpNorm (fun x => f.toH1Function.grad x i) 2
              (volumeMeasureOn (axisCube z L))).toReal) *
            (volume (axisCube z L)).toReal ^ (1 / p.exponent.toReal - 1 / 2)) := by
  obtain ⟨C, hC, hbound⟩ := cubeSobolevEmbedding_finiteLp (NeZero.pos d) p hpd
  let P := unitDirichletPoincareConst d
  have hP : 0 ≤ P := unitDirichletPoincareConst_nonneg d
  refine ⟨(C : ℝ) * (1 + P), mul_pos (by exact_mod_cast hC) (by positivity), ?_⟩
  intro q hpq z L hL f
  let : IsFiniteMeasure (volume.restrict (axisCube z L)) :=
    (isOpenBoundedConvexDomain_axisCube z L).isFiniteMeasure_restrict_volume
  let N := (eLpNorm f.toH1Function.toFun 2 (volumeMeasureOn (axisCube z L))).toReal
  let G := ∑ i : Fin d, (eLpNorm (fun x => f.toH1Function.grad x i) 2
    (volumeMeasureOn (axisCube z L))).toReal
  let V := (volume (axisCube z L)).toReal ^ (1 / p.exponent.toReal - 1 / 2)
  have hG : 0 ≤ G := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hV : 0 ≤ V := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hsum : (∑ i : Fin d, eLpNorm (fun x => f.toH1Function.grad x i)
      p.exponent (volumeMeasureOn (axisCube z L))) ≤ ENNReal.ofReal (G * V) := by
    calc
      _ ≤ ∑ i : Fin d, ENNReal.ofReal
          ((eLpNorm (fun x => f.toH1Function.grad x i) 2
            (volumeMeasureOn (axisCube z L))).toReal * V) :=
        Finset.sum_le_sum fun i _ => cube_downgrade hp z hL (f.toH1Function.gradMemL2 i)
      _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
          mul_nonneg ENNReal.toReal_nonneg hV), Finset.sum_mul]
  have hn := cube_downgrade hp z hL f.toH1Function.memL2
  have hpc : N ≤ P * L * G := scaled_dirichlet_poincare z hL f
  have habsorb : G + L⁻¹ * N ≤ (1 + P) * G := by
    have hh := mul_le_mul_of_nonneg_left hpc (inv_nonneg.mpr hL.le)
    have heq : L⁻¹ * (P * L * G) = P * G := by field_simp
    rw [heq] at hh
    nlinarith
  have hemb := hbound q hpq z L hL (f.toH1Function.toW1pOfExponentLETwo p hp)
  change eLpNorm f.toH1Function.toFun q.exponent _ ≤ _ at hemb
  calc
    _ ≤ (C : ℝ≥0∞) *
        ((∑ i : Fin d, eLpNorm (fun x => f.toH1Function.grad x i)
          p.exponent (volumeMeasureOn (axisCube z L))) +
        ENNReal.ofReal L⁻¹ * eLpNorm f.toH1Function.toFun p.exponent
          (volumeMeasureOn (axisCube z L))) := hemb
    _ ≤ (C : ℝ≥0∞) * (ENNReal.ofReal (G * V) +
        ENNReal.ofReal L⁻¹ * ENNReal.ofReal (N * V)) :=
      mul_le_mul_right (add_le_add hsum (mul_le_mul_right hn _)) _
    _ = ENNReal.ofReal ((C : ℝ) * ((G + L⁻¹ * N) * V)) := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (inv_nonneg.mpr hL.le),
        ← ENNReal.ofReal_add (mul_nonneg hG hV) (by positivity),
        ← ENNReal.ofReal_mul C.coe_nonneg]
      congr 1
      ring
    _ ≤ ENNReal.ofReal ((C : ℝ) * (1 + P) * G * V) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (C : ℝ) * (((1 + P) * G) * V) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right habsorb hV) C.coe_nonneg
        _ = _ := by ring

/-- The squared zero-trace Sobolev estimate with its Hölder volume factor. -/
theorem h10_cube_embedding_sq [NeZero d] (p : FiniteLpExponent)
    (hp : p.exponent ≤ 2) (hpd : p.exponent.toReal < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : FiniteLpExponent,
      (q.exponent.toReal)⁻¹ = p.exponent.toReal⁻¹ - (d : ℝ)⁻¹ →
      ∀ (z : Vec d) (L : ℝ), 0 < L → ∀ f : H10Function (axisCube z L),
        (eLpNorm f.toH1Function.toFun q.exponent (volumeMeasureOn (axisCube z L))) ^ 2 ≤
          ENNReal.ofReal (C * (volume (axisCube z L)).toReal ^
            (2 * (1 / p.exponent.toReal - 1 / 2))) *
          ENNReal.ofReal (energy (fun _ => 1) (axisCube z L) f.toH1Function) := by
  obtain ⟨A, hA, hbound⟩ := h10_cube_embedding p hp hpd
  refine ⟨A ^ 2 * d, mul_pos (sq_pos_of_pos hA) (by exact_mod_cast NeZero.pos d), ?_⟩
  intro q hpq z L hL f
  have h := pow_le_pow_left₀ zero_le (hbound q hpq z L hL f) 2
  let G := ∑ i : Fin d, (eLpNorm (fun x => f.toH1Function.grad x i) 2
    (volumeMeasureOn (axisCube z L))).toReal
  let V := (volume (axisCube z L)).toReal
  let t := 1 / p.exponent.toReal - 1 / 2
  have hG : 0 ≤ G := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hfac : 0 ≤ A * G * V ^ t := mul_nonneg (mul_nonneg hA.le hG) (Real.rpow_nonneg hV _)
  change _ ≤ (ENNReal.ofReal (A * G * V ^ t)) ^ 2 at h
  rw [← ENNReal.ofReal_pow hfac] at h
  refine h.trans ?_
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ A ^ 2 * (d : ℝ) * V ^ (2 * t))]
  apply ENNReal.ofReal_le_ofReal
  have hcs : G ^ 2 ≤ (d : ℝ) * energy (fun _ => 1) (axisCube z L) f.toH1Function :=
    sum_coordNorm_sq_le_energy f.toH1Function
  have hvpow : (V ^ t) ^ 2 = V ^ (2 * t) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hV]
    congr 1
    ring
  calc
    (A * G * V ^ t) ^ 2 = A ^ 2 * V ^ (2 * t) * G ^ 2 := by
      rw [mul_pow, mul_pow, hvpow]
      ring
    _ ≤ A ^ 2 * V ^ (2 * t) *
        ((d : ℝ) * energy (fun _ => 1) (axisCube z L) f.toH1Function) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = _ := by ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section11
