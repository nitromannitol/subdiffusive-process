/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import SubdiffusiveProcess.CoarseGrainingVocab.NegativeBesovSupport
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellGauge
import SubdiffusiveProcess.Section9.CutoffOneCubeTail
import Homogenization.Geometry.TriadicPartition

/-! # Opposite corner cubes for the cutoff mass recursion -/

namespace SubdiffusiveProcess.Section9

open Homogenization MeasureTheory
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

noncomputable section

/-- The all-zero-digit child of the centered cube at the next scale. -/
def cutoffLowerCornerCube (d m : ℕ) : Homogenization.TriadicCube d :=
  { scale := m
    index := fun _ ↦ -1 }

/-- The all-two-digit child of the centered cube at the next scale. -/
def cutoffUpperCornerCube (d m : ℕ) : Homogenization.TriadicCube d :=
  { scale := m
    index := fun _ ↦ 1 }

theorem cubeSet_cutoffLowerCornerCube_subset (d m : ℕ) :
    cubeSet (cutoffLowerCornerCube d m) ⊆ cubeSet (originCube d ((m + 1 : ℕ) : ℤ)) := by
  simpa [cutoffLowerCornerCube, originCube] using
    (cubeSet_childCube_subset (originCube d ((m + 1 : ℕ) : ℤ))
      (fun _ ↦ (0 : Fin 3)))

theorem cubeSet_cutoffUpperCornerCube_subset (d m : ℕ) :
    cubeSet (cutoffUpperCornerCube d m) ⊆ cubeSet (originCube d ((m + 1 : ℕ) : ℤ)) := by
  simpa [cutoffUpperCornerCube, originCube] using
    (cubeSet_childCube_subset (originCube d ((m + 1 : ℕ) : ℤ))
      (fun _ ↦ (2 : Fin 3)))

theorem disjoint_cutoffCornerCubes (d m : ℕ) (hd : 0 < d) :
    Disjoint (cubeSet (cutoffLowerCornerCube d m))
      (cubeSet (cutoffUpperCornerCube d m)) := by
  simpa [cutoffLowerCornerCube, cutoffUpperCornerCube, originCube] using
    (disjoint_cubeSet_childCube_of_ne (originCube d ((m + 1 : ℕ) : ℤ))
      (digits₁ := fun _ ↦ (0 : Fin 3)) (digits₂ := fun _ ↦ (2 : Fin 3)) (by
        intro h
        exact (by decide : (0 : Fin 3) ≠ 2) (congrFun h (⟨0, hd⟩ : Fin d))))

/-- Opposite corner children have exactly the one-scale separation required
by the cutoff finite-range API. -/
theorem cutoffCornerCubes_euclidean_separated {d m : ℕ}
    {x y : Homogenization.Vec d} (hx : x ∈ cubeSet (cutoffLowerCornerCube d m))
    (hy : y ∈ cubeSet (cutoffUpperCornerCube d m)) :
    Real.sqrt (d : ℝ) * (3 : ℝ) ^ m ≤ euclideanNorm (x - y) := by
  have hr : 0 < (3 : ℝ) ^ m := by positivity
  have hcoord : ∀ i : Fin d, (3 : ℝ) ^ m ≤ |x i - y i| := by
    intro i
    have hxi : x i < ((-1 : ℝ) + 1 / 2) * (3 : ℝ) ^ m := by
      simpa [cutoffLowerCornerCube, cubeScaleFactor] using (hx i).2
    have hyi : ((1 : ℝ) - 1 / 2) * (3 : ℝ) ^ m ≤ y i := by
      simpa [cutoffUpperCornerCube, cubeScaleFactor] using (hy i).1
    rw [abs_of_nonpos (by linarith)]
    linarith
  rw [← sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hr.le)
    (euclideanNorm_nonneg _), euclideanNorm_sq]
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  unfold vecNormSq vecDot
  calc
    (d : ℝ) * ((3 : ℝ) ^ m) ^ 2 =
        ∑ _i : Fin d, ((3 : ℝ) ^ m) ^ 2 := by simp
    _ ≤ ∑ i : Fin d, (x i - y i) * (x i - y i) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ((3 : ℝ) ^ m) ^ 2 ≤ |x i - y i| ^ 2 :=
          (sq_le_sq₀ hr.le (abs_nonneg _) |>.mpr (hcoord i))
        _ = (x i - y i) * (x i - y i) := by rw [sq_abs, pow_two]

/-- Pointwise one-shell lower bound used under the two child integrals. -/
theorem aCutoff_succ_lower_of_abs_shell_le {d m : ℕ}
    (M : GMCModel d) (omega : PotentialSample d) (G : ℝ) {x : Homogenization.Vec d}
    (hG : |omega (m + 1) x| ≤ G) :
    Real.exp (-G - tauSq M.P) * aCutoff M m omega x ≤
      aCutoff M (m + 1) omega x := by
  have hid := aCutoff_eq_pred_mul_freshShell M (m + 1) omega x
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, aCutoffAtInt,
    if_neg (not_lt_of_ge (Int.natCast_nonneg m)), Int.toNat_natCast] at hid
  rw [hid]
  have hlo : -G ≤ omega (m + 1) x := (abs_le.mp hG).1
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
    (aCutoff_pos M m omega x).le

/-- The pointwise fresh-shell estimate integrated on either actual corner
cube. Integrability is explicit so this lemma remains useful for any later
choice of representative of the cube boundary. -/
theorem exp_mul_setIntegral_aCutoff_le_setIntegral_succ {d m : ℕ}
    (M : GMCModel d) (omega : PotentialSample d) (G : ℝ)
    (Q : Homogenization.TriadicCube d)
    (hprev : IntegrableOn (aCutoff M m omega) (cubeSet Q))
    (hnext : IntegrableOn (aCutoff M (m + 1) omega) (cubeSet Q))
    (hG : ∀ x ∈ cubeSet Q, |omega (m + 1) x| ≤ G) :
    Real.exp (-G - tauSq M.P) *
        (∫ x in cubeSet Q, aCutoff M m omega x ∂volume) ≤
      ∫ x in cubeSet Q, aCutoff M (m + 1) omega x ∂volume := by
  rw [← integral_const_mul]
  apply integral_mono_ae (hprev.const_mul _) hnext
  filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with x hx
  exact aCutoff_succ_lower_of_abs_shell_le M omega G (hG x hx)

/-- The actual own-scale `(g2)` gauge controls a shell throughout its centered
open cube, at every shell index including the base index zero. -/
theorem abs_potentialShell_le_translatedShellG2_on_originCube {d k : ℕ}
    (omega : PotentialSample d) {x : Homogenization.Vec d}
    (hx : x ∈ openCubeSet (originCube d (k : ℤ))) :
    |omega k x| ≤ translatedShellG2 k 0 omega := by
  let u : Homogenization.Vec d := ((3 : ℝ) ^ k)⁻¹ • x
  have hu : u ∈ openCubeSet (originCube d 0) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have hxi := (mem_openCubeSet_originCube_iff.mp hx) i
    simp only [u, Pi.smul_apply, smul_eq_mul, zpow_zero, mul_one]
    rw [zpow_natCast] at hxi
    have hpow : 0 < (3 : ℝ) ^ k := by positivity
    constructor
    · rw [← div_eq_inv_mul]
      exact (lt_div_iff₀ hpow).2 hxi.1
    · rw [← div_eq_inv_mul]
      exact (div_lt_iff₀ hpow).2 hxi.2
  have hp := PotentialField.abs_apply_le_g2Observable
    (unscalePotential k (omega k)) hu
  rw [← shellUnitGauge_eq_translatedShellG2 k omega]
  simpa only [u, unscalePotential, PotentialField.spatialScale_apply, smul_smul,
    mul_inv_cancel₀ (by positivity : (3 : ℝ) ^ k ≠ 0), one_smul] using hp

/-- Exact deterministic two-corner splitting of the normalized cutoff mass. -/
theorem cutoffOriginCubeAverage_succ_ge_corner_split {d m : ℕ}
    (M : GMCModel d) (omega : PotentialSample d) :
    ((3 : ℝ) ^ d)⁻¹ *
          Real.exp (-tauSq M.P - translatedShellG2 (m + 1) 0 omega) *
        (cubeAverage (cutoffLowerCornerCube d m) (aCutoff M m omega) +
          cubeAverage (cutoffUpperCornerCube d m) (aCutoff M m omega)) ≤
      cutoffOriginCubeAverage M (m + 1) omega := by
  let Q := originCube d ((m + 1 : ℕ) : ℤ)
  let Qlo := cutoffLowerCornerCube d m
  let Qhi := cutoffUpperCornerCube d m
  let c := Real.exp (-translatedShellG2 (m + 1) 0 omega - tauSq M.P)
  have hint (r : ℕ) (R : Homogenization.TriadicCube d) :
      IntegrableOn (aCutoff M r omega) (openCubeSet R) := by
    exact ((continuous_aCutoff M r omega).continuousOn.integrableOn_compact
      (ProperSpace.isCompact_closedBall (cubeCenter R) (cubeRadius R))).mono_set
        ((openCubeSet_subset_cubeSet R).trans (cubeSet_subset_closedBall R))
  have hminus : c * (∫ x in openCubeSet Qlo, aCutoff M m omega x ∂volume) ≤
      ∫ x in openCubeSet Qlo, aCutoff M (m + 1) omega x ∂volume := by
    rw [← integral_const_mul]
    apply integral_mono_ae ((hint m Qlo).const_mul _) (hint (m + 1) Qlo)
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Qlo)] with x hx
    apply aCutoff_succ_lower_of_abs_shell_le
    exact abs_potentialShell_le_translatedShellG2_on_originCube omega
      (openCubeSet_childCube_subset (originCube d ((m + 1 : ℕ) : ℤ))
        (fun _ ↦ (0 : Fin 3)) (by simpa [Qlo, cutoffLowerCornerCube, originCube] using hx))
  have hplus : c * (∫ x in openCubeSet Qhi, aCutoff M m omega x ∂volume) ≤
      ∫ x in openCubeSet Qhi, aCutoff M (m + 1) omega x ∂volume := by
    rw [← integral_const_mul]
    apply integral_mono_ae ((hint m Qhi).const_mul _) (hint (m + 1) Qhi)
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Qhi)] with x hx
    apply aCutoff_succ_lower_of_abs_shell_le
    exact abs_potentialShell_le_translatedShellG2_on_originCube omega
      (openCubeSet_childCube_subset (originCube d ((m + 1 : ℕ) : ℤ))
        (fun _ ↦ (2 : Fin 3)) (by simpa [Qhi, cutoffUpperCornerCube, originCube] using hx))
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hdisj : Disjoint (openCubeSet Qlo) (openCubeSet Qhi) :=
    (disjoint_cutoffCornerCubes d m hd).mono
      (openCubeSet_subset_cubeSet Qlo) (openCubeSet_subset_cubeSet Qhi)
  have hsub : openCubeSet Qlo ∪ openCubeSet Qhi ⊆ openCubeSet Q := by
    intro x hx
    rcases hx with hx | hx
    · exact openCubeSet_childCube_subset (originCube d ((m + 1 : ℕ) : ℤ))
        (fun _ ↦ (0 : Fin 3)) (by simpa [Q, Qlo, cutoffLowerCornerCube, originCube] using hx)
    · exact openCubeSet_childCube_subset (originCube d ((m + 1 : ℕ) : ℤ))
        (fun _ ↦ (2 : Fin 3)) (by simpa [Q, Qhi, cutoffUpperCornerCube, originCube] using hx)
  have hparent :
      (∫ x in openCubeSet Qlo, aCutoff M (m + 1) omega x ∂volume) +
          ∫ x in openCubeSet Qhi, aCutoff M (m + 1) omega x ∂volume ≤
        ∫ x in openCubeSet Q, aCutoff M (m + 1) omega x ∂volume := by
    rw [← setIntegral_union hdisj (measurableSet_openCubeSet Qhi)
      (hint (m + 1) Qlo) (hint (m + 1) Qhi)]
    exact setIntegral_mono_set (hint (m + 1) Q)
      (Filter.Eventually.of_forall fun x ↦ (aCutoff_pos M (m + 1) omega x).le)
      (Filter.Eventually.of_forall hsub)
  have hraw : c * ((∫ x in openCubeSet Qlo, aCutoff M m omega x ∂volume) +
        ∫ x in openCubeSet Qhi, aCutoff M m omega x ∂volume) ≤
      ∫ x in openCubeSet Q, aCutoff M (m + 1) omega x ∂volume := by
    rw [mul_add]
    exact (add_le_add hminus hplus).trans hparent
  unfold cutoffOriginCubeAverage
  rw [← cubeAverage_eq_integral_normalizedCubeMeasure]
  simp only [cubeAverage]
  rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet]
  dsimp only [Q, Qlo, Qhi, c] at hraw ⊢
  have hvolParent : cubeVolume (originCube d ((m + 1 : ℕ) : ℤ)) =
      ((3 : ℝ) ^ (m + 1)) ^ d := by
    rw [cubeVolume_eq_pow_scale]
    change ((3 : ℝ) ^ ((m : ℤ) + 1)) ^ d = _
    rw [show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by omega, zpow_natCast]
  have hvolChildLo : cubeVolume (cutoffLowerCornerCube d m) = ((3 : ℝ) ^ m) ^ d := by
    simp [cubeVolume_eq_pow_scale, cutoffLowerCornerCube]
  have hvolChildHi : cubeVolume (cutoffUpperCornerCube d m) = ((3 : ℝ) ^ m) ^ d := by
    simp [cubeVolume_eq_pow_scale, cutoffUpperCornerCube]
  rw [hvolParent, hvolChildLo, hvolChildHi]
  have hratio : (((3 : ℝ) ^ (m + 1)) ^ d)⁻¹ =
      ((3 : ℝ) ^ d)⁻¹ * (((3 : ℝ) ^ m) ^ d)⁻¹ := by
    rw [pow_succ, mul_pow, mul_inv_rev]
  calc
    _ = (((3 : ℝ) ^ (m + 1)) ^ d)⁻¹ *
        (Real.exp (-translatedShellG2 (m + 1) 0 omega - tauSq M.P) *
          ((∫ x in openCubeSet (cutoffLowerCornerCube d m), aCutoff M m omega x ∂volume) +
           ∫ x in openCubeSet (cutoffUpperCornerCube d m), aCutoff M m omega x ∂volume)) := by
      rw [hratio]
      ring_nf
    _ ≤ (((3 : ℝ) ^ (m + 1)) ^ d)⁻¹ *
        (∫ x in openCubeSet (originCube d ((m + 1 : ℕ) : ℤ)),
          aCutoff M (m + 1) omega x ∂volume) := by
      exact mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr (by positivity))


end

end SubdiffusiveProcess.Section9
