import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeUniformSobolev
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubePositiveScaleTail
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionPositiveTail
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTorsionTest
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeClockComparison
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeFiniteTail

/-!
# Simultaneous ambient positive-scale good-cube tests

One dimension-only Sobolev exponent and constant work both on cubes with a
local factor-two coefficient ratio at arbitrary integer scales and outside a
single ambient bad event for any prescribed finite positive-scale family.
The event controls the actual coefficient average and the weighted torsion
comparison as well. The disorder threshold is chosen after the finite depth,
cardinality, and torsion tolerance, and before the model and cubes.

These bad events are ambient measurable majorants. Restricted-coefficient
locality is not part of this construction.
-/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open Homogenization.Book MeasureTheory SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A finite family of measurable bad-event majorants has one measurable
majorant with the sum of their common tail bounds. -/
theorem goodCube_exists_finite_bad_majorant
    {Omega Iota : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (F : Finset Iota) (B : ℝ≥0∞) (P : Iota → Omega → Prop)
    (h : ∀ i ∈ F, ∃ Bad : Set Omega, MeasurableSet Bad ∧ mu Bad ≤ B ∧
      ∀ omega, omega ∉ Bad → P i omega) :
    ∃ Bad : Set Omega, MeasurableSet Bad ∧ mu Bad ≤ (F.card : ℝ≥0∞) * B ∧
      ∀ omega, omega ∉ Bad → ∀ i ∈ F, P i omega := by
  classical
  choose Bad hmeas hle hP using h
  set S : Iota → Set Omega := fun i => if hi : i ∈ F then Bad i hi else ∅ with hS
  have hmeasS : ∀ i ∈ F, MeasurableSet (S i) := by
    intro i hi
    simp only [hS, dif_pos hi]
    exact hmeas i hi
  have hleS : ∀ i ∈ F, mu (S i) ≤ B := by
    intro i hi
    simp only [hS, dif_pos hi]
    exact hle i hi
  refine ⟨⋃ i ∈ F, S i, Finset.measurableSet_biUnion F hmeasS, ?_, ?_⟩
  · calc mu (⋃ i ∈ F, S i) ≤ ∑ i ∈ F, mu (S i) :=
      measure_biUnion_finset_le F S
    _ ≤ ∑ _i ∈ F, B := Finset.sum_le_sum fun i hi => hleS i hi
    _ = (F.card : ℝ≥0∞) * B := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  · intro omega homega i hi
    by_contra hcon
    have : omega ∈ S i := by
      simp only [hS, dif_pos hi]
      by_contra hnb
      exact hcon (hP i hi omega hnb)
    exact homega (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, this⟩⟩)

/-- A common threshold pays the depth comparison and absorbs the tail factor
for two tests on each member of a finite family. -/
theorem goodCube_exists_finite_test_threshold
    (J N : ℕ) (cS cT : ℝ) (hcS : 0 < cS) (hcT : 0 < cT) :
    ∃ c : ℝ, 0 < c ∧ c ≤ cS ∧ c ≤ cT ∧ c ≤ 1 / 2 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ c →
        2 * delta ^ 2 * (J : ℝ) ≤ Real.log 2 ∧
        (2 * ((N : ℝ) + 1)) *
          Real.exp (-((min cS cT) ^ 2) / (delta ^ 2 * (Real.log delta) ^ 2)) ≤
            Real.exp (-(c ^ 2 / (delta ^ 2 * (Real.log delta) ^ 2))) := by
  let b : ℝ := min (min cS cT) (Real.log 2 / (2 * ((J : ℝ) + 1)))
  have hden : (0 : ℝ) < 2 * ((J : ℝ) + 1) := by positivity
  have hb : 0 < b := lt_min (lt_min hcS hcT)
    (div_pos (Real.log_pos (by norm_num)) hden)
  obtain ⟨c, hc, hcb, hchalf, habs⟩ := goodCube_exists_finite_tail_absorption
    (2 * ((N : ℝ) + 1)) ((min cS cT) ^ 2) b (by positivity) (by positivity) hb
  have hcmin : c ≤ min cS cT := hcb.trans (min_le_left _ _)
  refine ⟨c, hc, hcmin.trans (min_le_left _ _), hcmin.trans (min_le_right _ _), hchalf, ?_⟩
  intro delta hdelta hdeltac
  refine ⟨?_, habs delta hdelta hdeltac⟩
  have hdelta_half : delta ≤ 1 / 2 := hdeltac.trans hchalf
  have hsq : delta ^ 2 ≤ delta := by
    nlinarith [mul_nonneg hdelta.le (show 0 ≤ 1 - delta by linarith)]
  have hdelta_bound : delta ≤ Real.log 2 / (2 * ((J : ℝ) + 1)) :=
    hdeltac.trans (hcb.trans (min_le_right _ _))
  have hlogBudget := (le_div_iff₀ hden).mp hdelta_bound
  calc
    2 * delta ^ 2 * (J : ℝ) ≤ 2 * delta ^ 2 * ((J : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ 2 * delta * ((J : ℝ) + 1) := by
      nlinarith only [mul_le_mul_of_nonneg_right hsq hden.le]
    _ = delta * (2 * ((J : ℝ) + 1)) := by ring
    _ ≤ Real.log 2 := hlogBudget

/-- One dimensional Sobolev exponent and constant cover both the local ratio
criterion at all integer scales and one simultaneous ambient event for a finite
family of positive descendant cubes. All analytic tests use the actual outer
cutoff and the physical translations; the torsion test retains every pair of
zero-trace weak solutions. -/
theorem exists_goodCube_positiveScale_finite_ambient_tests
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p A : ℝ, 2 < p ∧ 1 ≤ A ∧
      (∀ (M : GMCModel d) (L : ℕ) (omega : PotentialSample d) (m : ℤ) (z : Vec d),
        (∃ c : ℝ, 0 < c ∧ ∀ x ∈ openCubeSet (originCube d m),
          c ≤ aCutoff M L omega (x + z) ∧ aCutoff M L omega (x + z) ≤ 2 * c) →
        GoodCubeSobolevDisplay (aCutoff M L omega) p A
          (Section7Process.timeScale (ahom M)) (z, (3 : ℝ) ^ m)) ∧
      ∀ (J N : ℕ) (eps : ℝ), 0 < eps →
        ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
          ∀ M : GMCModel d, M.delta ≤ c → ∀ (n : ℕ) (F : Finset (ℕ × Vec d)),
            F.card ≤ N → (∀ q ∈ F, q.1 ≤ n ∧ n - q.1 ≤ J) →
            ∃ Bad : Set (PotentialSample d), MeasurableSet Bad ∧
              M.P.toMeasure Bad ≤ ENNReal.ofReal
                (Real.exp (-(c ^ 2 / (M.delta ^ 2 * (Real.log M.delta) ^ 2)))) ∧
              ∀ omega, omega ∉ Bad → ∀ q ∈ F,
                GoodCubeSobolevDisplay (aCutoff M n omega) p A
                  (Section7Process.timeScale (ahom M)) (q.2, (3 : ℝ) ^ q.1) ∧
                ((1 / 2 : ℝ) ≤ cubeAverage (originCube d (q.1 : ℤ))
                    (fun x => aCutoff M n omega (x + q.2)) ∧
                  cubeAverage (originCube d (q.1 : ℤ))
                    (fun x => aCutoff M n omega (x + q.2)) ≤ 3 / 2) ∧
                GoodCubeTorsionComparisonTest (originCube d (q.1 : ℤ))
                  (fun x => aCutoff M n omega (x + q.2)) (ahom M n) eps := by
  classical
  obtain ⟨p, A, hp, hA, hratio, hpositive⟩ := exists_goodCube_sobolev_common_tests d hd
  refine ⟨p, A, hp, hA, hratio, ?_⟩
  intro J N eps heps
  obtain ⟨cS, hcS, _, hS⟩ := exists_goodCube_positiveScale_ambient_tail d J hd 1 1
    (by norm_num) (by norm_num)
  obtain ⟨cT, hcT, _, hT⟩ := exists_goodCube_positiveScale_weightedTorsion_ambient_tail
    d J hd eps heps
  obtain ⟨c, hc, hccS, hccT, hchalf, hbudget⟩ :=
    goodCube_exists_finite_test_threshold J N cS cT hcS hcT
  refine ⟨c, hc, hchalf, ?_⟩
  intro M hM n F hF hdepth
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  obtain ⟨hclockBudget, htailBudget⟩ := hbudget M.delta hdelta hM
  let a : ℝ := (min cS cT) ^ 2
  let D : ℝ := M.delta ^ 2 * (Real.log M.delta) ^ 2
  let B : ℝ≥0∞ := ENNReal.ofReal (2 * Real.exp (-a / D))
  let P : (ℕ × Vec d) → PotentialSample d → Prop := fun q omega =>
    GoodCubeSobolevDisplay (aCutoff M n omega) p A
        (Section7Process.timeScale (ahom M)) (q.2, (3 : ℝ) ^ q.1) ∧
      ((1 / 2 : ℝ) ≤ cubeAverage (originCube d (q.1 : ℤ))
          (fun x => aCutoff M n omega (x + q.2)) ∧
        cubeAverage (originCube d (q.1 : ℤ))
          (fun x => aCutoff M n omega (x + q.2)) ≤ 3 / 2) ∧
      GoodCubeTorsionComparisonTest (originCube d (q.1 : ℤ))
        (fun x => aCutoff M n omega (x + q.2)) (ahom M n) eps
  have hD : 0 < D := by
    have hlog : Real.log M.delta < 0 :=
      Real.log_neg hdelta ((hM.trans hchalf).trans_lt (by norm_num))
    exact mul_pos (sq_pos_of_pos hdelta) (sq_pos_of_ne_zero (ne_of_lt hlog))
  have hmin : 0 < min cS cT := lt_min hcS hcT
  have haS : a ≤ cS ^ 2 := by
    dsimp [a]
    nlinarith [min_le_left cS cT]
  have haT : a ≤ cT ^ 2 := by
    dsimp [a]
    nlinarith [min_le_right cS cT]
  have hES : Real.exp (-(cS ^ 2 / D)) ≤ Real.exp (-a / D) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg (div_le_div_of_nonneg_right haS hD.le)
  have hET : Real.exp (-(cT ^ 2 / D)) ≤ Real.exp (-a / D) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg (div_le_div_of_nonneg_right haT hD.le)
  have hsingle : ∀ q ∈ F, ∃ Bad : Set (PotentialSample d), MeasurableSet Bad ∧
      M.P.toMeasure Bad ≤ B ∧ ∀ omega, omega ∉ Bad → P q omega := by
    intro q hq
    obtain ⟨hmn, hmJ⟩ := hdepth q hq
    obtain ⟨BadS, hBadSmeas, hBadStail, hBadSgood⟩ :=
      hS M (hM.trans hccS) n q.1 hmn hmJ q.2
    obtain ⟨BadT, hBadTmeas, hBadTtail, hBadTgood⟩ :=
      hT M (hM.trans hccT) n q.1 hmn hmJ q.2
    refine ⟨BadS ∪ BadT, hBadSmeas.union hBadTmeas, ?_, ?_⟩
    · calc
        _ ≤ M.P.toMeasure BadS + M.P.toMeasure BadT := measure_union_le _ _
        _ ≤ ENNReal.ofReal (Real.exp (-a / D)) +
            ENNReal.ofReal (Real.exp (-a / D)) :=
          add_le_add (hBadStail.trans (ENNReal.ofReal_le_ofReal hES))
            (hBadTtail.trans (ENNReal.ofReal_le_ofReal hET))
        _ = B := by
          dsimp [B]
          rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, two_mul]
    · intro omega homega
      have hnotS : omega ∉ BadS := fun h => homega (Or.inl h)
      have hnotT : omega ∉ BadT := fun h => homega (Or.inr h)
      obtain ⟨hE, _, hmass, _, hnorm⟩ := hBadSgood omega hnotS
      have hcoeff : aCutoff M n (translatePotentialSample q.2 omega) =
          fun x => aCutoff M n omega (x + q.2) := by
        funext x
        exact Section6Covariance.aCutoff_translatePotentialSample M n q.2 omega x
      rw [hcoeff] at hmass hnorm
      obtain ⟨_, hb, _⟩ := goodCube_cutoff_sobolev_data M n omega q.2
        (originCube d (q.1 : ℤ))
      have hclock := goodCube_ahom_scale_comparison M n q.1 J hmn hmJ hclockBudget
      have hsob := hpositive M n q.1 hmn omega q.2 (by simpa only [ENNReal.ofReal_one] using hE)
        hmass.2 hclock hb (hnorm hb)
      refine ⟨hsob, hmass, ?_⟩
      unfold GoodCubeTorsionComparisonTest
      simpa only [hcoeff] using hBadTgood omega hnotT
  obtain ⟨Bad, hBadmeas, hBadtail, hBadgood⟩ :=
    goodCube_exists_finite_bad_majorant M.P.toMeasure F B P hsingle
  refine ⟨Bad, hBadmeas, ?_, hBadgood⟩
  have hcard : (F.card : ℝ) ≤ (N : ℝ) + 1 := by
    have hFN : (F.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hF
    linarith
  have hfinite : (F.card : ℝ≥0∞) * B ≤
      ENNReal.ofReal ((2 * ((N : ℝ) + 1)) * Real.exp (-a / D)) := by
    dsimp [B]
    rw [← ENNReal.ofReal_natCast F.card, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      (F.card : ℝ) * (2 * Real.exp (-a / D)) ≤
          ((N : ℝ) + 1) * (2 * Real.exp (-a / D)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (2 * ((N : ℝ) + 1)) * Real.exp (-a / D) := by ring
  exact hBadtail.trans (hfinite.trans (ENNReal.ofReal_le_ofReal htailBudget))

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
