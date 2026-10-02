import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeCatalogueGeometry
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubePositiveScaleFiniteTests
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeCoefficientNormalization
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeUniformContrastTorsion
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTail
/-!
# One ambient event for a finite depth catalogue

The same dimension-only Sobolev constants work in both regimes. Above the
reference depth bound the positive-scale event supplies every member's tests;
for bounded cutoffs the local contrast event supplies them at every integer
native scale. The common volume floor supplies all pairwise mass comparisons.
-/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open Set MeasureTheory SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A single ambient measurable event supplies the full Sobolev, torsion
comparison, and all-pair mass tests for a finite reference-depth catalogue. -/
theorem exists_goodCube_finite_catalogue_ambient_tests
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p A : ℝ, 2 < p ∧ 1 ≤ A ∧
      ∀ (J N : ℕ) (eps : ℝ), 0 < eps →
        ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
          ∀ M : GMCModel d, M.delta ≤ c →
          ∀ (n : ℕ) (G : Finset (ℕ × Vec d)), G.card ≤ N →
            (∀ q ∈ G, q.1 ≤ J) →
            (∀ q ∈ G, cubeSet (q.2, (3 : ℝ) ^ (-(q.1 : ℤ))) ⊆
              cubeSet ((0 : Vec d), (1 : ℝ))) →
            ∃ Bad : Set (PotentialSample d), MeasurableSet Bad ∧
              M.P.toMeasure Bad ≤ ENNReal.ofReal
                (Real.exp (-(c ^ 2 / (M.delta ^ 2 * (Real.log M.delta) ^ 2)))) ∧
              ∀ omega, omega ∉ Bad →
                (∀ q ∈ G,
                  GoodCubeSobolevDisplay (aCutoff M n omega) p A
                    (Section7Process.timeScale (ahom M))
                    ((3 : ℝ) ^ n • q.2, (3 : ℝ) ^ ((n : ℤ) - q.1)) ∧
                  GoodCubeTorsionComparisonTest (originCube d ((n : ℤ) - q.1))
                    (fun x => aCutoff M n omega (x + (3 : ℝ) ^ n • q.2))
                    (if J ≤ n then ahom M n else 1) eps) ∧
                ∀ q ∈ G, ∀ r ∈ G,
                  ENNReal.ofReal ((((3 : ℝ) ^ (-(J : ℤ))) ^ d) / 3) *
                      weightedMeasure (aCutoff M n omega)
                        (cubeSet ((3 : ℝ) ^ n • r.2, (3 : ℝ) ^ ((n : ℤ) - r.1))) ≤
                    weightedMeasure (aCutoff M n omega)
                      (cubeSet ((3 : ℝ) ^ n • q.2, (3 : ℝ) ^ ((n : ℤ) - q.1))) := by
  classical
  obtain ⟨p, A, hp, hA, hnear, hpositive⟩ :=
    exists_goodCube_positiveScale_finite_ambient_tests d hd
  refine ⟨p, A, hp, hA, ?_⟩
  intro J N eps heps
  obtain ⟨tau, htau, htau1, hcontrastTest⟩ :=
    exists_goodCube_uniformContrast_torsionComparison d eps heps
  obtain ⟨cB, hcB, _, hcontrast⟩ :=
    exists_goodCube_boundedScale_coefficient_contrast d J htau
  obtain ⟨cP, hcP, _, hpositiveTail⟩ := hpositive J N eps heps
  let a : ℝ := min (cP ^ 2) 1
  let b : ℝ := min cP cB
  obtain ⟨c, hc, hcb, hchalf, habsorb⟩ := goodCube_exists_finite_tail_absorption
    2 a b (by norm_num) (lt_min (sq_pos_of_pos hcP) zero_lt_one) (lt_min hcP hcB)
  have hccP : c ≤ cP := hcb.trans (min_le_left _ _)
  have hccB : c ≤ cB := hcb.trans (min_le_right _ _)
  refine ⟨c, hc, hchalf, ?_⟩
  intro M hM n G hcard hdepth hinside
  let D : ℝ := M.delta ^ 2 * (Real.log M.delta) ^ 2
  let theta : ℝ := ((3 : ℝ) ^ (-(J : ℤ))) ^ d
  have htheta : 0 ≤ theta := by positivity
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hD : 0 < D := by
    have hlog : Real.log M.delta < 0 :=
      Real.log_neg hdelta ((hM.trans hchalf).trans_lt (by norm_num))
    exact mul_pos (sq_pos_of_pos hdelta) (sq_pos_of_ne_zero (ne_of_lt hlog))
  have hdecay (t : ℝ) (hat : a ≤ t) : Real.exp (-(t / D)) ≤ Real.exp (-a / D) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg (div_le_div_of_nonneg_right hat hD.le)
  have hbudget : 2 * Real.exp (-a / D) ≤ Real.exp (-(c ^ 2 / D)) :=
    habsorb M.delta hdelta hM
  have hptail : ENNReal.ofReal (Real.exp (-(cP ^ 2 / D))) ≤
      ENNReal.ofReal (Real.exp (-(c ^ 2 / D))) := by
    apply ENNReal.ofReal_le_ofReal
    exact (hdecay (cP ^ 2) (min_le_left _ _)).trans
      ((by linarith [Real.exp_pos (-a / D)] : Real.exp (-a / D) ≤
        2 * Real.exp (-a / D)).trans hbudget)
  have hbtail : ENNReal.ofReal (2 * Real.exp (-(1 / D))) ≤
      ENNReal.ofReal (Real.exp (-(c ^ 2 / D))) :=
    ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left
      (hdecay 1 (min_le_right _ _)) (by norm_num)).trans hbudget)
  have hvolume (q : ℕ × Vec d) (hq : q ∈ G) (r : ℕ × Vec d) (hr : r ∈ G) :
      ENNReal.ofReal theta *
        volume (cubeSet ((3 : ℝ) ^ n • r.2, (3 : ℝ) ^ ((n : ℤ) - r.1))) ≤
      volume (cubeSet ((3 : ℝ) ^ n • q.2, (3 : ℝ) ^ ((n : ℤ) - q.1))) :=
    goodCube_catalogue_volume_floor n J q.1 r.1 q.2 r.2 (hdepth q hq) (hdepth r hr)
  by_cases hn : J ≤ n
  · let F := G.image (fun q => (n - q.1, (3 : ℝ) ^ n • q.2))
    obtain ⟨hFcard, hFdepth, hscale⟩ :=
      goodCube_catalogue_positive_indices n J N hn G hcard hdepth
    obtain ⟨Bad, hBadmeas, hBadtail, hBadgood⟩ :=
      hpositiveTail M (hM.trans hccP) n F hFcard hFdepth
    refine ⟨Bad, hBadmeas, hBadtail.trans hptail, ?_⟩
    intro omega homega
    have hmem (q : ℕ × Vec d) (hq : q ∈ G) :
        (n - q.1, (3 : ℝ) ^ n • q.2) ∈ F := Finset.mem_image_of_mem _ hq
    constructor
    · intro q hq
      obtain ⟨hsob, _, htor⟩ := hBadgood omega homega _ (hmem q hq)
      refine ⟨?_, ?_⟩
      · simpa only [(hscale q hq).2] using hsob
      · simpa only [(hscale q hq).1, if_pos hn] using htor
    · intro q hq r hr
      have hqavg := (hBadgood omega homega _ (hmem q hq)).2.1
      have hravg := (hBadgood omega homega _ (hmem r hr)).2.1
      apply goodCube_cutoff_physical_mass_ratio M n omega
        ((n : ℤ) - q.1) ((n : ℤ) - r.1)
        ((3 : ℝ) ^ n • q.2) ((3 : ℝ) ^ n • r.2) htheta (hvolume q hq r hr)
      · simpa only [(hscale q hq).1] using hqavg.1
      · simpa only [(hscale r hr).1] using hravg.2
  · let Raw := coefficientLocalBadEvent M n 1 (goodCubeBad M n) (0 : Lattice d)
    let Bad := toMeasurable M.P.toMeasure Raw
    have hRawTail : M.P.toMeasure Raw ≤ ENNReal.ofReal (2 * Real.exp (-(1 / D))) := by
      have ht := measure_coefficientLocalBadEvent_goodCubeBad_le M n (0 : Lattice d)
      rw [tailIndex_sq] at ht
      exact ht
    have hBadTail : M.P.toMeasure Bad ≤ ENNReal.ofReal (Real.exp (-(c ^ 2 / D))) := by
      rw [show M.P.toMeasure Bad = M.P.toMeasure Raw from measure_toMeasurable Raw]
      exact hRawTail.trans hbtail
    refine ⟨Bad, measurableSet_toMeasurable _ _, hBadTail, ?_⟩
    intro omega homega
    have hnotRaw : omega ∉ Raw := fun h => homega (subset_toMeasurable _ _ h)
    obtain ⟨k, hk, hbound⟩ := hcontrast M (hM.trans hccB) n (by omega) 0 omega hnotRaw
    have hnative : nativeBox n 1 (0 : Lattice d) = cubeSet ((0 : Vec d), (3 : ℝ) ^ n) := by
      simp only [nativeBox, one_mul, goodCubeCentre_zero_lattice, cubeSet]
    have hboundParent : ∀ x ∈ cubeSet ((0 : Vec d), (3 : ℝ) ^ n),
        k ≤ aCutoff M n omega x ∧ aCutoff M n omega x ≤ (1 + tau) * k := by
      intro x hx
      have hh := hbound x (by rwa [hnative])
      exact ⟨hh.1, hh.2.1⟩
    have hfactor : (1 + tau) * k ≤ 2 * k := by nlinarith
    have hboundTwo : ∀ x ∈ cubeSet ((0 : Vec d), (3 : ℝ) ^ n),
        k ≤ aCutoff M n omega x ∧ aCutoff M n omega x ≤ 2 * k :=
      fun x hx => ⟨(hboundParent x hx).1, (hboundParent x hx).2.trans hfactor⟩
    have hsub (q : ℕ × Vec d) (hq : q ∈ G) :
        cubeSet ((3 : ℝ) ^ n • q.2, (3 : ℝ) ^ ((n : ℤ) - q.1)) ⊆
          cubeSet ((0 : Vec d), (3 : ℝ) ^ n) :=
      goodCube_catalogue_cube_subset_parent n q.1 q.2 (hinside q hq)
    constructor
    · intro q hq
      have hlocal : ∀ x ∈ openCubeSet (originCube d ((n : ℤ) - q.1)),
          k ≤ aCutoff M n omega (x + (3 : ℝ) ^ n • q.2) ∧
          aCutoff M n omega (x + (3 : ℝ) ^ n • q.2) ≤ (1 + tau) * k :=
        fun x hx => hboundParent _ (hsub q hq (goodCube_catalogue_pullback_mem_physical n q.1 q.2 x hx))
      refine ⟨hnear M n omega ((n : ℤ) - q.1) ((3 : ℝ) ^ n • q.2)
        ⟨k, hk, fun x hx => ⟨(hlocal x hx).1, (hlocal x hx).2.trans hfactor⟩⟩, ?_⟩
      rw [if_neg hn]
      exact hcontrastTest (originCube d ((n : ℤ) - q.1))
        (fun x => aCutoff M n omega (x + (3 : ℝ) ^ n • q.2)) k hk
        (((continuous_aCutoff M n omega).comp (continuous_id.add continuous_const)).continuousOn) hlocal
    · intro q hq r hr
      have hm := goodCube_cutoff_physical_mass_ratio_of_local_factor_two M n omega
        ((3 : ℝ) ^ n • q.2, (3 : ℝ) ^ ((n : ℤ) - q.1))
        ((3 : ℝ) ^ n • r.2, (3 : ℝ) ^ ((n : ℤ) - r.1))
        (hsub q hq) (hsub r hr) hk htheta hboundTwo (hvolume q hq r hr)
      have hthird : theta / 3 ≤ theta / 2 := by linarith
      exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal hthird) _).trans hm

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
