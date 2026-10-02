import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHessianObservableMeasurability
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepMixedNorm
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNestedMomentSweep
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceScale
import Homogenization.Besov.Localization
import Homogenization.Besov.Poincare.Projection




open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Exact scale ratio between a source cell and the lower cutoff endpoint,
independent of the outer finite-volume scale. -/
theorem oneStep_descendant_source_to_cutoff_ratio_eq
    {d : ℕ} {delta : ℝ} {n K : ℕ}
    (hsource : 16 * ⌈|Real.log delta / Real.log 3|⌉₊ ≤ n)
    (hK : oneStepLocalizationScale n delta ≤ K) :
    (cubeScaleFactor (originCube d K) /
          (3 : ℝ) ^ (K - oneStepLocalizationScale n delta)) /
        (3 : ℝ) ^ n =
      (3 : ℝ) ^ (-(oneStepLocalizationDepth delta : ℤ)) := by
  let j := oneStepLocalizationScale n delta
  let N := oneStepLocalizationDepth delta
  have hjN : j + N = n := by
    simpa only [j, N] using oneStepLocalizationScale_add_depth hsource
  have hdiff : (K : ℤ) - (K - j : ℕ) = (j : ℤ) := by omega
  have hfinal : (j : ℤ) - (n : ℤ) = -(N : ℤ) := by omega
  rw [cubeScaleFactor_originCube]
  norm_num only [zpow_natCast]
  calc
    (3 : ℝ) ^ (K : ℤ) / (3 : ℝ) ^ (K - j : ℕ) /
          (3 : ℝ) ^ (n : ℕ) =
        (3 : ℝ) ^ ((K : ℤ) - (K - j : ℕ)) /
          (3 : ℝ) ^ (n : ℤ) := by
      rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num only [zpow_natCast]
    _ = (3 : ℝ) ^ (j : ℤ) / (3 : ℝ) ^ (n : ℤ) := by rw [hdiff]
    _ = (3 : ℝ) ^ ((j : ℤ) - (n : ℤ)) := by
      rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    _ = (3 : ℝ) ^ (-(N : ℤ)) := by rw [hfinal]

/-- The source-cell/cutoff ratio contributes sixteen powers of the disorder. -/
theorem oneStep_descendant_source_to_cutoff_ratio_le_delta_sixteen
    {d : ℕ} {delta : ℝ} {n K : ℕ}
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hsource : 16 * ⌈|Real.log delta / Real.log 3|⌉₊ ≤ n)
    (hK : oneStepLocalizationScale n delta ≤ K) :
    cubeScaleFactor (originCube d K) /
          (3 : ℝ) ^ (K - oneStepLocalizationScale n delta) /
        (3 : ℝ) ^ n ≤ delta ^ (16 : ℕ) := by
  rw [oneStep_descendant_source_to_cutoff_ratio_eq hsource hK]
  have hfactor :
      (3 : ℝ) ^ (-(oneStepLocalizationDepth delta : ℤ)) =
        (3 : ℝ) ^ (-(oneStepLocalizationDepth delta : ℝ)) := by
    rw [← Real.rpow_intCast]
    norm_num
  rw [hfactor]
  exact rpow_three_neg_oneStepLocalizationDepth_le_delta_pow_sixteen
    hdelta0 hdelta1

/-- Fourth-power source ratio followed by the differentiated-shell `delta^4`
moment gives the printed `delta^68` budget. -/
theorem ofReal_oneStep_source_ratio_four_mul_delta_four_le_delta_sixtyEight
    {d : ℕ} {delta : ℝ} {n K : ℕ}
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hsource : 16 * ⌈|Real.log delta / Real.log 3|⌉₊ ≤ n)
    (hK : oneStepLocalizationScale n delta ≤ K) :
    ENNReal.ofReal
        ((cubeScaleFactor (originCube d K) /
            (3 : ℝ) ^ (K - oneStepLocalizationScale n delta) /
              (3 : ℝ) ^ n) ^ (4 : ℕ)) *
        (ENNReal.ofReal delta) ^ (4 : ℝ) ≤
      ENNReal.ofReal (delta ^ (68 : ℕ)) := by
  let ratio : ℝ := cubeScaleFactor (originCube d K) /
      (3 : ℝ) ^ (K - oneStepLocalizationScale n delta) / (3 : ℝ) ^ n
  have hratio0 : 0 ≤ ratio := by dsimp [ratio]; positivity
  have hratio := oneStep_descendant_source_to_cutoff_ratio_le_delta_sixteen
    (d := d) hdelta0 hdelta1 hsource hK
  have hreal : ratio ^ (4 : ℕ) * delta ^ (4 : ℕ) ≤
      delta ^ (68 : ℕ) := by
    calc
      ratio ^ (4 : ℕ) * delta ^ (4 : ℕ) ≤
          (delta ^ (16 : ℕ)) ^ (4 : ℕ) * delta ^ (4 : ℕ) := by
        gcongr
      _ = delta ^ (68 : ℕ) := by ring
  change ENNReal.ofReal (ratio ^ (4 : ℕ)) *
      (ENNReal.ofReal delta) ^ (4 : ℝ) ≤ _
  have hdeltaPow : (ENNReal.ofReal delta) ^ (4 : ℝ) =
      ENNReal.ofReal (delta ^ (4 : ℕ)) := by
    calc
      _ = (ENNReal.ofReal delta) ^ (4 : ℕ) := ENNReal.rpow_natCast _ 4
      _ = _ := (ENNReal.ofReal_pow hdelta0.le 4).symm
  rw [hdeltaPow]
  rw [← ENNReal.ofReal_mul (pow_nonneg hratio0 4)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The normalized fourth powers of a scalar `L⁴` field partition exactly
over the disjoint descendants of a triadic cube. -/
theorem descendantsAverage_cubeLpNorm_four_pow_four_eq
    {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) (depth : ℕ)
    (hf : MemLp f (4 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    descendantsAverage Q depth
        (fun R => (cubeLpNorm R (4 : ℝ≥0∞) f) ^ (4 : ℕ)) =
      (cubeLpNorm Q (4 : ℝ≥0∞) f) ^ (4 : ℕ) := by
  have hint : IntegrableOn (fun x => ‖f x‖ ^ (4 : ℝ))
      (cubeSet Q) volume := by
    exact integrableOn_of_integrable_normalizedCubeMeasure (Q := Q)
      (hf.integrable_norm_rpow (by norm_num) (by norm_num))
  calc
    descendantsAverage Q depth
        (fun R => (cubeLpNorm R (4 : ℝ≥0∞) f) ^ (4 : ℕ)) =
      descendantsAverage Q depth
        (fun R => cubeAverage R (fun x => ‖f x‖ ^ (4 : ℝ))) := by
          unfold descendantsAverage
          refine congrArg
            (fun t : ℝ =>
              (((descendantsAtDepth Q depth).card : ℝ)⁻¹) * t) ?_
          apply Finset.sum_congr rfl
          intro R hR
          simpa using
            (cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
              (Q := R) (p := (4 : ℝ≥0∞)) (f := f)
              (by norm_num) (by norm_num)
              (memLp_on_descendant_of_memLp_generic hR hf))
    _ = cubeAverage Q (fun x => ‖f x‖ ^ (4 : ℝ)) := by
          rw [← cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
            Q depth (fun x => ‖f x‖ ^ (4 : ℝ)) hint]
    _ = (cubeLpNorm Q (4 : ℝ≥0∞) f) ^ (4 : ℕ) := by
          simpa using
            (cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
              (Q := Q) (p := (4 : ℝ≥0∞)) (f := f)
              (by norm_num) (by norm_num) hf).symm

/-- Fourth-power finite-coordinate inequality in the form used for the
coordinate-sum weak-Hessian carrier. -/
theorem sum_fin_two_four_le_card_cubed_mul_sum_four
    {d : ℕ} (a : Fin d → Fin d → ℝ)
    (ha : ∀ i j, 0 ≤ a i j) :
    (∑ i : Fin d, ∑ j : Fin d, a i j) ^ (4 : ℕ) ≤
      ((d : ℝ) ^ 2) ^ (3 : ℕ) *
        ∑ i : Fin d, ∑ j : Fin d, (a i j) ^ (4 : ℕ) := by
  let I : Finset (Fin d × Fin d) :=
    (Finset.univ : Finset (Fin d)).product Finset.univ
  let b : Fin d × Fin d → ℝ := fun ij => a ij.1 ij.2
  have hpow := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := I) (f := b) (p := (4 : ℝ)) (by norm_num) (by
      intro ij hij
      exact ha ij.1 ij.2)
  have hsum : ∑ ij ∈ I, b ij =
      ∑ i : Fin d, ∑ j : Fin d, a i j := by
    change ∑ ij ∈
        (Finset.univ : Finset (Fin d)).product Finset.univ,
          a ij.1 ij.2 = _
    exact Finset.sum_product' Finset.univ Finset.univ a
  have hsumFour : ∑ ij ∈ I, b ij ^ (4 : ℝ) =
      ∑ i : Fin d, ∑ j : Fin d, (a i j) ^ (4 : ℝ) := by
    change ∑ ij ∈
        (Finset.univ : Finset (Fin d)).product Finset.univ,
          a ij.1 ij.2 ^ (4 : ℝ) = _
    exact Finset.sum_product' Finset.univ Finset.univ
      (fun i j => a i j ^ (4 : ℝ))
  have hcard : (I.card : ℝ) = (d : ℝ) ^ 2 := by
    simp [I, pow_two]
  rw [hsum, hsumFour, hcard] at hpow
  norm_num only [Real.rpow_natCast] at hpow
  simpa using hpow

/-- A global weak Hessian in normalized `L⁴` controls the normalized
descendant average of the fourth powers of the literal `B_z` observables.
The cell side is kept exact; this is where the source's sixteen-scale gain
enters after specialization. -/
theorem descendantsAverage_oneStepCellB_four_le
    {d : ℕ} {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u) (depth : ℕ)
    (hH4 : ∀ i j : Fin d,
      MemLp (fun x => H.hess i j x) (4 : ℝ≥0∞)
        (normalizedCubeMeasure Q)) :
    descendantsAverage Q depth (fun R =>
        if hR : R ∈ descendantsAtDepth Q depth then
          (oneStepCellB R
            (H.restrict (isOpen_openCubeSet R)
              (openCubeSet_subset_of_mem_descendantsAtDepth hR))) ^ (4 : ℕ)
        else 0) ≤
      (cubeScaleFactor Q / (3 : ℝ) ^ depth) ^ (4 : ℕ) *
        (((d : ℝ) ^ 2) ^ (3 : ℕ) *
          ∑ i : Fin d, ∑ j : Fin d,
            (cubeLpNorm Q (4 : ℝ≥0∞)
              (fun x => H.hess i j x)) ^ (4 : ℕ)) := by
  let D := descendantsAtDepth Q depth
  let c : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ depth
  have hc : 0 ≤ c := by
    dsimp only [c]
    exact div_nonneg (cubeScaleFactor_nonneg Q) (by positivity)
  have hpoint : ∀ R (hR : R ∈ descendantsAtDepth Q depth),
      (oneStepCellB R
          (H.restrict (isOpen_openCubeSet R)
            (openCubeSet_subset_of_mem_descendantsAtDepth hR))) ^ (4 : ℕ) ≤
        c ^ (4 : ℕ) * (((d : ℝ) ^ 2) ^ (3 : ℕ) *
          ∑ i : Fin d, ∑ j : Fin d,
            (cubeLpNorm R (4 : ℝ≥0∞)
              (fun x => H.hess i j x)) ^ (4 : ℕ)) := by
    intro R hR
    let HR := H.restrict (isOpen_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR)
    have hlocal : ∀ i j : Fin d,
        MemLp (fun x => HR.hess i j x) (4 : ℝ≥0∞)
          (normalizedCubeMeasure R) := by
      intro i j
      simpa only [HR, HasWeakHessianOn.restrict] using
        (memLp_on_descendant_of_memLp_generic hR (hH4 i j))
    have hsize := oneStepCellNormalizedHessianSize_le_hessianFourSize
      R HR hlocal
    have hside : cubeScaleFactor R = c := by
      simpa only [c] using cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR
    have hB : oneStepCellB R HR ≤
        c * (∑ i : Fin d, ∑ j : Fin d,
          cubeLpNorm R (4 : ℝ≥0∞) (fun x => H.hess i j x)) := by
      unfold oneStepCellB
      rw [hside]
      unfold oneStepCellHessianFourSize at hsize
      exact mul_le_mul_of_nonneg_left (by simpa only [HR,
        HasWeakHessianOn.restrict] using hsize) hc
    have hB0 : 0 ≤ oneStepCellB R HR := by
      unfold oneStepCellB
      exact mul_nonneg (cubeScaleFactor_nonneg R)
        (oneStepCellNormalizedHessianSize_nonneg R HR)
    have hsum0 : 0 ≤ ∑ i : Fin d, ∑ j : Fin d,
        cubeLpNorm R (4 : ℝ≥0∞) (fun x => H.hess i j x) := by
      exact Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => cubeLpNorm_nonneg R 4 _
    have hpowB := pow_le_pow_left₀ hB0 hB 4
    calc
      (oneStepCellB R HR) ^ (4 : ℕ) ≤
          (c * (∑ i : Fin d, ∑ j : Fin d,
            cubeLpNorm R (4 : ℝ≥0∞) (fun x => H.hess i j x))) ^
              (4 : ℕ) := hpowB
      _ = c ^ (4 : ℕ) *
          (∑ i : Fin d, ∑ j : Fin d,
            cubeLpNorm R (4 : ℝ≥0∞) (fun x => H.hess i j x)) ^
              (4 : ℕ) := by rw [mul_pow]
      _ ≤ c ^ (4 : ℕ) * (((d : ℝ) ^ 2) ^ (3 : ℕ) *
          ∑ i : Fin d, ∑ j : Fin d,
            (cubeLpNorm R (4 : ℝ≥0∞)
              (fun x => H.hess i j x)) ^ (4 : ℕ)) := by
        apply mul_le_mul_of_nonneg_left
        · exact sum_fin_two_four_le_card_cubed_mul_sum_four
            (fun i j => cubeLpNorm R (4 : ℝ≥0∞)
              (fun x => H.hess i j x)) (fun _ _ => cubeLpNorm_nonneg _ _ _)
        · positivity
  calc
    descendantsAverage Q depth (fun R =>
        if hR : R ∈ descendantsAtDepth Q depth then
          (oneStepCellB R
            (H.restrict (isOpen_openCubeSet R)
              (openCubeSet_subset_of_mem_descendantsAtDepth hR))) ^ (4 : ℕ)
        else 0) ≤
      descendantsAverage Q depth (fun R =>
        c ^ (4 : ℕ) * (((d : ℝ) ^ 2) ^ (3 : ℕ) *
          ∑ i : Fin d, ∑ j : Fin d,
            (cubeLpNorm R (4 : ℝ≥0∞)
              (fun x => H.hess i j x)) ^ (4 : ℕ))) := by
        apply descendantsAverage_le_descendantsAverage
        intro R hR
        rw [dif_pos hR]
        exact hpoint R hR
    _ = c ^ (4 : ℕ) * (((d : ℝ) ^ 2) ^ (3 : ℕ) *
          ∑ i : Fin d, ∑ j : Fin d,
            (cubeLpNorm Q (4 : ℝ≥0∞)
              (fun x => H.hess i j x)) ^ (4 : ℕ)) := by
        rw [descendantsAverage_mul_left]
        congr 1
        rw [descendantsAverage_mul_left]
        congr 1
        rw [descendantsAverage_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [descendantsAverage_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        exact descendantsAverage_cubeLpNorm_four_pow_four_eq
          Q (fun x => H.hess i j x) depth (hH4 i j)
    _ = (cubeScaleFactor Q / (3 : ℝ) ^ depth) ^ (4 : ℕ) *
        (((d : ℝ) ^ 2) ^ (3 : ℕ) *
          ∑ i : Fin d, ∑ j : Fin d,
            (cubeLpNorm Q (4 : ℝ≥0∞)
              (fun x => H.hess i j x)) ^ (4 : ℕ)) := by rfl

/-- Every Hessian coordinate `L⁴` norm is bounded by the full Hilbert-matrix
`L⁴` norm, so the coordinate fourth powers cost only `d²`. -/
theorem sum_cubeLpNorm_hessianCoord_four_pow_le
    {d : ℕ} (Q : TriadicCube d) (A : Vec d → Mat d)
    (hA : MemLp (fun x => HilbertMat.ofMat (A x)) (4 : ℝ≥0∞)
      (normalizedCubeMeasure Q)) :
    (∑ i : Fin d, ∑ j : Fin d,
        (cubeLpNorm Q (4 : ℝ≥0∞) (fun x => A x i j)) ^ (4 : ℕ)) ≤
      (d : ℝ) ^ 2 *
        (cubeLpNorm Q (4 : ℝ≥0∞)
          (fun x => HilbertMat.ofMat (A x))) ^ (4 : ℕ) := by
  have hcoord : ∀ i j : Fin d,
      cubeLpNorm Q (4 : ℝ≥0∞) (fun x => A x i j) ≤
        cubeLpNorm Q (4 : ℝ≥0∞) (fun x => HilbertMat.ofMat (A x)) := by
    intro i j
    unfold cubeLpNorm
    apply ENNReal.toReal_mono hA.eLpNorm_ne_top
    apply eLpNorm_mono_ae
    exact Filter.Eventually.of_forall fun x => by
      calc
        ‖A x i j‖ ≤ ‖(HilbertMat.ofMat (A x) : HilbertMat d).ofLp i‖ := by
          simpa only [HilbertMat.ofMat, HilbertVec.ofVec, PiLp.toLp_apply] using
            PiLp.norm_apply_le
              ((HilbertMat.ofMat (A x) : HilbertMat d).ofLp i) j
        _ ≤ ‖HilbertMat.ofMat (A x)‖ :=
          PiLp.norm_apply_le (HilbertMat.ofMat (A x) : HilbertMat d) i
  have hcoordPow : ∀ i j : Fin d,
      (cubeLpNorm Q (4 : ℝ≥0∞) (fun x => A x i j)) ^ (4 : ℕ) ≤
        (cubeLpNorm Q (4 : ℝ≥0∞)
          (fun x => HilbertMat.ofMat (A x))) ^ (4 : ℕ) := by
    intro i j
    exact pow_le_pow_left₀ (cubeLpNorm_nonneg Q 4 _) (hcoord i j) 4
  calc
    (∑ i : Fin d, ∑ j : Fin d,
        (cubeLpNorm Q (4 : ℝ≥0∞) (fun x => A x i j)) ^ (4 : ℕ)) ≤
      ∑ _i : Fin d, ∑ _j : Fin d,
        (cubeLpNorm Q (4 : ℝ≥0∞)
          (fun x => HilbertMat.ofMat (A x))) ^ (4 : ℕ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcoordPow i j
    _ = (d : ℝ) ^ 2 *
        (cubeLpNorm Q (4 : ℝ≥0∞)
          (fun x => HilbertMat.ofMat (A x))) ^ (4 : ℕ) := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      ring

/-- Matrix-norm version of `descendantsAverage_oneStepCellB_four_le`, ready
for direct insertion of the global Calderón--Zygmund estimate. -/
theorem descendantsAverage_oneStepCellB_four_le_matrix
    {d : ℕ} {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u) (depth : ℕ)
    (hH4 : MemLp
      (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))
      (4 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    descendantsAverage Q depth (fun R =>
        if hR : R ∈ descendantsAtDepth Q depth then
          (oneStepCellB R
            (H.restrict (isOpen_openCubeSet R)
              (openCubeSet_subset_of_mem_descendantsAtDepth hR))) ^ (4 : ℕ)
        else 0) ≤
      (cubeScaleFactor Q / (3 : ℝ) ^ depth) ^ (4 : ℕ) *
        ((d : ℝ) ^ (8 : ℕ) *
          (cubeLpNorm Q (4 : ℝ≥0∞)
            (fun x => HilbertMat.ofMat
              (fun i j => H.hess i j x))) ^ (4 : ℕ)) := by
  have hcoords : ∀ i j : Fin d,
      MemLp (fun x => H.hess i j x) (4 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    rw [memLp_piLp_iff] at hH4
    intro i j
    have hi := hH4 i
    rw [memLp_piLp_iff] at hi
    simpa only [Function.comp_apply, HilbertMat.ofMat, HilbertVec.ofVec,
      PiLp.toLp_apply] using hi j
  calc
    _ ≤ (cubeScaleFactor Q / (3 : ℝ) ^ depth) ^ (4 : ℕ) *
        (((d : ℝ) ^ 2) ^ (3 : ℕ) *
          ∑ i : Fin d, ∑ j : Fin d,
            (cubeLpNorm Q (4 : ℝ≥0∞)
              (fun x => H.hess i j x)) ^ (4 : ℕ)) :=
      descendantsAverage_oneStepCellB_four_le H depth hcoords
    _ ≤ (cubeScaleFactor Q / (3 : ℝ) ^ depth) ^ (4 : ℕ) *
        (((d : ℝ) ^ 2) ^ (3 : ℕ) *
          ((d : ℝ) ^ 2 *
            (cubeLpNorm Q (4 : ℝ≥0∞)
              (fun x => HilbertMat.ofMat
                (fun i j => H.hess i j x))) ^ (4 : ℕ))) := by
      gcongr
      exact sum_cubeLpNorm_hessianCoord_four_pow_le Q
        (fun x i j => H.hess i j x) hH4
    _ = (cubeScaleFactor Q / (3 : ℝ) ^ depth) ^ (4 : ℕ) *
        ((d : ℝ) ^ (8 : ℕ) *
          (cubeLpNorm Q (4 : ℝ≥0∞)
            (fun x => HilbertMat.ofMat
              (fun i j => H.hess i j x))) ^ (4 : ℕ)) := by ring

/-- Scale-normalized form of the descendant Hessian estimate.  The reference
scale `m` is kept independent of the ambient cube; in the one-step
application it is the lower cutoff endpoint. -/
theorem descendantsAverage_oneStepCellB_four_le_scaled_matrix
    {d : ℕ} {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u) (depth m : ℕ)
    (hH4 : MemLp
      (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))
      (4 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    descendantsAverage Q depth (fun R =>
        if hR : R ∈ descendantsAtDepth Q depth then
          (oneStepCellB R
            (H.restrict (isOpen_openCubeSet R)
              (openCubeSet_subset_of_mem_descendantsAtDepth hR))) ^ (4 : ℕ)
        else 0) ≤
      ((cubeScaleFactor Q / (3 : ℝ) ^ depth) / (3 : ℝ) ^ m) ^ (4 : ℕ) *
        ((d : ℝ) ^ (8 : ℕ) *
          (eLpNorm (fun x => (3 : ℝ) ^ m •
              HilbertMat.ofMat (fun i j => H.hess i j x)) 4
            (normalizedCubeMeasure Q)).toReal ^ (4 : ℕ)) := by
  have hscale : 0 < (3 : ℝ) ^ m := by positivity
  have hnorm :
      (eLpNorm (fun x => (3 : ℝ) ^ m •
          HilbertMat.ofMat (fun i j => H.hess i j x)) 4
        (normalizedCubeMeasure Q)).toReal =
        (3 : ℝ) ^ m *
          cubeLpNorm Q (4 : ℝ≥0∞)
            (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) := by
    unfold cubeLpNorm
    change (eLpNorm ((3 : ℝ) ^ m •
        (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))) 4
        (normalizedCubeMeasure Q)).toReal = _
    rw [eLpNorm_const_smul, ENNReal.toReal_mul]
    simp only [Real.enorm_eq_ofReal hscale.le, ENNReal.toReal_ofReal hscale.le]
  calc
    _ ≤ (cubeScaleFactor Q / (3 : ℝ) ^ depth) ^ (4 : ℕ) *
        ((d : ℝ) ^ (8 : ℕ) *
          (cubeLpNorm Q (4 : ℝ≥0∞)
            (fun x => HilbertMat.ofMat
              (fun i j => H.hess i j x))) ^ (4 : ℕ)) :=
      descendantsAverage_oneStepCellB_four_le_matrix H depth hH4
    _ = ((cubeScaleFactor Q / (3 : ℝ) ^ depth) / (3 : ℝ) ^ m) ^
          (4 : ℕ) *
        ((d : ℝ) ^ (8 : ℕ) *
          (eLpNorm (fun x => (3 : ℝ) ^ m •
              HilbertMat.ofMat (fun i j => H.hess i j x)) 4
            (normalizedCubeMeasure Q)).toReal ^ (4 : ℕ)) := by
      rw [hnorm]
      field_simp [hscale.ne']

private theorem norm_hilbertMat_ofMat_le_sum_abs {d : ℕ} (A : Mat d) :
    ‖HilbertMat.ofMat A‖ ≤ ∑ i : Fin d, ∑ j : Fin d, |A i j| := by
  let I : Finset (Fin d × Fin d) :=
    (Finset.univ : Finset (Fin d)).product Finset.univ
  let a : Fin d × Fin d → ℝ := fun ij => |A ij.1 ij.2|
  have hsumSq := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := I) (f := a) (fun ij _ => abs_nonneg _)
  have hleft : ‖HilbertMat.ofMat A‖ ^ 2 = ∑ ij ∈ I, a ij ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, HilbertMat.inner_def]
    change (∑ i : Fin d, ∑ j : Fin d, A i j * A i j) = _
    symm
    calc
      ∑ ij ∈ I, a ij ^ 2 =
          ∑ i : Fin d, ∑ j : Fin d, |A i j| ^ 2 := by
        exact Finset.sum_product' Finset.univ Finset.univ
          (fun i j => |A i j| ^ 2)
      _ = ∑ i : Fin d, ∑ j : Fin d, A i j * A i j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [sq_abs, pow_two]
  have hright : ∑ ij ∈ I, a ij =
      ∑ i : Fin d, ∑ j : Fin d, |A i j| := by
    change (∑ ij ∈
        (Finset.univ : Finset (Fin d)).product Finset.univ,
          |A ij.1 ij.2|) = _
    exact Finset.sum_product' Finset.univ Finset.univ
      (fun i j => |A i j|)
  apply le_of_sq_le_sq
  · rw [hleft, ← hright]
    exact hsumSq
  · exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => abs_nonneg _

/-- Spatial `L⁴` matrix norm bounded by the sum of the coordinate norms. -/
theorem eLpNorm_hilbertMat_ofMat_four_le_sum_coords
    {d : ℕ} {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (A : X → Mat d)
    (hcoord : ∀ i j : Fin d,
      AEStronglyMeasurable (fun x => A x i j) mu) :
    eLpNorm (fun x => HilbertMat.ofMat (A x)) 4 mu ≤
      ∑ i : Fin d, ∑ j : Fin d,
        eLpNorm (fun x => A x i j) 4 mu := by
  let f : Fin d × Fin d → X → ℝ := fun ij x => |A x ij.1 ij.2|
  have hf : ∀ ij : Fin d × Fin d, AEStronglyMeasurable (f ij) mu := by
    intro ij
    exact (hcoord ij.1 ij.2).norm
  calc
    eLpNorm (fun x => HilbertMat.ofMat (A x)) 4 mu ≤
        eLpNorm (∑ ij : Fin d × Fin d, f ij) 4 mu := by
      apply eLpNorm_mono_ae
      exact Filter.Eventually.of_forall fun x => by
        rw [Finset.sum_apply]
        have hnonneg : 0 ≤ ∑ ij : Fin d × Fin d, f ij x :=
          Finset.sum_nonneg fun ij _ => abs_nonneg _
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        simpa only [f, Fintype.sum_prod_type] using
          norm_hilbertMat_ofMat_le_sum_abs (A x)
    _ ≤ ∑ ij : Fin d × Fin d, eLpNorm (f ij) 4 mu := by
      exact eLpNorm_sum_le (s := Finset.univ)
        (fun ij _ => hf ij) (by norm_num)
    _ = ∑ i : Fin d, ∑ j : Fin d,
        eLpNorm (fun x => A x i j) 4 mu := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply eLpNorm_congr_norm_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [f, Real.norm_eq_abs, abs_abs]

/-- The coordinate payload in the full-Jacobian moment estimate is a
dimension-only constant times `delta^4` for unit probes. -/
theorem oneStepShellJacobianMatrix_payload_le_delta_four
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (p : Vec d)
    (hp : vecNormSq p = 1) :
    ((d : ℝ≥0∞) ^ 2) ^ (3 : ℝ) *
        ∑ i : Fin d, ∑ _j : Fin d,
          (ENNReal.ofReal
            (|p i| * (oneStepMultiplierDerivativeFourthConst * M.delta))) ^
              (4 : ℝ) ≤
      ((d : ℝ≥0∞) ^ 2) ^ (3 : ℝ) *
        ((d : ℝ≥0∞) ^ 2 *
          (ENNReal.ofReal oneStepMultiplierDerivativeFourthConst) ^ (4 : ℝ)) *
        (ENNReal.ofReal M.delta) ^ (4 : ℝ) := by
  have hpNorm := norm_le_one_of_vecNormSq_eq_one hp
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)] at hpNorm
  have hD0 : 0 ≤ oneStepMultiplierDerivativeFourthConst :=
    oneStepMultiplierDerivativeFourthConst_pos.le
  have hdelta0 : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  have hentry : ∀ i : Fin d,
      (ENNReal.ofReal
          (|p i| * (oneStepMultiplierDerivativeFourthConst * M.delta))) ^
            (4 : ℝ) ≤
        (ENNReal.ofReal
          (oneStepMultiplierDerivativeFourthConst * M.delta)) ^ (4 : ℝ) := by
    intro i
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    apply ENNReal.ofReal_le_ofReal
    have hi : |p i| ≤ 1 := by
      simpa only [Real.norm_eq_abs] using hpNorm i
    have hprod0 : 0 ≤ oneStepMultiplierDerivativeFourthConst * M.delta :=
      mul_nonneg hD0 hdelta0
    nlinarith [abs_nonneg (p i)]
  calc
    _ ≤ ((d : ℝ≥0∞) ^ 2) ^ (3 : ℝ) *
        ∑ _i : Fin d, ∑ _j : Fin d,
          (ENNReal.ofReal
            (oneStepMultiplierDerivativeFourthConst * M.delta)) ^ (4 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le _)
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      exact hentry i
    _ = ((d : ℝ≥0∞) ^ 2) ^ (3 : ℝ) *
        ((d : ℝ≥0∞) ^ 2 *
          (ENNReal.ofReal oneStepMultiplierDerivativeFourthConst) ^ (4 : ℝ)) *
        (ENNReal.ofReal M.delta) ^ (4 : ℝ) := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul hD0,
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4)]
      ring

/-- The parent-scale full Jacobian matrix has a uniform random fourth moment.
This is the matrix packaging of the coordinate Tonelli bounds. -/
theorem lintegral_eLpNorm_oneStepShellJacobianMatrix_four_le
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (hh : 0 < h)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    ∫⁻ omega,
        (eLpNorm (fun x => (3 : ℝ) ^ n •
          HilbertMat.ofMat
            ((oneStepShellForcingW14 M n h omega p
              Q hh).jacobian x))
          4 (normalizedCubeMeasure Q)) ^ (4 : ℝ)
        ∂M.P.toMeasure ≤
      ((d : ℝ≥0∞) ^ 2) ^ (3 : ℝ) *
        ∑ i : Fin d, ∑ _j : Fin d,
          (ENNReal.ofReal
            (|p i| * (oneStepMultiplierDerivativeFourthConst * M.delta))) ^
              (4 : ℝ) := by
  let nu := normalizedCubeMeasure Q
  let X : Fin d → Fin d →
      SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ≥0∞ := fun i j omega =>
    eLpNorm (fun x => (3 : ℝ) ^ n *
      (oneStepShellForcingW14 M n h omega p Q hh
        ).jacobian x i j) 4 nu
  have hXmeas : ∀ i j, Measurable (X i j) := by
    intro i j
    apply measurable_eLpNorm_four_prod_right
    exact measurable_const.mul
      (measurable_oneStepShellForcingW14_jacobian_uncurry
        M n h p Q hh i j)
  have hmatrix : ∀ omega,
      eLpNorm (fun x => (3 : ℝ) ^ n •
          HilbertMat.ofMat
            ((oneStepShellForcingW14 M n h omega p
              Q hh).jacobian x)) 4 nu ≤
        ∑ i : Fin d, ∑ j : Fin d, X i j omega := by
    intro omega
    apply eLpNorm_hilbertMat_ofMat_four_le_sum_coords
    intro i j
    have hm := (oneStepShellForcingW14 M n h omega p
      Q hh).jacobianHilbertMemLp
    rw [memLp_piLp_iff] at hm
    have hi := hm i
    rw [memLp_piLp_iff] at hi
    exact (hi j).aestronglyMeasurable.const_smul _
  calc
    _ ≤ ∫⁻ omega, (∑ i : Fin d, ∑ j : Fin d, X i j omega) ^ (4 : ℝ)
        ∂M.P.toMeasure := by
      apply lintegral_mono
      intro omega
      exact ENNReal.rpow_le_rpow (hmatrix omega) (by norm_num)
    _ ≤ ∫⁻ omega, ((d : ℝ≥0∞) ^ 2) ^ (3 : ℝ) *
          ∑ i : Fin d, ∑ j : Fin d, (X i j omega) ^ (4 : ℝ)
        ∂M.P.toMeasure := by
      apply lintegral_mono
      intro omega
      let I : Finset (Fin d × Fin d) :=
        (Finset.univ : Finset (Fin d)).product Finset.univ
      have hp := ENNReal.rpow_sum_le_const_mul_sum_rpow
        (s := I) (f := fun ij => X ij.1 ij.2 omega)
        (by norm_num : (1 : ℝ) ≤ 4)
      have hsum : ∑ ij ∈ I, X ij.1 ij.2 omega =
          ∑ i : Fin d, ∑ j : Fin d, X i j omega := by
        exact Finset.sum_product' Finset.univ Finset.univ
          (fun i j => X i j omega)
      have hsumFour : ∑ ij ∈ I, (X ij.1 ij.2 omega) ^ (4 : ℝ) =
          ∑ i : Fin d, ∑ j : Fin d, (X i j omega) ^ (4 : ℝ) := by
        exact Finset.sum_product' Finset.univ Finset.univ
          (fun i j => (X i j omega) ^ (4 : ℝ))
      have hcard : (I.card : ℝ≥0∞) = (d : ℝ≥0∞) ^ 2 := by
        simp [I, pow_two]
      rw [hsum, hsumFour, hcard] at hp
      norm_num only [ENNReal.rpow_natCast] at hp
      simpa using hp
    _ = ((d : ℝ≥0∞) ^ 2) ^ (3 : ℝ) *
        ∑ i : Fin d, ∑ j : Fin d,
          ∫⁻ omega, (X i j omega) ^ (4 : ℝ) ∂M.P.toMeasure := by
      rw [lintegral_const_mul]
      · rw [lintegral_finset_sum]
        · congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [lintegral_finset_sum]
          intro j _
          exact (hXmeas i j).pow_const _
        · intro i _
          exact Finset.measurable_sum Finset.univ fun j _ =>
            (hXmeas i j).pow_const _
      · exact Finset.measurable_sum Finset.univ fun i _ =>
          Finset.measurable_sum Finset.univ fun j _ =>
            (hXmeas i j).pow_const _
    _ ≤ ((d : ℝ≥0∞) ^ 2) ^ (3 : ℝ) *
        ∑ i : Fin d, ∑ j : Fin d,
          (ENNReal.ofReal
            (|p i| * (oneStepMultiplierDerivativeFourthConst * M.delta))) ^
              (4 : ℝ) := by
      apply mul_le_mul_right
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hcoord :=
        lintegral_lintegral_oneStepShellForcingW14_jacobian_four_le
          M n h p Q i j hh hscale
      have heq : ∫⁻ omega, (X i j omega) ^ (4 : ℝ) ∂M.P.toMeasure =
          ∫⁻ omega, ∫⁻ x,
            ‖(3 : ℝ) ^ n *
              |(oneStepShellForcingW14 M n h omega p
                Q hh).jacobian x i j|‖ₑ ^ (4 : ℝ)
              ∂nu ∂M.P.toMeasure := by
        apply lintegral_congr
        intro omega
        unfold X
        rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
        norm_num only [ENNReal.toReal_ofNat]
        rw [← ENNReal.rpow_mul, show (1 / 4 : ℝ) * 4 = 1 by norm_num,
          ENNReal.rpow_one]
        apply lintegral_congr
        intro x
        simp only [Real.enorm_eq_ofReal_abs, abs_mul, abs_abs]
      rw [heq]
      simpa only [nu] using hcoord

/-- A common positive spatial rescaling preserves a Calderon--Zygmund norm
comparison. -/
theorem eLpNorm_const_smul_le_const_mul_of_le
    {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (mu : Measure X) (p : ℝ≥0∞) (c : ℝ) (C : ℝ≥0∞)
    (f : X → E) (g : X → F)
    (h : eLpNorm f p mu ≤ C * eLpNorm g p mu) :
    eLpNorm (fun x => c • f x) p mu ≤
      C * eLpNorm (fun x => c • g x) p mu := by
  change eLpNorm (c • f) p mu ≤ C * eLpNorm (c • g) p mu
  rw [eLpNorm_const_smul, eLpNorm_const_smul]
  calc
    ‖c‖ₑ * eLpNorm f p mu ≤ ‖c‖ₑ * (C * eLpNorm g p mu) := by
      gcongr
    _ = C * (‖c‖ₑ * eLpNorm g p mu) := by ac_rfl

/-- Integrated descendant `B` estimate from a measurable family of global
weak-Hessian realizations and a pointwise Calderon--Zygmund comparison. -/
theorem lintegral_descendantsAverage_oneStepCellB_four_le_of_cz
    {d : ℕ} {Q : TriadicCube d}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h depth : ℕ)
    (p : Vec d) (hh : 0 < h) (hscale : (h : ℝ) ≤ M.delta⁻¹)
    (u : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d →
      H1Function (openCubeSet Q))
    (H : ∀ omega, HasWeakHessianOn (openCubeSet Q) (u omega))
    (hH4 : ∀ omega, MemLp
      (fun x => HilbertMat.ofMat (fun i j => (H omega).hess i j x))
      (4 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (C : ℝ≥0∞) (hCtop : C < ∞)
    (hcz : ∀ omega,
      eLpNorm (fun x => HilbertMat.ofMat
          (fun i j => (H omega).hess i j x)) 4
          (normalizedCubeMeasure Q) ≤
        C * eLpNorm (fun x => HilbertMat.ofMat
          ((oneStepShellForcingW14 M n h omega p Q hh).jacobian x)) 4
          (normalizedCubeMeasure Q)) :
    ∫⁻ omega, ENNReal.ofReal
        (descendantsAverage Q depth (fun R =>
          if hR : R ∈ descendantsAtDepth Q depth then
            (oneStepCellB R
              ((H omega).restrict (isOpen_openCubeSet R)
                (openCubeSet_subset_of_mem_descendantsAtDepth hR))) ^ (4 : ℕ)
          else 0)) ∂M.P.toMeasure ≤
      ENNReal.ofReal
          ((((cubeScaleFactor Q / (3 : ℝ) ^ depth) / (3 : ℝ) ^ n) ^
              (4 : ℕ)) * (d : ℝ) ^ (8 : ℕ)) *
        C ^ (4 : ℕ) *
          (((d : ℝ≥0∞) ^ 2) ^ (3 : ℝ) *
            ∑ i : Fin d, ∑ _j : Fin d,
              (ENNReal.ofReal
                (|p i| * (oneStepMultiplierDerivativeFourthConst * M.delta))) ^
                  (4 : ℝ)) := by
  let ratio : ℝ :=
    ((cubeScaleFactor Q / (3 : ℝ) ^ depth) / (3 : ℝ) ^ n) ^ (4 : ℕ)
  let X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ≥0∞ := fun omega =>
    eLpNorm (fun x => (3 : ℝ) ^ n • HilbertMat.ofMat
      (fun i j => (H omega).hess i j x)) 4 (normalizedCubeMeasure Q)
  let Y : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ≥0∞ := fun omega =>
    eLpNorm (fun x => (3 : ℝ) ^ n • HilbertMat.ofMat
      ((oneStepShellForcingW14 M n h omega p Q hh).jacobian x)) 4
      (normalizedCubeMeasure Q)
  have hXY : ∀ omega, X omega ≤ C * Y omega := by
    intro omega
    exact eLpNorm_const_smul_le_const_mul_of_le
      (normalizedCubeMeasure Q) 4 ((3 : ℝ) ^ n) C _ _ (hcz omega)
  have hXtop : ∀ omega, X omega ≠ ∞ := by
    intro omega
    exact ((hH4 omega).const_smul ((3 : ℝ) ^ n)).eLpNorm_ne_top
  have hYtop : ∀ omega, Y omega ≠ ∞ := by
    intro omega
    exact ((oneStepShellForcingW14 M n h omega p Q hh
      ).jacobianHilbertMemLp.const_smul ((3 : ℝ) ^ n)).eLpNorm_ne_top
  have hpoint : ∀ omega,
      ENNReal.ofReal
          (descendantsAverage Q depth (fun R =>
            if hR : R ∈ descendantsAtDepth Q depth then
              (oneStepCellB R
                ((H omega).restrict (isOpen_openCubeSet R)
                  (openCubeSet_subset_of_mem_descendantsAtDepth hR))) ^ (4 : ℕ)
            else 0)) ≤
        ENNReal.ofReal (ratio * (d : ℝ) ^ (8 : ℕ)) *
          (C ^ (4 : ℕ) * (Y omega) ^ (4 : ℕ)) := by
    intro omega
    have hdet := descendantsAverage_oneStepCellB_four_le_scaled_matrix
      (H omega) depth n (hH4 omega)
    have hratio0 : 0 ≤ ratio := by dsimp [ratio]; positivity
    have hd0 : 0 ≤ (d : ℝ) ^ (8 : ℕ) := by positivity
    have hCYtop : C * Y omega ≠ ∞ :=
      ENNReal.mul_ne_top hCtop.ne (hYtop omega)
    have hto : (X omega).toReal ≤ (C * Y omega).toReal :=
      ENNReal.toReal_mono hCYtop (hXY omega)
    have hreal :
        descendantsAverage Q depth (fun R =>
            if hR : R ∈ descendantsAtDepth Q depth then
              (oneStepCellB R
                ((H omega).restrict (isOpen_openCubeSet R)
                  (openCubeSet_subset_of_mem_descendantsAtDepth hR))) ^ (4 : ℕ)
            else 0) ≤
          ratio * (d : ℝ) ^ (8 : ℕ) * (C * Y omega).toReal ^ (4 : ℕ) := by
      calc
        _ ≤ ratio * ((d : ℝ) ^ (8 : ℕ) * (X omega).toReal ^ (4 : ℕ)) := by
          simpa only [ratio, X] using hdet
        _ ≤ ratio * ((d : ℝ) ^ (8 : ℕ) *
            (C * Y omega).toReal ^ (4 : ℕ)) := by
          gcongr
        _ = ratio * (d : ℝ) ^ (8 : ℕ) *
            (C * Y omega).toReal ^ (4 : ℕ) := by ring
    calc
      _ ≤ ENNReal.ofReal
          (ratio * (d : ℝ) ^ (8 : ℕ) *
            (C * Y omega).toReal ^ (4 : ℕ)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (ratio * (d : ℝ) ^ (8 : ℕ)) *
          (C ^ (4 : ℕ) * (Y omega) ^ (4 : ℕ)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hratio0 hd0),
          ENNReal.ofReal_pow ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hCYtop]
        ring
  calc
    _ ≤ ∫⁻ omega,
        ENNReal.ofReal (ratio * (d : ℝ) ^ (8 : ℕ)) *
          (C ^ (4 : ℕ) * (Y omega) ^ (4 : ℕ)) ∂M.P.toMeasure :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal (ratio * (d : ℝ) ^ (8 : ℕ)) * C ^ (4 : ℕ) *
        ∫⁻ omega, (Y omega) ^ (4 : ℕ) ∂M.P.toMeasure := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top hCtop.ne),
        mul_assoc]
    _ ≤ ENNReal.ofReal (ratio * (d : ℝ) ^ (8 : ℕ)) * C ^ (4 : ℕ) *
        (((d : ℝ≥0∞) ^ 2) ^ (3 : ℝ) *
          ∑ i : Fin d, ∑ _j : Fin d,
            (ENNReal.ofReal
              (|p i| * (oneStepMultiplierDerivativeFourthConst * M.delta))) ^
                (4 : ℝ)) := by
      gcongr
      have hf := lintegral_eLpNorm_oneStepShellJacobianMatrix_four_le
        M n h p Q hh hscale
      calc
        (∫⁻ omega, (Y omega) ^ (4 : ℕ) ∂M.P.toMeasure) =
            ∫⁻ omega, (Y omega) ^ (4 : ℝ) ∂M.P.toMeasure := by
          apply lintegral_congr
          intro omega
          exact (ENNReal.rpow_natCast (Y omega) 4).symm
        _ ≤ _ := by simpa only [Y] using hf
    _ = _ := rfl

/-- Dimension-only coefficient left after summing the shell-Jacobian matrix
coordinates. -/
def oneStepShellJacobianMatrixFourthConst (d : ℕ) : ℝ≥0∞ :=
  ((d : ℝ≥0∞) ^ 2) ^ (3 : ℝ) *
    ((d : ℝ≥0∞) ^ 2 *
      (ENNReal.ofReal oneStepMultiplierDerivativeFourthConst) ^ (4 : ℝ))

/-- Unit-probe specialization of the integrated descendant estimate. -/
theorem lintegral_descendantsAverage_oneStepCellB_four_le_of_cz_unit
    {d : ℕ} {Q : TriadicCube d}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h depth : ℕ)
    (p : Vec d) (hp : vecNormSq p = 1)
    (hh : 0 < h) (hscale : (h : ℝ) ≤ M.delta⁻¹)
    (u : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d →
      H1Function (openCubeSet Q))
    (H : ∀ omega, HasWeakHessianOn (openCubeSet Q) (u omega))
    (hH4 : ∀ omega, MemLp
      (fun x => HilbertMat.ofMat (fun i j => (H omega).hess i j x))
      (4 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (C : ℝ≥0∞) (hCtop : C < ∞)
    (hcz : ∀ omega,
      eLpNorm (fun x => HilbertMat.ofMat
          (fun i j => (H omega).hess i j x)) 4
          (normalizedCubeMeasure Q) ≤
        C * eLpNorm (fun x => HilbertMat.ofMat
          ((oneStepShellForcingW14 M n h omega p Q hh).jacobian x)) 4
          (normalizedCubeMeasure Q)) :
    ∫⁻ omega, ENNReal.ofReal
        (descendantsAverage Q depth (fun R =>
          if hR : R ∈ descendantsAtDepth Q depth then
            (oneStepCellB R
              ((H omega).restrict (isOpen_openCubeSet R)
                (openCubeSet_subset_of_mem_descendantsAtDepth hR))) ^ (4 : ℕ)
          else 0)) ∂M.P.toMeasure ≤
      ENNReal.ofReal
          ((((cubeScaleFactor Q / (3 : ℝ) ^ depth) / (3 : ℝ) ^ n) ^
              (4 : ℕ)) * (d : ℝ) ^ (8 : ℕ)) *
        C ^ (4 : ℕ) * oneStepShellJacobianMatrixFourthConst d *
          (ENNReal.ofReal M.delta) ^ (4 : ℝ) := by
  refine (lintegral_descendantsAverage_oneStepCellB_four_le_of_cz
    M n h depth p hh hscale u H hH4 C hCtop hcz).trans ?_
  have hpayload := oneStepShellJacobianMatrix_payload_le_delta_four M p hp
  calc
    _ ≤ ENNReal.ofReal
          ((((cubeScaleFactor Q / (3 : ℝ) ^ depth) / (3 : ℝ) ^ n) ^
              (4 : ℕ)) * (d : ℝ) ^ (8 : ℕ)) *
        C ^ (4 : ℕ) *
          (oneStepShellJacobianMatrixFourthConst d *
            (ENNReal.ofReal M.delta) ^ (4 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hpayload (zero_le _)
    _ = _ := by ring

/-- The actual measurable Dirichlet solution family admits the preceding
large-cube descendant estimate.  This is the literal finite-volume `B_z`
carrier before the source-depth arithmetic is inserted. -/
theorem exists_lintegral_oneStepDirichlet_descendantCellB_four_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h K depth : ℕ)
        (p : Vec d) (_hp : vecNormSq p = 1)
        (hh : 0 < h) (_hscale : (h : ℝ) ≤ M.delta⁻¹),
        ∃ (uD : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d →
              H10Function (openCubeSet (originCube d K)))
          (V : ∀ _omega, CubeVectorW1pFunction
              (originCube d K) oneStepFourExponent),
          ∃ hV : ∀ omega,
              (V omega).toField = (uD omega).toH1Function.grad,
            (∀ omega,
              CubeDirichletDivergenceProblem (originCube d K) (uD omega)
                (oneStepShellForcingH1 M n h omega p
                  (originCube d K) hh).toField) ∧
            Measurable (fun omega =>
              oneStepCellB (originCube d K)
                (weakHessianOfCubeVectorW1pFour (V omega) (hV omega))) ∧
            ∫⁻ omega, ENNReal.ofReal
                (descendantsAverage (originCube d K) depth (fun R =>
                  if hR : R ∈ descendantsAtDepth (originCube d K) depth then
                    (oneStepCellB R
                      ((weakHessianOfCubeVectorW1pFour (V omega) (hV omega)
                        ).restrict (isOpen_openCubeSet R)
                          (openCubeSet_subset_of_mem_descendantsAtDepth hR))) ^
                            (4 : ℕ)
                  else 0)) ∂M.P.toMeasure ≤
              ENNReal.ofReal
                  ((((cubeScaleFactor (originCube d K) / (3 : ℝ) ^ depth) /
                      (3 : ℝ) ^ n) ^ (4 : ℕ)) * (d : ℝ) ^ (8 : ℕ)) *
                C ^ (4 : ℕ) * oneStepShellJacobianMatrixFourthConst d *
                  (ENNReal.ofReal M.delta) ^ (4 : ℝ) := by
  obtain ⟨C, hCtop, hpack⟩ :=
    exists_measurable_oneStepShellDirichlet_cellB d
  refine ⟨C, hCtop, ?_⟩
  intro M n h K depth p hp hh hscale
  obtain ⟨uD, V, hV, huD, hBmeas, hcz⟩ := hpack M n h p K hh
  refine ⟨uD, V, hV, huD, hBmeas, ?_⟩
  apply lintegral_descendantsAverage_oneStepCellB_four_le_of_cz_unit
    M n h depth p hp hh hscale (fun omega => (uD omega).toH1Function)
      (fun omega => weakHessianOfCubeVectorW1pFour (V omega) (hV omega))
      (fun omega => by
        simpa only [weakHessianOfCubeVectorW1pFour] using
          (V omega).jacobianHilbertMemLp)
      C hCtop hcz

/-- Concrete source-depth Dirichlet `B_z` fourth-moment budget.  The outer
scale is arbitrary once it contains the source cells. -/
theorem exists_lintegral_oneStepDirichlet_descendantCellB_source_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h K : ℕ)
        (p : Vec d) (_hp : vecNormSq p = 1)
        (hh : 0 < h) (_hscale : (h : ℝ) ≤ M.delta⁻¹)
        (_hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
        (_hK : oneStepLocalizationScale n M.delta ≤ K),
        ∃ (uD : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d →
              H10Function (openCubeSet (originCube d K)))
          (V : ∀ _omega, CubeVectorW1pFunction
              (originCube d K) oneStepFourExponent),
          ∃ hV : ∀ omega,
              (V omega).toField = (uD omega).toH1Function.grad,
            (∀ omega,
              CubeDirichletDivergenceProblem (originCube d K) (uD omega)
                (oneStepShellForcingH1 M n h omega p
                  (originCube d K) hh).toField) ∧
            Measurable (fun omega =>
              oneStepCellB (originCube d K)
                (weakHessianOfCubeVectorW1pFour (V omega) (hV omega))) ∧
            ∫⁻ omega, ENNReal.ofReal
                (descendantsAverage (originCube d K)
                  (K - oneStepLocalizationScale n M.delta) (fun R =>
                    if hR : R ∈ descendantsAtDepth (originCube d K)
                        (K - oneStepLocalizationScale n M.delta) then
                      (oneStepCellB R
                        ((weakHessianOfCubeVectorW1pFour (V omega) (hV omega)
                          ).restrict (isOpen_openCubeSet R)
                            (openCubeSet_subset_of_mem_descendantsAtDepth hR))) ^
                              (4 : ℕ)
                    else 0)) ∂M.P.toMeasure ≤
              C * ENNReal.ofReal (M.delta ^ (68 : ℕ)) := by
  obtain ⟨Ccz, hCczTop, hraw⟩ :=
    exists_lintegral_oneStepDirichlet_descendantCellB_four_le d
  let C : ℝ≥0∞ := ENNReal.ofReal ((d : ℝ) ^ (8 : ℕ)) *
    Ccz ^ (4 : ℕ) * oneStepShellJacobianMatrixFourthConst d
  have hCtop : C < ∞ := by
    apply lt_top_iff_ne_top.2
    dsimp only [C]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_ne_top hCczTop.ne))
      (by
        unfold oneStepShellJacobianMatrixFourthConst
        finiteness)
  refine ⟨C, hCtop, ?_⟩
  intro M n h K p hp hh hscale hsource hK
  obtain ⟨uD, V, hV, huD, hBmeas, hmoment⟩ :=
    hraw M n h K (K - oneStepLocalizationScale n M.delta)
      p hp hh hscale
  refine ⟨uD, V, hV, huD, hBmeas, hmoment.trans ?_⟩
  let ratio : ℝ := cubeScaleFactor (originCube d K) /
    (3 : ℝ) ^ (K - oneStepLocalizationScale n M.delta) / (3 : ℝ) ^ n
  have hratio0 : 0 ≤ ratio := by dsimp [ratio]; positivity
  have hsourceMoment :=
    ofReal_oneStep_source_ratio_four_mul_delta_four_le_delta_sixtyEight
      (d := d) M.shellPrefix.delta_pos
      (M.shellPrefix.delta_le_half.trans (by norm_num)) hsource hK
  calc
    ENNReal.ofReal
          ((((cubeScaleFactor (originCube d K) /
              (3 : ℝ) ^ (K - oneStepLocalizationScale n M.delta)) /
                (3 : ℝ) ^ n) ^ (4 : ℕ)) * (d : ℝ) ^ (8 : ℕ)) *
        Ccz ^ (4 : ℕ) * oneStepShellJacobianMatrixFourthConst d *
          (ENNReal.ofReal M.delta) ^ (4 : ℝ) =
      C * (ENNReal.ofReal (ratio ^ (4 : ℕ)) *
        (ENNReal.ofReal M.delta) ^ (4 : ℝ)) := by
      rw [ENNReal.ofReal_mul (pow_nonneg hratio0 4)]
      dsimp only [C, ratio]
      ring
    _ ≤ C * ENNReal.ofReal (M.delta ^ (68 : ℕ)) := by
      gcongr

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
