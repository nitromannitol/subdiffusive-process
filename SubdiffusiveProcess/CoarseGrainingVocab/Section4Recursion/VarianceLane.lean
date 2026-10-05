module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ResponseMeasureTheory
public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffRange
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open scoped BigOperators ProbabilityTheory

noncomputable section



/-! ## Mean/variance algebra -/

/-- The three-term mean/variance decomposition used when two stationary
coarse-matrix entries are compared. -/
theorem integral_sq_sub_le_three_variances_add_mean_gap
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    ∫ ω, (X ω - Y ω) ^ 2 ∂μ ≤
      3 * variance X μ + 3 * variance Y μ + 3 * (μ[X] - μ[Y]) ^ 2 := by
  let Xm : ℝ := μ[X]
  let Ym : ℝ := μ[Y]
  have hpoint : ∀ ω,
      (X ω - Y ω) ^ 2 ≤
        3 * (X ω - Xm) ^ 2 + 3 * (Y ω - Ym) ^ 2 + 3 * (Xm - Ym) ^ 2 := by
    intro ω
    have hsq₁ : 0 ≤ ((X ω - Xm) - (Y ω - Ym)) ^ 2 := sq_nonneg _
    have hsq₂ : 0 ≤ ((X ω - Xm) - (Xm - Ym)) ^ 2 := sq_nonneg _
    have hsq₃ : 0 ≤ ((Y ω - Ym) + (Xm - Ym)) ^ 2 := sq_nonneg _
    nlinarith
  have hleft : Integrable (fun ω => (X ω - Y ω) ^ 2) μ := by
    simpa only [Pi.sub_apply] using!
      (memLp_two_iff_integrable_sq (hX.sub hY).aestronglyMeasurable).1 (hX.sub hY)
  have hXcenter : Integrable (fun ω => (X ω - Xm) ^ 2) μ := by
    simpa only [Pi.sub_apply] using!
      (memLp_two_iff_integrable_sq
        (hX.sub (memLp_const Xm)).aestronglyMeasurable).1
          (hX.sub (memLp_const Xm))
  have hYcenter : Integrable (fun ω => (Y ω - Ym) ^ 2) μ := by
    simpa only [Pi.sub_apply] using!
      (memLp_two_iff_integrable_sq
        (hY.sub (memLp_const Ym)).aestronglyMeasurable).1
          (hY.sub (memLp_const Ym))
  have hright : Integrable (fun ω =>
      3 * (X ω - Xm) ^ 2 + 3 * (Y ω - Ym) ^ 2 + 3 * (Xm - Ym) ^ 2) μ := by
    exact ((hXcenter.const_mul 3).add (hYcenter.const_mul 3)).add (integrable_const _)
  calc
    ∫ ω, (X ω - Y ω) ^ 2 ∂μ ≤
        ∫ ω, (3 * (X ω - Xm) ^ 2 + 3 * (Y ω - Ym) ^ 2 +
          3 * (Xm - Ym) ^ 2) ∂μ :=
      integral_mono hleft hright hpoint
    _ = 3 * variance X μ + 3 * variance Y μ + 3 * (μ[X] - μ[Y]) ^ 2 := by
      rw [integral_add, integral_add, integral_const_mul, integral_const_mul,
        integral_const]
      · rw [← variance_eq_integral hX.aemeasurable,
          ← variance_eq_integral hY.aemeasurable]
        simp only [Xm, Ym, probReal_univ, one_smul]
      · exact hXcenter.const_mul 3
      · exact hYcenter.const_mul 3
      · exact (hXcenter.const_mul 3).add (hYcenter.const_mul 3)
      · exact integrable_const _

/-- Stationarity transports the variance of an inverse-star coarse-matrix
entry from any triadic cube to the centered cube at the same scale. -/
theorem variance_randomAStarInv_entry_cube_eq_originCube {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (i j : Fin d) :
    variance (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i j) M.P.toMeasure =
      variance (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        (randomAStarMatrix M L
          (Ch02.cubeDomain (originCube d Q.scale)) omega)⁻¹ i j) M.P.toMeasure := by
  let X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i j
  let Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    (randomAStarMatrix M L
      (Ch02.cubeDomain (originCube d Q.scale)) omega)⁻¹ i j
  have hXmeas : AEStronglyMeasurable X M.P.toMeasure :=
    ((((integrable_randomAStarMatrix_inv M L (Ch02.cubeDomain Q)).eval i).eval j).1)
  have hYmeas : AEStronglyMeasurable Y M.P.toMeasure :=
    ((((integrable_randomAStarMatrix_inv M L
      (Ch02.cubeDomain (originCube d Q.scale))).eval i).eval j).1)
  have hX : MemLp X 2 M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hXmeas).2
      (integrable_randomAStarInv_entry_sq M L (Ch02.cubeDomain Q) i j)
  have hY : MemLp Y 2 M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hYmeas).2
      (integrable_randomAStarInv_entry_sq M L
        (Ch02.cubeDomain (originCube d Q.scale)) i j)
  rw [variance_eq_sub hX, variance_eq_sub hY]
  exact congrArg₂ (fun a b : ℝ => a - b ^ 2)
    (integral_randomAStarInv_entry_sq_cube_eq_originCube M L Q i j)
    (integral_randomAStarInv_entry_cube_eq_originCube M L Q i j)

/-- Concrete Step-4 comparison for two translated inverse-star matrix
entries.  Both variance terms and both means are represented on centered
cubes, using! the stationarity and square-integrability interfaces from
`ResponseMeasureTheory`. -/
theorem integral_randomAStarInv_entry_sub_sq_le_mean_variance {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (Q R : TriadicCube d) (i j : Fin d) :
    ∫ omega,
        ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i j -
          (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j) ^ 2
        ∂M.P.toMeasure ≤
      3 * variance (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
          (randomAStarMatrix M L
            (Ch02.cubeDomain (originCube d Q.scale)) omega)⁻¹ i j) M.P.toMeasure +
      3 * variance (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
          (randomAStarMatrix M L
            (Ch02.cubeDomain (originCube d R.scale)) omega)⁻¹ i j) M.P.toMeasure +
      3 * ((∫ omega, (randomAStarMatrix M L
              (Ch02.cubeDomain (originCube d Q.scale)) omega)⁻¹ i j ∂M.P.toMeasure) -
            ∫ omega, (randomAStarMatrix M L
              (Ch02.cubeDomain (originCube d R.scale)) omega)⁻¹ i j ∂M.P.toMeasure) ^ 2 := by
  let X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i j
  let Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j
  have hXmeas : AEStronglyMeasurable X M.P.toMeasure :=
    ((((integrable_randomAStarMatrix_inv M L (Ch02.cubeDomain Q)).eval i).eval j).1)
  have hYmeas : AEStronglyMeasurable Y M.P.toMeasure :=
    ((((integrable_randomAStarMatrix_inv M L (Ch02.cubeDomain R)).eval i).eval j).1)
  have hX : MemLp X 2 M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hXmeas).2
      (integrable_randomAStarInv_entry_sq M L (Ch02.cubeDomain Q) i j)
  have hY : MemLp Y 2 M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hYmeas).2
      (integrable_randomAStarInv_entry_sq M L (Ch02.cubeDomain R) i j)
  have h := integral_sq_sub_le_three_variances_add_mean_gap hX hY
  rw [variance_randomAStarInv_entry_cube_eq_originCube M L Q i j,
    variance_randomAStarInv_entry_cube_eq_originCube M L R i j,
    integral_randomAStarInv_entry_cube_eq_originCube M L Q i j,
    integral_randomAStarInv_entry_cube_eq_originCube M L R i j] at h
  exact h

/-- Averaged translated-cube form of the Step-4 decomposition.  If every cube
in the finite family has scale `k`, stationarity collapses every summand to the
same scale-`k` variance and mean. -/
theorem average_integral_randomAStarInv_entry_sub_sq_le_mean_variance {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (s : Finset (TriadicCube d)) (hs : s.Nonempty) (k : ℤ)
    (hscale : ∀ Q ∈ s, Q.scale = k) (R : TriadicCube d) (i j : Fin d) :
    ((s.card : ℝ)⁻¹) * ∑ Q ∈ s,
        ∫ omega,
          ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i j -
            (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j) ^ 2
          ∂M.P.toMeasure ≤
      3 * variance (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
          (randomAStarMatrix M L
            (Ch02.cubeDomain (originCube d k)) omega)⁻¹ i j) M.P.toMeasure +
      3 * variance (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
          (randomAStarMatrix M L
            (Ch02.cubeDomain (originCube d R.scale)) omega)⁻¹ i j) M.P.toMeasure +
      3 * ((∫ omega, (randomAStarMatrix M L
              (Ch02.cubeDomain (originCube d k)) omega)⁻¹ i j ∂M.P.toMeasure) -
            ∫ omega, (randomAStarMatrix M L
              (Ch02.cubeDomain (originCube d R.scale)) omega)⁻¹ i j ∂M.P.toMeasure) ^ 2 := by
  let B : ℝ :=
    3 * variance (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        (randomAStarMatrix M L
          (Ch02.cubeDomain (originCube d k)) omega)⁻¹ i j) M.P.toMeasure +
    3 * variance (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        (randomAStarMatrix M L
          (Ch02.cubeDomain (originCube d R.scale)) omega)⁻¹ i j) M.P.toMeasure +
    3 * ((∫ omega, (randomAStarMatrix M L
            (Ch02.cubeDomain (originCube d k)) omega)⁻¹ i j ∂M.P.toMeasure) -
          ∫ omega, (randomAStarMatrix M L
            (Ch02.cubeDomain (originCube d R.scale)) omega)⁻¹ i j ∂M.P.toMeasure) ^ 2
  have hterm : ∀ Q ∈ s,
      (∫ omega,
        ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i j -
          (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j) ^ 2
        ∂M.P.toMeasure) ≤ B := by
    intro Q hQ
    have h := integral_randomAStarInv_entry_sub_sq_le_mean_variance M L Q R i j
    simpa only [hscale Q hQ] using! h
  calc
    ((s.card : ℝ)⁻¹) * ∑ Q ∈ s,
        ∫ omega,
          ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i j -
            (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j) ^ 2
          ∂M.P.toMeasure ≤
        ((s.card : ℝ)⁻¹) * ∑ _Q ∈ s, B := by
      gcongr with Q hQ
      exact hterm Q hQ
    _ = B := by
      have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
      simp [hcard]

/-! ## The finite-range coloring -/

/-- Same-colored distinct scale-`L` cubes are separated by the natural range
`sqrt(d) * 3^L` of the finite cutoff. -/
theorem cutoffRangeSeparated_of_cubeFreshShellColor_eq_of_scale {d : ℕ}
    {L : ℕ} {R S : TriadicCube d}
    (hRscale : R.scale = (L : ℤ)) (hSscale : S.scale = (L : ℤ))
    (hcolor : cubeFreshShellColor R = cubeFreshShellColor S) (hne : R ≠ S) :
    ∀ ⦃x y : Vec d⦄, x ∈ openCubeSet R → y ∈ openCubeSet S →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ L ≤ Ch02.vecNorm (x - y) := by
  intro x y hx hy
  let k : ℤ := -((L : ℤ) + 1)
  let R' := Ch02.dilateCube k R
  let S' := Ch02.dilateCube k S
  have hR' : R'.scale = -1 := by simp [R', k, hRscale]
  have hS' : S'.scale = -1 := by simp [S', k, hSscale]
  have hcolor' : cubeFreshShellColor R' = cubeFreshShellColor S' := by
    simpa [R', S', cubeFreshShellColor, Ch02.dilateCube] using! hcolor
  have hne' : R' ≠ S' := fun h => hne (Ch02.dilateCube_injective k h)
  have hx' : Ch02.dilateVec k x ∈ openCubeSet R' :=
    Ch02.dilateVec_mem_openCubeSet_dilateCube k hx
  have hy' : Ch02.dilateVec k y ∈ openCubeSet S' :=
    Ch02.dilateVec_mem_openCubeSet_dilateCube k hy
  have hsep := potentialRangeSeparated_of_cubeFreshShellColor_eq_of_scale_neg_one
    hR' hS' hcolor' hne'
      (openCubeSet_subset_cubeSet R' hx') (openCubeSet_subset_cubeSet S' hy')
  have hnormEq (z : Vec d) : Homogenization.euclideanNorm z = Ch02.vecNorm z := by
    rw [← sq_eq_sq₀ (Homogenization.euclideanNorm_nonneg z) (Ch02.vecNorm_nonneg z),
      Homogenization.euclideanNorm_sq, Ch02.vecNorm_sq_eq_vecNormSq]
  have hscaled : Real.sqrt (d : ℝ) ≤
      Ch02.triadicDilationFactor k * Ch02.vecNorm (x - y) := by
    rw [← hnormEq]
    simpa [Ch02.dilateVec, ← smul_sub, Homogenization.euclideanNorm_smul,
      abs_of_pos (Ch02.triadicDilationFactor_pos k)] using! hsep
  have hkEq : Ch02.triadicDilationFactor k = (3 : ℝ)⁻¹ * ((3 : ℝ) ^ L)⁻¹ := by
    dsimp only [k, Ch02.triadicDilationFactor]
    rw [zpow_neg, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have hpow : 0 < (3 : ℝ) ^ L := by positivity
  rw [hkEq] at hscaled
  have hmul := mul_le_mul_of_nonneg_left hscaled
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hpow.le)
  have hcancel : (3 * (3 : ℝ) ^ L) *
      ((3 : ℝ)⁻¹ * ((3 : ℝ) ^ L)⁻¹ * Ch02.vecNorm (x - y)) =
      Ch02.vecNorm (x - y) := by
    field_simp [ne_of_gt hpow]
  rw [hcancel] at hmul
  nlinarith [Real.sqrt_nonneg (d : ℝ), hpow]

/-- A fixed fresh-shell color class of scale-`L` descendants is pairwise
independent for every scalar observable measurable from the corresponding
cutoff-local sigma field. -/
theorem pairwise_indepFun_cutoff_descendants_colorClass {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (_hLn : L ≤ n)
    (c : FreshShellColor d)
    (X : TriadicCube d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ)
    (hX : ∀ R ∈ descendantsAtScale (originCube d (n : ℤ)) (L : ℤ),
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        ((LocalSigmaR (openCubeSet R)).comap (aCutoffRegCoeffField M L)) _ (X R)) :
    Set.Pairwise
      ↑((descendantsAtScale (originCube d (n : ℤ)) (L : ℤ)).filter
        (fun R => cubeFreshShellColor R = c))
      (fun R S => IndepFun (X R) (X S) M.P.toMeasure) := by
  intro R hR S hS hne
  change R ∈ (descendantsAtScale (originCube d (n : ℤ)) (L : ℤ)).filter
    (fun T => cubeFreshShellColor T = c) at hR
  change S ∈ (descendantsAtScale (originCube d (n : ℤ)) (L : ℤ)).filter
    (fun T => cubeFreshShellColor T = c) at hS
  rw [Finset.mem_filter] at hR hS
  rw [IndepFun_iff_Indep]
  have hsep := cutoffRangeSeparated_of_cubeFreshShellColor_eq_of_scale
    (L := L)
    (scale_eq_of_mem_descendantsAtScale hR.1)
    (scale_eq_of_mem_descendantsAtScale hS.1)
    (hR.2.trans hS.2.symm) hne
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left
      (indep_aCutoffRegCoeffField_local_of_separation M L
        (openCubeSet R) (openCubeSet S) (isOpen_openCubeSet R)
        (isOpen_openCubeSet S) hsep)
      (hX R hR.1).comap_le)
    (hX S hS.1).comap_le

/-! ## Colored-average variance -/

/-- Normalized finite average of random variables on a probability space. -/
noncomputable def probabilityFinsetAverage {Ω ι : Type*}
    (s : Finset ι) (X : ι → Ω → ℝ) : Ω → ℝ :=
  fun omega => ((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i omega

/-- The square of the mean of a normalized finite average is bounded by any
uniform one-cell second-moment budget.  This discharges the separate
`hlocalJMean` premise in the two-channel endpoint. -/
theorem sq_integral_probabilityFinsetAverage_le_of_secondMoment
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (s : Finset ι) (hs : s.Nonempty) (X : ι → Ω → ℝ) {B : ℝ}
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (hsecond : ∀ i ∈ s, ∫ omega, (X i omega) ^ 2 ∂μ ≤ B) :
    (μ[probabilityFinsetAverage s X]) ^ 2 ≤ B := by
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  have hint : μ[probabilityFinsetAverage s X] =
      ((s.card : ℝ)⁻¹) * ∑ i ∈ s, μ[X i] := by
    simp only [probabilityFinsetAverage, integral_const_mul]
    rw [integral_finsetSum]
    intro i hi
    exact (hX i hi).integrable one_le_two
  have hmeanSq : ∀ i ∈ s, μ[X i] ^ 2 ≤ B := by
    intro i hi
    have hvar := variance_nonneg (X i) μ
    rw [variance_eq_sub (hX i hi)] at hvar
    simp only [Pi.pow_apply] at hvar
    linarith [hsecond i hi]
  rw [hint, mul_pow]
  calc
    ((s.card : ℝ)⁻¹) ^ 2 * (∑ i ∈ s, μ[X i]) ^ 2 ≤
        ((s.card : ℝ)⁻¹) ^ 2 *
          ((s.card : ℝ) * ∑ i ∈ s, μ[X i] ^ 2) := by
      gcongr
      exact sq_sum_le_card_mul_sum_sq
    _ ≤ ((s.card : ℝ)⁻¹) ^ 2 *
          ((s.card : ℝ) * ∑ _i ∈ s, B) := by
      gcongr with i hi
      exact hmeanSq i hi
    _ = B := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      field_simp [hcard]

/-- A finite palette with pairwise independence inside every used color class
gives the standard `#colors / #blocks` variance gain. -/
theorem variance_probabilityFinsetAverage_le_of_coloring
    {Ω ι κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [DecidableEq κ]
    (s : Finset ι) (hs : s.Nonempty) (color : ι → κ)
    {X : ι → Ω → ℝ} {B : ℝ}
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (hindep : ∀ c ∈ s.image color,
      Set.Pairwise ↑(s.filter (fun i => color i = c))
        (fun i j => IndepFun (X i) (X j) μ))
    (hvar : ∀ i ∈ s, variance (X i) μ ≤ B) :
    variance (probabilityFinsetAverage s X) μ ≤
      ((s.image color).card : ℝ) * ((s.card : ℝ)⁻¹) * B := by
  let colors := s.image color
  let classSum : κ → Ω → ℝ := fun c =>
    ∑ i ∈ s.filter (fun i => color i = c), X i
  have hclassLp (c : κ) : MemLp (classSum c) 2 μ := by
    change MemLp (∑ i ∈ s.filter (fun i => color i = c), X i) 2 μ
    exact memLp_finsetSum' (s.filter (fun i => color i = c))
      (fun i hi => hX i (Finset.mem_of_mem_filter i hi))
  have havgLp : MemLp (probabilityFinsetAverage s X) 2 μ := by
    simpa only [probabilityFinsetAverage, Finset.sum_apply] using!
      (memLp_finsetSum' s (fun i hi => hX i hi)).const_mul ((s.card : ℝ)⁻¹)
  have hpartition : (fun omega => ∑ c ∈ colors, classSum c omega) =
      (fun omega => ∑ i ∈ s, X i omega) := by
    funext omega
    simpa only [colors, classSum, Finset.sum_apply] using!
      (Finset.sum_fiberwise_of_maps_to (s := s)
        (fun i hi => Finset.mem_image_of_mem color hi) (fun i => X i omega))
  have hcenteredPartition : (fun omega =>
      probabilityFinsetAverage s X omega - μ[probabilityFinsetAverage s X]) =
      (fun omega => (s.card : ℝ)⁻¹ *
        ∑ c ∈ colors, (classSum c omega - μ[classSum c])) := by
    funext omega
    simp only [probabilityFinsetAverage, integral_const_mul,
      integral_finsetSum _ (fun i hi => (hX i hi).integrable one_le_two)]
    have hIntPartition : ∑ c ∈ colors, μ[classSum c] = ∑ i ∈ s, μ[X i] := by
      rw [← integral_finsetSum _ (fun c _ => (hclassLp c).integrable one_le_two),
        ← integral_finsetSum _ (fun i hi => (hX i hi).integrable one_le_two)]
      exact integral_congr_ae (Filter.Eventually.of_forall (congrFun hpartition))
    rw [Finset.sum_sub_distrib, hIntPartition, congrFun hpartition omega]
    ring
  have hsqPoint : ∀ omega,
      (probabilityFinsetAverage s X omega - μ[probabilityFinsetAverage s X]) ^ 2 ≤
        ((s.card : ℝ)⁻¹) ^ 2 * (colors.card : ℝ) *
          ∑ c ∈ colors, (classSum c omega - μ[classSum c]) ^ 2 := by
    intro omega
    rw [congrFun hcenteredPartition omega, mul_pow]
    calc
      (↑s.card)⁻¹ ^ 2 * (∑ c ∈ colors, (classSum c omega - μ[classSum c])) ^ 2 ≤
          (↑s.card)⁻¹ ^ 2 *
            ((colors.card : ℝ) *
              ∑ c ∈ colors, (classSum c omega - μ[classSum c]) ^ 2) :=
        mul_le_mul_of_nonneg_left sq_sum_le_card_mul_sum_sq (sq_nonneg _)
      _ = (↑s.card)⁻¹ ^ 2 * (colors.card : ℝ) *
          ∑ c ∈ colors, (classSum c omega - μ[classSum c]) ^ 2 := by ring
  have hcenterInt : ∀ c, Integrable (fun omega =>
      (classSum c omega - μ[classSum c]) ^ 2) μ := fun c =>
    (memLp_two_iff_integrable_sq
      ((hclassLp c).sub (memLp_const _)).aestronglyMeasurable).1
        ((hclassLp c).sub (memLp_const _))
  have hbound := integral_mono
    ((memLp_two_iff_integrable_sq
      (havgLp.sub (memLp_const _)).aestronglyMeasurable).1
        (havgLp.sub (memLp_const _)))
    (((integrable_finsetSum _ fun c _ => hcenterInt c).const_mul
      (((s.card : ℝ)⁻¹) ^ 2 * (colors.card : ℝ))))
    hsqPoint
  have hbound' : variance (probabilityFinsetAverage s X) μ ≤
      ∫ x, ((s.card : ℝ)⁻¹) ^ 2 * (colors.card : ℝ) *
        ∑ i ∈ colors, (classSum i x - μ[classSum i]) ^ 2 ∂μ := by
    rw [variance_eq_integral havgLp.aemeasurable]
    simpa only [Pi.sub_apply] using! hbound
  rw [integral_const_mul, integral_finsetSum _ (fun c _ => hcenterInt c)] at hbound'
  have hclassVar (c : κ) (hc : c ∈ colors) :
      variance (classSum c) μ =
        ∑ i ∈ s.filter (fun i => color i = c), variance (X i) μ := by
    exact IndepFun.variance_sum
      (fun i hi => hX i (Finset.mem_of_mem_filter i hi)) (hindep c hc)
  have hsumVar : ∑ c ∈ colors, variance (classSum c) μ ≤ (s.card : ℝ) * B := by
    calc
      ∑ c ∈ colors, variance (classSum c) μ =
          ∑ c ∈ colors, ∑ i ∈ s.filter (fun i => color i = c), variance (X i) μ := by
        exact Finset.sum_congr rfl fun c hc => hclassVar c hc
      _ ≤ ∑ c ∈ colors, ∑ _i ∈ s.filter (fun i => color i = c), B := by
        gcongr with c hc i hi
        exact hvar i (Finset.mem_of_mem_filter i hi)
      _ = (s.card : ℝ) * B := by
        rw [show ∑ c ∈ colors, ∑ _i ∈ s.filter (fun i => color i = c), B =
          ∑ i ∈ s, B by
            exact Finset.sum_fiberwise_of_maps_to
              (fun i hi => Finset.mem_image_of_mem color hi) (fun _ => B)]
        simp
  have hnonneg : 0 ≤ ((s.card : ℝ)⁻¹) ^ 2 * (colors.card : ℝ) := by positivity
  calc
    variance (probabilityFinsetAverage s X) μ ≤
        ((s.card : ℝ)⁻¹) ^ 2 * (colors.card : ℝ) *
          ∑ c ∈ colors, variance (classSum c) μ := by
      simpa only [variance_eq_integral (hclassLp _).aemeasurable] using! hbound'
    _ ≤ ((s.card : ℝ)⁻¹) ^ 2 * (colors.card : ℝ) * ((s.card : ℝ) * B) :=
      mul_le_mul_of_nonneg_left hsumVar hnonneg
    _ = ((s.image color).card : ℝ) * ((s.card : ℝ)⁻¹) * B := by
      have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
      dsimp only [colors]
      field_simp

/-- Raw second moments can replace the per-block variance hypotheses in the
colored-average estimate. -/
theorem variance_probabilityFinsetAverage_le_of_coloring_secondMoment
    {Ω ι κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [DecidableEq κ]
    (s : Finset ι) (hs : s.Nonempty) (color : ι → κ)
    {X : ι → Ω → ℝ} {B : ℝ}
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (hindep : ∀ c ∈ s.image color,
      Set.Pairwise ↑(s.filter (fun i => color i = c))
        (fun i j => IndepFun (X i) (X j) μ))
    (hsecond : ∀ i ∈ s, ∫ omega, (X i omega) ^ 2 ∂μ ≤ B) :
    variance (probabilityFinsetAverage s X) μ ≤
      ((s.image color).card : ℝ) * ((s.card : ℝ)⁻¹) * B := by
  apply variance_probabilityFinsetAverage_le_of_coloring s hs color hX hindep
  intro i hi
  exact (variance_le_expectation_sq (hX i hi).aestronglyMeasurable).trans (hsecond i hi)

/-! ## Triadic cardinality and the literal scale decay -/

/-- The reciprocal number of scale-`L` descendants of `cube_n` is the literal
paper factor `3^{-d(n-L)}`. -/
theorem inv_card_descendantsAtScale_originCube_eq_rpow {d L n : ℕ}
    (hLn : L ≤ n) :
    (((descendantsAtScale (originCube d (n : ℤ)) (L : ℤ)).card : ℝ)⁻¹) =
      Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)) := by
  have hscale : (L : ℤ) ≤ (originCube d (n : ℤ)).scale := by
    change (L : ℤ) ≤ (n : ℤ)
    exact_mod_cast hLn
  rw [descendantsAtScale_eq_descendantsAtDepth (originCube d (n : ℤ)) hscale]
  simp only [originCube] at *
  have hdepth : Int.toNat ((n : ℤ) - (L : ℤ)) = n - L := by omega
  rw [hdepth, descendantsAtDepth_card]
  have hrpow : Real.rpow (3 : ℝ) (-((d * (n - L) : ℕ) : ℝ)) =
      ((3 : ℝ) ^ (d * (n - L)))⁻¹ := by
    calc
      Real.rpow (3 : ℝ) (-((d * (n - L) : ℕ) : ℝ)) =
          (Real.rpow (3 : ℝ) ((d * (n - L) : ℕ) : ℝ))⁻¹ :=
        Real.rpow_neg (by norm_num) _
      _ = ((3 : ℝ) ^ (d * (n - L)))⁻¹ :=
        congrArg Inv.inv (Real.rpow_natCast 3 (d * (n - L)))
  rw [hrpow]
  have hp : ((((3 ^ d) ^ (n - L) : ℕ) : ℝ)) =
      (((3 ^ (d * (n - L)) : ℕ) : ℝ)) :=
    congrArg (fun q : ℕ => (q : ℝ)) (pow_mul 3 d (n - L)).symm
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using! congrArg Inv.inv hp

/-- The fresh-shell palette converts the abstract colored-average ratio into
the literal triadic decay, with a dimension-only color constant. -/
theorem freshShellColor_ratio_descendantsAtScale_le {d L n : ℕ}
    (hLn : L ≤ n) :
    (((descendantsAtScale (originCube d (n : ℤ)) (L : ℤ)).image
        cubeFreshShellColor).card : ℝ) *
        (((descendantsAtScale (originCube d (n : ℤ)) (L : ℤ)).card : ℝ)⁻¹) ≤
      ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
        Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)) := by
  rw [inv_card_descendantsAtScale_originCube_eq_rpow hLn]
  have hcard := card_image_cubeFreshShellColor_le
    (descendantsAtScale (originCube d (n : ℤ)) (L : ℤ))
  have hcardReal :
      (((descendantsAtScale (originCube d (n : ℤ)) (L : ℤ)).image
        cubeFreshShellColor).card : ℝ) ≤ ((freshShellColorPeriod d ^ d : ℕ) : ℝ) := by
    exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right
    hcardReal
    (Real.rpow_nonneg (by norm_num) _)

/-! ## Quantitative two-channel closure -/

/-- The exact accepted Step-6 shape.  The finite-range calculation supplies
the two colored averages; the deterministic two-plus-eight estimate is the
`hsplit` hypothesis.  The dual-matrix and local-`J` second moments are explicit
payload hypotheses. -/
theorem variance_twoChannel_le_accepted_form
    {Ω ι κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [DecidableEq κ]
    (s : Finset ι) (hs : s.Nonempty) (color : ι → κ)
    {dual localJ : ι → Ω → ℝ} {targetVar ahom delta decay Ccolor : ℝ}
    (hdualLp : ∀ i ∈ s, MemLp (dual i) 2 μ)
    (hlocalJLp : ∀ i ∈ s, MemLp (localJ i) 2 μ)
    (hdualIndep : ∀ c ∈ s.image color,
      Set.Pairwise ↑(s.filter (fun i => color i = c))
        (fun i j => IndepFun (dual i) (dual j) μ))
    (hlocalJIndep : ∀ c ∈ s.image color,
      Set.Pairwise ↑(s.filter (fun i => color i = c))
        (fun i j => IndepFun (localJ i) (localJ j) μ))
    (hahom : 0 < ahom) (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hdecay0 : 0 ≤ decay)
    (hcolor : ((s.image color).card : ℝ) * ((s.card : ℝ)⁻¹) ≤ Ccolor * decay)
    (hdualSecond : ∀ i ∈ s,
      ∫ omega, (dual i omega) ^ 2 ∂μ ≤ ahom⁻¹ ^ 2 * delta)
    (hlocalJSecond : ∀ i ∈ s,
      ∫ omega, (localJ i omega) ^ 2 ∂μ ≤ ahom⁻¹ ^ 2 * delta ^ 2)
    (hsplit : targetVar ≤
      2 * variance (probabilityFinsetAverage s dual) μ +
        8 * μ[(probabilityFinsetAverage s localJ) ^ 2]) :
    targetVar ≤ (10 * Ccolor + 8) * ahom⁻¹ ^ 2 * delta * (delta + decay) := by
  have hdualVar := variance_probabilityFinsetAverage_le_of_coloring_secondMoment
    s hs color hdualLp hdualIndep hdualSecond
  have hJVar := variance_probabilityFinsetAverage_le_of_coloring_secondMoment
    s hs color hlocalJLp hlocalJIndep hlocalJSecond
  have hJavgLp : MemLp (probabilityFinsetAverage s localJ) 2 μ := by
    simpa only [probabilityFinsetAverage, Finset.sum_apply] using!
      (memLp_finsetSum' s (fun i hi => hlocalJLp i hi)).const_mul ((s.card : ℝ)⁻¹)
  have hlocalJMean :
      (μ[probabilityFinsetAverage s localJ]) ^ 2 ≤ ahom⁻¹ ^ 2 * delta ^ 2 :=
    sq_integral_probabilityFinsetAverage_le_of_secondMoment
      s hs localJ hlocalJLp hlocalJSecond
  have hJsecondEq : μ[(probabilityFinsetAverage s localJ) ^ 2] =
      variance (probabilityFinsetAverage s localJ) μ +
        μ[probabilityFinsetAverage s localJ] ^ 2 := by
    linarith only [variance_eq_sub hJavgLp]
  have hcolor0 : 0 ≤ Ccolor := by
    by_contra h
    have hneg : Ccolor * decay ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hdecay0
    have hleft0 : 0 ≤ ((s.image color).card : ℝ) * ((s.card : ℝ)⁻¹) := by positivity
    have hzero := le_antisymm (hcolor.trans hneg) hleft0
    have himage : (s.image color).Nonempty := hs.image color
    have hpos : 0 < ((s.image color).card : ℝ) * ((s.card : ℝ)⁻¹) :=
      mul_pos (by exact_mod_cast himage.card_pos) (inv_pos.mpr (by exact_mod_cast hs.card_pos))
    linarith
  have hdualBound : variance (probabilityFinsetAverage s dual) μ ≤
      Ccolor * decay * (ahom⁻¹ ^ 2 * delta) :=
    hdualVar.trans (mul_le_mul_of_nonneg_right hcolor
      (mul_nonneg (sq_nonneg _) hdelta0))
  have hJVarBound : variance (probabilityFinsetAverage s localJ) μ ≤
      Ccolor * decay * (ahom⁻¹ ^ 2 * delta ^ 2) :=
    hJVar.trans (mul_le_mul_of_nonneg_right hcolor
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  rw [hJsecondEq] at hsplit
  calc
    targetVar ≤ 2 * (Ccolor * decay * (ahom⁻¹ ^ 2 * delta)) +
        8 * (Ccolor * decay * (ahom⁻¹ ^ 2 * delta ^ 2) +
          ahom⁻¹ ^ 2 * delta ^ 2) := by
      exact hsplit.trans (add_le_add
        (mul_le_mul_of_nonneg_left hdualBound (by norm_num))
        (mul_le_mul_of_nonneg_left (add_le_add hJVarBound hlocalJMean) (by norm_num)))
    _ ≤ (10 * Ccolor + 8) * ahom⁻¹ ^ 2 * delta * (delta + decay) := by
      have hdeltaSqDecay : delta ^ 2 * decay ≤ delta * decay := by
        nlinarith [mul_nonneg hdelta0 hdecay0,
          mul_nonneg (sub_nonneg.mpr hdelta1) (mul_nonneg hdelta0 hdecay0)]
      have hinv : 0 ≤ ahom⁻¹ ^ 2 := (sq_pos_of_pos (inv_pos.mpr hahom)).le
      have hscaledDeltaSqDecay : ahom⁻¹ ^ 2 * (delta ^ 2 * decay) ≤
          ahom⁻¹ ^ 2 * (delta * decay) :=
        mul_le_mul_of_nonneg_left hdeltaSqDecay hinv
      nlinarith [mul_nonneg hcolor0 hdecay0,
        mul_nonneg hinv hdelta0, mul_nonneg hinv (sq_nonneg delta),
        hscaledDeltaSqDecay]



theorem variance_cutoff_descendants_twoChannel_le_accepted_form
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (hLn : L ≤ n)
    (dual localJ : TriadicCube d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ)
    {targetVar ahom delta : ℝ}
    (hdualLocal : ∀ R ∈ descendantsAtScale (originCube d (n : ℤ)) (L : ℤ),
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        ((LocalSigmaR (openCubeSet R)).comap (aCutoffRegCoeffField M L)) _ (dual R))
    (hlocalJLocal : ∀ R ∈ descendantsAtScale (originCube d (n : ℤ)) (L : ℤ),
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        ((LocalSigmaR (openCubeSet R)).comap (aCutoffRegCoeffField M L)) _ (localJ R))
    (hdualLp : ∀ R ∈ descendantsAtScale (originCube d (n : ℤ)) (L : ℤ),
      MemLp (dual R) 2 M.P.toMeasure)
    (hlocalJLp : ∀ R ∈ descendantsAtScale (originCube d (n : ℤ)) (L : ℤ),
      MemLp (localJ R) 2 M.P.toMeasure)
    (hahom : 0 < ahom) (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hdualSecond : ∀ R ∈ descendantsAtScale (originCube d (n : ℤ)) (L : ℤ),
      ∫ omega, (dual R omega) ^ 2 ∂M.P.toMeasure ≤ ahom⁻¹ ^ 2 * delta)
    (hlocalJSecond : ∀ R ∈ descendantsAtScale (originCube d (n : ℤ)) (L : ℤ),
      ∫ omega, (localJ R omega) ^ 2 ∂M.P.toMeasure ≤ ahom⁻¹ ^ 2 * delta ^ 2)
    (hsplit : targetVar ≤
      2 * variance (probabilityFinsetAverage
        (descendantsAtScale (originCube d (n : ℤ)) (L : ℤ)) dual) M.P.toMeasure +
      8 * M.P.toMeasure[(probabilityFinsetAverage
        (descendantsAtScale (originCube d (n : ℤ)) (L : ℤ)) localJ) ^ 2]) :
    targetVar ≤
      (10 * ((freshShellColorPeriod d ^ d : ℕ) : ℝ) + 8) * ahom⁻¹ ^ 2 * delta *
        (delta + Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ))) := by
  let s := descendantsAtScale (originCube d (n : ℤ)) (L : ℤ)
  have hs : s.Nonempty := by
    dsimp only [s]
    have hscale : (L : ℤ) ≤ (originCube d (n : ℤ)).scale := by
      change (L : ℤ) ≤ (n : ℤ)
      exact_mod_cast hLn
    rw [descendantsAtScale_eq_descendantsAtDepth (originCube d (n : ℤ)) hscale]
    exact descendantsAtDepth_nonempty _ _
  apply variance_twoChannel_le_accepted_form s hs cubeFreshShellColor
    (hdualLp := hdualLp) (hlocalJLp := hlocalJLp)
    (ahom := ahom) (delta := delta)
    (decay := Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)))
    (Ccolor := (freshShellColorPeriod d ^ d : ℕ))
  · intro c _hc
    exact pairwise_indepFun_cutoff_descendants_colorClass M L n hLn c dual hdualLocal
  · intro c _hc
    exact pairwise_indepFun_cutoff_descendants_colorClass M L n hLn c localJ hlocalJLocal
  · exact hahom
  · exact hdelta0
  · exact hdelta1
  · exact Real.rpow_nonneg (by norm_num) _
  · exact freshShellColor_ratio_descendantsAtScale_le hLn
  · exact hdualSecond
  · exact hlocalJSecond
  · exact hsplit

end

end SubdiffusiveProcess.CoarseGrainingVocab
