module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.CampanatoWindowGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SubcubeAveraging

@[expose] public section

/-!
# Mean comparison on concentric triadic cubes

The centered Campanato contract controls normalized `L²` oscillations.  This
module records the deterministic conversion to increments of the averages on
two consecutive concentric triadic cubes.  The price is the exact square root
of the volume ratio, `sqrt (3^d)`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- The half-exponent contraction supplied by the theta-Campanato row. -/
def boundedMultiplierCampanatoRatio : ℝ :=
  (3 : ℝ) ^ (-(1 / 2 : ℝ))

theorem boundedMultiplierCampanatoRatio_nonneg :
    0 ≤ boundedMultiplierCampanatoRatio := by
  exact Real.rpow_nonneg (by norm_num) _

theorem boundedMultiplierCampanatoRatio_lt_one :
    boundedMultiplierCampanatoRatio < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem three_rpow_neg_half_natCast_eq_campanatoRatio_pow (i : ℕ) :
    (3 : ℝ) ^ (-(1 / 2 : ℝ) * (i : ℝ)) =
      boundedMultiplierCampanatoRatio ^ i := by
  rw [boundedMultiplierCampanatoRatio, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]

private theorem geom_sum_range_le_inv_one_sub {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ i ∈ Finset.range N, r ^ i ≤ (1 - r)⁻¹ := by
  have hpos : (0 : ℝ) < 1 - r := by linarith
  have hmul := geom_sum_mul r N
  have hpow : (0 : ℝ) ≤ r ^ N := pow_nonneg hr0 N
  have hval : (∑ i ∈ Finset.range N, r ^ i) * (1 - r) =
      1 - r ^ N := by
    linear_combination -hmul
  rw [← one_div, le_div_iff₀ hpos, hval]
  linarith

/-- The finite half-exponent geometric series costs at most `5/2`. -/
theorem sum_range_boundedMultiplierCampanatoRatio_le (N : ℕ) :
    ∑ i ∈ Finset.range N, boundedMultiplierCampanatoRatio ^ i ≤ 5 / 2 := by
  have hsqrtlow : (5 : ℝ) / 3 ≤ Real.sqrt 3 := by
    rw [show (5 / 3 : ℝ) = Real.sqrt ((5 / 3 : ℝ) ^ 2) by
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5 / 3)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrtpos : (0 : ℝ) < Real.sqrt 3 := by positivity
  have hprod : boundedMultiplierCampanatoRatio * Real.sqrt 3 = 1 := by
    rw [boundedMultiplierCampanatoRatio, Real.sqrt_eq_rpow,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    norm_num
  have hrle : boundedMultiplierCampanatoRatio ≤ 3 / 5 := by
    nlinarith
  have hbound := geom_sum_range_le_inv_one_sub
    boundedMultiplierCampanatoRatio_nonneg
    boundedMultiplierCampanatoRatio_lt_one N
  have hpos : 0 < 1 - boundedMultiplierCampanatoRatio := by
    linarith [boundedMultiplierCampanatoRatio_lt_one]
  have hcancel : (1 - boundedMultiplierCampanatoRatio)⁻¹ *
      (1 - boundedMultiplierCampanatoRatio) = 1 :=
    inv_mul_cancel₀ (ne_of_gt hpos)
  have hinvnn : 0 ≤ (1 - boundedMultiplierCampanatoRatio)⁻¹ :=
    inv_nonneg.mpr hpos.le
  have hinv : (1 - boundedMultiplierCampanatoRatio)⁻¹ ≤ 5 / 2 := by
    nlinarith
  exact hbound.trans hinv

/-- The Lebesgue volume of a translated scale-`ell` cube. -/
theorem volume_translatedCube_toReal (ell : ℤ) (z : Vec d) :
    (volume (translatedCube d ell z)).toReal = ((3 : ℝ) ^ ell) ^ d := by
  rw [translatedCube, cube,
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.image_add_eq_translateSet,
    volume_translateSet_eq, volume_openCubeSet_toReal, cubeVolume_eq_pow_scale]
  simp only [originCube]

/-- A translated triadic cube has positive finite volume. -/
theorem volume_translatedCube_toReal_pos (ell : ℤ) (z : Vec d) :
    0 < (volume (translatedCube d ell z)).toReal := by
  rw [volume_translatedCube_toReal]
  positivity

/-- A translated triadic cube has finite volume. -/
theorem volume_translatedCube_ne_top (ell : ℤ) (z : Vec d) :
    volume (translatedCube d ell z) ≠ ⊤ := by
  apply ne_of_lt
  rw [translatedCube, cube,
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.image_add_eq_translateSet,
    volume_translateSet_eq]
  exact volume_openCubeSet_lt_top (originCube d ell)

/-- The square-root volume ratio between consecutive concentric triadic
cubes is exactly `sqrt (3^d)`. -/
theorem sqrt_consecutive_translatedCube_volumeRatio
    (ell : ℤ) (z : Vec d) :
    Real.sqrt
        ((volume (translatedCube d ell z)).toReal /
          (volume (translatedCube d (ell - 1) z)).toReal) =
      Real.sqrt ((3 : ℝ) ^ d) := by
  rw [volume_translatedCube_toReal, volume_translatedCube_toReal]
  have hthree : (3 : ℝ) ≠ 0 := by norm_num
  have hpow : (3 : ℝ) ^ (ell - 1) = (3 : ℝ) ^ ell / 3 := by
    rw [zpow_sub₀ hthree]
    norm_num
  rw [hpow, div_pow]
  have hscale : (3 : ℝ) ^ ell ≠ 0 := zpow_ne_zero _ hthree
  congr 1
  field_simp

/-- The consecutive-scale volume ratio is independent of both cube
centres. -/
theorem sqrt_consecutive_translatedCube_volumeRatio_twoCenters
    (ell : ℤ) (zInner zOuter : Vec d) :
    Real.sqrt
        ((volume (translatedCube d ell zOuter)).toReal /
          (volume (translatedCube d (ell - 1) zInner)).toReal) =
      Real.sqrt ((3 : ℝ) ^ d) := by
  rw [volume_translatedCube_toReal, volume_translatedCube_toReal]
  have hthree : (3 : ℝ) ≠ 0 := by norm_num
  have hpow : (3 : ℝ) ^ (ell - 1) = (3 : ℝ) ^ ell / 3 := by
    rw [zpow_sub₀ hthree]
    norm_num
  rw [hpow, div_pow]
  have hscale : (3 : ℝ) ^ ell ≠ 0 := zpow_ne_zero _ hthree
  congr 1
  field_simp

/-- Consecutive concentric means differ by at most the centered normalized
`L²` oscillation on the larger cube times `sqrt (3^d)`. -/
theorem abs_averageOn_translatedCube_pred_sub_le
    {ell : ℤ} {z : Vec d} {f : Vec d → ℝ}
    (hf : IntegrableOn f (translatedCube d ell z))
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2) (translatedCube d ell z)) :
    |averageOn (translatedCube d (ell - 1) z) f -
        averageOn (translatedCube d ell z) f| ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        normalizedL2On (translatedCube d ell z)
          (fun x ↦ f x - averageOn (translatedCube d ell z) f) := by
  have hsub : translatedCube d (ell - 1) z ⊆ translatedCube d ell z :=
    translatedCube_subset_translatedCube_sameCenter (by omega) z
  have hmeas : MeasurableSet (translatedCube d (ell - 1) z) := by
    rw [translatedCube_eq_metricBall]
    exact measurableSet_ball
  have hraw := abs_averageOn_subset_sub_averageOn_le
    hmeas hsub
    (volume_translatedCube_ne_top ell z)
    (volume_translatedCube_toReal_pos ell z)
    (volume_translatedCube_toReal_pos (ell - 1) z) hf hf2
  rwa [sqrt_consecutive_translatedCube_volumeRatio] at hraw

/-- Consecutive means on any nested pair of translated triadic cubes have
the same `sqrt (3^d)` price; concentricity is unnecessary. -/
theorem abs_averageOn_translatedCube_pred_sub_le_of_subset
    {ell : ℤ} {zInner zOuter : Vec d} {f : Vec d → ℝ}
    (hsub : translatedCube d (ell - 1) zInner ⊆
      translatedCube d ell zOuter)
    (hf : IntegrableOn f (translatedCube d ell zOuter))
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2)
      (translatedCube d ell zOuter)) :
    |averageOn (translatedCube d (ell - 1) zInner) f -
        averageOn (translatedCube d ell zOuter) f| ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        normalizedL2On (translatedCube d ell zOuter)
          (fun x ↦ f x - averageOn (translatedCube d ell zOuter) f) := by
  have hmeas : MeasurableSet (translatedCube d (ell - 1) zInner) := by
    rw [translatedCube_eq_metricBall]
    exact measurableSet_ball
  have hraw := abs_averageOn_subset_sub_averageOn_le
    hmeas hsub
    (volume_translatedCube_ne_top ell zOuter)
    (volume_translatedCube_toReal_pos ell zOuter)
    (volume_translatedCube_toReal_pos (ell - 1) zInner) hf hf2
  rwa [sqrt_consecutive_translatedCube_volumeRatio_twoCenters] at hraw

/-- Finite telescope along any nested chain of translated triadic cubes.
The centre may change at every scale. -/
theorem abs_averageOn_translatedCube_chain_sub_le_sum
    {ell : ℤ} (center : ℕ → Vec d) {f : Vec d → ℝ} (N : ℕ)
    (hsub : ∀ i < N,
      translatedCube d (ell - ((i + 1 : ℕ) : ℤ)) (center (i + 1)) ⊆
        translatedCube d (ell - (i : ℤ)) (center i))
    (hf : ∀ i < N,
      IntegrableOn f (translatedCube d (ell - (i : ℤ)) (center i)))
    (hf2 : ∀ i < N,
      IntegrableOn (fun x ↦ f x ^ 2)
        (translatedCube d (ell - (i : ℤ)) (center i))) :
    |averageOn (translatedCube d (ell - (N : ℤ)) (center N)) f -
        averageOn (translatedCube d ell (center 0)) f| ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        ∑ i ∈ Finset.range N,
          normalizedL2On
            (translatedCube d (ell - (i : ℤ)) (center i))
            (fun x ↦ f x - averageOn
              (translatedCube d (ell - (i : ℤ)) (center i)) f) := by
  let a : ℕ → ℝ := fun i ↦
    averageOn (translatedCube d (ell - (i : ℤ)) (center i)) f
  let price : ℕ → ℝ := fun i ↦
    Real.sqrt ((3 : ℝ) ^ d) *
      normalizedL2On
        (translatedCube d (ell - (i : ℤ)) (center i))
        (fun x ↦ f x - averageOn
          (translatedCube d (ell - (i : ℤ)) (center i)) f)
  have hstep : ∀ {i}, i < N → dist (a i) (a (i + 1)) ≤ price i := by
    intro i hi
    have hone : ell - ((i + 1 : ℕ) : ℤ) =
        (ell - (i : ℤ)) - 1 := by
      push_cast
      ring
    have hmean := abs_averageOn_translatedCube_pred_sub_le_of_subset
      (ell := ell - (i : ℤ)) (zInner := center (i + 1))
      (zOuter := center i) (f := f)
      (by simpa only [hone] using hsub i hi) (hf i hi) (hf2 i hi)
    simpa only [a, price, Real.dist_eq, abs_sub_comm, hone] using hmean
  have hpoly := dist_le_range_sum_of_dist_le N hstep
  simpa only [a, price, Real.dist_eq, abs_sub_comm, Int.ofNat_zero,
    sub_zero, Finset.mul_sum] using hpoly

/-- Geometric absorption for a nested translated-centre chain. -/
theorem abs_averageOn_translatedCube_chain_sub_le_of_geometric
    {ell : ℤ} (center : ℕ → Vec d) {f : Vec d → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (N : ℕ)
    (hsub : ∀ i < N,
      translatedCube d (ell - ((i + 1 : ℕ) : ℤ)) (center (i + 1)) ⊆
        translatedCube d (ell - (i : ℤ)) (center i))
    (hf : ∀ i < N,
      IntegrableOn f (translatedCube d (ell - (i : ℤ)) (center i)))
    (hf2 : ∀ i < N,
      IntegrableOn (fun x ↦ f x ^ 2)
        (translatedCube d (ell - (i : ℤ)) (center i)))
    (hdecay : ∀ i < N,
      normalizedL2On
          (translatedCube d (ell - (i : ℤ)) (center i))
          (fun x ↦ f x - averageOn
            (translatedCube d (ell - (i : ℤ)) (center i)) f) ≤
        A * boundedMultiplierCampanatoRatio ^ i) :
    |averageOn (translatedCube d (ell - (N : ℤ)) (center N)) f -
        averageOn (translatedCube d ell (center 0)) f| ≤
      5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * A := by
  have htelescope := abs_averageOn_translatedCube_chain_sub_le_sum
    center N hsub hf hf2
  have hsum :
      (∑ i ∈ Finset.range N,
          normalizedL2On
            (translatedCube d (ell - (i : ℤ)) (center i))
            (fun x ↦ f x - averageOn
              (translatedCube d (ell - (i : ℤ)) (center i)) f)) ≤
        ∑ i ∈ Finset.range N,
          A * boundedMultiplierCampanatoRatio ^ i := by
    exact Finset.sum_le_sum fun i hi ↦ hdecay i (Finset.mem_range.mp hi)
  have hsqrt : 0 ≤ Real.sqrt ((3 : ℝ) ^ d) := Real.sqrt_nonneg _
  have hgeom := sum_range_boundedMultiplierCampanatoRatio_le N
  calc
    |averageOn (translatedCube d (ell - (N : ℤ)) (center N)) f -
        averageOn (translatedCube d ell (center 0)) f| ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        ∑ i ∈ Finset.range N,
          normalizedL2On
            (translatedCube d (ell - (i : ℤ)) (center i))
            (fun x ↦ f x - averageOn
              (translatedCube d (ell - (i : ℤ)) (center i)) f) := htelescope
    _ ≤ Real.sqrt ((3 : ℝ) ^ d) *
        ∑ i ∈ Finset.range N,
          A * boundedMultiplierCampanatoRatio ^ i :=
      mul_le_mul_of_nonneg_left hsum hsqrt
    _ = Real.sqrt ((3 : ℝ) ^ d) * A *
        ∑ i ∈ Finset.range N, boundedMultiplierCampanatoRatio ^ i := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ Real.sqrt ((3 : ℝ) ^ d) * A * (5 / 2) :=
      mul_le_mul_of_nonneg_left hgeom (mul_nonneg hsqrt hA)
    _ = 5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * A := by ring

/-- Finite telescope of concentric triadic means.  The summand at index `i`
is the centered oscillation on the scale immediately outside the `i`-th
mean increment. -/
theorem abs_averageOn_translatedCube_sub_natCast_sub_le_sum
    {ell : ℤ} {z : Vec d} {f : Vec d → ℝ}
    (hf : IntegrableOn f (translatedCube d ell z))
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2) (translatedCube d ell z))
    (N : ℕ) :
    |averageOn (translatedCube d (ell - (N : ℤ)) z) f -
        averageOn (translatedCube d ell z) f| ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        ∑ i ∈ Finset.range N,
          normalizedL2On (translatedCube d (ell - (i : ℤ)) z)
            (fun x ↦ f x -
              averageOn (translatedCube d (ell - (i : ℤ)) z) f) := by
  induction N with
  | zero => simp
  | succ N ih =>
      let QN := translatedCube d (ell - (N : ℤ)) z
      have hQNsub : QN ⊆ translatedCube d ell z := by
        dsimp only [QN]
        exact translatedCube_subset_translatedCube_sameCenter (by omega) z
      have hstep := abs_averageOn_translatedCube_pred_sub_le
        (ell := ell - (N : ℤ)) (z := z) (f := f)
        (hf.mono_set hQNsub) (hf2.mono_set hQNsub)
      have htri :
          |averageOn (translatedCube d (ell - ((N + 1 : ℕ) : ℤ)) z) f -
              averageOn (translatedCube d ell z) f| ≤
            |averageOn (translatedCube d ((ell - (N : ℤ)) - 1) z) f -
              averageOn QN f| +
            |averageOn QN f - averageOn (translatedCube d ell z) f| := by
        have := abs_sub_le
          (averageOn (translatedCube d ((ell - (N : ℤ)) - 1) z) f)
          (averageOn QN f)
          (averageOn (translatedCube d ell z) f)
        have hscale : ell - ((N + 1 : ℕ) : ℤ) =
            (ell - (N : ℤ)) - 1 := by
          push_cast
          ring
        rw [hscale]
        simpa only [QN] using this
      calc
        |averageOn (translatedCube d (ell - ((N + 1 : ℕ) : ℤ)) z) f -
            averageOn (translatedCube d ell z) f| ≤
            |averageOn (translatedCube d ((ell - (N : ℤ)) - 1) z) f -
                averageOn QN f| +
              |averageOn QN f - averageOn (translatedCube d ell z) f| := htri
        _ ≤ Real.sqrt ((3 : ℝ) ^ d) *
                normalizedL2On QN
                  (fun x ↦ f x - averageOn QN f) +
              Real.sqrt ((3 : ℝ) ^ d) *
                ∑ i ∈ Finset.range N,
                  normalizedL2On (translatedCube d (ell - (i : ℤ)) z)
                    (fun x ↦ f x -
                      averageOn (translatedCube d (ell - (i : ℤ)) z) f) :=
          add_le_add hstep ih
        _ = Real.sqrt ((3 : ℝ) ^ d) *
              ∑ i ∈ Finset.range (N + 1),
                normalizedL2On (translatedCube d (ell - (i : ℤ)) z)
                  (fun x ↦ f x -
                    averageOn (translatedCube d (ell - (i : ℤ)) z) f) := by
          rw [Finset.sum_range_succ]
          dsimp only [QN]
          ring

/-- A geometric centered-oscillation row gives a dimension-only bound for
the full finite mean telescope. -/
theorem abs_averageOn_translatedCube_sub_natCast_sub_le_of_geometric
    {ell : ℤ} {z : Vec d} {f : Vec d → ℝ} {A : ℝ}
    (hA : 0 ≤ A)
    (hf : IntegrableOn f (translatedCube d ell z))
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2) (translatedCube d ell z))
    (N : ℕ)
    (hdecay : ∀ i < N,
      normalizedL2On (translatedCube d (ell - (i : ℤ)) z)
          (fun x ↦ f x -
            averageOn (translatedCube d (ell - (i : ℤ)) z) f) ≤
        A * boundedMultiplierCampanatoRatio ^ i) :
    |averageOn (translatedCube d (ell - (N : ℤ)) z) f -
        averageOn (translatedCube d ell z) f| ≤
      5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * A := by
  have htelescope := abs_averageOn_translatedCube_sub_natCast_sub_le_sum
    hf hf2 N
  have hsum :
      (∑ i ∈ Finset.range N,
          normalizedL2On (translatedCube d (ell - (i : ℤ)) z)
            (fun x ↦ f x -
              averageOn (translatedCube d (ell - (i : ℤ)) z) f)) ≤
        ∑ i ∈ Finset.range N,
          A * boundedMultiplierCampanatoRatio ^ i := by
    exact Finset.sum_le_sum fun i hi ↦ hdecay i (Finset.mem_range.mp hi)
  have hsqrt : 0 ≤ Real.sqrt ((3 : ℝ) ^ d) := Real.sqrt_nonneg _
  have hgeom := sum_range_boundedMultiplierCampanatoRatio_le N
  calc
    |averageOn (translatedCube d (ell - (N : ℤ)) z) f -
        averageOn (translatedCube d ell z) f| ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        ∑ i ∈ Finset.range N,
          normalizedL2On (translatedCube d (ell - (i : ℤ)) z)
            (fun x ↦ f x -
              averageOn (translatedCube d (ell - (i : ℤ)) z) f) := htelescope
    _ ≤ Real.sqrt ((3 : ℝ) ^ d) *
        ∑ i ∈ Finset.range N,
          A * boundedMultiplierCampanatoRatio ^ i :=
      mul_le_mul_of_nonneg_left hsum hsqrt
    _ = Real.sqrt ((3 : ℝ) ^ d) * A *
        ∑ i ∈ Finset.range N, boundedMultiplierCampanatoRatio ^ i := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ Real.sqrt ((3 : ℝ) ^ d) * A * (5 / 2) :=
      mul_le_mul_of_nonneg_left hgeom (mul_nonneg hsqrt hA)
    _ = 5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * A := by ring

/-- Nat-scale specialization of the geometric mean telescope, matching the
literal half-exponent row. -/
theorem abs_averageOn_translatedCube_nat_sub_le_of_halfDecay
    {top n : ℕ} (hntop : n ≤ top) {z : Vec d} {f : Vec d → ℝ} {A : ℝ}
    (hA : 0 ≤ A)
    (hf : IntegrableOn f (translatedCube d (top : ℤ) z))
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2)
      (translatedCube d (top : ℤ) z))
    (hdecay : ∀ s : ℕ, n ≤ s → s ≤ top →
      normalizedL2On (translatedCube d (s : ℤ) z)
          (fun x ↦ f x - averageOn (translatedCube d (s : ℤ) z) f) ≤
        A * (3 : ℝ) ^
          (-(1 / 2 : ℝ) * ((top : ℝ) - (s : ℝ)))) :
    |averageOn (translatedCube d (n : ℤ) z) f -
        averageOn (translatedCube d (top : ℤ) z) f| ≤
      5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * A := by
  let N := top - n
  have hscale : (top : ℤ) - (N : ℤ) = (n : ℤ) := by
    dsimp only [N]
    omega
  have hgeo := abs_averageOn_translatedCube_sub_natCast_sub_le_of_geometric
    (ell := (top : ℤ)) (z := z) (f := f) hA hf hf2 N
  rw [hscale] at hgeo
  apply hgeo
  intro i hi
  have hiTop : i ≤ top := by
    dsimp only [N] at hi
    omega
  let s := top - i
  have hns : n ≤ s := by
    dsimp only [s, N] at hi ⊢
    omega
  have hstop : s ≤ top := Nat.sub_le _ _
  have hscaleI : (top : ℤ) - (i : ℤ) = (s : ℤ) := by
    dsimp only [s]
    omega
  have hgap : (top : ℝ) - (s : ℝ) = (i : ℝ) := by
    dsimp only [s]
    rw [Nat.cast_sub hiTop]
    ring
  rw [hscaleI, ← three_rpow_neg_half_natCast_eq_campanatoRatio_pow]
  simpa only [hgap] using hdecay s hns hstop

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
