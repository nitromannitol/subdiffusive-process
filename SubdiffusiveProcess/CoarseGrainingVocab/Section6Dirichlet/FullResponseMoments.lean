module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.ResponseCoefficientMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.InductionHypothesis
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.MomentAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Action
public import SubdiffusiveProcess.Frozen.Section4.CoarseGrainedBound
public import SubdiffusiveProcess.Frozen.Section4.MultiscaleResponseLargeCubes

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

theorem aux_dedup_d153_coefficientSigma_rescaledCutoffCoefficient_le_ambient
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ) :
    coefficientSigma (fun omega ↦ rescaledCutoffCoefficient M L N omega) ≤
      (inferInstance : MeasurableSpace (Sample d)) := by
  unfold coefficientSigma
  refine iSup_le fun x ↦ ?_
  exact (measurable_const.mul
    (SubdiffusiveProcess.Frozen.Assumptions.measurable_aCutoff M L
      ((3 : ℝ) ^ N • x))).comap_le

private theorem coefficientSigma_rescaledCutoffCoefficient_le_ambient
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ) :
    coefficientSigma (fun omega ↦ rescaledCutoffCoefficient M L N omega) ≤
      (inferInstance : MeasurableSpace (Sample d)) := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.aux_dedup_d153_coefficientSigma_rescaledCutoffCoefficient_le_ambient (d := d) (M := M) (L := L) (N := N)

/-- Ambient measurability of the first real response readout. -/
theorem measurable_dirichletFullResponseOne
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ) (s : ℝ) :
    Measurable (dirichletFullResponseOne M L N s) := by
  exact (coefficientMeasurable_dirichletFullResponseOne M L N s).mono
    (coefficientSigma_rescaledCutoffCoefficient_le_ambient M L N) le_rfl

/-- Ambient measurability of the second real response readout. -/
theorem measurable_dirichletFullResponseTwo
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ) (s : ℝ) :
    Measurable (dirichletFullResponseTwo M L N s) := by
  exact (coefficientMeasurable_dirichletFullResponseTwo M L N s).mono
    (coefficientSigma_rescaledCutoffCoefficient_le_ambient M L N) le_rfl

/-- Ambient measurability of the raw second response error.  Keeping this
`ENNReal` carrier is what allows a finite moment to imply a.e. finiteness. -/
theorem measurable_dirichletFullResponseTwoENNReal
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ) (s : ℝ) :
    Measurable (fun omega ↦
      paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
        (s / 2) .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L)) := by
  exact
    (measurable_paperHomogenizationError_infinity_finite_rescaledCoefficientSigma
      M L N (originCube d (N : ℤ)) (N : ℤ) (s / 2) 2).mono
        (coefficientSigma_rescaledCutoffCoefficient_le_ambient M L N) le_rfl

/-- Passing from an `ENNReal` observable to its real readout can only decrease
its `eLpNorm`.  This direction needs no pointwise finiteness assumption. -/
private theorem eLpNorm_toReal_le_paperENNRealLpNorm
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p : ℝ} (hp : 0 < p) (X : Omega → ℝ≥0∞) :
    SubdiffusiveProcess.RawLp.eLpNorm (fun omega ↦ (X omega).toReal) (ENNReal.ofReal p) mu ≤
      paperENNRealLpNorm mu p X  := by
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  unfold paperENNRealLpNorm
  simp only [one_div]
  apply ENNReal.rpow_le_rpow _ (inv_nonneg.mpr hp.le)
  apply lintegral_mono
  intro omega
  apply ENNReal.rpow_le_rpow _ hp.le
  rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

/-- Fixed moments of the two full response errors are `O(delta)`, uniformly
in the cutoff and outer cube.  The lower bound on `xi` is exactly the
dimensionally enlarged fixed-moment choice made in the manuscript. -/
theorem exists_dirichletFullResponse_paper_moment_bound
    {d : ℕ} [NeZero d] {s xi : ℝ}
    (hs : 0 < s) (hsOne : s ≤ 1) (hxiOne : 1 ≤ xi)
    (hdim : 4 * (d : ℝ) * (s / 2)⁻¹ ≤ xi) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
        ∀ L N : ℕ, L ≤ N →
          paperENNRealLpNorm M.P.toMeasure xi
              (fun omega ↦ paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
                s .infinity (.finite 1) (aCutoffFamily M L omega) (ahom M L)) ≤
            ENNReal.ofReal (C * M.delta) ∧
          paperENNRealLpNorm M.P.toMeasure xi
              (fun omega ↦ paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
                (s / 2) .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L)) ≤
            ENNReal.ofReal (C * M.delta) := by
  obtain ⟨c0, C0, hc0, hC0, hcoarse⟩ :=
    SubdiffusiveProcess.Frozen.Section4.coarse_grained_bound (d := d)
  obtain ⟨c1, C1, hc1, hC1, hlarge⟩ :=
    SubdiffusiveProcess.Frozen.Section4.multiscale_response_large_cubes (d := d)
  let u := s / 2
  let K := 1 + C0 * xi * Real.log (2 + xi) + xi / (c1 * u)
  let D := 1 + C0 * xi + K
  let delta0 := (2 * D)⁻¹
  let C := C1 * Real.sqrt K *
    (Real.rpow s (-(1 / (1 : ℝ))) + Real.rpow u (-(1 / (2 : ℝ))))
  have hxi : 0 < xi := zero_lt_one.trans_le hxiOne
  have hu : 0 < u := by dsimp only [u]; linarith
  have hlog : 0 < Real.log (2 + xi) := Real.log_pos (by linarith)
  have hK : 1 < K := by
    dsimp only [K]
    have hfirst : 0 < C0 * xi * Real.log (2 + xi) := by positivity
    have hsecond : 0 < xi / (c1 * u) := by positivity
    linarith
  have hD : 1 < D := by
    dsimp only [D]
    have : 0 < C0 * xi := by positivity
    linarith
  have hdelta0 : 0 < delta0 := by dsimp only [delta0]; positivity
  have hC : 0 < C := by
    dsimp only [C]
    exact mul_pos (mul_pos hC1 (Real.sqrt_pos.2 (zero_lt_one.trans hK)))
      (add_pos (Real.rpow_pos_of_pos hs _)
        (Real.rpow_pos_of_pos hu _))
  refine ⟨delta0, C, hdelta0, hC, ?_⟩
  intro M hM L N hLN
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hdeltaOne : M.delta ≤ 1 :=
    M.shellPrefix.delta_le_half.trans (by norm_num)
  have hdeltaD : 2 * D * M.delta ≤ 1 := by
    calc
      2 * D * M.delta ≤ 2 * D * delta0 :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = 1 := by
        dsimp only [delta0]
        field_simp [hD.ne']
  have hdeltaK : K * M.delta ^ 2 < 1 := by
    have hKD : K < D := by dsimp only [D]; nlinarith [mul_pos hC0 hxi]
    have hKDdelta : K * M.delta < D * M.delta :=
      mul_lt_mul_of_pos_right hKD hdelta
    have hDdelta : D * M.delta ≤ 1 / 2 := by nlinarith
    have hdeltaHalf := M.shellPrefix.delta_le_half
    nlinarith
  let delta1 := K * M.delta ^ 2
  have hdelta1 : 0 < delta1 := by dsimp only [delta1]; positivity
  have hdelta1lt : delta1 < 1 := hdeltaK
  have hdeltaSq : M.delta ^ 2 ≤ delta1 := by
    dsimp only [delta1]
    nlinarith [sq_nonneg M.delta]
  have hcoarseRange :
      xi ≤ C0⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ := by
    have hlogNonzero : |Real.log M.delta| ≠ 0 := by
      have hlt : M.delta < 1 :=
        M.shellPrefix.delta_le_half.trans_lt (by norm_num)
      exact abs_ne_zero.mpr (ne_of_lt (Real.log_neg hdelta hlt))
    have hproduct : C0 * xi * (M.delta ^ 2 * |Real.log M.delta|) ≤ 1 := by
      have hlogloss := Section5Support.delta_sq_mul_abs_log_le_self
        hdelta hdeltaOne
      have hCxiD : C0 * xi ≤ D := by
        dsimp only [D]
        linarith [hK]
      have hmul := mul_le_mul_of_nonneg_left hlogloss
        (mul_nonneg hC0.le hxi.le)
      calc
        C0 * xi * (M.delta ^ 2 * |Real.log M.delta|) ≤
            C0 * xi * M.delta := hmul
        _ ≤ D * M.delta :=
          mul_le_mul_of_nonneg_right hCxiD hdelta.le
        _ ≤ 1 := by nlinarith
    rw [show C0⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ =
        (C0 * (M.delta ^ 2) * |Real.log M.delta|)⁻¹ by
      field_simp [hC0.ne', hdelta.ne', hlogNonzero]]
    have hden : 0 < C0 * (M.delta ^ 2) * |Real.log M.delta| := by positivity
    rw [show (C0 * (M.delta ^ 2) * |Real.log M.delta|)⁻¹ =
        (C0 * (M.delta ^ 2) * |Real.log M.delta|)⁻¹ * 1 by ring,
      le_inv_mul_iff₀ hden]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hproduct
  have hcoarseBound : ∀ m : ℕ,
      paperENNRealLpNorm M.P.toMeasure xi
          (normalizedDefect M m (Ch02.cubeDomain (originCube d (m : ℤ)))) ≤
        ENNReal.ofReal delta1 := by
    intro m
    have hm := (hcoarse M xi hxiOne hcoarseRange m).1
    refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
    have hcoeff : C0 * xi * Real.log (2 + xi) ≤ K := by
      dsimp only [K]
      have : 0 ≤ xi / (c1 * u) := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right hcoeff (sq_nonneg M.delta)
  have hIH : inductionHypothesis M N xi delta1 :=
    Section4Recursion.inductionHypothesis_of_scale_bounds
      M N hxiOne hdelta1 hdelta1lt (fun m _ ↦ hcoarseBound m)
  have hxiLargeU : xi ≤ c1 * u * (M.delta ^ 2)⁻¹ * delta1 := by
    rw [show delta1 = K * M.delta ^ 2 by rfl]
    field_simp [hdelta.ne']
    have hterm : xi < c1 * u * K := by
      dsimp only [K]
      calc
        xi = c1 * u * (xi / (c1 * u)) := by field_simp
        _ < c1 * u *
            (1 + C0 * xi * Real.log (2 + xi) + xi / (c1 * u)) := by
          gcongr
          have hfirst : 0 < C0 * xi * Real.log (2 + xi) := by positivity
          linarith
        _ = c1 * u * K := rfl
    linarith
  have huOne : u ≤ 1 := by dsimp only [u]; linarith
  have hdimS : 4 * (d : ℝ) * s⁻¹ ≤ xi := by
    have hinv : s⁻¹ ≤ u⁻¹ :=
      inv_anti₀ hu (by dsimp only [u]; linarith)
    exact (mul_le_mul_of_nonneg_left hinv (by positivity)).trans hdim
  have hxiLargeS : xi ≤ c1 * s * (M.delta ^ 2)⁻¹ * delta1 := by
    have hus : u ≤ s := by dsimp only [u]; linarith
    calc
      xi ≤ c1 * u * (M.delta ^ 2)⁻¹ * delta1 := hxiLargeU
      _ ≤ c1 * s * (M.delta ^ 2)⁻¹ * delta1 := by
        gcongr
  have hOne := hlarge M L N s delta1 xi hs hsOne hdeltaSq hdelta1lt hLN
    hdimS hxiLargeS hIH N hLN 0 1 (Or.inl rfl)
  have hTwo := hlarge M L N u delta1 xi hu huOne hdeltaSq hdelta1lt hLN
    hdim hxiLargeU hIH N hLN 0 2 (Or.inr rfl)
  have hOnePaper : paperENNRealLpNorm M.P.toMeasure xi
      (fun omega ↦ paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
        s .infinity (.finite 1) (aCutoffFamily M L omega) (ahom M L)) ≤
      ENNReal.ofReal (C1 * Real.rpow s (-(1 / (1 : ℝ))) * Real.sqrt delta1) := by
    have hEq : (fun omega : Sample d ↦
        paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
          s .infinity (.finite 1) (aCutoffFamily M L omega) (ahom M L)) =
        translatedHomogenizationErrorRandom M L N 0 s 1 := by
      funext omega
      simp [translatedHomogenizationErrorRandom]
    rw [hEq]
    simpa only [Nat.cast_one] using hOne
  have hTwoPaper : paperENNRealLpNorm M.P.toMeasure xi
      (fun omega ↦ paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
        u .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L)) ≤
      ENNReal.ofReal (C1 * Real.rpow u (-(1 / (2 : ℝ))) * Real.sqrt delta1) := by
    have hEq : (fun omega : Sample d ↦
        paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
          u .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L)) =
        translatedHomogenizationErrorRandom M L N 0 u 2 := by
      funext omega
      simp [translatedHomogenizationErrorRandom]
    rw [hEq]
    norm_num at hTwo ⊢
    exact hTwo
  have hsqrtDelta : Real.sqrt delta1 = Real.sqrt K * M.delta := by
    dsimp only [delta1]
    rw [Real.sqrt_mul (zero_lt_one.trans hK).le,
      Real.sqrt_sq_eq_abs, abs_of_pos hdelta]
  constructor
  · refine hOnePaper.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hsqrtDelta]
    dsimp only [C]
    have hsecond : 0 ≤ Real.rpow u (-(1 / (2 : ℝ))) :=
      Real.rpow_nonneg hu.le _
    calc
      C1 * Real.rpow s (-(1 / (1 : ℝ))) * (Real.sqrt K * M.delta) =
          (C1 * Real.sqrt K) * Real.rpow s (-(1 / (1 : ℝ))) * M.delta := by
        ring
      _ ≤ (C1 * Real.sqrt K) *
          (Real.rpow s (-(1 / (1 : ℝ))) +
            Real.rpow u (-(1 / (2 : ℝ)))) * M.delta := by
        gcongr
        exact le_add_of_nonneg_right hsecond
      _ = C * M.delta := rfl
  · refine hTwoPaper.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hsqrtDelta]
    dsimp only [C]
    have hfirst : 0 ≤ Real.rpow s (-(1 / (1 : ℝ))) :=
      Real.rpow_nonneg hs.le _
    calc
      C1 * Real.rpow u (-(1 / (2 : ℝ))) * (Real.sqrt K * M.delta) =
          (C1 * Real.sqrt K) * Real.rpow u (-(1 / (2 : ℝ))) * M.delta := by
        ring
      _ ≤ (C1 * Real.sqrt K) *
          (Real.rpow s (-(1 / (1 : ℝ))) +
            Real.rpow u (-(1 / (2 : ℝ)))) * M.delta := by
        gcongr
        exact le_add_of_nonneg_left hfirst
      _ = C * M.delta := rfl

/-- Real-valued form of `exists_dirichletFullResponse_paper_moment_bound`.
It is the direct interface used by the eventual common random factor. -/
theorem exists_dirichletFullResponse_moment_bound
    {d : ℕ} [NeZero d] {s xi : ℝ}
    (hs : 0 < s) (hsOne : s ≤ 1) (hxiOne : 1 ≤ xi)
    (hdim : 4 * (d : ℝ) * (s / 2)⁻¹ ≤ xi) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
        ∀ L N : ℕ, L ≤ N →
          eLpNorm (dirichletFullResponseOne M L N s)
              (ENNReal.ofReal xi) M.P.toMeasure ≤
            ENNReal.ofReal (C * M.delta) ∧
          eLpNorm (dirichletFullResponseTwo M L N s)
              (ENNReal.ofReal xi) M.P.toMeasure ≤
            ENNReal.ofReal (C * M.delta) := by
  obtain ⟨delta0, C, hdelta0, hC, hpaper⟩ :=
    exists_dirichletFullResponse_paper_moment_bound hs hsOne hxiOne hdim
  refine ⟨delta0, C, hdelta0, hC, ?_⟩
  intro M hM L N hLN
  obtain ⟨hOne, hTwo⟩ := hpaper M hM L N hLN
  constructor
  · rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded
      (measurable_dirichletFullResponseOne M L N s).aestronglyMeasurable]
    exact (eLpNorm_toReal_le_paperENNRealLpNorm M.P.toMeasure
      (zero_lt_one.trans_le hxiOne)
      (fun omega ↦ paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
        s .infinity (.finite 1) (aCutoffFamily M L omega) (ahom M L))).trans hOne
  · rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded
      (measurable_dirichletFullResponseTwo M L N s).aestronglyMeasurable]
    exact (eLpNorm_toReal_le_paperENNRealLpNorm M.P.toMeasure
      (zero_lt_one.trans_le hxiOne)
      (fun omega ↦ paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
        (s / 2) .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L))).trans hTwo

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
