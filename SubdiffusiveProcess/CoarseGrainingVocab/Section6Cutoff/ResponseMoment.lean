import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.LargeCubePartitionResponse
import SubdiffusiveProcess.Frozen.Section4.CoarseGrainedBound




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open Filter MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- A matching-scale moment bound propagates to every larger triadic cube by
normalized response subadditivity and stationarity. -/
theorem normalizedDefect_largeCube_lpnorm_le_of_origin {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L k : ℕ} {xi : ℝ}
    (hxi : 1 ≤ xi) (hLk : L ≤ k) (Q : TriadicCube d)
    (hQ : Q.scale = (k : ℤ)) (A : ℝ≥0∞)
    (hbase :
      paperENNRealLpNorm M.P.toMeasure xi
          (normalizedDefect M L
            (Ch02.cubeDomain (originCube d (L : ℤ)))) ≤ A) :
    paperENNRealLpNorm M.P.toMeasure xi
        (normalizedDefect M L (Ch02.cubeDomain Q)) ≤ A := by
  classical
  let j := k - L
  let D := descendantsAtDepth Q j
  let c : ℝ≥0∞ := (D.card : ℝ≥0∞)⁻¹
  let X : TriadicCube d → Sample d → ℝ≥0∞ := fun R omega =>
    normalizedDefect M L (Ch02.cubeDomain R) omega
  have hxiPos : 0 < xi := zero_lt_one.trans_le hxi
  have hD : D.Nonempty := by
    simpa only [D] using descendantsAtDepth_nonempty Q j
  have hscale : ∀ R ∈ D, R.scale = (L : ℤ) := by
    intro R hR
    rw [show R.scale = Q.scale - (j : ℕ) from
      scale_eq_sub_of_mem_descendantsAtDepth hR, hQ]
    dsimp only [j]
    omega
  have hXmeas : ∀ R ∈ D, Measurable (X R) := by
    intro R _hR
    exact (measurable_normalizedDefect_potentialShellIndexSigma_Iic
      M L (Ch02.cubeDomain R)).mono
        (potentialShellIndexSigma_le_borel (d := d) (Set.Iic L)) le_rfl
  have hXmoment : ∀ R ∈ D,
      paperENNRealLpNorm M.P.toMeasure xi (X R) ≤ A := by
    intro R hR
    rw [show X R = normalizedDefect M L (Ch02.cubeDomain R) by rfl,
      paperENNRealLpNorm_normalizedDefect_cube_eq_origin M L xi R,
      hscale R hR]
    exact hbase
  have hpoint : ∀ omega,
      normalizedDefect M L (Ch02.cubeDomain Q) omega ≤
        c * ∑ R ∈ D, X R omega := by
    intro omega
    simpa only [descendantsENNAverage, D, c, X] using
      normalizedDefect_le_descendantsENNAverage M L Q j omega
  calc
    paperENNRealLpNorm M.P.toMeasure xi
        (normalizedDefect M L (Ch02.cubeDomain Q)) ≤
        paperENNRealLpNorm M.P.toMeasure xi
          (fun omega => c * ∑ R ∈ D, X R omega) :=
      paperENNRealLpNorm_mono_ae M.P.toMeasure hxiPos.le
        (Filter.Eventually.of_forall hpoint)
    _ = c * paperENNRealLpNorm M.P.toMeasure xi
          (fun omega => ∑ R ∈ D, X R omega) := by
      rw [paperENNRealLpNorm_const_mul_eq M.P.toMeasure hxiPos c]
      exact Finset.measurable_sum _ hXmeas
    _ ≤ c * ∑ R ∈ D,
          paperENNRealLpNorm M.P.toMeasure xi (X R) := by
      gcongr
      exact paperENNRealLpNorm_finset_sum_le M.P.toMeasure hxi D X hXmeas
    _ ≤ c * ∑ _R ∈ D, A := by
      gcongr with R hR
      exact hXmoment R hR
    _ = A := by
      simp only [Finset.sum_const, nsmul_eq_mul, c]
      rw [← mul_assoc, ENNReal.inv_mul_cancel]
      · simp
      · exact_mod_cast Finset.card_ne_zero.mpr hD
      · exact ENNReal.coe_ne_top

/-- The Section 4 headline controls the normalized cutoff response on every
cube scale, with the response cutoff truncated at `min n L`. -/
theorem exists_cutoffNormalizedResponse_moment_bound (d : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (xi : ℝ),
        1 ≤ xi →
        xi ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        ∀ L n : ℕ,
          paperENNRealLpNorm M.P.toMeasure xi
              (normalizedDefect M (min n L)
                (Ch02.cubeDomain (originCube d (n : ℤ)))) ≤
            ENNReal.ofReal (C * xi * Real.log (2 + xi) * M.delta ^ 2) := by
  obtain ⟨c, C, hc, hC, hheadline⟩ :=
    SubdiffusiveProcess.Frozen.Section4.coarse_grained_bound (d := d)
  refine ⟨c, C, hc, hC, ?_⟩
  intro M xi hxi hxiMax L n
  let q := min n L
  have hqn : q ≤ n := min_le_left _ _
  have hbase := (hheadline M xi hxi hxiMax q).1
  exact normalizedDefect_largeCube_lpnorm_le_of_origin M hxi hqn
    (originCube d (n : ℤ)) rfl _ (by simpa only [q] using hbase)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
