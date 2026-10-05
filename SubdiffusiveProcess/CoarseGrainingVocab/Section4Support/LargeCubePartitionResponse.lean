module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ResponseRosenthal
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.MomentAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.ResponseObservableMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.TranslatedDefect
public import Homogenization.Sobolev.Fractional.EuclideanWspLocalization

@[expose] public section

/-!
# Section 4 support: translated large-cube partition response

This file supplies the missing finite-volume step in
`l.multiscale.response.large.cubes`: response subadditivity moves a normalized
parent response to the average of its scale-`L` descendants, and stationarity
plus finite-sum Minkowski removes that average without a cardinality loss.

Argument: the deterministic step is the public
`ResponseSubadditivityAndScalingTheory.responseJ_subadditive` route already
specialized in `Section4Recursion/ResponseRosenthal.lean`.  The translation step uses law transport.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal BigOperators

noncomputable section


/-- `ENNReal.ofReal` carries a normalized real descendant average to the
corresponding normalized `ENNReal` average when all entries are nonnegative. -/
theorem ofReal_descendantsAverage_eq_descendantsENNAverage_of_nonneg
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → ℝ)
    (hF : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ F R) :
    ENNReal.ofReal (descendantsAverage Q j F) =
      descendantsENNAverage Q j (fun R => ENNReal.ofReal (F R)) := by
  unfold descendantsAverage descendantsENNAverage
  have hcard : 0 ≤ ((descendantsAtDepth Q j).card : ℝ) := by positivity
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hcard),
    ENNReal.ofReal_inv_of_pos (by
      exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q j)),
    ENNReal.ofReal_natCast,
    ENNReal.ofReal_sum_of_nonneg hF]

/-- Pathwise normalized response subadditivity: the scalar unit-sphere
response of a parent cube is bounded by the normalized average of its
depth-`j` descendants. -/
theorem normalizedDefect_le_descendantsENNAverage {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (j : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    normalizedDefect M L (Ch02.cubeDomain Q) omega ≤
      descendantsENNAverage Q j (fun R =>
        normalizedDefect M L (Ch02.cubeDomain R) omega) := by
  unfold normalizedDefect paperScalarProbeMaxOn
  apply iSup_le
  intro e
  let p : Vec d := (Real.sqrt (ahom M L))⁻¹ • (e : Vec d)
  let q : Vec d := Real.sqrt (ahom M L) • (e : Vec d)
  have hsub := cutoffResponseOnCube_le_descendantsAverage M L p q Q j omega
  have hnonneg : ∀ R ∈ descendantsAtDepth Q j,
      0 ≤ cutoffResponseOnCube M L p q R omega := by
    intro R _hR
    exact Ch02.responseJ_nonneg (Ch02.cubeDomain R)
      ((aCutoffFamily M L omega).coeffOn R) p q
  calc
    ENNReal.ofReal
        (J (Ch02.cubeDomain Q)
          (aCutoffCoeffOnData M L omega (Ch02.cubeDomain Q)).toCoeffOn p q) =
        ENNReal.ofReal (cutoffResponseOnCube M L p q Q omega) := by
      rfl
    _ ≤ ENNReal.ofReal (descendantsAverage Q j
        (fun R => cutoffResponseOnCube M L p q R omega)) :=
      ENNReal.ofReal_le_ofReal hsub
    _ = descendantsENNAverage Q j (fun R =>
        ENNReal.ofReal (cutoffResponseOnCube M L p q R omega)) :=
      ofReal_descendantsAverage_eq_descendantsENNAverage_of_nonneg Q j _ hnonneg
    _ ≤ descendantsENNAverage Q j (fun R =>
        ⨆ e : {e : Vec d // vecNormSq e = 1},
          ENNReal.ofReal
            (J (Ch02.cubeDomain R)
              (aCutoffCoeffOnData M L omega (Ch02.cubeDomain R)).toCoeffOn
              ((Real.sqrt (ahom M L))⁻¹ • (e : Vec d))
              (Real.sqrt (ahom M L) • (e : Vec d)))) := by
      unfold descendantsENNAverage
      gcongr with R hR
      exact le_iSup (fun e : {e : Vec d // vecNormSq e = 1} =>
        ENNReal.ofReal
          (J (Ch02.cubeDomain R)
            (aCutoffCoeffOnData M L omega (Ch02.cubeDomain R)).toCoeffOn
            ((Real.sqrt (ahom M L))⁻¹ • (e : Vec d))
            (Real.sqrt (ahom M L) • (e : Vec d)))) e
    _ = descendantsENNAverage Q j (fun R =>
        normalizedDefect M L (Ch02.cubeDomain R) omega) := by
      rfl

/-- The induction hypothesis controls a large translated cube after
subadditivity onto its scale-`L` partition.  No descendant-cardinality loss
remains. -/
theorem normalizedDefect_largeCube_lpnorm_le_induction {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L k m0 : ℕ}
    {xi delta1 : ℝ} (hxi : 1 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1)
    (hLk : L ≤ k) (hLm0 : L ≤ m0) (Q : TriadicCube d)
    (hQ : Q.scale = (k : ℤ)) :
    paperENNRealLpNorm M.P.toMeasure xi
        (normalizedDefect M L (Ch02.cubeDomain Q)) ≤
      ENNReal.ofReal delta1 := by
  classical
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  let j := k - L
  let D := descendantsAtDepth Q j
  let c : ℝ≥0∞ := (D.card : ℝ≥0∞)⁻¹
  let X : TriadicCube d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun R omega =>
    normalizedDefect M L (Ch02.cubeDomain R) omega
  have hxiPos : 0 < xi := zero_lt_one.trans_le hxi
  have hD : D.Nonempty := by
    simpa only [D] using! descendantsAtDepth_nonempty Q j
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
      paperENNRealLpNorm M.P.toMeasure xi (X R) ≤ ENNReal.ofReal delta1 := by
    intro R hR
    exact inductionHypothesis_normalizedDefect_cube M hS hLm0 R (hscale R hR)
  have hpoint : ∀ omega,
      normalizedDefect M L (Ch02.cubeDomain Q) omega ≤
        c * ∑ R ∈ D, X R omega := by
    intro omega
    simpa only [descendantsENNAverage, D, c, X] using!
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
    _ ≤ c * ∑ _R ∈ D, ENNReal.ofReal delta1 := by
      gcongr with R hR
      exact hXmoment R hR
    _ = ENNReal.ofReal delta1 := by
      simp only [Finset.sum_const, nsmul_eq_mul, c]
      rw [← mul_assoc, ENNReal.inv_mul_cancel]
      · simp
      · exact_mod_cast Finset.card_ne_zero.mpr hD
      · exact ENNReal.coe_ne_top

/-- Every measurable observable of the cutoff sequence has the same paper
moment after an arbitrary deterministic translation.  This is the exact
stationarity equality used to remove the outer translated cube. -/
theorem paperENNRealLpNorm_comp_translatePotentialSample_eq {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : PaperCubeTranslate d)
    {xi : ℝ} (F : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞) (hF : Measurable F) :
    paperENNRealLpNorm M.P.toMeasure xi
        (fun omega => F (translatePotentialSample z omega)) =
      paperENNRealLpNorm M.P.toMeasure xi F := by
  unfold paperENNRealLpNorm
  let G : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun omega => F omega ^ xi
  have hG : Measurable G := ENNReal.continuous_rpow_const.measurable.comp hF
  change (∫⁻ omega, G (translatePotentialSequence z omega)
      ∂M.P.toMeasure) ^ xi⁻¹ = (∫⁻ omega, G omega ∂M.P.toMeasure) ^ xi⁻¹
  rw [← MeasureTheory.lintegral_map hG
    (measurable_translatePotentialSequence z),
    potentialSequenceLaw_stationary M z]

end

end SubdiffusiveProcess.CoarseGrainingVocab
