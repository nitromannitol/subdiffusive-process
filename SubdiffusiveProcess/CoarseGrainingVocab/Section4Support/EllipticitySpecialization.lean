import SubdiffusiveProcess.CoarseGrainingVocab.Section45Support

open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization Homogenization.Book

noncomputable section

/-!
# Section 4 support: the diagonal ellipticity specialization

These lemmas formalize Step 3 of the printed proof of `l.ellipticity.bound`:
at `m = n = L`, the tail coefficient is `ahom L`, and the root cube is one
of the cubes in the defining supremum.  Thus the homogenization-error display
is a direct specialization of the first display.
-/

/-- At equal cutoff and cube scales, the paper tail coefficient is the
homogenized coefficient. -/
theorem tailCoefficient_self {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) :
    tailCoefficient M L L ω x = ahom M L := by
  simp only [tailCoefficient, min_self]
  rw [div_self (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L ω x).ne']
  ring

/-- The normalized cube average of the equal-scale tail coefficient is
`ahom L`. -/
theorem tailCoefficientCubeAverage_self {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    tailCoefficientCubeAverage M L L ω = ahom M L := by
  unfold tailCoefficientCubeAverage Ch02.average
  simp_rw [tailCoefficient_self]
  rw [MeasureTheory.integral_const]
  simp only [Ch02.cubeDomain_coe]
  rw [MeasureTheory.measureReal_restrict_apply_univ]
  rw [Homogenization.volume_openCubeSet_toReal]
  simp only [smul_eq_mul]
  have hvolReal : MeasureTheory.volume.real
      (openCubeSet (originCube d (L : ℤ))) =
        Homogenization.cubeVolume (originCube d (L : ℤ)) := by
    change (MeasureTheory.volume
      (openCubeSet (originCube d (L : ℤ)))).toReal = _
    exact Homogenization.volume_openCubeSet_toReal _
  rw [hvolReal]
  rw [← mul_assoc, inv_mul_cancel₀ (Homogenization.cubeVolume_pos _).ne']
  simp



/-- Every triadic cube is its own descendant at its own scale. -/
theorem mem_descendantsAtScale_self {d : ℕ} (R : TriadicCube d) :
    R ∈ descendantsAtScale R R.scale := by
  simp [descendantsAtScale]

/-- Pointwise form of the printed Step 3 specialization. -/
theorem homogenizationErrorRandom_le_ellipticityMomentObservable_self
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    homogenizationErrorRandom M L L s ω ≤
      ellipticityMomentObservable M L (L : ℤ) s ω := by
  let Q : TriadicCube d := originCube d (L : ℤ)
  have hQ : Q ∈ descendantsAtScale Q (L : ℤ) := by
    change Q ∈ descendantsAtScale Q Q.scale
    exact mem_descendantsAtScale_self Q
  unfold ellipticityMomentObservable
  apply le_iSup_of_le (⟨L, le_rfl⟩ : {K : ℕ // L ≤ K})
  apply le_iSup_of_le (⟨Q, hQ⟩ :
    {R : TriadicCube d //
      R ∈ descendantsAtScale (originCube d (L : ℤ)) (L : ℤ)})
  simp only [Q, homogenizationErrorRandom]
  rw [tailCoefficientCubeAverage_self]



/-- Monotonicity of the paper's `ENNReal` `L^ξ` carrier. -/
theorem paperENNRealLpNorm_mono
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {ξ : ℝ}
    (hξ : 0 ≤ ξ) {X Y : Ω → ℝ≥0∞} (hXY : ∀ ω, X ω ≤ Y ω) :
    paperENNRealLpNorm μ ξ X ≤ paperENNRealLpNorm μ ξ Y := by
  unfold paperENNRealLpNorm
  apply ENNReal.rpow_le_rpow
  · exact lintegral_mono fun ω => ENNReal.rpow_le_rpow (hXY ω) hξ
  · positivity

/-- `L^ξ` form of the printed Step 3 specialization. -/
theorem homogenizationErrorRandom_lpnorm_le_ellipticityMomentObservable_self
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    {ξ s : ℝ} (hξ : 0 ≤ ξ) :
    paperENNRealLpNorm M.P.toMeasure ξ (homogenizationErrorRandom M L L s) ≤
      paperENNRealLpNorm M.P.toMeasure ξ
        (ellipticityMomentObservable M L (L : ℤ) s) := by
  exact paperENNRealLpNorm_mono M.P.toMeasure hξ
    (homogenizationErrorRandom_le_ellipticityMomentObservable_self M L s)

end

end SubdiffusiveProcess.CoarseGrainingVocab
