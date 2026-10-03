module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.CampanatoRepresentative

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

open MeasureTheory Homogenization Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The dimension-only coefficient of the Hölder row. -/
def smallContrastHolderOutputConstant (d : ℕ) : ℝ :=
  (smallContrastHolderChainLength d : ℝ) *
    smallContrastLocalHolderConstant d * smallContrastGradientConstant d

theorem smallContrastHolderOutputConstant_nonneg (d : ℕ) :
    0 ≤ smallContrastHolderOutputConstant d := by
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (smallContrastLocalHolderConstant_nonneg d))
    (smallContrastGradientConstant_nonneg d)

/-- The single dimension-only constant in the final Schauder statement. -/
def smallContrastSchauderConstant (d : ℕ) : ℝ :=
  max (smallContrastGradientConstant d) (smallContrastHolderOutputConstant d)

theorem smallContrastSchauderConstant_nonneg (d : ℕ) :
    0 ≤ smallContrastSchauderConstant d :=
  le_trans (smallContrastGradientConstant_nonneg d) (le_max_left _ _)

theorem smallContrastDataSize_nonneg
    {alpha : ℝ} (halpha : alpha < 1)
    (u : H1Function (smallContrastUnitBall d)) (f : Vec d → Vec d) :
    0 ≤ smallContrastDataSize d alpha u f := by
  exact add_nonneg ENNReal.toReal_nonneg
    (mul_nonneg (inv_nonneg.mpr (by linarith)) ENNReal.toReal_nonneg)

/-- A globally defined representative: the Campanato representative on the
interior half-ball and the original Sobolev representative elsewhere. -/
def smallContrastSchauderRepresentative
    (u : H1Function (smallContrastUnitBall d)) (x : Vec d) : ℝ :=
  if x ∈ smallContrastBall d (1 / 2) then
    smallContrastCampanatoRepresentative (d := d) u.toFun x
  else u.toFun x

theorem smallContrastSchauderRepresentative_of_mem
    {u : H1Function (smallContrastUnitBall d)} {x : Vec d}
    (hx : x ∈ smallContrastBall d (1 / 2)) :
    smallContrastSchauderRepresentative u x =
      smallContrastCampanatoRepresentative (d := d) u.toFun x := by
  simp only [smallContrastSchauderRepresentative, if_pos hx]

theorem smallContrastSchauderRepresentative_ae_eq [NeZero d]
    {alpha K : ℝ} {u : H1Function (smallContrastUnitBall d)}
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hcamp : HasSmallContrastBallCampanatoBound alpha K u) :
    smallContrastSchauderRepresentative u =ᵐ[
      volume.restrict (smallContrastUnitBall d)] u.toFun := by
  have hhalf := campanatoRepresentative_ae_eq halpha hcamp
  have hhalfGlobal := (ae_restrict_iff'
    (isOpen_euclideanBall 0 (1 / 2 : ℝ)).measurableSet).1 hhalf
  refine (ae_restrict_iff'
    (isOpen_euclideanBall 0 (1 : ℝ)).measurableSet).2 ?_
  filter_upwards [hhalfGlobal] with x hx hunit
  by_cases hxin : x ∈ smallContrastBall d (1 / 2)
  · rw [smallContrastSchauderRepresentative_of_mem hxin, hx hxin]
  · simp only [smallContrastSchauderRepresentative, if_neg hxin]

theorem continuousOn_smallContrastSchauderRepresentative [NeZero d]
    {alpha K : ℝ} {u : H1Function (smallContrastUnitBall d)}
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1) (hK : 0 ≤ K)
    (hcamp : HasSmallContrastBallCampanatoBound alpha K u) :
    ContinuousOn (smallContrastSchauderRepresentative u)
      (smallContrastBall d (1 / 2)) := by
  exact (continuousOn_smallContrastCampanatoRepresentative halpha hK hcamp).congr
    (fun x hx => smallContrastSchauderRepresentative_of_mem hx)

/-- The repaired version of `p.Schauder.Calpha` (D-054 / E-28).  The output
constant depends only on `d`; all dependence on `alpha` is the displayed
factor `(1-alpha)^{-1}` inside `smallContrastDataSize`. -/
theorem smallContrastSchauder [NeZero d]
    {a : CoeffField d} {u : H1Function (smallContrastUnitBall d)}
    {f : Vec d → Vec d} {lam Lam delta alpha : ℝ}
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hEll : IsEllipticFieldOn lam Lam (smallContrastUnitBall d) a)
    (ha : CoefficientIdentityDistanceLE (smallContrastUnitBall d) a delta)
    (hu : IsMatrixDivFormWeakSolutionOn a (smallContrastUnitBall d) u f)
    (hf : MemVectorLpOn (smallContrastUnitBall d)
      (schauderSourceExponent d alpha) f) :
    SmallContrastSchauderConclusion alpha
      (smallContrastSchauderConstant d * smallContrastDataSize d alpha u f) u := by
  let D := smallContrastDataSize d alpha u f
  have hD : 0 ≤ D := smallContrastDataSize_nonneg halpha.2 u f
  have hgrad := gradientScaleBound_of_smallContrast hd halpha hdelta0 hdelta hEll ha hu hf
  have hgradInterior :=
    interiorGradientScaleBound_of_smallContrast hd halpha hdelta0 hdelta hEll ha hu hf
  have hcamp := ballCampanatoBound_of_interiorGradient halpha hgradInterior
  constructor
  · intro r hr hr1
    exact (hgrad r hr hr1).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hD)
  · refine ⟨smallContrastSchauderRepresentative u,
      continuousOn_smallContrastSchauderRepresentative halpha
        (mul_nonneg (smallContrastGradientConstant_nonneg d) hD) hcamp,
      smallContrastSchauderRepresentative_ae_eq halpha hcamp, ?_⟩
    intro x hx y hy
    have hsup := holder_smallContrastCampanatoRepresentative halpha
      (mul_nonneg (smallContrastGradientConstant_nonneg d) hD) hcamp
      (x := x) (y := y) hx hy
    have hpow : ‖x - y‖ ^ alpha ≤ euclideanNorm (x - y) ^ alpha :=
      Real.rpow_le_rpow (norm_nonneg _) (norm_le_euclideanNorm _)
        (by linarith [halpha.1] : 0 ≤ alpha)
    have hholderCoeff : 0 ≤
        (smallContrastHolderChainLength d : ℝ) *
          smallContrastLocalHolderConstant d * smallContrastGradientConstant d * D :=
      mul_nonneg (smallContrastHolderOutputConstant_nonneg d) hD
    rw [smallContrastSchauderRepresentative_of_mem hx,
      smallContrastSchauderRepresentative_of_mem hy]
    calc
      |smallContrastCampanatoRepresentative (d := d) u.toFun x -
          smallContrastCampanatoRepresentative (d := d) u.toFun y| ≤
          (smallContrastHolderChainLength d : ℝ) *
            smallContrastLocalHolderConstant d *
              (smallContrastGradientConstant d * D) * ‖x - y‖ ^ alpha := hsup
      _ = smallContrastHolderOutputConstant d * D * ‖x - y‖ ^ alpha := by
        rw [smallContrastHolderOutputConstant]
        ring
      _ ≤ smallContrastHolderOutputConstant d * D *
          euclideanNorm (x - y) ^ alpha :=
        mul_le_mul_of_nonneg_left hpow hholderCoeff
      _ ≤ smallContrastSchauderConstant d * D *
          euclideanNorm (x - y) ^ alpha := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hD)
          (Real.rpow_nonneg (euclideanNorm_nonneg _) _)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
