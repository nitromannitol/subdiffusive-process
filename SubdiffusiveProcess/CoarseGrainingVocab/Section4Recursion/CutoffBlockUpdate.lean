module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SharpTwoBlockMoment
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.BlockUpdate
public import SubdiffusiveProcess.Section3.AnnealedMatrixBounds

@[expose] public section

/-!
# Parent-cube cutoff block update

The localization update in the headline induction observes the full scale-`r`
cube while comparing cutoffs `k < r`.  This is a different carrier from the
scale-`k` descendant used by the sharp two-block positive-scale estimate.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization Homogenization.Book Homogenization.IndependentSums
open scoped ENNReal

noncomputable section


/-- The common full-parent majorant for the forward and inverse cutoff ratios
between `k` and `r`. -/
noncomputable def parentCubeCutoffRatioRepresentative {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (r k : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  Real.exp
      (coveredLowBlockEnvelope k r (r : ℤ) omega +
        ((r - k : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1

theorem parentCubeCutoffRatioRepresentative_nonneg {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (r k : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ parentCubeCutoffRatioRepresentative M r k omega := by
  unfold parentCubeCutoffRatioRepresentative
  apply sub_nonneg.mpr
  apply Real.one_le_exp
  exact add_nonneg (coveredLowBlockEnvelope_nonneg _ _ _ _)
    (mul_nonneg (by positivity) M.G4.tauSq_pos.le)

private theorem measurable_coveredLowBlockEnvelope_potentialShellIndexSigma_Ioi
    {d : ℕ} (r k : ℕ) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ (potentialShellIndexSigma (Set.Ioi k))
      inferInstance (coveredLowBlockEnvelope k r (r : ℤ)) := by
  let : MeasurableSpace (_root_.SubdiffusiveProcess.Model.PotentialSample d) := potentialShellIndexSigma (Set.Ioi k)
  let Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
    (shellCoverShifts d ((r : ℤ) - (k : ℤ))).sup'
      (shellCoverShifts_nonempty d ((r : ℤ) - (k : ℤ))) fun z =>
        smallCubeBlockEnvelope (k + 1) r (k : ℤ)
          (physicalShellCoverCenter k z)
  have hY : Measurable Y := Finset.measurable_sup'
    (shellCoverShifts_nonempty d ((r : ℤ) - (k : ℤ)))
    (fun z _ => by
      simpa only [show (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) by omega] using!
        measurable_smallCubeBlockEnvelope_potentialShellIndexSigma_Ioi
          (d := d) r k (physicalShellCoverCenter k z))
  have heq : Y = coveredLowBlockEnvelope k r (r : ℤ) := by
    funext omega
    exact Finset.sup'_apply
      (shellCoverShifts_nonempty d ((r : ℤ) - (k : ℤ)))
      (fun z => smallCubeBlockEnvelope (k + 1) r (k : ℤ)
        (physicalShellCoverCenter k z)) omega
  rwa [← heq]

theorem measurable_parentCubeCutoffRatioRepresentative {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (r k : ℕ) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ (potentialShellIndexSigma (Set.Ioi k))
      inferInstance (parentCubeCutoffRatioRepresentative M r k) := by
  unfold parentCubeCutoffRatioRepresentative
  exact ((measurable_coveredLowBlockEnvelope_potentialShellIndexSigma_Ioi
    (d := d) r k).add_const _).exp.sub_const 1

/-- Lognormal moment of the parent-cube representative.  The weak-tail scale
is linear in the block length because the shell field is maximized on the
full scale-`r` cube. -/
theorem parentCubeCutoffRatioRepresentative_moment {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {r k : ℕ} (hkr : k < r)
    (p : ℝ) (hp : 1 ≤ p) :
    let A := coveredLowBlockConst d * M.delta * ((r - k : ℕ) : ℝ)
    let b := ((r - k : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P
    Integrable (fun omega =>
        parentCubeCutoffRatioRepresentative M r k omega ^ p) M.P.toMeasure ∧
      (∫ omega, parentCubeCutoffRatioRepresentative M r k omega ^ p
          ∂M.P.toMeasure) ^ p⁻¹ ≤
        2 * Homogenization.IndependentSums.gammaMomentConst 2 *
          Real.sqrt (2 * p) * (A + b) *
          Real.exp (p * A ^ 2 + b) := by
  dsimp only
  let Z : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := coveredLowBlockEnvelope k r (r : ℤ)
  let A : ℝ := coveredLowBlockConst d * M.delta * ((r - k : ℕ) : ℝ)
  let b : ℝ := ((r - k : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P
  have hA : 0 < A := by
    dsimp only [A]
    have hgap : (0 : ℝ) < (r - k : ℕ) := by
      exact_mod_cast Nat.sub_pos_iff_lt.mpr hkr
    exact mul_pos (mul_pos (coveredLowBlockConst_pos M) M.shellPrefix.delta_pos)
      hgap
  have hb0 : 0 ≤ b := by
    dsimp only [b]
    exact mul_nonneg (Nat.cast_nonneg _) M.G4.tauSq_pos.le
  have hZtail0 := isBigOWith_gammaTwo_coveredLowBlockEnvelope
    M k r (r : ℤ) (by exact_mod_cast hkr) hkr le_rfl
  have hZ0 : ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      0 ≤ coveredLowBlockEnvelope k r (r : ℤ) omega :=
    coveredLowBlockEnvelope_nonneg k r (r : ℤ)
  have hZtail : IsBigO M.P.toMeasure (gammaSigma 2) Z A := by
    simpa [IsBigO, Z, A, Int.cast_sub, Nat.cast_sub hkr.le,
      abs_of_nonneg (hZ0 _)] using! hZtail0
  have htransfer := integral_abs_exp_sub_const_sub_one_rpow_root_le
    (mu := M.P.toMeasure) (X := Z) (A := A) (p := p) (b := -b)
    hA hp
    (measurable_coveredLowBlockEnvelope (d := d) k r (r : ℤ)).aemeasurable
    hZtail
  have hW0 : ∀ omega, 0 ≤ parentCubeCutoffRatioRepresentative M r k omega :=
    parentCubeCutoffRatioRepresentative_nonneg M r k
  have hfun : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      parentCubeCutoffRatioRepresentative M r k omega ^ p) =
      fun omega => |Real.exp (Z omega - -b) - 1| ^ p := by
    funext omega
    rw [sub_neg_eq_add]
    change parentCubeCutoffRatioRepresentative M r k omega ^ p =
      |parentCubeCutoffRatioRepresentative M r k omega| ^ p
    rw [abs_of_nonneg (hW0 omega)]
  constructor
  · rw [hfun]
    exact htransfer.1
  · rw [hfun]
    simpa only [abs_neg, abs_of_nonneg hb0, sub_neg_eq_add] using! htransfer.2

private theorem paperENNRealLpNorm_le_of_real_moment
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p : ℝ} (hp : 0 < p) {X : Omega → ℝ≥0∞} {W : Omega → ℝ}
    (hW0 : ∀ omega, 0 ≤ W omega)
    (hWint : Integrable (fun omega => W omega ^ p) mu)
    (hXW : ∀ᵐ omega ∂mu, X omega ≤ ENNReal.ofReal (W omega)) :
    paperENNRealLpNorm mu p X ≤
      ENNReal.ofReal ((∫ omega, W omega ^ p ∂mu) ^ p⁻¹) := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d091_paperENNRealLpNorm_le_of_real_moment (Omega := Omega) (mu := mu) (p := p) (hp := hp) (X := X) (W := W) (hW0 := hW0) (hWint := hWint) (hXW := hXW)

private theorem paperENNRealLpNorm_sq
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p : ℝ} (hp : 0 < p) (X : Omega → ℝ≥0∞) :
    paperENNRealLpNorm mu p (fun omega => X omega ^ (2 : ℕ)) =
      (paperENNRealLpNorm mu (2 * p) X) ^ (2 : ℕ) := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d131_paperENNRealLpNorm_sq (Omega := Omega) (mu := mu) (p := p) (hp := hp) (X := X)

private theorem abs_exp_sub_one_le_exp_abs_sub_one (t : ℝ) :
    |Real.exp t - 1| ≤ Real.exp |t| - 1 := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht, abs_of_nonneg
      (sub_nonneg.mpr (Real.one_le_exp ht))]
  · have ht0 : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht0, abs_of_nonpos
      (sub_nonpos.mpr (Real.exp_le_one_iff.mpr ht0))]
    have hpos := Real.add_one_le_exp t
    have hneg := Real.add_one_le_exp (-t)
    nlinarith

theorem abs_cutoffRatioMinusOne_le_parentCubeRepresentative {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {r k : ℕ} (hkr : k < r)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (r : ℤ))) :
    |cutoffRatioMinusOne M r (k : ℤ) omega x| ≤
      parentCubeCutoffRatioRepresentative M r k omega := by
  let Z := coveredLowBlockEnvelope k r (r : ℤ) omega
  let b := ((r - k : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P
  have hZ0 : 0 ≤ Z := coveredLowBlockEnvelope_nonneg _ _ _ _
  have hb0 : 0 ≤ b := mul_nonneg (by positivity) M.G4.tauSq_pos.le
  have hshell : |cutoffShellSum r (k : ℤ) x omega| ≤ Z := by
    simpa only [Z] using!
      abs_lowBlock_le_coveredLowBlockEnvelope (d := d) k r (r : ℤ) omega hx
  rw [cutoffRatioMinusOne_eq_exp_shell M r (k : ℤ) omega x
    (by omega) (by exact_mod_cast hkr)]
  have hcast : ((((r : ℤ) - (k : ℤ) : ℤ) : ℝ)) = ((r - k : ℕ) : ℝ) := by
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, Nat.cast_sub hkr.le]
  rw [hcast]
  calc
    |Real.exp (cutoffShellSum r (k : ℤ) x omega - b) - 1| ≤
        Real.exp |cutoffShellSum r (k : ℤ) x omega - b| - 1 :=
      abs_exp_sub_one_le_exp_abs_sub_one _
    _ ≤ Real.exp (Z + b) - 1 := by
      apply sub_le_sub_right (Real.exp_le_exp.mpr _) 1
      calc
        |cutoffShellSum r (k : ℤ) x omega - b| ≤
            |cutoffShellSum r (k : ℤ) x omega| + |b| := abs_sub _ _
        _ = |cutoffShellSum r (k : ℤ) x omega| + b := by rw [abs_of_nonneg hb0]
        _ ≤ Z + b := add_le_add hshell le_rfl
    _ = parentCubeCutoffRatioRepresentative M r k omega := rfl

theorem abs_inverseCutoffRatioMinusOne_le_parentCubeRepresentative {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {r k : ℕ} (hkr : k < r)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (r : ℤ))) :
    |inverseCutoffRatioMinusOne M r (k : ℤ) omega x| ≤
      parentCubeCutoffRatioRepresentative M r k omega := by
  let Z := coveredLowBlockEnvelope k r (r : ℤ) omega
  let b := ((r - k : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P
  have hb0 : 0 ≤ b := mul_nonneg (by positivity) M.G4.tauSq_pos.le
  have hshell : |cutoffShellSum r (k : ℤ) x omega| ≤ Z := by
    simpa only [Z] using!
      abs_lowBlock_le_coveredLowBlockEnvelope (d := d) k r (r : ℤ) omega hx
  rw [inverseCutoffRatioMinusOne_eq_exp_shell M r (k : ℤ) omega x
    (by omega) (by exact_mod_cast hkr)]
  have hcast : ((((r : ℤ) - (k : ℤ) : ℤ) : ℝ)) = ((r - k : ℕ) : ℝ) := by
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, Nat.cast_sub hkr.le]
  rw [hcast]
  calc
    |Real.exp (-cutoffShellSum r (k : ℤ) x omega + b) - 1| ≤
        Real.exp |-cutoffShellSum r (k : ℤ) x omega + b| - 1 :=
      abs_exp_sub_one_le_exp_abs_sub_one _
    _ ≤ Real.exp (Z + b) - 1 := by
      apply sub_le_sub_right (Real.exp_le_exp.mpr _) 1
      calc
        |-cutoffShellSum r (k : ℤ) x omega + b| =
            |cutoffShellSum r (k : ℤ) x omega - b| := by
          rw [show -cutoffShellSum r (k : ℤ) x omega + b =
            -(cutoffShellSum r (k : ℤ) x omega - b) by ring, abs_neg]
        _ ≤ |cutoffShellSum r (k : ℤ) x omega| + |b| := abs_sub _ _
        _ = |cutoffShellSum r (k : ℤ) x omega| + b := by rw [abs_of_nonneg hb0]
        _ ≤ Z + b := add_le_add hshell le_rfl
    _ = parentCubeCutoffRatioRepresentative M r k omega := rfl

/-- Deterministic annealed ordering and the parent-cube shell envelope in the
exact symmetric localization-error carrier. -/
noncomputable def parentCubeLocalizationRepresentative {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (r k : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  2 * ((1 + annealedRatioDefect M r k) *
    (1 + parentCubeCutoffRatioRepresentative M r k omega) - 1)

theorem parentCubeLocalizationRepresentative_nonneg {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (r k : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ parentCubeLocalizationRepresentative M r k omega := by
  have hD := annealedRatioDefect_nonneg M r k
  have hW := parentCubeCutoffRatioRepresentative_nonneg M r k omega
  unfold parentCubeLocalizationRepresentative
  nlinarith [mul_nonneg hD hW]

theorem measurable_parentCubeLocalizationRepresentative {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (r k : ℕ) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ (potentialShellIndexSigma (Set.Ioi k))
      inferInstance (parentCubeLocalizationRepresentative M r k) := by
  unfold parentCubeLocalizationRepresentative
  exact measurable_const.mul
    ((measurable_const.mul (measurable_const.add
      (measurable_parentCubeCutoffRatioRepresentative M r k))).sub_const 1)

/-- Raw squared moment obtained by composing the Gamma-two parent-cube shell
bound with the deterministic annealed ratio.  This is the quantitative input
which is subsequently absorbed into `delta1/12`. -/
theorem parentCubeLocalizationRepresentative_squared_moment_le_raw {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {r k : ℕ} (hkr : k < r)
    (xi : ℝ) (hxi : 1 ≤ xi) :
    let A := coveredLowBlockConst d * M.delta * ((r - k : ℕ) : ℝ)
    let b := ((r - k : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P
    let B := 2 * gammaMomentConst 2 * Real.sqrt (4 * xi) * (A + b) *
      Real.exp (2 * xi * A ^ 2 + b)
    let C := 2 * (annealedRatioDefect M r k +
      (1 + annealedRatioDefect M r k) * B)
    paperENNRealLpNorm M.P.toMeasure xi (fun omega =>
        ENNReal.ofReal (parentCubeLocalizationRepresentative M r k omega ^ 2)) ≤
      ENNReal.ofReal (C ^ 2) := by
  dsimp only
  let A : ℝ := coveredLowBlockConst d * M.delta * ((r - k : ℕ) : ℝ)
  let b : ℝ := ((r - k : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P
  let B : ℝ := 2 * gammaMomentConst 2 * Real.sqrt (4 * xi) * (A + b) *
    Real.exp (2 * xi * A ^ 2 + b)
  let D : ℝ := annealedRatioDefect M r k
  let C : ℝ := 2 * (D + (1 + D) * B)
  let W : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := parentCubeCutoffRatioRepresentative M r k
  let Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun omega => ENNReal.ofReal (W omega)
  let R : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := parentCubeLocalizationRepresentative M r k
  have hxi0 : 0 < xi := zero_lt_one.trans_le hxi
  have h2xi : 1 ≤ 2 * xi := by linarith
  have hW0 : ∀ omega, 0 ≤ W omega := parentCubeCutoffRatioRepresentative_nonneg M r k
  have hD0 : 0 ≤ D := annealedRatioDefect_nonneg M r k
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (mul_nonneg (coveredLowBlockConst_pos M).le
      M.shellPrefix.delta_pos.le) (Nat.cast_nonneg _)
  have hb0 : 0 ≤ b := by
    dsimp only [b]
    exact mul_nonneg (Nat.cast_nonneg _) M.G4.tauSq_pos.le
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (gammaMomentConst_pos (by norm_num : (0 : ℝ) < 2)).le)
          (Real.sqrt_nonneg _)) (add_nonneg hA0 hb0))
      (Real.exp_pos _).le
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (by norm_num) (add_nonneg hD0
      (mul_nonneg (by linarith) hB0))
  have hR0 : ∀ omega, 0 ≤ R omega :=
    parentCubeLocalizationRepresentative_nonneg M r k
  obtain ⟨hWint, hWroot⟩ :=
    parentCubeCutoffRatioRepresentative_moment M hkr (2 * xi) h2xi
  have hWroot' :
      (∫ omega, W omega ^ (2 * xi) ∂M.P.toMeasure) ^ (2 * xi)⁻¹ ≤ B := by
    simpa only [W, A, b, B, show 2 * (2 * xi) = 4 * xi by ring] using! hWroot
  have hYnorm : paperENNRealLpNorm M.P.toMeasure (2 * xi) Y ≤
      ENNReal.ofReal B := by
    exact (paperENNRealLpNorm_le_of_real_moment M.P.toMeasure
      (by positivity : 0 < 2 * xi) hW0 hWint
      (Filter.Eventually.of_forall fun omega => le_rfl)).trans
        (ENNReal.ofReal_le_ofReal hWroot')
  have hYmeas : Measurable Y := by
    dsimp only [Y, W]
    exact ((measurable_parentCubeCutoffRatioRepresentative M r k).mono
      (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi k)) le_rfl).ennreal_ofReal
  have hRof : (fun omega => ENNReal.ofReal (R omega)) = fun omega =>
      2 * (ENNReal.ofReal D + (1 + ENNReal.ofReal D) * Y omega) := by
    funext omega
    dsimp only [R, Y, W, D]
    unfold parentCubeLocalizationRepresentative
    have hW := parentCubeCutoffRatioRepresentative_nonneg M r k omega
    have hDin := annealedRatioDefect_nonneg M r k
    rw [show (1 + annealedRatioDefect M r k) *
          (1 + parentCubeCutoffRatioRepresentative M r k omega) - 1 =
        annealedRatioDefect M r k +
          (1 + annealedRatioDefect M r k) *
            parentCubeCutoffRatioRepresentative M r k omega by ring,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_add hDin (mul_nonneg (by positivity) hW),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by norm_num) hDin,
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  have hRnorm : paperENNRealLpNorm M.P.toMeasure (2 * xi)
      (fun omega => ENNReal.ofReal (R omega)) ≤ ENNReal.ofReal C := by
    rw [hRof]
    calc
      paperENNRealLpNorm M.P.toMeasure (2 * xi) (fun omega =>
          2 * (ENNReal.ofReal D + (1 + ENNReal.ofReal D) * Y omega)) =
          2 * paperENNRealLpNorm M.P.toMeasure (2 * xi) (fun omega =>
            ENNReal.ofReal D + (1 + ENNReal.ofReal D) * Y omega) := by
        exact paperENNRealLpNorm_const_mul_eq M.P.toMeasure (by positivity) 2 _
          (measurable_const.add (measurable_const.mul hYmeas))
      _ ≤ 2 * (paperENNRealLpNorm M.P.toMeasure (2 * xi)
            (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => ENNReal.ofReal D) +
          paperENNRealLpNorm M.P.toMeasure (2 * xi) (fun omega =>
            (1 + ENNReal.ofReal D) * Y omega)) := by
        gcongr
        exact paperENNRealLpNorm_add_le M.P.toMeasure h2xi
          measurable_const.aemeasurable
          (measurable_const.mul hYmeas).aemeasurable
      _ = 2 * (ENNReal.ofReal D + (1 + ENNReal.ofReal D) *
          paperENNRealLpNorm M.P.toMeasure (2 * xi) Y) := by
        have hconstD : paperENNRealLpNorm M.P.toMeasure (2 * xi)
            (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => ENNReal.ofReal D) = ENNReal.ofReal D := by
          rw [show (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => ENNReal.ofReal D) =
              (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => ENNReal.ofReal D * 1) by funext omega; simp]
          rw [paperENNRealLpNorm_const_mul_eq M.P.toMeasure (by positivity)
            (ENNReal.ofReal D) (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => 1) measurable_const,
            paperENNRealLpNorm_one, mul_one]
        rw [hconstD]
        rw [paperENNRealLpNorm_const_mul_eq M.P.toMeasure (by positivity)
          (1 + ENNReal.ofReal D) Y hYmeas]
      _ ≤ 2 * (ENNReal.ofReal D + (1 + ENNReal.ofReal D) * ENNReal.ofReal B) := by
        gcongr
      _ = ENNReal.ofReal C := by
        symm
        dsimp only [C]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_add hD0 (mul_nonneg (by linarith) hB0),
          ENNReal.ofReal_mul (by linarith),
          ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hD0,
          ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  have hsqfun : (fun omega => ENNReal.ofReal (R omega ^ 2)) =
      fun omega => (ENNReal.ofReal (R omega)) ^ (2 : ℕ) := by
    funext omega
    exact ENNReal.ofReal_pow (hR0 omega) 2
  rw [show (fun omega => ENNReal.ofReal
      (parentCubeLocalizationRepresentative M r k omega ^ 2)) =
      (fun omega => ENNReal.ofReal (R omega ^ 2)) by rfl,
    hsqfun, paperENNRealLpNorm_sq M.P.toMeasure hxi0]
  exact (pow_le_pow_left' hRnorm 2).trans_eq (ENNReal.ofReal_pow hC0 2).symm

/-! ## Numerical absorption of the parent-cube shell moment -/

/-- Dimension-only coefficient which envelopes the annealed ordering defect
and the Gamma-two parent-cube shell moment. -/
noncomputable def cutoffBlockRawFactor (d : ℕ) : ℝ :=
  let qD := 4 * Real.exp 2
  let qB := 4 * gammaMomentConst 2 * (coveredLowBlockConst d + 1) *
    Real.exp (2 * coveredLowBlockConst d ^ 2 + 1)
  2 * (qD + qB + qD * qB)

theorem cutoffBlockRawFactor_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    0 < cutoffBlockRawFactor d := by
  dsimp only [cutoffBlockRawFactor]
  have hc := coveredLowBlockConst_pos M
  have hg := gammaMomentConst_pos (by norm_num : (0 : ℝ) < 2)
  positivity

/-- One explicit admissible dimension-only constant for the first induction's
cutoff update. -/
noncomputable def cutoffBlockAbsorptionConst (d : ℕ) : ℝ :=
  max 1 (12 * cutoffBlockRawFactor d ^ 2)

theorem cutoffBlockAbsorptionConst_one_le (d : ℕ) :
    1 ≤ cutoffBlockAbsorptionConst d := by
  exact le_max_left _ _

theorem cutoffBlockAbsorptionConst_raw (d : ℕ) :
    12 * cutoffBlockRawFactor d ^ 2 ≤ cutoffBlockAbsorptionConst d := by
  exact le_max_right _ _

/-- The raw parent-cube localization moment is absorbed by the two printed
smallness inequalities.  The block length may be any upper bound for `r-k`,
which is the form needed while sliding through a block of length `h`. -/
theorem parentCubeLocalizationRepresentative_squared_moment_le_absorbed
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {r k h : ℕ} (hkr : k < r) (hgap : r - k ≤ h) (hh : 0 < h)
    {xi delta1 : ℝ} (hxi : 1 ≤ xi) (hdelta1 : 0 ≤ delta1)
    (hsmall : xi * M.delta ^ 2 * (h : ℝ) ^ 2 ≤
      (cutoffBlockAbsorptionConst d)⁻¹ * delta1)
    (hsmall' : (cutoffBlockAbsorptionConst d)⁻¹ * delta1 ≤
      (cutoffBlockAbsorptionConst d)⁻¹ ^ 2) :
    paperENNRealLpNorm M.P.toMeasure xi (fun omega =>
        ENNReal.ofReal (parentCubeLocalizationRepresentative M r k omega ^ 2)) ≤
      ENNReal.ofReal ((1 / 12 : ℝ) * delta1) := by
  let c : ℝ := coveredLowBlockConst d
  let g : ℝ := gammaMomentConst 2
  let gap : ℝ := ((r - k : ℕ) : ℝ)
  let H : ℝ := (h : ℝ)
  let T : ℝ := xi * M.delta ^ 2 * H ^ 2
  let s : ℝ := Real.sqrt T
  let qD : ℝ := 4 * Real.exp 2
  let qB : ℝ := 4 * g * (c + 1) * Real.exp (2 * c ^ 2 + 1)
  let q : ℝ := 2 * (qD + qB + qD * qB)
  let A : ℝ := c * M.delta * gap
  let b : ℝ := gap * _root_.SubdiffusiveProcess.Model.tauSq M.P
  let B : ℝ := 2 * g * Real.sqrt (4 * xi) * (A + b) *
    Real.exp (2 * xi * A ^ 2 + b)
  let D : ℝ := annealedRatioDefect M r k
  let C : ℝ := 2 * (D + (1 + D) * B)
  have hc : 0 < c := by simpa [c] using! coveredLowBlockConst_pos M
  have hg : 0 < g := by
    simpa [g] using! gammaMomentConst_pos (by norm_num : (0 : ℝ) < 2)
  have hH : 1 ≤ H := by
    dsimp only [H]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hh))
  have hgap0 : 0 ≤ gap := by dsimp only [gap]; positivity
  have hgapH : gap ≤ H := by
    dsimp only [gap, H]
    exact_mod_cast hgap
  have hxi0 : 0 < xi := zero_lt_one.trans_le hxi
  have hT0 : 0 ≤ T := by dsimp only [T]; positivity
  have hK : 1 ≤ cutoffBlockAbsorptionConst d :=
    cutoffBlockAbsorptionConst_one_le d
  have hKpos : 0 < cutoffBlockAbsorptionConst d := zero_lt_one.trans_le hK
  have hKinv0 : 0 ≤ (cutoffBlockAbsorptionConst d)⁻¹ :=
    inv_nonneg.mpr hKpos.le
  have hKinv_le_one : (cutoffBlockAbsorptionConst d)⁻¹ ≤ 1 :=
    inv_le_one₀ hKpos |>.2 hK
  have hKinvSq_le_one : (cutoffBlockAbsorptionConst d)⁻¹ ^ 2 ≤ 1 := by
    nlinarith only [sq_nonneg ((cutoffBlockAbsorptionConst d)⁻¹), hKinv0, hKinv_le_one]
  have hTle : T ≤ (cutoffBlockAbsorptionConst d)⁻¹ * delta1 := by
    simpa only [T, H] using! hsmall
  have hT1 : T ≤ 1 := hTle.trans (hsmall'.trans hKinvSq_le_one)
  have hdeltaSqT : M.delta ^ 2 ≤ T := by
    dsimp only [T]
    have hHsq : 1 ≤ H ^ 2 := by nlinarith only [hH]
    have hδ2 : 0 ≤ M.delta ^ 2 := sq_nonneg _
    have hfirst : M.delta ^ 2 ≤ xi * M.delta ^ 2 := by nlinarith only [hxi, hδ2]
    have hsecond : xi * M.delta ^ 2 ≤ xi * M.delta ^ 2 * H ^ 2 := by
      exact le_mul_of_one_le_right (mul_nonneg hxi0.le hδ2) hHsq
    exact hfirst.trans hsecond
  have hdelta_le_one : M.delta ≤ 1 := by
    nlinarith only [M.shellPrefix.delta_pos, hdeltaSqT, hT1]
  have hs0 : 0 ≤ s := by dsimp only [s]; positivity
  have hsSq : s ^ 2 = T := by
    dsimp only [s]
    exact Real.sq_sqrt hT0
  have hs1 : s ≤ 1 := by nlinarith only [hs0, hsSq, hT1]
  have hTs : T ≤ s := by nlinarith only [hsSq, mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  have hsqrtT : Real.sqrt xi * M.delta * H = s := by
    have hleft : 0 ≤ Real.sqrt xi * M.delta * H :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) M.shellPrefix.delta_pos.le)
        (Nat.cast_nonneg _)
    have hleftSq : (Real.sqrt xi * M.delta * H) ^ 2 = T := by
      dsimp only [T]
      rw [mul_pow, mul_pow, Real.sq_sqrt hxi0.le]
    exact (sq_eq_sq₀ hleft hs0).mp (hleftSq.trans hsSq.symm)
  have hsqrt4xi : Real.sqrt (4 * xi) = 2 * Real.sqrt xi := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hb0 : 0 ≤ b := by
    dsimp only [b]
    exact mul_nonneg hgap0 M.G4.tauSq_pos.le
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (mul_nonneg hc.le M.shellPrefix.delta_pos.le) hgap0
  have hsqrtA : Real.sqrt xi * A ≤ c * s := by
    dsimp only [A]
    have hm := mul_le_mul_of_nonneg_left hgapH
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg xi) hc.le)
        M.shellPrefix.delta_pos.le)
    rw [← hsqrtT]
    nlinarith only [hm]
  have htau : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ M.delta ^ 2 := by
    have hlog : Real.log 2 / 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith only [h]
    exact (tauSq_le_delta_sq M).trans
      (mul_le_of_le_one_left (sq_nonneg _) hlog)
  have hsqrtb : Real.sqrt xi * b ≤ s := by
    have hbδ : b ≤ gap * M.delta ^ 2 := by
      dsimp only [b]
      exact mul_le_mul_of_nonneg_left htau hgap0
    have hgapδ : gap * M.delta ^ 2 ≤ M.delta ^ 2 * H := by
      nlinarith only [mul_le_mul_of_nonneg_right hgapH (sq_nonneg M.delta)]
    calc
      Real.sqrt xi * b ≤ Real.sqrt xi * (M.delta ^ 2 * H) :=
        mul_le_mul_of_nonneg_left (hbδ.trans hgapδ) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt xi * M.delta * H := by
        have hδsq : M.delta ^ 2 ≤ M.delta := by
          nlinarith only [M.shellPrefix.delta_pos, hdelta_le_one]
        rw [show Real.sqrt xi * (M.delta ^ 2 * H) =
          (Real.sqrt xi * H) * M.delta ^ 2 by ring,
          show Real.sqrt xi * M.delta * H =
            (Real.sqrt xi * H) * M.delta by ring]
        exact mul_le_mul_of_nonneg_left hδsq (by positivity)
      _ = s := hsqrtT
  have hA2 : xi * A ^ 2 ≤ c ^ 2 * T := by
    have hsquare := sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hA0) (by positivity) |>.2
      hsqrtA
    rw [mul_pow, Real.sq_sqrt hxi0.le] at hsquare
    nlinarith only [hsquare, hsSq]
  have hbT : b ≤ T := by
    calc
      b ≤ gap * M.delta ^ 2 := by
        dsimp only [b]
        exact mul_le_mul_of_nonneg_left htau hgap0
      _ ≤ M.delta ^ 2 * H := by nlinarith only [hgapH, sq_nonneg M.delta]
      _ ≤ M.delta ^ 2 * H ^ 2 := by
        exact mul_le_mul_of_nonneg_left (by nlinarith only [hH] : H ≤ H ^ 2)
          (sq_nonneg M.delta)
      _ ≤ T := by
        dsimp only [T]
        nlinarith only [mul_nonneg (sub_nonneg.mpr hxi) (mul_nonneg (sq_nonneg M.delta)
          (sq_nonneg H))]
  have hexponent : 2 * xi * A ^ 2 + b ≤ 2 * c ^ 2 + 1 := by
    have hc20 : 0 ≤ c ^ 2 := sq_nonneg _
    nlinarith only [hA2, hbT, hT1, mul_nonneg hc20 (sub_nonneg.mpr hT1)]
  have hB : B ≤ qB * s := by
    have hexp := Real.exp_le_exp.mpr hexponent
    have hsum : Real.sqrt xi * (A + b) ≤ (c + 1) * s := by
      nlinarith only [hsqrtA, hsqrtb]
    dsimp only [B, qB]
    rw [hsqrt4xi]
    have hupper0 : 0 ≤ 4 * g * ((c + 1) * s) := by positivity
    calc
      2 * g * (2 * Real.sqrt xi) * (A + b) *
          Real.exp (2 * xi * A ^ 2 + b) =
          (4 * g * (Real.sqrt xi * (A + b))) *
            Real.exp (2 * xi * A ^ 2 + b) := by ring
      _ ≤ (4 * g * ((c + 1) * s)) * Real.exp (2 * c ^ 2 + 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsum (by positivity)) hexp
          (Real.exp_pos _).le hupper0
      _ = 4 * g * (c + 1) * Real.exp (2 * c ^ 2 + 1) * s := by ring
  have hD : D ≤ qD * s := by
    have horder := _root_.SubdiffusiveProcess.Section3.annealed_matrix_bounds.2 M r k hkr
    have hraw := annealedOrderingRatio_of_ordering M hkr.le horder
    have hδgap : M.delta ^ 2 * gap ≤ T := by
      calc
        M.delta ^ 2 * gap ≤ M.delta ^ 2 * H :=
          mul_le_mul_of_nonneg_left hgapH (sq_nonneg _)
        _ ≤ M.delta ^ 2 * H ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith only [hH] : H ≤ H ^ 2) (sq_nonneg _)
        _ ≤ T := by
          dsimp only [T]
          convert le_mul_of_one_le_left
            (mul_nonneg (sq_nonneg M.delta) (sq_nonneg H)) hxi using 1
          all_goals ring
    have hexp : Real.exp (2 * M.delta ^ 2 * gap) ≤ Real.exp 2 := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hδgap, hT1]
    have hraw' : D ≤ 4 * M.delta ^ 2 * gap *
        Real.exp (2 * M.delta ^ 2 * gap) := by
      simpa only [D, gap] using! hraw
    calc
      D ≤ 4 * M.delta ^ 2 * gap *
          Real.exp (2 * M.delta ^ 2 * gap) := hraw'
      _ ≤ 4 * T * Real.exp 2 := by
        exact mul_le_mul (by nlinarith only [hδgap]) hexp (Real.exp_pos _).le
          (by positivity)
      _ ≤ qD * s := by
        dsimp only [qD]
        calc
          4 * T * Real.exp 2 = (4 * Real.exp 2) * T := by ring
          _ ≤ (4 * Real.exp 2) * s :=
            mul_le_mul_of_nonneg_left hTs (by positivity)
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hD0 : 0 ≤ D := annealedRatioDefect_nonneg M r k
  have hC : C ≤ q * s := by
    have hDB : D * B ≤ qD * qB * s := by
      calc
        D * B ≤ (qD * s) * (qB * s) :=
          mul_le_mul hD hB hB0 (by positivity)
        _ = (qD * qB) * (s * s) := by ring
        _ ≤ (qD * qB) * s :=
          mul_le_mul_of_nonneg_left (by nlinarith only [hsSq, hTs] : s * s ≤ s) (by positivity)
    dsimp only [C, q]
    rw [show (1 + D) * B = B + D * B by ring]
    nlinarith only [hD, hB, hDB]
  have hqEq : q = cutoffBlockRawFactor d := by
    dsimp only [q, qD, qB, c, g, cutoffBlockRawFactor]
  have hq0 : 0 ≤ q := by
    rw [hqEq]
    exact (cutoffBlockRawFactor_pos M).le
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (by norm_num) (add_nonneg hD0 (mul_nonneg (by linarith only [hD0]) hB0))
  have hC2 : C ^ 2 ≤ q ^ 2 * T := by
    have hsquare := sq_le_sq₀ hC0 (mul_nonneg hq0 hs0) |>.2 hC
    nlinarith only [hsquare, hsSq]
  have hqK : 12 * q ^ 2 ≤ cutoffBlockAbsorptionConst d := by
    rw [hqEq]
    exact cutoffBlockAbsorptionConst_raw d
  have hfinal : C ^ 2 ≤ (1 / 12 : ℝ) * delta1 := by
    have hq2K : q ^ 2 ≤ (1 / 12 : ℝ) * cutoffBlockAbsorptionConst d := by
      nlinarith only [hqK]
    have hTK := mul_le_mul_of_nonneg_left hTle (sq_nonneg q)
    have hcancel : q ^ 2 * ((cutoffBlockAbsorptionConst d)⁻¹ * delta1) ≤
        (1 / 12 : ℝ) * delta1 := by
      calc
        q ^ 2 * ((cutoffBlockAbsorptionConst d)⁻¹ * delta1) =
            (q ^ 2 * (cutoffBlockAbsorptionConst d)⁻¹) * delta1 := by ring
        _ ≤ ((1 / 12 : ℝ) * cutoffBlockAbsorptionConst d *
              (cutoffBlockAbsorptionConst d)⁻¹) * delta1 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hq2K hKinv0) hdelta1
        _ = (1 / 12 : ℝ) * delta1 := by field_simp [hKpos.ne']
    exact hC2.trans (hTK.trans hcancel)
  have hraw := parentCubeLocalizationRepresentative_squared_moment_le_raw
    M hkr xi hxi
  exact hraw.trans (ENNReal.ofReal_le_ofReal (by simpa only [A, b, B, C] using! hfinal))

private theorem scalarRatioLInf_le_of_forall_bound
    {d : ℕ} {U : Ch02.Domain d} {a b : Vec d → ℝ} {W : ℝ}
    (hW0 : 0 ≤ W) (h : ∀ x ∈ (U : Set (Vec d)), |a x / b x - 1| ≤ W) :
    scalarRatioLInf U a b ≤ W := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d190_scalarRatioLInf_le_of_forall_bound (d := d) (U := U) (a := a) (b := b) (W := W) (hW0 := hW0) (h := h)

theorem parentCubeLocalizationRepresentative_dominates {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {r k : ℕ} (hkr : k < r)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    responseLocalizationError M r k
        (Ch02.cubeDomain (originCube d (r : ℤ))) (ahom M r) omega ≤
      parentCubeLocalizationRepresentative M r k omega := by
  let D := annealedRatioDefect M r k
  let W := parentCubeCutoffRatioRepresentative M r k omega
  let E := (1 + D) * (1 + W) - 1
  have hD0 : 0 ≤ D := annealedRatioDefect_nonneg M r k
  have hW0 : 0 ≤ W := parentCubeCutoffRatioRepresentative_nonneg M r k omega
  have hE0 : 0 ≤ E := by dsimp only [E]; nlinarith [mul_nonneg hD0 hW0]
  have hrpos : 0 < ahom M r := (Real.exp_pos _).trans_le
    (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M r)
  have hkpos : 0 < ahom M k := (Real.exp_pos _).trans_le
    (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M k)
  have hfirst : scalarRatioLInf (Ch02.cubeDomain (originCube d (r : ℤ)))
      (fun x => ahom M r / ahom M k * _root_.SubdiffusiveProcess.Model.aCutoff M k omega x)
      (_root_.SubdiffusiveProcess.Model.aCutoff M r omega) ≤ E := by
    apply scalarRatioLInf_le_of_forall_bound hE0
    intro x hx
    have hp := abs_mul_three_sub_one_le_product_envelope hD0 hW0
      (show |ahom M r / ahom M k - 1| ≤ D by
        dsimp only [D, annealedRatioDefect]
        rw [div_eq_mul_inv]
        exact le_add_of_nonneg_right (abs_nonneg _))
      (abs_inverseCutoffRatioMinusOne_le_parentCubeRepresentative M hkr omega hx)
      (show |(1 : ℝ) - 1| ≤ 0 by norm_num)
    have hid :
        (ahom M r / ahom M k * _root_.SubdiffusiveProcess.Model.aCutoff M k omega x) /
            _root_.SubdiffusiveProcess.Model.aCutoff M r omega x =
          (ahom M r / ahom M k) *
            (_root_.SubdiffusiveProcess.Model.aCutoff M k omega x /
              _root_.SubdiffusiveProcess.Model.aCutoff M r omega x) * 1 := by ring
    rw [hid]
    simpa only [D, W, E, inverseCutoffRatioMinusOne, aCutoffAtInt,
      Int.toNat_natCast, ite_eq_right (by omega : ¬((k : ℤ) < 0)), mul_one,
      add_zero] using! hp
  have hsecond : scalarRatioLInf (Ch02.cubeDomain (originCube d (r : ℤ)))
      (fun x => (ahom M r / ahom M k)⁻¹ *
        _root_.SubdiffusiveProcess.Model.aCutoff M r omega x)
      (_root_.SubdiffusiveProcess.Model.aCutoff M k omega) ≤ E := by
    apply scalarRatioLInf_le_of_forall_bound hE0
    intro x hx
    have hp := abs_mul_three_sub_one_le_product_envelope hD0 hW0
      (show |ahom M k / ahom M r - 1| ≤ D by
        dsimp only [D, annealedRatioDefect]
        rw [div_eq_mul_inv, mul_comm]
        exact le_add_of_nonneg_left (abs_nonneg _))
      (abs_cutoffRatioMinusOne_le_parentCubeRepresentative M hkr omega hx)
      (show |(1 : ℝ) - 1| ≤ 0 by norm_num)
    have hinv : (ahom M r / ahom M k)⁻¹ = ahom M k / ahom M r := by
      field_simp [hrpos.ne', hkpos.ne']
    have hid :
        ((ahom M r / ahom M k)⁻¹ *
            _root_.SubdiffusiveProcess.Model.aCutoff M r omega x) /
            _root_.SubdiffusiveProcess.Model.aCutoff M k omega x =
          (ahom M k / ahom M r) *
            (_root_.SubdiffusiveProcess.Model.aCutoff M r omega x /
              _root_.SubdiffusiveProcess.Model.aCutoff M k omega x) * 1 := by
      rw [hinv]
      ring
    rw [hid]
    simpa only [D, W, E, cutoffRatioMinusOne, aCutoffAtInt,
      Int.toNat_natCast, ite_eq_right (by omega : ¬((k : ℤ) < 0)), mul_one,
      add_zero] using! hp
  unfold responseLocalizationError
  have hsum := add_le_add hfirst hsecond
  dsimp only [E] at hsum
  unfold parentCubeLocalizationRepresentative
  dsimp only [D, W]
  linarith

/-- `e.J.localization.block.moment` on the actual headline carrier: the
scale-`r` cube is compared from cutoff `k` to cutoff `r`, and the strict
suffix representative factors from the cutoff-`k` normalized defect. -/
theorem normalizedDefectAt_cutoff_update_lpnorm_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {r k : ℕ} (hkr : k < r)
    {xi : ℝ} (hxi : 1 ≤ xi) :
    paperENNRealLpNorm M.P.toMeasure xi (normalizedDefectAt M r r) ≤
      2 * paperENNRealLpNorm M.P.toMeasure xi (normalizedDefectAt M k r) +
        3 * paperENNRealLpNorm M.P.toMeasure xi (fun omega =>
          ENNReal.ofReal (parentCubeLocalizationRepresentative M r k omega ^ 2)) *
          (paperENNRealLpNorm M.P.toMeasure xi (normalizedDefectAt M k r) + 1) := by
  let U := Ch02.cubeDomain (originCube d (r : ℤ))
  let D : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := normalizedDefect M k U
  let X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun omega => ENNReal.ofReal
    (parentCubeLocalizationRepresentative M r k omega ^ 2)
  have hDmeas : @Measurable _ _ (potentialShellIndexSigma (d := d) (Set.Iic k))
      inferInstance D :=
    measurable_normalizedDefect_potentialShellIndexSigma_Iic M k U
  have hXmeas : @Measurable _ _ (potentialShellIndexSigma (d := d) (Set.Ioi k))
      inferInstance X := by
    dsimp only [X]
    exact ((measurable_parentCubeLocalizationRepresentative M r k).pow_const 2).ennreal_ofReal
  have hpoint : ∀ᵐ omega ∂M.P.toMeasure,
      normalizedDefectAt M r r omega ≤
        2 * D omega + 3 * X omega * (D omega + 1) := by
    filter_upwards with omega
    have hloc := paperScalarProbeMaxOn_cutoff_le_localized M r k U (ahom M r)
      ((Real.exp_pos _).trans_le
        (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M r)) omega
    have herr := parentCubeLocalizationRepresentative_dominates M hkr omega
    have hsquare :
        responseLocalizationError M r k U (ahom M r) omega ^ 2 ≤
          parentCubeLocalizationRepresentative M r k omega ^ 2 :=
      pow_le_pow_left₀ (responseLocalizationError_nonneg M r k U (ahom M r) omega)
        herr 2
    have hloc' :
        paperScalarProbeMaxOn U
            (aCutoffCoeffOnData M r omega U).toCoeffOn (ahom M r) ≤
          2 * D omega + 3 * X omega * (D omega + 1) := hloc.trans (by
      gcongr
      exact ENNReal.ofReal_le_ofReal hsquare)
    simpa only [normalizedDefectAt, normalizedDefect, paperScalarProbeMax,
      aCutoffFamily, aCutoffTriadicData, U, D, X] using! hloc'
  have hraw := paperENNRealLpNorm_localized_prefix_suffix M k hxi
    hDmeas hXmeas hpoint
  simpa only [D, X, U, normalizedDefectAt, normalizedDefect,
    paperScalarProbeMax, aCutoffFamily, aCutoffTriadicData] using! hraw

/-- The exact `delta1/4 + delta1/12` absorption after the parent-cube
factorization. -/
theorem normalizedDefectAt_cutoff_update_close {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {r k : ℕ} (hkr : k < r)
    {xi delta1 : ℝ} (hxi : 1 ≤ xi) (hdelta : 0 ≤ delta1)
    (hdelta' : delta1 ≤ 1)
    (hold : paperENNRealLpNorm M.P.toMeasure xi (normalizedDefectAt M k r) ≤
      ENNReal.ofReal ((1 / 4 : ℝ) * delta1))
    (hshell : paperENNRealLpNorm M.P.toMeasure xi (fun omega =>
        ENNReal.ofReal (parentCubeLocalizationRepresentative M r k omega ^ 2)) ≤
      ENNReal.ofReal ((1 / 12 : ℝ) * delta1)) :
    paperENNRealLpNorm M.P.toMeasure xi (normalizedDefectAt M r r) ≤
      ENNReal.ofReal delta1 := by
  have hraw := normalizedDefectAt_cutoff_update_lpnorm_le M hkr hxi
  have hbound :
      paperENNRealLpNorm M.P.toMeasure xi (normalizedDefectAt M r r) ≤
        2 * ENNReal.ofReal ((1 / 4 : ℝ) * delta1) +
          3 * ENNReal.ofReal ((1 / 12 : ℝ) * delta1) *
            (ENNReal.ofReal ((1 / 4 : ℝ) * delta1) + 1) := by
    exact hraw.trans (by gcongr)
  have hreal :
      2 * ((1 / 4 : ℝ) * delta1) +
          3 * ((1 / 12 : ℝ) * delta1) *
            (1 + (1 / 4 : ℝ) * delta1) ≤ delta1 := by
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.firstBlockUpdate_close
      hdelta hdelta' le_rfl le_rfl le_rfl (by positivity)
  calc
    _ ≤ 2 * ENNReal.ofReal ((1 / 4 : ℝ) * delta1) +
          3 * ENNReal.ofReal ((1 / 12 : ℝ) * delta1) *
            (ENNReal.ofReal ((1 / 4 : ℝ) * delta1) + 1) := hbound
    _ = ENNReal.ofReal
          (2 * ((1 / 4 : ℝ) * delta1) +
            3 * ((1 / 12 : ℝ) * delta1) *
              (1 + (1 / 4 : ℝ) * delta1)) := by
      have hfirst :
          2 * ENNReal.ofReal ((1 / 4 : ℝ) * delta1) =
            ENNReal.ofReal (2 * ((1 / 4 : ℝ) * delta1)) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hplus :
          ENNReal.ofReal ((1 / 4 : ℝ) * delta1) + 1 =
            ENNReal.ofReal (1 + (1 / 4 : ℝ) * delta1) := by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by norm_num,
          ← ENNReal.ofReal_add (by positivity) (by norm_num : (0 : ℝ) ≤ 1)]
        congr 1
        ring
      have hsecond :
          3 * ENNReal.ofReal ((1 / 12 : ℝ) * delta1) *
              (ENNReal.ofReal ((1 / 4 : ℝ) * delta1) + 1) =
            ENNReal.ofReal
              (3 * ((1 / 12 : ℝ) * delta1) *
                (1 + (1 / 4 : ℝ) * delta1)) := by
        rw [hplus, show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
          ← ENNReal.ofReal_mul (by positivity)]
      rw [hfirst, hsecond, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal delta1 := ENNReal.ofReal_le_ofReal hreal

end

end SubdiffusiveProcess.CoarseGrainingVocab
