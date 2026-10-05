module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepDescendantHessianMoments
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNeumannCellBesov

@[expose] public section

/-!
# Source-cell fourth moment of the shell derivative carrier

The cell observable `oneStepShellForcingCellB` has one factor of the source
cell scale.  Partitioning its coordinatewise spatial `L⁴` norms over the
source cells and using the existing parent-scale shell-Jacobian moment gives
the sixteen-scale gain to the fourth power, hence `delta ^ 68`.
-/

open MeasureTheory Homogenization
open scoped BigOperators ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Deterministic source-cell partition bound for the shell derivative
observable, expressed in the parent-scale normalized matrix norm. -/
theorem descendantsAverage_oneStepShellForcingCellB_four_le_scaled_matrix
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h depth : ℕ)
    (p : Vec d) (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    descendantsAverage Q depth (fun R =>
        (oneStepShellForcingCellB (Q := Q) (R := R)
          M n h omega p hh) ^ (4 : ℕ)) ≤
      ((cubeScaleFactor Q / (3 : ℝ) ^ depth) / (3 : ℝ) ^ n) ^ (4 : ℕ) *
        (((d : ℝ) ^ 2) ^ (4 : ℕ) *
          (eLpNorm (fun x => (3 : ℝ) ^ n •
              HilbertMat.ofMat
                ((oneStepShellForcingW14 M n h omega p Q hh).jacobian x))
            4 (normalizedCubeMeasure Q)).toReal ^ (4 : ℕ)) := by
  let A : Vec d → Mat d :=
    fun x => (oneStepShellForcingW14 M n h omega p Q hh).jacobian x
  have hA : MemLp (fun x => HilbertMat.ofMat (A x)) (4 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    simpa only [A, oneStepFourExponent_exponent] using
      (oneStepShellForcingW14 M n h omega p Q hh).jacobianHilbertMemLp
  let c : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ depth
  have hc : 0 ≤ c := by
    dsimp only [c]
    exact div_nonneg (cubeScaleFactor_nonneg Q) (by positivity)
  have hpoint : ∀ R (hR : R ∈ descendantsAtDepth Q depth),
      (oneStepShellForcingCellB (Q := Q) (R := R)
        M n h omega p hh) ^ (4 : ℕ) ≤
        c ^ (4 : ℕ) * (((d : ℝ) ^ 2) ^ (3 : ℕ) *
          ∑ i : Fin d, ∑ j : Fin d,
            (cubeLpNorm R (4 : ℝ≥0∞) (fun x => A x i j)) ^ (4 : ℕ)) := by
    intro R hR
    let : IsProbabilityMeasure (normalizedCubeMeasure R) :=
      ⟨normalizedCubeMeasure_apply_univ R⟩
    have hside : cubeScaleFactor R = c := by
      simpa only [c] using cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR
    have hcoord : ∀ i j : Fin d,
        cubeLpNorm R (2 : ℝ≥0∞) (fun x => A x i j) ≤
          cubeLpNorm R (4 : ℝ≥0∞) (fun x => A x i j) := by
      intro i j
      have hcoordQ : MemLp (fun x => A x i j) (4 : ℝ≥0∞)
          (normalizedCubeMeasure Q) := by
        rw [memLp_piLp_iff] at hA
        have hi := hA i
        rw [memLp_piLp_iff] at hi
        exact hi j
      have hcoordR := memLp_on_descendant_of_memLp_generic hR hcoordQ
      unfold cubeLpNorm
      exact ENNReal.toReal_mono hcoordR.eLpNorm_ne_top
        (eLpNorm_le_eLpNorm_of_exponent_le (p := 2) (q := 4) (by norm_num))
    have hsum : ∑ i : Fin d, ∑ j : Fin d,
        cubeLpNorm R (2 : ℝ≥0∞) (fun x => A x i j) ≤
      ∑ i : Fin d, ∑ j : Fin d,
        cubeLpNorm R (4 : ℝ≥0∞) (fun x => A x i j) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcoord i j
    have hsum0 : 0 ≤ ∑ i : Fin d, ∑ j : Fin d,
        cubeLpNorm R (2 : ℝ≥0∞) (fun x => A x i j) :=
      Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => cubeLpNorm_nonneg R 2 _
    have hpow := pow_le_pow_left₀ hsum0 hsum 4
    unfold oneStepShellForcingCellB
    rw [hside]
    calc
      (c * ∑ i : Fin d, ∑ j : Fin d,
          cubeLpNorm R (2 : ℝ≥0∞) (fun x => A x i j)) ^ (4 : ℕ) ≤
        (c * ∑ i : Fin d, ∑ j : Fin d,
          cubeLpNorm R (4 : ℝ≥0∞) (fun x => A x i j)) ^ (4 : ℕ) := by
        gcongr
      _ = c ^ (4 : ℕ) *
          (∑ i : Fin d, ∑ j : Fin d,
            cubeLpNorm R (4 : ℝ≥0∞) (fun x => A x i j)) ^ (4 : ℕ) := by
        rw [mul_pow]
      _ ≤ c ^ (4 : ℕ) * (((d : ℝ) ^ 2) ^ (3 : ℕ) *
          ∑ i : Fin d, ∑ j : Fin d,
            (cubeLpNorm R (4 : ℝ≥0∞) (fun x => A x i j)) ^ (4 : ℕ)) := by
        gcongr
        exact sum_fin_two_four_le_card_cubed_mul_sum_four
          (fun i j => cubeLpNorm R (4 : ℝ≥0∞) (fun x => A x i j))
          (fun _ _ => cubeLpNorm_nonneg _ _ _)
  have hbase : descendantsAverage Q depth (fun R =>
      (oneStepShellForcingCellB (Q := Q) (R := R)
        M n h omega p hh) ^ (4 : ℕ)) ≤
      c ^ (4 : ℕ) * (((d : ℝ) ^ 2) ^ (4 : ℕ) *
        (cubeLpNorm Q (4 : ℝ≥0∞)
          (fun x => HilbertMat.ofMat (A x))) ^ (4 : ℕ)) := by
    calc
      _ ≤ descendantsAverage Q depth (fun R =>
          c ^ (4 : ℕ) * (((d : ℝ) ^ 2) ^ (3 : ℕ) *
            ∑ i : Fin d, ∑ j : Fin d,
              (cubeLpNorm R (4 : ℝ≥0∞) (fun x => A x i j)) ^ (4 : ℕ))) := by
        apply descendantsAverage_le_descendantsAverage
        exact hpoint
      _ = c ^ (4 : ℕ) * (((d : ℝ) ^ 2) ^ (3 : ℕ) *
          ∑ i : Fin d, ∑ j : Fin d,
            (cubeLpNorm Q (4 : ℝ≥0∞) (fun x => A x i j)) ^ (4 : ℕ)) := by
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
        exact descendantsAverage_cubeLpNorm_four_pow_four_eq Q
          (fun x => A x i j) depth (by
            rw [memLp_piLp_iff] at hA
            have hi := hA i
            rw [memLp_piLp_iff] at hi
            exact hi j)
      _ ≤ c ^ (4 : ℕ) * (((d : ℝ) ^ 2) ^ (3 : ℕ) *
          ((d : ℝ) ^ 2 *
            (cubeLpNorm Q (4 : ℝ≥0∞)
              (fun x => HilbertMat.ofMat (A x))) ^ (4 : ℕ))) := by
        gcongr
        exact sum_cubeLpNorm_hessianCoord_four_pow_le Q A hA
      _ = _ := by ring
  have hscale : 0 < (3 : ℝ) ^ n := by positivity
  have hnorm :
      (eLpNorm (fun x => (3 : ℝ) ^ n • HilbertMat.ofMat (A x)) 4
        (normalizedCubeMeasure Q)).toReal =
        (3 : ℝ) ^ n * cubeLpNorm Q (4 : ℝ≥0∞)
          (fun x => HilbertMat.ofMat (A x)) := by
    unfold cubeLpNorm
    change (eLpNorm ((3 : ℝ) ^ n •
        (fun x => HilbertMat.ofMat (A x))) 4
        (normalizedCubeMeasure Q)).toReal = _
    rw [eLpNorm_const_smul, ENNReal.toReal_mul]
    simp only [Real.enorm_eq_ofReal hscale.le, ENNReal.toReal_ofReal hscale.le]
  refine hbase.trans_eq ?_
  rw [hnorm]
  dsimp only [c]
  field_simp [hscale.ne']

/-- The normalized source-cell fourth moment of the shell derivative carrier
is `O(delta ^ 68)`, uniformly in the outer cube and block length. -/
theorem exists_lintegral_oneStepShellForcingCellB_source_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h K : ℕ)
        (p : Vec d) (_hp : vecNormSq p = 1)
        (hh : 0 < h) (_hscale : (h : ℝ) ≤ M.delta⁻¹)
        (_hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
        (_hK : oneStepLocalizationScale n M.delta ≤ K),
        ∫⁻ omega, ENNReal.ofReal
            ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
              ∑ R ∈ oneStepSourceCells d K n M.delta,
                (oneStepShellForcingCellB
                  (Q := originCube d (K : ℤ)) (R := R)
                  M n h omega p hh) ^ (4 : ℕ)) ∂M.P.toMeasure ≤
          C * ENNReal.ofReal (M.delta ^ (68 : ℕ)) := by
  let C : ℝ≥0∞ := ((d : ℝ≥0∞) ^ 2) ^ (4 : ℕ) *
    oneStepShellJacobianMatrixFourthConst d
  have hCtop : C < ∞ := by
    dsimp only [C, oneStepShellJacobianMatrixFourthConst]
    finiteness
  refine ⟨C, hCtop, ?_⟩
  intro M n h K p hp hh hscale hsource hK
  let Q := originCube d (K : ℤ)
  let depth := K - oneStepLocalizationScale n M.delta
  let Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun omega =>
    eLpNorm (fun x => (3 : ℝ) ^ n • HilbertMat.ofMat
        ((oneStepShellForcingW14 M n h omega p Q hh).jacobian x))
      4 (normalizedCubeMeasure Q)
  have hdet : ∀ omega,
      descendantsAverage Q depth (fun R =>
          (oneStepShellForcingCellB (Q := Q) (R := R)
            M n h omega p hh) ^ (4 : ℕ)) ≤
        ((cubeScaleFactor Q / (3 : ℝ) ^ depth) / (3 : ℝ) ^ n) ^ (4 : ℕ) *
          (((d : ℝ) ^ 2) ^ (4 : ℕ) * (Y omega).toReal ^ (4 : ℕ)) := by
    intro omega
    simpa only [Y] using
      descendantsAverage_oneStepShellForcingCellB_four_le_scaled_matrix
        M n h depth p Q omega hh
  have hratio := ofReal_oneStep_source_ratio_four_mul_delta_four_le_delta_sixtyEight
    (d := d) M.shellPrefix.delta_pos
      (M.shellPrefix.delta_le_half.trans (by norm_num)) hsource hK
  have hY := lintegral_eLpNorm_oneStepShellJacobianMatrix_four_le
    M n h p Q hh hscale
  have hY' : ∫⁻ omega, (Y omega) ^ (4 : ℕ) ∂M.P.toMeasure ≤
      oneStepShellJacobianMatrixFourthConst d *
        (ENNReal.ofReal M.delta) ^ (4 : ℝ) := by
    calc
      _ = ∫⁻ omega, (Y omega) ^ (4 : ℝ) ∂M.P.toMeasure := by
        apply lintegral_congr
        intro omega
        exact (ENNReal.rpow_natCast (Y omega) 4).symm
      _ ≤ _ := hY.trans (oneStepShellJacobianMatrix_payload_le_delta_four M p hp)
  have hpoint : ∀ omega,
      ENNReal.ofReal (descendantsAverage Q depth (fun R =>
          (oneStepShellForcingCellB (Q := Q) (R := R)
            M n h omega p hh) ^ (4 : ℕ))) ≤
        ENNReal.ofReal
            (((cubeScaleFactor Q / (3 : ℝ) ^ depth) / (3 : ℝ) ^ n) ^
              (4 : ℕ) * ((d : ℝ) ^ 2) ^ (4 : ℕ)) *
          (Y omega) ^ (4 : ℕ) := by
    intro omega
    have hYtop : Y omega ≠ ∞ := by
      dsimp only [Y]
      have hm := (oneStepShellForcingW14 M n h omega p Q hh).jacobianHilbertMemLp
      simpa only [oneStepFourExponent_exponent] using! hm.const_smul ((3 : ℝ) ^ n) |>.eLpNorm_ne_top
    calc
      _ ≤ ENNReal.ofReal
          (((cubeScaleFactor Q / (3 : ℝ) ^ depth) / (3 : ℝ) ^ n) ^
            (4 : ℕ) * (((d : ℝ) ^ 2) ^ (4 : ℕ) *
              (Y omega).toReal ^ (4 : ℕ))) := ENNReal.ofReal_le_ofReal (hdet omega)
      _ = ENNReal.ofReal
            (((cubeScaleFactor Q / (3 : ℝ) ^ depth) / (3 : ℝ) ^ n) ^
              (4 : ℕ) * ((d : ℝ) ^ 2) ^ (4 : ℕ)) *
          (Y omega) ^ (4 : ℕ) := by
        rw [ENNReal.ofReal_mul (by positivity :
            0 ≤ ((cubeScaleFactor Q / (3 : ℝ) ^ depth) /
              (3 : ℝ) ^ n) ^ (4 : ℕ)),
          ENNReal.ofReal_mul (by positivity :
            0 ≤ (((d : ℝ) ^ 2) ^ (4 : ℕ))),
          ENNReal.ofReal_mul (by positivity :
            0 ≤ ((cubeScaleFactor Q / (3 : ℝ) ^ depth) /
              (3 : ℝ) ^ n) ^ (4 : ℕ)),
          ENNReal.ofReal_pow ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hYtop]
        simp only [mul_assoc]
  change ∫⁻ omega, ENNReal.ofReal
      (descendantsAverage Q depth (fun R =>
        (oneStepShellForcingCellB (Q := Q) (R := R)
          M n h omega p hh) ^ (4 : ℕ))) ∂M.P.toMeasure ≤ _
  calc
    _ ≤ ∫⁻ omega,
        ENNReal.ofReal
            (((cubeScaleFactor Q / (3 : ℝ) ^ depth) / (3 : ℝ) ^ n) ^
              (4 : ℕ) * ((d : ℝ) ^ 2) ^ (4 : ℕ)) *
          (Y omega) ^ (4 : ℕ) ∂M.P.toMeasure := lintegral_mono hpoint
    _ = ENNReal.ofReal
          (((cubeScaleFactor Q / (3 : ℝ) ^ depth) / (3 : ℝ) ^ n) ^
            (4 : ℕ) * ((d : ℝ) ^ 2) ^ (4 : ℕ)) *
        ∫⁻ omega, (Y omega) ^ (4 : ℕ) ∂M.P.toMeasure := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal
          (((cubeScaleFactor Q / (3 : ℝ) ^ depth) / (3 : ℝ) ^ n) ^
            (4 : ℕ) * ((d : ℝ) ^ 2) ^ (4 : ℕ)) *
        oneStepShellJacobianMatrixFourthConst d *
          (ENNReal.ofReal M.delta) ^ (4 : ℝ) := by
      simpa only [mul_assoc] using
        (mul_le_mul_right hY'
          (ENNReal.ofReal
            (((cubeScaleFactor Q / (3 : ℝ) ^ depth) / (3 : ℝ) ^ n) ^
              (4 : ℕ) * ((d : ℝ) ^ 2) ^ (4 : ℕ))))
    _ = ((d : ℝ≥0∞) ^ 2) ^ (4 : ℕ) *
          oneStepShellJacobianMatrixFourthConst d *
        (ENNReal.ofReal
          (((cubeScaleFactor Q / (3 : ℝ) ^ depth) / (3 : ℝ) ^ n) ^
            (4 : ℕ)) * (ENNReal.ofReal M.delta) ^ (4 : ℝ)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      norm_num [ENNReal.ofReal_pow]
      ring
    _ ≤ C * ENNReal.ofReal (M.delta ^ (68 : ℕ)) := by
      dsimp only [C]
      gcongr

theorem oneStepShellForcingCellB_nonneg_support
    {d : ℕ} {Q R : TriadicCube d}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q : Vec d) (hh : 0 < h) :
    0 ≤ oneStepShellForcingCellB (Q := Q) (R := R)
      M n h omega q hh := by
  unfold oneStepShellForcingCellB
  exact mul_nonneg (cubeScaleFactor_nonneg R) <|
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      cubeLpNorm_nonneg R 2 _

/-- Real-integral spelling consumed by the shell-enlarged finite fold. -/
theorem exists_oneStepShellForcingCellB_source_fourth_budget
    (d : ℕ) [NeZero d] :
    ∃ CS : ℝ, 0 ≤ CS ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h K : ℕ) (q : Vec d),
        vecNormSq q = 1 → ∀ hh : 0 < h, (h : ℝ) ≤ M.delta⁻¹ →
          16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n →
          oneStepLocalizationScale n M.delta ≤ K →
          (∀ R ∈ oneStepSourceCells d K n M.delta,
            Integrable (fun omega ↦
              oneStepShellForcingCellB (Q := originCube d (K : ℤ)) (R := R)
                M n h omega q hh ^ (4 : ℕ)) M.P.toMeasure) ∧
          ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
              ∑ R ∈ oneStepSourceCells d K n M.delta,
                ∫ omega, oneStepShellForcingCellB
                  (Q := originCube d (K : ℤ)) (R := R)
                  M n h omega q hh ^ (4 : ℕ) ∂M.P.toMeasure ≤
            CS * M.delta ^ (68 : ℕ)) := by
  obtain ⟨C, hCtop, hC⟩ :=
    exists_lintegral_oneStepShellForcingCellB_source_le d
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro M n h K q hq hh hscale hsource hK
  let Q := originCube d (K : ℤ)
  let depth := K - oneStepLocalizationScale n M.delta
  have hbudget := hC M n h K q hq hh hscale hsource hK
  have hKtop : C * ENNReal.ofReal (M.delta ^ (68 : ℕ)) ≠ ∞ :=
    ENNReal.mul_ne_top hCtop.ne ENNReal.ofReal_ne_top
  have hpack := finiteFamily_four_budget_of_lintegral_descendantsAverage
    Q depth
    (fun R omega ↦ oneStepShellForcingCellB (Q := Q) (R := R)
      M n h omega q hh)
    (fun R _hR ↦ measurable_oneStepShellForcingCellB M n h q hh)
    (fun R _hR omega ↦
      oneStepShellForcingCellB_nonneg_support M n h omega q hh)
    hKtop hbudget
  have htoReal :
      (C * ENNReal.ofReal (M.delta ^ (68 : ℕ))).toReal =
        C.toReal * M.delta ^ (68 : ℕ) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal]
    exact pow_nonneg M.shellPrefix.delta_pos.le 68
  simpa only [Q, depth, oneStepSourceCells, htoReal] using hpack

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
