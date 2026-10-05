module

public import SubdiffusiveProcess.CoarseGrainingVocab.AhomCharacterization
public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments

@[expose] public section

/-!
# Reciprocal-law support for the homogenized lower bound

The expectation identities are those of the paper.
The product-law transport uses independent-coordinate uniqueness.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory ProbabilityTheory Homogenization

noncomputable section

private abbrev Sample (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d
private abbrev Field (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialField d

def negatePotentialSequence {d : ℕ} (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : _root_.SubdiffusiveProcess.Model.PotentialSample d :=
  fun k => _root_.SubdiffusiveProcess.Model.PotentialField.negate (omega k)

theorem measurable_negatePotentialSequence {d : ℕ} :
    Measurable (negatePotentialSequence (d := d)) := by
  apply measurable_pi_iff.mpr
  intro k
  exact _root_.SubdiffusiveProcess.Model.PotentialField.measurable_negate.comp
    (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k)

private theorem negate_triadicScale {d : ℕ} (k : ℕ) (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
    _root_.SubdiffusiveProcess.Model.PotentialField.negate
        (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g) =
      _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k
        (_root_.SubdiffusiveProcess.Model.PotentialField.negate g) := by
  apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
  intro x
  rfl

theorem potentialMarginalLaw_negation {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) :
    Measure.map _root_.SubdiffusiveProcess.Model.PotentialField.negate
        (_root_.SubdiffusiveProcess.Model.potentialMarginalLaw M.P k).toMeasure =
      (_root_.SubdiffusiveProcess.Model.potentialMarginalLaw M.P k).toMeasure := by
  have hscale := congrArg ProbabilityMeasure.toMeasure
    (M.shellPrefix.marginal_scaling k)
  have hzero := congrArg ProbabilityMeasure.toMeasure M.G3.negation
  change (_root_.SubdiffusiveProcess.Model.potentialMarginalLaw M.P k).toMeasure =
    Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure at hscale
  change Measure.map _root_.SubdiffusiveProcess.Model.PotentialField.negate
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure =
    (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure at hzero
  calc
    Measure.map _root_.SubdiffusiveProcess.Model.PotentialField.negate
        (_root_.SubdiffusiveProcess.Model.potentialMarginalLaw M.P k).toMeasure =
      Measure.map _root_.SubdiffusiveProcess.Model.PotentialField.negate
        (Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)
          (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) := by rw [hscale]
    _ = Measure.map
        (_root_.SubdiffusiveProcess.Model.PotentialField.negate ∘
          _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure :=
      Measure.map_map _root_.SubdiffusiveProcess.Model.PotentialField.measurable_negate
        (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale k)
    _ = Measure.map
        (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k ∘
          _root_.SubdiffusiveProcess.Model.PotentialField.negate)
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
      apply congrArg (fun f : _root_.SubdiffusiveProcess.Model.PotentialField d → _root_.SubdiffusiveProcess.Model.PotentialField d =>
        Measure.map f (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
      funext g
      exact negate_triadicScale k g
    _ = Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)
        (Measure.map _root_.SubdiffusiveProcess.Model.PotentialField.negate
          (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) :=
      (Measure.map_map
        (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale k)
        _root_.SubdiffusiveProcess.Model.PotentialField.measurable_negate).symm
    _ = Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by rw [hzero]
    _ = (_root_.SubdiffusiveProcess.Model.potentialMarginalLaw M.P k).toMeasure := by rw [hscale]

theorem potentialSequenceLaw_negation {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    Measure.map (negatePotentialSequence (d := d)) M.P.toMeasure = M.P.toMeasure := by
  have hprod := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun k : ℕ => _root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k)).mp
      M.shellPrefix.independent
  have hnegInd : iIndepFun
      (fun k : ℕ => fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        _root_.SubdiffusiveProcess.Model.PotentialField.negate (omega k)) M.P.toMeasure :=
    M.shellPrefix.independent.comp
      (fun _ => _root_.SubdiffusiveProcess.Model.PotentialField.negate)
      (fun _ => _root_.SubdiffusiveProcess.Model.PotentialField.measurable_negate)
  have hnegProd := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun _ : ℕ => _root_.SubdiffusiveProcess.Model.PotentialField.measurable_negate.comp
      (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate _))).mp hnegInd
  calc
    Measure.map (negatePotentialSequence (d := d)) M.P.toMeasure =
      Measure.infinitePi (fun k : ℕ =>
        Measure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
          _root_.SubdiffusiveProcess.Model.PotentialField.negate (omega k)) M.P.toMeasure) := by
      simpa only [negatePotentialSequence, Function.comp_def] using! hnegProd
    _ = Measure.infinitePi (fun k : ℕ =>
        Measure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega k) M.P.toMeasure) := by
      apply congrArg Measure.infinitePi
      funext k
      calc
        Measure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
            _root_.SubdiffusiveProcess.Model.PotentialField.negate (omega k)) M.P.toMeasure =
          Measure.map _root_.SubdiffusiveProcess.Model.PotentialField.negate
            (Measure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega k) M.P.toMeasure) := by
            change Measure.map
              (_root_.SubdiffusiveProcess.Model.PotentialField.negate ∘
                fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega k) M.P.toMeasure = _
            rw [Measure.map_map _root_.SubdiffusiveProcess.Model.PotentialField.measurable_negate
              (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k)]
        _ = Measure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega k) M.P.toMeasure :=
          potentialMarginalLaw_negation M k
    _ = Measure.map (fun omega (k : ℕ) => omega k) M.P.toMeasure := hprod.symm
    _ = M.P.toMeasure := Measure.map_id'

theorem aCutoff_negatePotentialSequence {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (x : Vec d) :
    _root_.SubdiffusiveProcess.Model.aCutoff M m (negatePotentialSequence omega) x =
      Real.exp (-2 * (m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        (_root_.SubdiffusiveProcess.Model.aCutoff M m omega x)⁻¹ := by
  rw [_root_.SubdiffusiveProcess.Model.aCutoff, _root_.SubdiffusiveProcess.Model.aCutoff]
  simp only [negatePotentialSequence, _root_.SubdiffusiveProcess.Model.PotentialField.negate_apply]
  rw [← Real.exp_neg, ← Real.exp_add]
  congr 1
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- After undoing the mean-one normalization, negating every shell gives the
pointwise reciprocal coefficient, as used at paper label `p.homogenized.coefficient.reciprocal.lower`. -/
theorem uncenteredCutoff_negatePotentialSequence {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (x : Vec d) :
    Real.exp ((m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        _root_.SubdiffusiveProcess.Model.aCutoff M m (negatePotentialSequence omega) x =
      (Real.exp ((m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        _root_.SubdiffusiveProcess.Model.aCutoff M m omega x)⁻¹ := by
  rw [aCutoff_negatePotentialSequence]
  rw [mul_inv, ← mul_assoc, ← Real.exp_add]
  rw [← Real.exp_neg]
  congr 1
  ring_nf

/-- The inverse finite cutoff has the exact lognormal expectation from
the lognormal expectation identities for `a_L` in the special case `n = -1`. -/
theorem integral_inv_aCutoff_apply {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (x : Vec d) :
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, (_root_.SubdiffusiveProcess.Model.aCutoff M m omega x)⁻¹
        ∂M.P.toMeasure =
      Real.exp (2 * (m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
  let T := negatePotentialSequence (d := d)
  let c := Real.exp (2 * (m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
  have hpoint : ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      (_root_.SubdiffusiveProcess.Model.aCutoff M m omega x)⁻¹ =
        c * _root_.SubdiffusiveProcess.Model.aCutoff M m (T omega) x := by
    intro omega
    have hneg := aCutoff_negatePotentialSequence M m omega x
    dsimp [T, c]
    rw [hneg]
    rw [← mul_assoc, ← Real.exp_add]
    have hexp :
        2 * (m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
            -2 * (m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P = 0 := by ring
    rw [hexp, Real.exp_zero, one_mul]
  calc
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, (_root_.SubdiffusiveProcess.Model.aCutoff M m omega x)⁻¹
        ∂M.P.toMeasure =
      ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, c * _root_.SubdiffusiveProcess.Model.aCutoff M m (T omega) x
        ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      exact hpoint omega
    _ = c * ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        _root_.SubdiffusiveProcess.Model.aCutoff M m (T omega) x ∂M.P.toMeasure := by
      rw [integral_const_mul]
    _ = c * ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        _root_.SubdiffusiveProcess.Model.aCutoff M m omega x ∂M.P.toMeasure := by
      rw [Homogenization.integral_comp_eq_of_map_eq
        measurable_negatePotentialSequence (potentialSequenceLaw_negation M)
        (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => _root_.SubdiffusiveProcess.Model.aCutoff M m omega x)
        (_root_.SubdiffusiveProcess.Model.measurable_aCutoff M m x).aestronglyMeasurable]
    _ = Real.exp (2 * (m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
      rw [SubdiffusiveProcess.CoarseGrainingVocab.integral_aCutoff_apply M m x]
      simp [c]

private theorem integral_exp_centered_potentialCoordinate {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) (x : Vec d) :
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        Real.exp (omega k x - _root_.SubdiffusiveProcess.Model.tauSq M.P) ∂M.P.toMeasure = 1 := by
  let phi : ℝ → ℝ := fun z =>
    Real.exp (z - _root_.SubdiffusiveProcess.Model.tauSq M.P)
  let evalK : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega => omega k x
  let eval00 : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega => omega 0 0
  have hphi : Measurable phi :=
    (measurable_id.sub measurable_const).exp
  have hevalK : Measurable evalK :=
    (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).comp
      (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k)
  have heval00 : Measurable eval00 :=
    (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0).comp
      (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate 0)
  have hmap : Measure.map evalK M.P.toMeasure = Measure.map eval00 M.P.toMeasure := by
    exact (SubdiffusiveProcess.CoarseGrainingVocab.map_potentialCoordinate_apply_eq_zero M k x).trans
      (SubdiffusiveProcess.CoarseGrainingVocab.map_potentialCoordinate_apply_eq_zero M 0 0).symm
  calc
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        Real.exp (omega k x - _root_.SubdiffusiveProcess.Model.tauSq M.P) ∂M.P.toMeasure =
      ∫ z, phi z ∂Measure.map evalK M.P.toMeasure := by
        exact (integral_map hevalK.aemeasurable hphi.aestronglyMeasurable).symm
    _ = ∫ z, phi z ∂Measure.map eval00 M.P.toMeasure := by rw [hmap]
    _ = ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        Real.exp (omega 0 0 - _root_.SubdiffusiveProcess.Model.tauSq M.P) ∂M.P.toMeasure := by
      exact integral_map heval00.aemeasurable hphi.aestronglyMeasurable
    _ = 1 := by
      simpa [_root_.SubdiffusiveProcess.Model.aCutoff] using
        SubdiffusiveProcess.CoarseGrainingVocab.integral_aCutoff_apply M 0 0

/-- First of the lognormal expectation identities for `a_L`, for the paper's `a_{-1}=1`
convention and every admissible shell interval. -/
theorem integral_cutoffRatio {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (n : ℤ)
    (x : Vec d) (hn : -1 ≤ n) (hnm : n < (m : ℤ)) :
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        (SubdiffusiveProcess.CoarseGrainingVocab.cutoffRatioMinusOne M m n omega x + 1)
        ∂M.P.toMeasure = 1 := by
  let X : ℕ → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun k omega =>
    omega k x - _root_.SubdiffusiveProcess.Model.tauSq M.P
  let s := SubdiffusiveProcess.CoarseGrainingVocab.cutoffShellIndices m n
  have hIndep : iIndepFun X M.P.toMeasure := by
    simpa [X, Function.comp_def] using M.shellPrefix.independent.comp
      (fun _ g => g x - _root_.SubdiffusiveProcess.Model.tauSq M.P)
      (fun _ => (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).sub
        measurable_const)
  have hMeas : ∀ k, Measurable (X k) := fun k =>
    ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).comp
      (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k)).sub measurable_const
  have hFactor : ∀ k, ProbabilityTheory.mgf (X k) M.P.toMeasure 1 = 1 := by
    intro k
    simpa [ProbabilityTheory.mgf, X] using
      integral_exp_centered_potentialCoordinate M k x
  calc
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        (SubdiffusiveProcess.CoarseGrainingVocab.cutoffRatioMinusOne M m n omega x + 1)
        ∂M.P.toMeasure =
      ProbabilityTheory.mgf (∑ k ∈ s, X k) M.P.toMeasure 1 := by
        apply integral_congr_ae
        filter_upwards with omega
        rw [SubdiffusiveProcess.CoarseGrainingVocab.cutoffRatioMinusOne_eq_exp_shell
          M m n omega x hn hnm]
        simp only [sub_add_cancel]
        congr 1
        simp [s, X, SubdiffusiveProcess.CoarseGrainingVocab.cutoffShellSum,
          Finset.sum_sub_distrib,
          SubdiffusiveProcess.CoarseGrainingVocab.cutoffShellIndices_card m n hn hnm]
        have hdiff : 0 ≤ (m : ℤ) - n := by omega
        have hcast : ((((m : ℤ) - n).toNat : ℕ) : ℝ) =
            (((m : ℤ) - n : ℤ) : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hdiff
        rw [hcast]
        left
        norm_cast
    _ = ∏ k ∈ s, ProbabilityTheory.mgf (X k) M.P.toMeasure 1 :=
      hIndep.mgf_sum hMeas s
    _ = 1 := by simp [hFactor]

/-- Second of the lognormal expectation identities for `a_L`. -/
theorem integral_inverseCutoffRatio {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (n : ℤ)
    (x : Vec d) (hn : -1 ≤ n) (hnm : n < (m : ℤ)) :
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        (SubdiffusiveProcess.CoarseGrainingVocab.inverseCutoffRatioMinusOne M m n omega x + 1)
        ∂M.P.toMeasure =
      Real.exp (2 * (((m : ℤ) - n : ℤ) : ℝ) *
        _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
  let N : ℝ := (((m : ℤ) - n : ℤ) : ℝ)
  let T := negatePotentialSequence (d := d)
  have hpoint : ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      SubdiffusiveProcess.CoarseGrainingVocab.inverseCutoffRatioMinusOne M m n omega x + 1 =
        Real.exp (2 * N * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
          (SubdiffusiveProcess.CoarseGrainingVocab.cutoffRatioMinusOne M m n (T omega) x + 1) := by
    intro omega
    rw [SubdiffusiveProcess.CoarseGrainingVocab.inverseCutoffRatioMinusOne_eq_exp_shell
      M m n omega x hn hnm,
      SubdiffusiveProcess.CoarseGrainingVocab.cutoffRatioMinusOne_eq_exp_shell
        M m n (T omega) x hn hnm]
    simp only [sub_add_cancel]
    rw [← Real.exp_add]
    congr 1
    dsimp [SubdiffusiveProcess.CoarseGrainingVocab.cutoffShellSum, T,
      negatePotentialSequence, N]
    simp only [_root_.SubdiffusiveProcess.Model.PotentialField.negate_apply,
      Finset.sum_neg_distrib]
    ring
  calc
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        (SubdiffusiveProcess.CoarseGrainingVocab.inverseCutoffRatioMinusOne M m n omega x + 1)
        ∂M.P.toMeasure =
      ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        Real.exp (2 * N * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
          (SubdiffusiveProcess.CoarseGrainingVocab.cutoffRatioMinusOne M m n (T omega) x + 1)
        ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      exact hpoint omega
    _ = Real.exp (2 * N * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          (SubdiffusiveProcess.CoarseGrainingVocab.cutoffRatioMinusOne M m n (T omega) x + 1)
          ∂M.P.toMeasure := by rw [integral_const_mul]
    _ = Real.exp (2 * N * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          (SubdiffusiveProcess.CoarseGrainingVocab.cutoffRatioMinusOne M m n omega x + 1)
          ∂M.P.toMeasure := by
      congr 1
      change (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          (fun z : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
            SubdiffusiveProcess.CoarseGrainingVocab.cutoffRatioMinusOne M m n z x + 1)
            (negatePotentialSequence omega) ∂M.P.toMeasure) = _
      have hg : Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
          SubdiffusiveProcess.CoarseGrainingVocab.cutoffRatioMinusOne M m n omega x + 1) := by
        have heq : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
            SubdiffusiveProcess.CoarseGrainingVocab.cutoffRatioMinusOne M m n omega x + 1) =
            fun omega => Real.exp (SubdiffusiveProcess.CoarseGrainingVocab.cutoffShellSum m n x omega -
              (((m : ℤ) - n : ℤ) : ℝ) *
                _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
          funext omega
          rw [SubdiffusiveProcess.CoarseGrainingVocab.cutoffRatioMinusOne_eq_exp_shell
            M m n omega x hn hnm]
          ring
        rw [heq]
        exact ((SubdiffusiveProcess.CoarseGrainingVocab.measurable_cutoffShellSum m n x).sub
          measurable_const).exp
      exact Homogenization.integral_comp_eq_of_map_eq
        measurable_negatePotentialSequence (potentialSequenceLaw_negation M)
        (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
          SubdiffusiveProcess.CoarseGrainingVocab.cutoffRatioMinusOne M m n omega x + 1)
        hg.aestronglyMeasurable
    _ = Real.exp (2 * (((m : ℤ) - n : ℤ) : ℝ) *
        _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
      rw [integral_cutoffRatio M m n x hn hnm]
      simp [N]

end

end SubdiffusiveProcess.CoarseGrainingVocab
