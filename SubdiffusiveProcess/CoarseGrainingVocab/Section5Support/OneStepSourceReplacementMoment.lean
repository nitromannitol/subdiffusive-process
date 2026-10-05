module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepInverseExponentialRemainder
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepParentWeightedEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNestedSourceParentReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCellObservableMeasurability
public import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Additivity.AnalyticInequalities

@[expose] public section




open MeasureTheory Homogenization Homogenization.Book
open Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private theorem cutoffRatio_eq_exp_oneStepCenteredShellAt
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) (hh : 0 < h) :
    _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x /
        _root_.SubdiffusiveProcess.Model.aCutoff M n omega x =
      Real.exp (oneStepCenteredShellAt M n h x omega) := by
  have hrepr := cutoffRatioMinusOne_eq_exp_shell
    M (n + h) (n : ℤ) omega x (by omega)
      (by exact_mod_cast Nat.lt_add_of_pos_right hh)
  unfold cutoffRatioMinusOne aCutoffAtInt at hrepr
  simp only [show ¬ (n : ℤ) < 0 by omega, ite_false,
    Int.toNat_natCast] at hrepr
  dsimp only [oneStepCenteredShellAt]
  have hgap : ((((n + h : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) = h := by
    push_cast
    ring
  rw [hgap] at hrepr
  calc
    _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x /
        _root_.SubdiffusiveProcess.Model.aCutoff M n omega x =
      (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x /
        _root_.SubdiffusiveProcess.Model.aCutoff M n omega x - 1) + 1 := by ring
    _ = (Real.exp (cutoffShellSum (n + h) (n : ℤ) x omega -
        (h : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1) + 1 := by
      rw [hrepr]
    _ = Real.exp (oneStepCenteredShellAt M n h x omega) := by
      rw [oneStepCenteredShellAt]
      ring

private theorem inverseCutoffRatio_eq_exp_neg_oneStepCenteredShellAt
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) (hh : 0 < h) :
    _root_.SubdiffusiveProcess.Model.aCutoff M n omega x /
        _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x =
      Real.exp (-oneStepCenteredShellAt M n h x omega) := by
  have hrepr := inverseCutoffRatioMinusOne_eq_exp_shell
    M (n + h) (n : ℤ) omega x (by omega)
      (by exact_mod_cast Nat.lt_add_of_pos_right hh)
  unfold inverseCutoffRatioMinusOne aCutoffAtInt at hrepr
  simp only [show ¬ (n : ℤ) < 0 by omega, ite_false,
    Int.toNat_natCast] at hrepr
  dsimp only [oneStepCenteredShellAt]
  have hgap : ((((n + h : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) = h := by
    push_cast
    ring
  rw [hgap] at hrepr
  calc
    _root_.SubdiffusiveProcess.Model.aCutoff M n omega x /
        _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x =
      (_root_.SubdiffusiveProcess.Model.aCutoff M n omega x /
        _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x - 1) + 1 := by ring
    _ = (Real.exp (-cutoffShellSum (n + h) (n : ℤ) x omega +
        (h : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1) + 1 := by
      rw [hrepr]
    _ = Real.exp (-oneStepCenteredShellAt M n h x omega) := by
      rw [oneStepCenteredShellAt]
      ring_nf

/-- The source-cell forward supremum is within the exponential of the
cellwise shell oscillation of every pointwise cutoff ratio. -/
theorem oneStepUpperSourceCellWeight_le_exp_two_envelope_mul
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hscale : R.scale ≤ (n : ℤ)) (hh : 0 < h)
    {x : Vec d} (hx : x ∈ openCubeSet R) :
    oneStepUpperSourceCellWeight M n h R omega ≤
      Real.exp (2 * oneStepSourceCellShellOscillationEnvelope n h R omega) *
        Real.exp (oneStepCenteredShellAt M n h x omega) := by
  unfold oneStepUpperSourceCellWeight cutoffRatioSup
  apply csSup_le
  · obtain ⟨y, hy⟩ := (Ch02.cubeDomain R).nonempty
    exact ⟨_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega y /
      _root_.SubdiffusiveProcess.Model.aCutoff M n omega y, y, hy, rfl⟩
  · rintro r ⟨y, hy, rfl⟩
    have hy' : y ∈ openCubeSet R := by
      simpa only [Ch02.cubeDomain_coe] using hy
    rw [cutoffRatio_eq_exp_oneStepCenteredShellAt M n h omega y hh]
    have hosc := abs_oneStepCenteredShellAt_sub_le_two_envelope
      M n h R omega hscale hx hy'
    have hle : oneStepCenteredShellAt M n h y omega ≤
        2 * oneStepSourceCellShellOscillationEnvelope n h R omega +
          oneStepCenteredShellAt M n h x omega := by
      linarith [(abs_le.mp hosc).2]
    calc
      Real.exp (oneStepCenteredShellAt M n h y omega) ≤
          Real.exp (2 * oneStepSourceCellShellOscillationEnvelope n h R omega +
            oneStepCenteredShellAt M n h x omega) := Real.exp_le_exp.mpr hle
      _ = _ := by rw [Real.exp_add]

/-- Reciprocal copy of the pointwise-relative source-cell supremum bound. -/
theorem oneStepLowerSourceCellWeight_le_exp_two_envelope_mul
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hscale : R.scale ≤ (n : ℤ)) (hh : 0 < h)
    {x : Vec d} (hx : x ∈ openCubeSet R) :
    oneStepLowerSourceCellWeight M n h R omega ≤
      Real.exp (2 * oneStepSourceCellShellOscillationEnvelope n h R omega) *
        Real.exp (-oneStepCenteredShellAt M n h x omega) := by
  unfold oneStepLowerSourceCellWeight cutoffRatioSup
  apply csSup_le
  · obtain ⟨y, hy⟩ := (Ch02.cubeDomain R).nonempty
    exact ⟨_root_.SubdiffusiveProcess.Model.aCutoff M n omega y /
      _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega y, y, hy, rfl⟩
  · rintro r ⟨y, hy, rfl⟩
    have hy' : y ∈ openCubeSet R := by
      simpa only [Ch02.cubeDomain_coe] using hy
    rw [inverseCutoffRatio_eq_exp_neg_oneStepCenteredShellAt
      M n h omega y hh]
    have hosc := abs_oneStepCenteredShellAt_sub_le_two_envelope
      M n h R omega hscale hx hy'
    have hle : -oneStepCenteredShellAt M n h y omega ≤
        2 * oneStepSourceCellShellOscillationEnvelope n h R omega -
          oneStepCenteredShellAt M n h x omega := by
      linarith [(abs_le.mp hosc).1]
    calc
      Real.exp (-oneStepCenteredShellAt M n h y omega) ≤
          Real.exp (2 * oneStepSourceCellShellOscillationEnvelope n h R omega -
            oneStepCenteredShellAt M n h x omega) := Real.exp_le_exp.mpr hle
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add]

private theorem one_sub_exp_neg_le (t : ℝ) :
    1 - Real.exp (-t) ≤ t := by
  have h := Real.add_one_le_exp (-t)
  linarith

/-- The forward cell supremum differs from any pointwise multiplier by at
most the supremum times twice the shell-oscillation envelope. -/
theorem oneStepUpperSourceCellWeight_sub_exp_le_two_mul_envelope
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hscale : R.scale ≤ (n : ℤ)) (hh : 0 < h)
    {x : Vec d} (hx : x ∈ openCubeSet R) :
    oneStepUpperSourceCellWeight M n h R omega -
        Real.exp (oneStepCenteredShellAt M n h x omega) ≤
      2 * oneStepUpperSourceCellWeight M n h R omega *
        oneStepSourceCellShellOscillationEnvelope n h R omega := by
  let E := oneStepSourceCellShellOscillationEnvelope n h R omega
  let W := oneStepUpperSourceCellWeight M n h R omega
  let X := oneStepCenteredShellAt M n h x omega
  have hE : 0 ≤ E :=
    oneStepSourceCellShellOscillationEnvelope_nonneg n h R omega
  have hW : 0 ≤ W := (cutoffRatioSup_pos M (n + h) n
    (Ch02.cubeDomain R) omega).le
  have hraw : W ≤ Real.exp (2 * E) * Real.exp X := by
    simpa only [W, E, X] using
      oneStepUpperSourceCellWeight_le_exp_two_envelope_mul
        M n h R omega hscale hh hx
  have hscaled := mul_le_mul_of_nonneg_left hraw (Real.exp_pos (-(2 * E))).le
  have hlower : Real.exp (-(2 * E)) * W ≤ Real.exp X := by
    calc
      Real.exp (-(2 * E)) * W ≤
          Real.exp (-(2 * E)) * (Real.exp (2 * E) * Real.exp X) := hscaled
      _ = Real.exp X := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hexp : 1 - Real.exp (-(2 * E)) ≤ 2 * E :=
    one_sub_exp_neg_le (2 * E)
  calc
    W - Real.exp X ≤ W - Real.exp (-(2 * E)) * W := sub_le_sub_left hlower W
    _ = W * (1 - Real.exp (-(2 * E))) := by ring
    _ ≤ W * (2 * E) := mul_le_mul_of_nonneg_left hexp hW
    _ = 2 * W * E := by ring

/-- Reciprocal copy of the pointwise cell-supremum gap estimate. -/
theorem oneStepLowerSourceCellWeight_sub_exp_neg_le_two_mul_envelope
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hscale : R.scale ≤ (n : ℤ)) (hh : 0 < h)
    {x : Vec d} (hx : x ∈ openCubeSet R) :
    oneStepLowerSourceCellWeight M n h R omega -
        Real.exp (-oneStepCenteredShellAt M n h x omega) ≤
      2 * oneStepLowerSourceCellWeight M n h R omega *
        oneStepSourceCellShellOscillationEnvelope n h R omega := by
  let E := oneStepSourceCellShellOscillationEnvelope n h R omega
  let W := oneStepLowerSourceCellWeight M n h R omega
  let X := -oneStepCenteredShellAt M n h x omega
  have hE : 0 ≤ E :=
    oneStepSourceCellShellOscillationEnvelope_nonneg n h R omega
  have hW : 0 ≤ W := (cutoffRatioSup_pos M n (n + h)
    (Ch02.cubeDomain R) omega).le
  have hraw : W ≤ Real.exp (2 * E) * Real.exp X := by
    simpa only [W, E, X] using
      oneStepLowerSourceCellWeight_le_exp_two_envelope_mul
        M n h R omega hscale hh hx
  have hscaled := mul_le_mul_of_nonneg_left hraw (Real.exp_pos (-(2 * E))).le
  have hlower : Real.exp (-(2 * E)) * W ≤ Real.exp X := by
    calc
      Real.exp (-(2 * E)) * W ≤
          Real.exp (-(2 * E)) * (Real.exp (2 * E) * Real.exp X) := hscaled
      _ = Real.exp X := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hexp : 1 - Real.exp (-(2 * E)) ≤ 2 * E :=
    one_sub_exp_neg_le (2 * E)
  calc
    W - Real.exp X ≤ W - Real.exp (-(2 * E)) * W := sub_le_sub_left hlower W
    _ = W * (1 - Real.exp (-(2 * E))) := by ring
    _ ≤ W * (2 * E) := mul_le_mul_of_nonneg_left hexp hW
    _ = 2 * W * E := by ring

private theorem memLp_sqrt_vecNormSq_of_memLp_two
    {d : ℕ} {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    MemLp (fun x ↦ Real.sqrt (vecNormSq (F x))) 2
      (normalizedCubeMeasure Q) := by
  let T : Vec d →L[ℝ] HilbertVec d :=
    ((HilbertVec.continuousLinearEquivVec d).symm).toContinuousLinearMap
  have hHilbert : MemLp (fun x ↦ HilbertVec.ofVec (F x)) 2
      (normalizedCubeMeasure Q) := by
    exact T.comp_memLp' hF
  have hnorm := hHilbert.norm
  convert hnorm using 1
  funext x
  rw [← euclideanNorm_sq, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (euclideanNorm_nonneg _),
    euclideanNorm_eq_norm_ofVec]

/-- Euclidean Jensen inequality for a normalized vector-valued cube
average, expressed in the project's coordinate-free square norm. -/
theorem vecNormSq_cubeAverageVec_le_cubeAverage_vecNormSq
    {d : ℕ} (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    vecNormSq (cubeAverageVec Q F) ≤
      cubeAverage Q (fun x ↦ vecNormSq (F x)) := by
  refine (vecNormSq_cubeAverageVec_le_sum_cubeAverage_sq_of_memLp
    Q F hF).trans_eq ?_
  simp_rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  simp only [vecNormSq, vecDot, pow_two]
  rw [integral_finsetSum]
  intro i _hi
  have hFi : MemLp (fun x ↦ F x i) 2 (normalizedCubeMeasure Q) := by
    exact (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hF
  simpa only [pow_two] using (memLp_two_iff_integrable_sq hFi.aestronglyMeasurable).mp hFi

private theorem cubeAverage_mono_of_integrable_of_le_on_openCube
    {d : ℕ} (Q : TriadicCube d) (f g : Vec d → ℝ)
    (hf : Integrable f (normalizedCubeMeasure Q))
    (hg : Integrable g (normalizedCubeMeasure Q))
    (hle : ∀ x ∈ openCubeSet Q, f x ≤ g x) :
    cubeAverage Q f ≤ cubeAverage Q g := by
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  apply integral_mono_ae hf hg
  apply Gagliardo.ae_normalizedCubeMeasure_iff.2
  rw [cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
  exact hle x hx

/-- A pointwise weight-gap estimate plus Euclidean Jensen controls a
weighted cell mean by the weighted full field and one unweighted error. -/
theorem weight_mul_vecNormSq_cubeAverageVec_le
    {d : ℕ} (Q : TriadicCube d) (W E : ℝ)
    (w : Vec d → ℝ) (F : Vec d → Vec d)
    (hW : 0 ≤ W)
    (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hwMeas : AEStronglyMeasurable w (normalizedCubeMeasure Q))
    (hw0 : ∀ x ∈ openCubeSet Q, 0 ≤ w x)
    (hwLe : ∀ x ∈ openCubeSet Q, w x ≤ W)
    (hgap : ∀ x ∈ openCubeSet Q, W - w x ≤ 2 * W * E) :
    W * vecNormSq (cubeAverageVec Q F) ≤
      cubeAverage Q (fun x ↦ w x * vecNormSq (F x)) +
        2 * W * E * cubeAverage Q (fun x ↦ vecNormSq (F x)) := by
  have hplain := integrable_vecNormSq_of_memLp_two hF
  have hweighted : Integrable (fun x ↦ w x * vecNormSq (F x))
      (normalizedCubeMeasure Q) := by
    refine (hplain.const_mul W).mono'
      (hwMeas.mul hplain.1) ?_
    apply Gagliardo.ae_normalizedCubeMeasure_iff.2
    rw [cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (hw0 x hx) (vecNormSq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hwLe x hx) (vecNormSq_nonneg _)
  have herror : Integrable (fun x ↦
      2 * W * E * vecNormSq (F x)) (normalizedCubeMeasure Q) :=
    hplain.const_mul (2 * W * E)
  have hpoint : ∀ x ∈ openCubeSet Q,
      W * vecNormSq (F x) ≤
        w x * vecNormSq (F x) + 2 * W * E * vecNormSq (F x) := by
    intro x hx
    have := mul_le_mul_of_nonneg_right (hgap x hx) (vecNormSq_nonneg (F x))
    linarith
  calc
    W * vecNormSq (cubeAverageVec Q F) ≤
        W * cubeAverage Q (fun x ↦ vecNormSq (F x)) :=
      mul_le_mul_of_nonneg_left
        (vecNormSq_cubeAverageVec_le_cubeAverage_vecNormSq Q F hF) hW
    _ = cubeAverage Q (fun x ↦ W * vecNormSq (F x)) := by
      rw [cubeAverage_const_mul]
    _ ≤ cubeAverage Q (fun x ↦
        w x * vecNormSq (F x) + 2 * W * E * vecNormSq (F x)) :=
      cubeAverage_mono_of_integrable_of_le_on_openCube Q _ _
        (hplain.const_mul W) (hweighted.add herror) hpoint
    _ = cubeAverage Q (fun x ↦ w x * vecNormSq (F x)) +
        2 * W * E * cubeAverage Q (fun x ↦ vecNormSq (F x)) := by
      simp_rw [cubeAverage_eq_integral_normalizedCubeMeasure]
      rw [integral_add hweighted herror, integral_const_mul]

/-- Primal source-cell replacement with no fluctuation term: normalized
Jensen leaves only the shell-oscillation envelope times the unweighted cell
energy. -/
theorem oneStepUpperSourceCellWeight_mul_dirichletCellSlope_le
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d) (R : TriadicCube d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    oneStepUpperSourceCellWeight M n h R omega *
        vecNormSq (oneStepDirichletCellSlope M n h p
          (originCube d (K : ℤ)) R omega hh) ≤
      cubeAverage R (fun x ↦
        Real.exp (oneStepCenteredShellAt M n h x omega) *
          vecNormSq (oneStepDirichletSlopeField M n h p
            (originCube d (K : ℤ)) omega hh x)) +
      2 * oneStepUpperSourceCellWeight M n h R omega *
        oneStepSourceCellShellOscillationEnvelope n h R omega *
        cubeAverage R (fun x ↦
          vecNormSq (oneStepDirichletSlopeField M n h p
            (originCube d (K : ℤ)) omega hh x)) := by
  let F := oneStepDirichletSlopeField M n h p
    (originCube d (K : ℤ)) omega hh
  let W := oneStepUpperSourceCellWeight M n h R omega
  let E := oneStepSourceCellShellOscillationEnvelope n h R omega
  let w : Vec d → ℝ := fun x ↦
    Real.exp (oneStepCenteredShellAt M n h x omega)
  have hscale : R.scale ≤ (n : ℤ) := by
    rw [oneStepSourceCells_scale_eq hK hR]
    exact_mod_cast Nat.sub_le n (oneStepLocalizationDepth M.delta)
  have hF : MemLp F 2 (normalizedCubeMeasure R) :=
    oneStepDirichletSlopeField_memLp_sourceCell M n h p R hR omega hh
  have hbound := weight_mul_vecNormSq_cubeAverageVec_le R W E w F
    (le_of_lt (cutoffRatioSup_pos M (n + h) n
      (Ch02.cubeDomain R) omega)) hF
    ((measurable_oneStepCenteredShellAt_space M n h omega).exp
      |>.aestronglyMeasurable)
    (fun _ _ ↦ (Real.exp_pos _).le)
    (fun x hx ↦ by
      exact exp_oneStepCenteredShellAt_le_upperSourceCellWeight
        M n h R omega hh hx)
    (fun x hx ↦ by
      exact oneStepUpperSourceCellWeight_sub_exp_le_two_mul_envelope
        M n h R omega hscale hh hx)
  rw [oneStepDirichletCellSlope_eq_cubeAverageVec
    M n h p (originCube d (K : ℤ)) R (mem_oneStepSourceCells hR) omega hh]
  simpa only [F, W, E, w, mul_assoc] using hbound

/-- Reciprocal Jensen replacement for the Neumann source-cell slope. -/
theorem oneStepLowerSourceCellWeight_mul_neumannCellSlope_le
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (q : Vec d) (R : TriadicCube d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    oneStepLowerSourceCellWeight M n h R omega *
        vecNormSq (oneStepNeumannCellSlope M n h q
          (originCube d (K : ℤ)) R omega hh) ≤
      cubeAverage R (fun x ↦
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq (oneStepNeumannSlopeField M n h q
            (originCube d (K : ℤ)) omega hh x)) +
      2 * oneStepLowerSourceCellWeight M n h R omega *
        oneStepSourceCellShellOscillationEnvelope n h R omega *
        cubeAverage R (fun x ↦
          vecNormSq (oneStepNeumannSlopeField M n h q
            (originCube d (K : ℤ)) omega hh x)) := by
  let F := oneStepNeumannSlopeField M n h q
    (originCube d (K : ℤ)) omega hh
  let W := oneStepLowerSourceCellWeight M n h R omega
  let E := oneStepSourceCellShellOscillationEnvelope n h R omega
  let w : Vec d → ℝ := fun x ↦
    Real.exp (-oneStepCenteredShellAt M n h x omega)
  have hscale : R.scale ≤ (n : ℤ) := by
    rw [oneStepSourceCells_scale_eq hK hR]
    exact_mod_cast Nat.sub_le n (oneStepLocalizationDepth M.delta)
  have hF : MemLp F 2 (normalizedCubeMeasure R) :=
    oneStepNeumannSlopeField_memLp_sourceCell M n h q R hR omega hh
  have hbound := weight_mul_vecNormSq_cubeAverageVec_le R W E w F
    (le_of_lt (cutoffRatioSup_pos M n (n + h)
      (Ch02.cubeDomain R) omega)) hF
    ((measurable_oneStepCenteredShellAt_space M n h omega).neg.exp
      |>.aestronglyMeasurable)
    (fun _ _ ↦ (Real.exp_pos _).le)
    (fun x hx ↦ by
      exact exp_neg_oneStepCenteredShellAt_le_lowerSourceCellWeight
        M n h R omega hh hx)
    (fun x hx ↦ by
      exact oneStepLowerSourceCellWeight_sub_exp_neg_le_two_mul_envelope
        M n h R omega hscale hh hx)
  rw [oneStepNeumannCellSlope_eq_cubeAverageVec
    M n h q (originCube d (K : ℤ)) R (mem_oneStepSourceCells hR) omega hh]
  simpa only [F, W, E, w, mul_assoc] using hbound

/-- The small primal Jensen replacement price on one source cell. -/
def oneStepDirichletSourceCellJensenError
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d) (R : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) : ℝ :=
  2 * oneStepUpperSourceCellWeight M n h R omega *
    oneStepSourceCellShellOscillationEnvelope n h R omega *
    cubeAverage R (fun x ↦
      vecNormSq (oneStepDirichletSlopeField M n h p
        (originCube d (K : ℤ)) omega hh x))

/-- Reciprocal source-cell Jensen replacement price. -/
def oneStepNeumannSourceCellJensenError
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (q : Vec d) (R : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) : ℝ :=
  2 * oneStepLowerSourceCellWeight M n h R omega *
    oneStepSourceCellShellOscillationEnvelope n h R omega *
    cubeAverage R (fun x ↦
      vecNormSq (oneStepNeumannSlopeField M n h q
        (originCube d (K : ℤ)) omega hh x))

/-- The normalized primal source-family weights are controlled by the
literal parent weighted slope plus the small Jensen errors. -/
theorem normalized_sum_oneStepDirichletSourceCellWeight_le_parent_add_jensenError
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          oneStepUpperSourceCellWeight M n h R omega *
            vecNormSq (oneStepDirichletCellSlope M n h p
              (originCube d (K : ℤ)) R omega hh) ≤
      cubeAverage (originCube d (K : ℤ)) (fun x ↦
        Real.exp (oneStepCenteredShellAt M n h x omega) *
          vecNormSq (oneStepDirichletSlopeField M n h p
            (originCube d (K : ℤ)) omega hh x)) +
      (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          oneStepDirichletSourceCellJensenError
            (K := K) M n h p R omega hh := by
  have hcells : ∀ R ∈ oneStepSourceCells d K n M.delta,
      oneStepUpperSourceCellWeight M n h R omega *
          vecNormSq (oneStepDirichletCellSlope M n h p
            (originCube d (K : ℤ)) R omega hh) ≤
        cubeAverage R (fun x ↦
          Real.exp (oneStepCenteredShellAt M n h x omega) *
            vecNormSq (oneStepDirichletSlopeField M n h p
              (originCube d (K : ℤ)) omega hh x)) +
        oneStepDirichletSourceCellJensenError
          (K := K) M n h p R omega hh := by
    intro R hR
    exact oneStepUpperSourceCellWeight_mul_dirichletCellSlope_le
      M n h p R hK hR omega hh
  have hsum := Finset.sum_le_sum hcells
  let c : ℝ := (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹)
  have hmul := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ c by dsimp only [c]; positivity)
  dsimp only [c] at hmul
  rw [Finset.sum_add_distrib, mul_add,
    normalized_sum_oneStepDirichletWeightedSlope_eq_parent
      M n h p omega hh] at hmul
  exact hmul

/-- Reciprocal normalized source-family Jensen comparison. -/
theorem normalized_sum_oneStepNeumannSourceCellWeight_le_parent_add_jensenError
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (q : Vec d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          oneStepLowerSourceCellWeight M n h R omega *
            vecNormSq (oneStepNeumannCellSlope M n h q
              (originCube d (K : ℤ)) R omega hh) ≤
      cubeAverage (originCube d (K : ℤ)) (fun x ↦
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq (oneStepNeumannSlopeField M n h q
            (originCube d (K : ℤ)) omega hh x)) +
      (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          oneStepNeumannSourceCellJensenError
            (K := K) M n h q R omega hh := by
  have hcells : ∀ R ∈ oneStepSourceCells d K n M.delta,
      oneStepLowerSourceCellWeight M n h R omega *
          vecNormSq (oneStepNeumannCellSlope M n h q
            (originCube d (K : ℤ)) R omega hh) ≤
        cubeAverage R (fun x ↦
          Real.exp (-oneStepCenteredShellAt M n h x omega) *
            vecNormSq (oneStepNeumannSlopeField M n h q
              (originCube d (K : ℤ)) omega hh x)) +
        oneStepNeumannSourceCellJensenError
          (K := K) M n h q R omega hh := by
    intro R hR
    exact oneStepLowerSourceCellWeight_mul_neumannCellSlope_le
      M n h q R hK hR omega hh
  have hsum := Finset.sum_le_sum hcells
  let c : ℝ := (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹)
  have hmul := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ c by dsimp only [c]; positivity)
  dsimp only [c] at hmul
  rw [Finset.sum_add_distrib, mul_add,
    normalized_sum_oneStepNeumannWeightedSlope_eq_parent
      M n h q omega hh] at hmul
  exact hmul

/-! ## Measurable literal cell energies -/

private theorem oneStepWindowL2Norm_sq_eq_indicator_integral
    {d : ℕ} {U S : Set (Vec d)} (hS : MeasurableSet S)
    (f : HilbertVectorL2 U) :
    oneStepWindowL2Norm U S f ^ 2 =
      ∫ x, ‖S.indicator (fun y => f y) x‖ ^ 2 ∂volumeMeasureOn U := by
  have hf : MemLp (S.indicator fun x => f x) 2 (volumeMeasureOn U) :=
    (Lp.memLp f).indicator hS
  unfold oneStepWindowL2Norm
  rw [← eLpNorm_norm _ hf.aestronglyMeasurable]
  exact Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq hf.norm

/-- A continuous Hilbert-window energy agrees with the literal vector-field
set integral whenever the Hilbert class is represented by that field. -/
theorem oneStepWindowL2Norm_sq_toHilbertVectorL2OfVecField
    {d : ℕ} {U S : Set (Vec d)} (hS : MeasurableSet S)
    (hSU : S ⊆ U) {F : Vec d → Vec d} (hF : MemVectorL2 U F) :
    oneStepWindowL2Norm U S (toHilbertVectorL2OfVecField hF) ^ 2 =
      ∫ x in S, vecNormSq (F x) := by
  rw [oneStepWindowL2Norm_sq_eq_indicator_integral hS]
  have hind : (fun x =>
      ‖S.indicator (fun y => (toHilbertVectorL2OfVecField hF :
        HilbertVectorL2 U) y) x‖ ^ 2) =
      S.indicator (fun x => ‖(toHilbertVectorL2OfVecField hF :
        HilbertVectorL2 U) x‖ ^ 2) := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  rw [hind, integral_indicator hS]
  rw [Measure.restrict_restrict_of_subset hSU]
  apply integral_congr_ae
  have hle : volumeMeasureOn S ≤ volumeMeasureOn U :=
    Measure.restrict_mono_set volume hSU
  filter_upwards
    [ae_mono hle (coeFn_toHilbertVectorL2OfVecField hF)] with x hx
  rw [hx]
  exact HilbertVec.norm_sq_ofVec (F x)

/-- The literal normalized energy on a descendant is the squared continuous
window norm of its ambient Hilbert representative. -/
theorem cubeAverage_vecNormSq_eq_oneStepWindowL2Norm_sq
    {d j : ℕ} {Q R : TriadicCube d}
    (hRQ : R ∈ descendantsAtDepth Q j) {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) :
    cubeAverage R (fun x => vecNormSq (F x)) =
      (cubeVolume R)⁻¹ *
        oneStepWindowL2Norm (openCubeSet Q) (openCubeSet R)
          (toHilbertVectorL2OfVecField hF) ^ 2 := by
  rw [oneStepWindowL2Norm_sq_toHilbertVectorL2OfVecField
    (measurableSet_openCubeSet R)
    (openCubeSet_subset_of_mem_descendantsAtDepth hRQ) hF]
  unfold cubeAverage
  rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet]

/-- The normalized square of the local quadratic energies on a descendant
partition is bounded by the parent normalized fourth power.  This is the
spatial Jensen step used before integrating the source-cell family in the
random parameter. -/
theorem normalized_sum_descendant_cubeAverage_vecNormSq_sq_le_parent
    {d j : ℕ} (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : MemLp (hilbertifyVecField F) 4 (normalizedCubeMeasure Q)) :
    (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
        ∑ R ∈ descendantsAtDepth Q j,
          cubeAverage R (fun x => vecNormSq (F x)) ^ 2 ≤
      cubeAverage Q (fun x => vecNormSq (F x) ^ 2) := by
  let : ENNReal.HolderTriple (4 : ℝ≥0∞) (4 : ℝ≥0∞) (2 : ℝ≥0∞) := ⟨by
    rw [← two_mul]
    have h4 : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
    rw [h4, ENNReal.mul_inv (Or.inl (by norm_num))
      (Or.inl (by norm_num))]
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num)
      (by norm_num), one_mul]⟩
  let G : Vec d → HilbertVec d := hilbertifyVecField F
  let e : Vec d → ℝ := fun x => vecNormSq (F x)
  have heq : ∀ x, e x = ‖G x‖ ^ 2 := by
    intro x
    exact (HilbertVec.norm_sq_ofVec (F x)).symm
  have hcell : ∀ R ∈ descendantsAtDepth Q j,
      cubeAverage R e ^ 2 ≤ cubeAverage R (fun x => e x ^ 2) := by
    intro R hR
    have hFR : MemLp G 4 (normalizedCubeMeasure R) :=
      memLp_on_descendant_of_memLp_generic hR hF
    have heR : MemLp e 2 (normalizedCubeMeasure R) := by
      have hmul : MemLp (fun x => ‖G x‖ * ‖G x‖) 2
          (normalizedCubeMeasure R) := hFR.norm.mul hFR.norm
      convert hmul using 1
      funext x
      rw [heq x]
      ring
    exact sq_cubeAverage_le_cubeAverage_sq_of_memLp R e heR
  have heSqInt : Integrable (fun x => e x ^ 2)
      (normalizedCubeMeasure Q) := by
    have he2 : MemLp e 2 (normalizedCubeMeasure Q) := by
      have hmul : MemLp (fun x =>
          ‖hilbertifyVecField F x‖ * ‖hilbertifyVecField F x‖) 2
          (normalizedCubeMeasure Q) := hF.norm.mul hF.norm
      convert hmul using 1
      funext x
      rw [heq x]
      ring
    exact (memLp_two_iff_integrable_sq he2.aestronglyMeasurable).mp he2
  have hcollapse := cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
    Q j (fun x => e x ^ 2)
      (integrableOn_of_integrable_normalizedCubeMeasure Q heSqInt)
  calc
    (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
        ∑ R ∈ descendantsAtDepth Q j, cubeAverage R e ^ 2 ≤
      (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
        ∑ R ∈ descendantsAtDepth Q j,
          cubeAverage R (fun x => e x ^ 2) := by
      gcongr with R hR
      exact hcell R hR
    _ = cubeAverage Q (fun x => e x ^ 2) := hcollapse.symm
    _ = cubeAverage Q (fun x => vecNormSq (F x) ^ 2) := rfl

/-- Measurability of the literal primal source-cell energy, obtained by
composing the measurable solution operator with the continuous window norm. -/
theorem measurable_oneStepDirichletSourceCellEnergy
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d) (R : TriadicCube d)
    (hR : R ∈ oneStepSourceCells d K n M.delta) (hh : 0 < h) :
    Measurable fun omega => cubeAverage R (fun x =>
      vecNormSq (oneStepDirichletSlopeField M n h p
        (originCube d (K : ℤ)) omega hh x)) := by
  let Q := originCube d (K : ℤ)
  have hSlope : Measurable
      (oneStepDirichletSlopeL2 M n h p Q · hh) :=
    (measurable_oneStepDirichletSlopeL2_potentialShellIndexSigma_Ioi
      M n h p Q hh).mono
        (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi n)) le_rfl
  have hwindow : Measurable fun omega =>
      oneStepWindowL2Norm (openCubeSet Q) (openCubeSet R)
        (oneStepDirichletSlopeL2 M n h p Q omega hh) :=
    (continuous_oneStepWindowL2Norm _ _ (measurableSet_openCubeSet R))
      |>.measurable.comp hSlope
  have heq : (fun omega => cubeAverage R (fun x =>
      vecNormSq (oneStepDirichletSlopeField M n h p Q omega hh x))) =
      fun omega => (cubeVolume R)⁻¹ *
        oneStepWindowL2Norm (openCubeSet Q) (openCubeSet R)
          (oneStepDirichletSlopeL2 M n h p Q omega hh) ^ 2 := by
    funext omega
    rw [oneStepDirichletSlopeL2_eq_toHilbertVectorL2OfVecField]
    exact cubeAverage_vecNormSq_eq_oneStepWindowL2Norm_sq
      (mem_oneStepSourceCells hR)
        (oneStepDirichletSlopeField_memVectorL2 M n h p Q omega hh)
  rw [heq]
  exact measurable_const.mul (hwindow.pow_const 2)

/-- Reciprocal measurable source-cell energy. -/
theorem measurable_oneStepNeumannSourceCellEnergy
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (q : Vec d) (R : TriadicCube d)
    (hR : R ∈ oneStepSourceCells d K n M.delta) (hh : 0 < h) :
    Measurable fun omega => cubeAverage R (fun x =>
      vecNormSq (oneStepNeumannSlopeField M n h q
        (originCube d (K : ℤ)) omega hh x)) := by
  let Q := originCube d (K : ℤ)
  have hSlope : Measurable
      (oneStepNeumannSlopeL2 M n h q Q · hh) :=
    (measurable_oneStepNeumannSlopeL2_potentialShellIndexSigma_Ioi
      M n h q Q hh).mono
        (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi n)) le_rfl
  have hwindow : Measurable fun omega =>
      oneStepWindowL2Norm (openCubeSet Q) (openCubeSet R)
        (oneStepNeumannSlopeL2 M n h q Q omega hh) :=
    (continuous_oneStepWindowL2Norm _ _ (measurableSet_openCubeSet R))
      |>.measurable.comp hSlope
  have heq : (fun omega => cubeAverage R (fun x =>
      vecNormSq (oneStepNeumannSlopeField M n h q Q omega hh x))) =
      fun omega => (cubeVolume R)⁻¹ *
        oneStepWindowL2Norm (openCubeSet Q) (openCubeSet R)
          (oneStepNeumannSlopeL2 M n h q Q omega hh) ^ 2 := by
    funext omega
    rw [oneStepNeumannSlopeL2_eq_toHilbertVectorL2OfVecField]
    exact cubeAverage_vecNormSq_eq_oneStepWindowL2Norm_sq
      (mem_oneStepSourceCells hR)
        (oneStepNeumannSlopeField_memVectorL2 M n h q Q omega hh)
  rw [heq]
  exact measurable_const.mul (hwindow.pow_const 2)

/-! ## Probability-space moment fold for the Jensen error -/

/-- Hölder in the exact `L⁴ × L⁴ × L²` setting used by the source-cell Jensen
error.  The probability-space assumption also supplies the usual exponent
downgrades used below. -/
theorem integral_three_nonnegative_le_eLpNorm_four_four_two
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    (W E A : Omega → ℝ)
    (hW0 : ∀ omega, 0 ≤ W omega)
    (hE0 : ∀ omega, 0 ≤ E omega)
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hW : MemLp W 4 mu) (hE : MemLp E 4 mu) (hA : MemLp A 2 mu) :
    Integrable (fun omega ↦ W omega * E omega * A omega) mu ∧
      ∫ omega, W omega * E omega * A omega ∂mu ≤
        (eLpNorm W 4 mu * eLpNorm E 4 mu * eLpNorm A 2 mu).toReal := by
  let : ENNReal.HolderTriple (4 : ℝ≥0∞) (4 : ℝ≥0∞) (2 : ℝ≥0∞) := ⟨by
    rw [← two_mul]
    have h4 : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
    rw [h4, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩
  let : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) (1 : ℝ≥0∞) := ⟨by
    rw [inv_one, ← two_mul,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]⟩
  let WE : Omega → ℝ := fun omega ↦ W omega * E omega
  let P : Omega → ℝ := fun omega ↦ WE omega * A omega
  have hWE : MemLp WE 2 mu := by
    exact hW.mul (r := 2) hE
  have hP : MemLp P 1 mu := by
    exact hWE.mul (r := 1) hA
  have hWEnorm : eLpNorm WE 2 mu ≤
      eLpNorm W 4 mu * eLpNorm E 4 mu := by
    simpa only [ENNReal.coe_one, one_mul] using
      eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (p := (4 : ℝ≥0∞)) (q := (4 : ℝ≥0∞)) (r := (2 : ℝ≥0∞))
      (fun a b : ℝ ↦ a * b) 1 (by fun_prop) hW.aestronglyMeasurable hE.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ ↦ by simp)
  have hPnorm : eLpNorm P 1 mu ≤ eLpNorm WE 2 mu * eLpNorm A 2 mu := by
    simpa only [ENNReal.coe_one, one_mul] using
      eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
      (fun a b : ℝ ↦ a * b) 1 (by fun_prop) hWE.aestronglyMeasurable hA.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ ↦ by simp)
  have hP0 : ∀ omega, 0 ≤ P omega := fun omega ↦
    mul_nonneg (mul_nonneg (hW0 omega) (hE0 omega)) (hA0 omega)
  refine ⟨by
    simpa only [P, WE] using hP.integrable (by norm_num), ?_⟩
  have heq : ∫ omega, P omega ∂mu = (eLpNorm P 1 mu).toReal := by
    rw [hP.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top]
    norm_num only [ENNReal.toReal_one, inv_one, Real.rpow_one,
      ENNReal.toReal_ofReal]
    rw [ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _)]
    exact integral_congr_ae <| Filter.Eventually.of_forall fun omega ↦ by
      change P omega = |P omega|
      rw [abs_of_nonneg (hP0 omega)]
  rw [show (fun omega ↦ W omega * E omega * A omega) = P by rfl, heq]
  apply ENNReal.toReal_mono
  · exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hW.eLpNorm_ne_top hE.eLpNorm_ne_top)
      hA.eLpNorm_ne_top
  · exact hPnorm.trans <| by
      gcongr

/-- Finite-family version of the `L⁴ × L⁴ × L²` fold.  Uniform fourth
norms for the weight and shell envelope combine with an averaged square of
the cell-energy `L²` norms.  This is the probability-space algebra needed
after the source-cell localization estimates have supplied the last budget. -/
theorem normalized_finset_integral_two_mul_three_le
    {iota Omega : Type*} [DecidableEq iota] [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (s : Finset iota) (hs : s.Nonempty)
    (W E A : iota → Omega → ℝ)
    (hW0 : ∀ i ∈ s, ∀ omega, 0 ≤ W i omega)
    (hE0 : ∀ i ∈ s, ∀ omega, 0 ≤ E i omega)
    (hA0 : ∀ i ∈ s, ∀ omega, 0 ≤ A i omega)
    (hW : ∀ i ∈ s, MemLp (W i) 4 mu)
    (hE : ∀ i ∈ s, MemLp (E i) 4 mu)
    (hA : ∀ i ∈ s, MemLp (A i) 2 mu)
    {w e a : ℝ} (hw0 : 0 ≤ w) (he0 : 0 ≤ e) (ha0 : 0 ≤ a)
    (hWnorm : ∀ i ∈ s, (eLpNorm (W i) 4 mu).toReal ≤ w)
    (hEnorm : ∀ i ∈ s, (eLpNorm (E i) 4 mu).toReal ≤ e)
    (hAsq : (((s.card : ℝ)⁻¹) * ∑ i ∈ s,
      ∫ omega, A i omega ^ 2 ∂mu ≤ a ^ 2)) :
    (((s.card : ℝ)⁻¹) * ∑ i ∈ s,
        ∫ omega, 2 * W i omega * E i omega * A i omega ∂mu ≤
      2 * w * e * a) := by
  let N : iota → ℝ := fun i ↦ (eLpNorm (A i) 2 mu).toReal
  have hcell : ∀ i ∈ s,
      ∫ omega, 2 * W i omega * E i omega * A i omega ∂mu ≤
        2 * w * e * N i := by
    intro i hi
    have hraw := (integral_three_nonnegative_le_eLpNorm_four_four_two
      (W i) (E i) (A i) (hW0 i hi) (hE0 i hi) (hA0 i hi)
        (hW i hi) (hE i hi) (hA i hi)).2
    have hraw' : ∫ omega, W i omega * E i omega * A i omega ∂mu ≤
        (eLpNorm (W i) 4 mu).toReal *
          (eLpNorm (E i) 4 mu).toReal * N i := by
      simpa only [ENNReal.toReal_mul, N] using hraw
    rw [show (fun omega ↦ 2 * W i omega * E i omega * A i omega) =
        fun omega ↦ 2 * (W i omega * E i omega * A i omega) by
      funext omega; ring,
      integral_const_mul]
    calc
      2 * ∫ omega, W i omega * E i omega * A i omega ∂mu ≤
          2 * ((eLpNorm (W i) 4 mu).toReal *
            (eLpNorm (E i) 4 mu).toReal * N i) := by gcongr
      _ ≤ 2 * (w * e * N i) := by
        gcongr
        · exact hWnorm i hi
        · exact hEnorm i hi
      _ = 2 * w * e * N i := by ring
  have hnormSq : ((s.card : ℝ)⁻¹) * ∑ i ∈ s, N i ^ 2 ≤ a ^ 2 := by
    calc
      ((s.card : ℝ)⁻¹) * ∑ i ∈ s, N i ^ 2 =
          ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
            ∫ omega, A i omega ^ 2 ∂mu := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        exact Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq (hA i hi)
      _ ≤ a ^ 2 := hAsq
  have havgN : ((s.card : ℝ)⁻¹) * ∑ i ∈ s, N i ≤ a := by
    have hcs := normalized_finset_sum_mul_le_sqrt_mul_sqrt s hs
      (fun _ ↦ (1 : ℝ)) N
    have hones : ((s.card : ℝ)⁻¹) * ∑ _i ∈ s, (1 : ℝ) ^ 2 = 1 := by
      simp [hs.card_ne_zero]
    have hsqrtA : Real.sqrt ((((s.card : ℝ)⁻¹) * ∑ i ∈ s,
        N i ^ 2)) ≤ a := by
      rw [← Real.sqrt_sq ha0]
      exact Real.sqrt_le_sqrt hnormSq
    calc
      ((s.card : ℝ)⁻¹) * ∑ i ∈ s, N i =
          ((s.card : ℝ)⁻¹) * ∑ i ∈ s, (1 : ℝ) * N i := by
        simp
      _ ≤ Real.sqrt (((s.card : ℝ)⁻¹) *
            ∑ _i ∈ s, (1 : ℝ) ^ 2) *
          Real.sqrt (((s.card : ℝ)⁻¹) * ∑ i ∈ s, N i ^ 2) := hcs
      _ = Real.sqrt (((s.card : ℝ)⁻¹) * ∑ i ∈ s, N i ^ 2) := by
        rw [hones, Real.sqrt_one, one_mul]
      _ ≤ a := hsqrtA
  calc
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
        ∫ omega, 2 * W i omega * E i omega * A i omega ∂mu ≤
      ((s.card : ℝ)⁻¹) * ∑ i ∈ s, 2 * w * e * N i := by
        gcongr with i hi
        exact hcell i hi
    _ = 2 * w * e * (((s.card : ℝ)⁻¹) * ∑ i ∈ s, N i) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ 2 * w * e * a := by
      exact mul_le_mul_of_nonneg_left havgN
        (mul_nonneg (mul_nonneg (by norm_num) hw0) he0)

/-! ## Concrete source-cell fourth-norm inputs -/

/-- The forward source-cell cutoff supremum belongs to the fourth moment
argument in the one-step range. -/
theorem memLp_four_oneStepUpperSourceCellWeight_of_block
    {d K : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta) (hh : 0 < h)
    (hblock : (h : ℝ) ≤ M.delta⁻¹) :
    MemLp (oneStepUpperSourceCellWeight M n h R) 4 M.P.toMeasure := by
  have hmeas : Measurable (oneStepUpperSourceCellWeight M n h R) :=
    (measurable_oneStepUpperSourceCellWeight_potentialShellIndexSigma_Ioi
      M n h R hh).mono
        (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi n)) le_rfl
  have hnorm :=
    (eLpNorm_oneStepSourceCellWeights_four_le
      M n h R hK hR hh hblock).1
  exact lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top

/-- Reciprocal source-cell cutoff supremum in `L⁴`. -/
theorem memLp_four_oneStepLowerSourceCellWeight_of_block
    {d K : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta) (hh : 0 < h)
    (hblock : (h : ℝ) ≤ M.delta⁻¹) :
    MemLp (oneStepLowerSourceCellWeight M n h R) 4 M.P.toMeasure := by
  have hmeas : Measurable (oneStepLowerSourceCellWeight M n h R) :=
    (measurable_oneStepLowerSourceCellWeight_potentialShellIndexSigma_Ioi
      M n h R hh).mono
        (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi n)) le_rfl
  have hnorm :=
    (eLpNorm_oneStepSourceCellWeights_four_le
      M n h R hK hR hh hblock).2
  exact lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top

/-- The source-cell oscillation envelope belongs to `L⁴`; the proof spends
only half of the already proved eighth-moment exponent. -/
theorem memLp_four_oneStepSourceCellShellOscillationEnvelope
    {d K : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d)
    (hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta) (hh : 0 < h) :
    MemLp (oneStepSourceCellShellOscillationEnvelope n h R)
      4 M.P.toMeasure := by
  have hmeas := measurable_oneStepSourceCellShellOscillationEnvelope n h R
  have hnorm := eLpNorm_oneStepSourceCellShellOscillationEnvelope_eight_le
    M n h K R hsource hK hR hh
  have hmemEight : MemLp
      (oneStepSourceCellShellOscillationEnvelope n h R)
      8 M.P.toMeasure :=
    lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top
  exact hmemEight.mono_exponent (by norm_num)

/-- Real fourth-norm bound for either orientation of the source-cell cutoff
supremum. -/
theorem toReal_eLpNorm_oneStepSourceCellWeights_four_le
    {d K : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta) (hh : 0 < h)
    (hblock : (h : ℝ) ≤ M.delta⁻¹) :
    (eLpNorm (oneStepUpperSourceCellWeight M n h R)
        4 M.P.toMeasure).toReal ≤ oneStepSourceCellWeightFourthRootConst d + 1 ∧
      (eLpNorm (oneStepLowerSourceCellWeight M n h R)
        4 M.P.toMeasure).toReal ≤ oneStepSourceCellWeightFourthRootConst d + 1 := by
  have h := eLpNorm_oneStepSourceCellWeights_four_le
    M n h R hK hR hh hblock
  have hc0 : 0 ≤ oneStepSourceCellWeightFourthRootConst d + 1 :=
    add_nonneg (oneStepSourceCellWeightFourthRootConst_pos M).le zero_le_one
  constructor
  · simpa only [ENNReal.toReal_ofReal hc0]
      using ENNReal.toReal_mono ENNReal.ofReal_ne_top h.1
  · simpa only [ENNReal.toReal_ofReal hc0]
      using ENNReal.toReal_mono ENNReal.ofReal_ne_top h.2

/-- Real fourth-norm form of the `delta^17` source-cell oscillation gain. -/
theorem toReal_eLpNorm_oneStepSourceCellShellOscillationEnvelope_four_le
    {d K : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d)
    (hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta) (hh : 0 < h) :
    (eLpNorm (oneStepSourceCellShellOscillationEnvelope n h R)
        4 M.P.toMeasure).toReal ≤
      oneStepDerivativeGaugeConst * M.delta ^ (17 : ℕ) := by
  have hmemEight : MemLp
      (oneStepSourceCellShellOscillationEnvelope n h R)
      8 M.P.toMeasure := by
    have hmeas := measurable_oneStepSourceCellShellOscillationEnvelope n h R
    have hnorm := eLpNorm_oneStepSourceCellShellOscillationEnvelope_eight_le
      M n h K R hsource hK hR hh
    exact lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top
  have hdown : eLpNorm (oneStepSourceCellShellOscillationEnvelope n h R)
      4 M.P.toMeasure ≤
      eLpNorm (oneStepSourceCellShellOscillationEnvelope n h R)
        8 M.P.toMeasure := by
    simpa using eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (f := oneStepSourceCellShellOscillationEnvelope n h R)
      (μ := M.P.toMeasure) (by norm_num : (4 : ℝ≥0∞) ≤ 8) hmemEight.aestronglyMeasurable
  have hnorm := hdown.trans
    (eLpNorm_oneStepSourceCellShellOscillationEnvelope_eight_le
      M n h K R hsource hK hR hh)
  have hnonneg : 0 ≤ oneStepDerivativeGaugeConst * M.delta ^ (17 : ℕ) :=
    mul_nonneg oneStepDerivativeGaugeConst_pos.le
      (pow_nonneg M.shellPrefix.delta_pos.le 17)
  simpa only [ENNReal.toReal_ofReal hnonneg] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm

/-! ## Literal Jensen-error folds -/

/-- The primal source-cell Jensen prices have the exact `delta^17` gain once
the normalized local slope energies have an averaged `L²(Omega)` budget. -/
theorem normalized_sum_integral_oneStepDirichletSourceCellJensenError_le
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d)
    (hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hh : 0 < h) (hblock : (h : ℝ) ≤ M.delta⁻¹)
    {a : ℝ} (ha0 : 0 ≤ a)
    (hA : ∀ R ∈ oneStepSourceCells d K n M.delta,
      MemLp (fun omega ↦ cubeAverage R (fun x ↦
        vecNormSq (oneStepDirichletSlopeField M n h p
          (originCube d (K : ℤ)) omega hh x))) 2 M.P.toMeasure)
    (hAsq :
      ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, (cubeAverage R (fun x ↦
            vecNormSq (oneStepDirichletSlopeField M n h p
              (originCube d (K : ℤ)) omega hh x))) ^ 2
            ∂M.P.toMeasure ≤ a ^ 2)) :
    ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, oneStepDirichletSourceCellJensenError
            (K := K) M n h p R omega hh ∂M.P.toMeasure) ≤
      2 * (oneStepSourceCellWeightFourthRootConst d + 1) *
        (oneStepDerivativeGaugeConst * M.delta ^ (17 : ℕ)) * a := by
  let s := oneStepSourceCells d K n M.delta
  let W : TriadicCube d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun R ↦
    oneStepUpperSourceCellWeight M n h R
  let E : TriadicCube d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun R ↦
    oneStepSourceCellShellOscillationEnvelope n h R
  let A : TriadicCube d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun R omega ↦
    cubeAverage R (fun x ↦ vecNormSq (oneStepDirichletSlopeField
      M n h p (originCube d (K : ℤ)) omega hh x))
  have hraw := normalized_finset_integral_two_mul_three_le
    s (oneStepSourceCells_nonempty d K n M.delta) W E A
    (fun R hR omega ↦ (cutoffRatioSup_pos M (n + h) n
      (Ch02.cubeDomain R) omega).le)
    (fun R hR omega ↦
      oneStepSourceCellShellOscillationEnvelope_nonneg n h R omega)
    (fun R hR omega ↦ cubeAverage_nonneg_of_nonneg_on
      (fun x hx ↦ vecNormSq_nonneg _))
    (fun R hR ↦ memLp_four_oneStepUpperSourceCellWeight_of_block
      M n h R hK hR hh hblock)
    (fun R hR ↦ memLp_four_oneStepSourceCellShellOscillationEnvelope
      M n h R hsource hK hR hh)
    (fun R hR ↦ hA R hR)
    (add_nonneg (oneStepSourceCellWeightFourthRootConst_pos M).le zero_le_one)
    (mul_nonneg oneStepDerivativeGaugeConst_pos.le
      (pow_nonneg M.shellPrefix.delta_pos.le 17)) ha0
    (fun R hR ↦
      (toReal_eLpNorm_oneStepSourceCellWeights_four_le
        M n h R hK hR hh hblock).1)
    (fun R hR ↦
      toReal_eLpNorm_oneStepSourceCellShellOscillationEnvelope_four_le
        M n h R hsource hK hR hh)
    hAsq
  simpa only [s, W, E, A, oneStepDirichletSourceCellJensenError] using hraw

/-- Reciprocal source-cell Jensen fold with the same localization gain. -/
theorem normalized_sum_integral_oneStepNeumannSourceCellJensenError_le
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (q : Vec d)
    (hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hh : 0 < h) (hblock : (h : ℝ) ≤ M.delta⁻¹)
    {a : ℝ} (ha0 : 0 ≤ a)
    (hA : ∀ R ∈ oneStepSourceCells d K n M.delta,
      MemLp (fun omega ↦ cubeAverage R (fun x ↦
        vecNormSq (oneStepNeumannSlopeField M n h q
          (originCube d (K : ℤ)) omega hh x))) 2 M.P.toMeasure)
    (hAsq :
      ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, (cubeAverage R (fun x ↦
            vecNormSq (oneStepNeumannSlopeField M n h q
              (originCube d (K : ℤ)) omega hh x))) ^ 2
            ∂M.P.toMeasure ≤ a ^ 2)) :
    ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, oneStepNeumannSourceCellJensenError
            (K := K) M n h q R omega hh ∂M.P.toMeasure) ≤
      2 * (oneStepSourceCellWeightFourthRootConst d + 1) *
        (oneStepDerivativeGaugeConst * M.delta ^ (17 : ℕ)) * a := by
  let s := oneStepSourceCells d K n M.delta
  let W : TriadicCube d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun R ↦
    oneStepLowerSourceCellWeight M n h R
  let E : TriadicCube d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun R ↦
    oneStepSourceCellShellOscillationEnvelope n h R
  let A : TriadicCube d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun R omega ↦
    cubeAverage R (fun x ↦ vecNormSq (oneStepNeumannSlopeField
      M n h q (originCube d (K : ℤ)) omega hh x))
  have hraw := normalized_finset_integral_two_mul_three_le
    s (oneStepSourceCells_nonempty d K n M.delta) W E A
    (fun R hR omega ↦ (cutoffRatioSup_pos M n (n + h)
      (Ch02.cubeDomain R) omega).le)
    (fun R hR omega ↦
      oneStepSourceCellShellOscillationEnvelope_nonneg n h R omega)
    (fun R hR omega ↦ cubeAverage_nonneg_of_nonneg_on
      (fun x hx ↦ vecNormSq_nonneg _))
    (fun R hR ↦ memLp_four_oneStepLowerSourceCellWeight_of_block
      M n h R hK hR hh hblock)
    (fun R hR ↦ memLp_four_oneStepSourceCellShellOscillationEnvelope
      M n h R hsource hK hR hh)
    (fun R hR ↦ hA R hR)
    (add_nonneg (oneStepSourceCellWeightFourthRootConst_pos M).le zero_le_one)
    (mul_nonneg oneStepDerivativeGaugeConst_pos.le
      (pow_nonneg M.shellPrefix.delta_pos.le 17)) ha0
    (fun R hR ↦
      (toReal_eLpNorm_oneStepSourceCellWeights_four_le
        M n h R hK hR hh hblock).2)
    (fun R hR ↦
      toReal_eLpNorm_oneStepSourceCellShellOscillationEnvelope_four_le
        M n h R hsource hK hR hh)
    hAsq
  simpa only [s, W, E, A, oneStepNeumannSourceCellJensenError] using hraw

/-- Normalized spatial Cauchy--Schwarz in the exact square-energy language
of the source-cell replacement envelope. -/
theorem cubeAverage_sqrt_vecNormSq_mul_le
    {d : ℕ} (Q : TriadicCube d) (F G : Vec d → Vec d)
    (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hG : MemLp G 2 (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x ↦
        Real.sqrt (vecNormSq (F x)) * Real.sqrt (vecNormSq (G x))) ≤
      Real.sqrt (cubeAverage Q (fun x ↦ vecNormSq (F x))) *
        Real.sqrt (cubeAverage Q (fun x ↦ vecNormSq (G x))) := by
  let f : Vec d → ℝ := fun x ↦ Real.sqrt (vecNormSq (F x))
  let g : Vec d → ℝ := fun x ↦ Real.sqrt (vecNormSq (G x))
  have hf := memLp_sqrt_vecNormSq_of_memLp_two hF
  have hg := memLp_sqrt_vecNormSq_of_memLp_two hG
  have hfg : Integrable (fun x ↦ f x * g x)
      (normalizedCubeMeasure Q) := by
    exact hf.integrable_mul hg
  have hbound :=
    abs_cubeAverage_le_sqrt_cubeAverage_mul_sqrt_cubeAverage_of_ae_abs_le_sqrt_mul_sqrt
      Q hfg
      (Filter.Eventually.of_forall fun x ↦ vecNormSq_nonneg (F x))
      (Filter.Eventually.of_forall fun x ↦ vecNormSq_nonneg (G x))
      hf hg (Filter.Eventually.of_forall fun x ↦ by
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (Real.sqrt_nonneg _)])
  have hnonneg : 0 ≤ cubeAverage Q (fun x ↦ f x * g x) :=
    cubeAverage_nonneg_of_nonneg_on fun x _hx ↦
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [abs_of_nonneg hnonneg] at hbound
  simpa only [f, g] using hbound

/-- Pull the two cellwise constants out of the normalized average and apply
the preceding spatial Cauchy--Schwarz estimate to the only nonconstant term. -/
theorem cubeAverage_const_mul_add_sqrt_vecNormSq_le
    {d : ℕ} (Q : TriadicCube d) (W A : ℝ) (F G : Vec d → Vec d)
    (hW : 0 ≤ W)
    (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hG : MemLp G 2 (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x ↦ W *
        (A + Real.sqrt (vecNormSq (F x)) *
          Real.sqrt (vecNormSq (G x)))) ≤
      W * (A +
        Real.sqrt (cubeAverage Q (fun x ↦ vecNormSq (F x))) *
          Real.sqrt (cubeAverage Q (fun x ↦ vecNormSq (G x)))) := by
  let f : Vec d → ℝ := fun x ↦
    Real.sqrt (vecNormSq (F x)) * Real.sqrt (vecNormSq (G x))
  have hf : Integrable f (normalizedCubeMeasure Q) := by
    exact (memLp_sqrt_vecNormSq_of_memLp_two hF).integrable_mul
      (memLp_sqrt_vecNormSq_of_memLp_two hG)
  have hsplit : cubeAverage Q (fun x ↦ W * (A + f x)) =
      W * (A + cubeAverage Q f) := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure]
    have hconst : Integrable (fun _ : Vec d ↦ A)
        (normalizedCubeMeasure Q) := integrable_const A
    rw [integral_const_mul, integral_add hconst hf, integral_const]
    simp only [Measure.real, normalizedCubeMeasure_apply_univ,
      ENNReal.toReal_one, one_smul]
  rw [hsplit]
  apply mul_le_mul_of_nonneg_left _ hW
  exact add_le_add le_rfl (cubeAverage_sqrt_vecNormSq_mul_le Q F G hF hG)

/-- Deterministic normalized-energy bound for the primal literal replacement
error.  The remaining random quantities are precisely the weight, shell
oscillation, source-cell slope, and centered source-cell fluctuation whose
fourth moments are provided by the source-scale modules. -/
theorem oneStepDirichletSourceCellReplacementError_le
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d) (R : TriadicCube d)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    oneStepDirichletSourceCellReplacementError
        (K := K) M n h p R omega hh ≤
      oneStepUpperSourceCellWeight M n h R omega *
        (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
            vecNormSq (oneStepDirichletCellSlope M n h p
              (originCube d (K : ℤ)) R omega hh) +
          Real.sqrt (cubeAverage R (fun x ↦ vecNormSq
            (cubeFluctuationVec R
              (oneStepDirichletSlopeField M n h p
                (originCube d (K : ℤ)) omega hh) x))) *
          Real.sqrt (cubeAverage R (fun x ↦ vecNormSq
            (oneStepDirichletCellSlope M n h p
                (originCube d (K : ℤ)) R omega hh +
              oneStepDirichletSlopeField M n h p
                (originCube d (K : ℤ)) omega hh x)))) := by
  let F : Vec d → Vec d := cubeFluctuationVec R
    (oneStepDirichletSlopeField M n h p
      (originCube d (K : ℤ)) omega hh)
  let G : Vec d → Vec d := fun x ↦
    oneStepDirichletCellSlope M n h p
        (originCube d (K : ℤ)) R omega hh +
      oneStepDirichletSlopeField M n h p
        (originCube d (K : ℤ)) omega hh x
  have hF : MemLp F 2 (normalizedCubeMeasure R) :=
    cubeFluctuationVec_oneStepDirichletSlopeField_memLp_sourceCell
      M n h p R hR omega hh
  have hSlope := oneStepDirichletSlopeField_memLp_sourceCell
    M n h p R hR omega hh
  have hG : MemLp G 2 (normalizedCubeMeasure R) := by
    exact (memLp_const
      (oneStepDirichletCellSlope M n h p
        (originCube d (K : ℤ)) R omega hh)).add hSlope
  unfold oneStepDirichletSourceCellReplacementError
  simpa only [F, G] using
    cubeAverage_const_mul_add_sqrt_vecNormSq_le R
      (oneStepUpperSourceCellWeight M n h R omega)
      (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
        vecNormSq (oneStepDirichletCellSlope M n h p
          (originCube d (K : ℤ)) R omega hh)) F G
      (le_of_lt (by
        unfold oneStepUpperSourceCellWeight
        exact cutoffRatioSup_pos M (n + h) n (Ch02.cubeDomain R) omega))
      hF hG

/-- Reciprocal copy of the deterministic normalized-energy replacement
bound. -/
theorem oneStepNeumannSourceCellReplacementError_le
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (q : Vec d) (R : TriadicCube d)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    oneStepNeumannSourceCellReplacementError
        (K := K) M n h q R omega hh ≤
      oneStepLowerSourceCellWeight M n h R omega *
        (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
            vecNormSq (oneStepNeumannCellSlope M n h q
              (originCube d (K : ℤ)) R omega hh) +
          Real.sqrt (cubeAverage R (fun x ↦ vecNormSq
            (cubeFluctuationVec R
              (oneStepNeumannSlopeField M n h q
                (originCube d (K : ℤ)) omega hh) x))) *
          Real.sqrt (cubeAverage R (fun x ↦ vecNormSq
            (oneStepNeumannCellSlope M n h q
                (originCube d (K : ℤ)) R omega hh +
              oneStepNeumannSlopeField M n h q
                (originCube d (K : ℤ)) omega hh x)))) := by
  let F : Vec d → Vec d := cubeFluctuationVec R
    (oneStepNeumannSlopeField M n h q
      (originCube d (K : ℤ)) omega hh)
  let G : Vec d → Vec d := fun x ↦
    oneStepNeumannCellSlope M n h q
        (originCube d (K : ℤ)) R omega hh +
      oneStepNeumannSlopeField M n h q
        (originCube d (K : ℤ)) omega hh x
  have hF : MemLp F 2 (normalizedCubeMeasure R) :=
    cubeFluctuationVec_oneStepNeumannSlopeField_memLp_sourceCell
      M n h q R hR omega hh
  have hSlope := oneStepNeumannSlopeField_memLp_sourceCell
    M n h q R hR omega hh
  have hG : MemLp G 2 (normalizedCubeMeasure R) := by
    exact (memLp_const
      (oneStepNeumannCellSlope M n h q
        (originCube d (K : ℤ)) R omega hh)).add hSlope
  unfold oneStepNeumannSourceCellReplacementError
  simpa only [F, G] using
    cubeAverage_const_mul_add_sqrt_vecNormSq_le R
      (oneStepLowerSourceCellWeight M n h R omega)
      (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
        vecNormSq (oneStepNeumannCellSlope M n h q
          (originCube d (K : ℤ)) R omega hh)) F G
      (le_of_lt (by
        unfold oneStepLowerSourceCellWeight
        exact cutoffRatioSup_pos M n (n + h) (Ch02.cubeDomain R) omega))
      hF hG

/-- The primal literal replacement envelope is nonnegative. -/
theorem oneStepDirichletSourceCellReplacementError_nonneg
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d) (R : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    0 ≤ oneStepDirichletSourceCellReplacementError
      (K := K) M n h p R omega hh := by
  unfold oneStepDirichletSourceCellReplacementError
  apply cubeAverage_nonneg_of_nonneg_on
  intro x _hx
  exact mul_nonneg
    (le_of_lt (cutoffRatioSup_pos M (n + h) n
      (Ch02.cubeDomain R) omega))
    (add_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (oneStepSourceCellShellOscillationEnvelope_nonneg n h R omega))
        (vecNormSq_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

/-- The reciprocal literal replacement envelope is nonnegative. -/
theorem oneStepNeumannSourceCellReplacementError_nonneg
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (q : Vec d) (R : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    0 ≤ oneStepNeumannSourceCellReplacementError
      (K := K) M n h q R omega hh := by
  unfold oneStepNeumannSourceCellReplacementError
  apply cubeAverage_nonneg_of_nonneg_on
  intro x _hx
  exact mul_nonneg
    (le_of_lt (cutoffRatioSup_pos M n (n + h)
      (Ch02.cubeDomain R) omega))
    (add_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (oneStepSourceCellShellOscillationEnvelope_nonneg n h R omega))
        (vecNormSq_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

theorem oneStepDirichletSlope_fourthNorm_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hh : 0 < h) (hp : vecNormSq p = 1) :
    oneStepNormalizedFourthNormBorel (originCube d (K : ℤ))
        (oneStepDirichletSlopeL2 M n h p (originCube d (K : ℤ)) omega hh) ≤
      1 + oneStepNormalizedFourthNormBorel (originCube d (K : ℤ))
        (oneStepOriginDirichletGradientL2 M n h p (K : ℤ) omega) := by
  let Q := originCube d (K : ℤ)
  let c := oneStepConstantVectorL2 Q p
  let g := H1Function.gradToHilbertVectorL2
    (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
  have hc4 : MemLp (c : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    have hcoe : (c : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
        fun _ => HilbertVec.ofVec p := by
      apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      exact coeFn_toHilbertVectorL2OfVecField (memVectorL2_const p)
    exact (memLp_const (HilbertVec.ofVec p)).ae_eq hcoe.symm
  obtain ⟨_C, _hC, hcz⟩ := exists_oneStepOriginDirichlet_gradient_four_cz d
  have hg4 : MemLp (g : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    dsimp only [g, Q]
    rw [← oneStepOriginDirichletGradientL2_eq_triadic
      M n h p (K : ℤ) omega hh]
    have hx := memLp_four_gradToHilbertVectorL2_normalizedCubeMeasure
      (originCube d (K : ℤ))
      (oneStepOriginDirichletSolution M n h p (K : ℤ) omega hh).toH1Function
      (hcz M n h omega p (K : ℤ) hh hp).1
    rw [oneStepOriginDirichletSolution_gradient_eq
      M n h p (K : ℤ) omega hh] at hx
    exact hx
  have htri : oneStepNormalizedFourthNormBorel Q (c + g) ≤
      oneStepNormalizedFourthNormBorel Q c +
        oneStepNormalizedFourthNormBorel Q g := by
    have hadd : ((c + g : HilbertVectorL2 (openCubeSet Q)) :
        Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
        (c : Vec d → HilbertVec d) + (g : Vec d → HilbertVec d) := by
      apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      exact Lp.coeFn_add c g
    simp only [oneStepNormalizedFourthNormBorel_eq_cubeLpNorm]
    simp only [cubeLpNorm]
    rw [eLpNorm_norm _ ((hc4.add hg4).aestronglyMeasurable.congr hadd.symm),
      eLpNorm_norm _ hc4.aestronglyMeasurable,
      eLpNorm_norm _ hg4.aestronglyMeasurable, eLpNorm_congr_ae hadd]
    have hb := cubeLpNorm_add_le Q 4 (c : Vec d → HilbertVec d)
      (g : Vec d → HilbertVec d) hc4 hg4 (by norm_num)
    dsimp only [cubeLpNorm] at hb
    exact hb
  have hc : oneStepNormalizedFourthNormBorel Q c = 1 := by
    rw [oneStepNormalizedFourthNormBorel_eq_cubeLpNorm]
    have hcoe : (c : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
        fun _ => HilbertVec.ofVec p := by
      apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      exact coeFn_toHilbertVectorL2OfVecField (memVectorL2_const p)
    have hnorm : ‖HilbertVec.ofVec p‖ = 1 := by
      have hsquare : ‖HilbertVec.ofVec p‖ ^ 2 = 1 := by
        rw [HilbertVec.norm_sq_ofVec]
        simpa only [vecNormSq] using hp
      nlinarith [norm_nonneg (HilbertVec.ofVec p)]
    have hnormAe : (fun x => ‖(c : Vec d → HilbertVec d) x‖) =ᵐ[
        normalizedCubeMeasure Q] fun _ => ‖HilbertVec.ofVec p‖ := by
      filter_upwards [hcoe] with x hx
      rw [hx]
    unfold cubeLpNorm
    rw [eLpNorm_congr_ae hnormAe]
    have hc := cubeLpNorm_const Q 4 (1 : ℝ) (by norm_num)
    dsimp only [cubeLpNorm] at hc
    simpa only [hnorm, norm_one] using hc
  have hg : oneStepNormalizedFourthNormBorel Q g =
      oneStepNormalizedFourthNormBorel Q
        (oneStepOriginDirichletGradientL2 M n h p (K : ℤ) omega) := by
    dsimp only [g, Q]
    rw [← oneStepOriginDirichletGradientL2_eq_triadic
      M n h p (K : ℤ) omega hh]
  simpa only [Q, c, g, oneStepDirichletSlopeL2, hc, hg] using htri

theorem exists_memLp_four_oneStepDirichletSlopeFourthNorm
    (d : ℕ) [NeZero d] :
    ∃ D : ℝ≥0∞, D < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (K : ℕ) (hh : 0 < h) (_hp : vecNormSq p = 1),
        (h : ℝ) ≤ M.delta⁻¹ →
        let S := fun omega => oneStepNormalizedFourthNormBorel
          (originCube d (K : ℤ))
          (oneStepDirichletSlopeL2 M n h p
            (originCube d (K : ℤ)) omega hh)
        MemLp S 4 M.P.toMeasure ∧ eLpNorm S 4 M.P.toMeasure ≤ D := by
  obtain ⟨C, hC, hgrad⟩ :=
    exists_memLp_four_oneStepOriginDirichletFourthNorm d
  let D : ℝ≥0∞ := 1 +
    (C * (ENNReal.ofReal oneStepRatioEightUniformConst) ^ (4 : ℝ)) ^
      (1 / 4 : ℝ)
  have hD : D < ∞ := by
    dsimp only [D]
    finiteness
  refine ⟨D, hD, ?_⟩
  intro M n h p K hh hp hblock
  let Q := originCube d (K : ℤ)
  let G : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    oneStepNormalizedFourthNormBorel Q
      (oneStepOriginDirichletGradientL2 M n h p (K : ℤ) omega)
  let S : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    oneStepNormalizedFourthNormBorel Q
      (oneStepDirichletSlopeL2 M n h p Q omega hh)
  have hGraw := hgrad M n h p (K : ℤ) hh hp
  have hratio : ENNReal.ofReal (oneStepRatioMinusOneEightBound M h) ≤
      ENNReal.ofReal oneStepRatioEightUniformConst :=
    ENNReal.ofReal_le_ofReal (oneStepRatioMinusOneEightBound_le_uniform
      M h hblock)
  have hA : (C *
      (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ)) ^
        (1 / 4 : ℝ) ≤
      (C * (ENNReal.ofReal oneStepRatioEightUniformConst) ^ (4 : ℝ)) ^
        (1 / 4 : ℝ) := by
    gcongr
  have hG : MemLp G 4 M.P.toMeasure := by
    simpa only [G, Q] using hGraw.1
  have hGnorm : eLpNorm G 4 M.P.toMeasure ≤
      (C * (ENNReal.ofReal oneStepRatioEightUniformConst) ^ (4 : ℝ)) ^
        (1 / 4 : ℝ) := by
    have hraw := hGraw.2.trans hA
    simpa only [G, Q] using hraw
  have hSmeas : AEStronglyMeasurable S M.P.toMeasure := by
    apply Measurable.aestronglyMeasurable
    exact (measurable_oneStepNormalizedFourthNormBorel Q).comp
      ((measurable_oneStepDirichletSlopeL2_potentialShellIndexSigma_Ioi
        M n h p Q hh).mono
          (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi n)) le_rfl)
  have hmajor : MemLp (fun omega => 1 + G omega) 4 M.P.toMeasure := by
    exact (memLp_const (1 : ℝ)).add hG
  have hpoint : ∀ omega, S omega ≤ 1 + G omega := by
    intro omega
    exact oneStepDirichletSlope_fourthNorm_le M n h p K omega hh hp
  have hS : MemLp S 4 M.P.toMeasure := by
    apply hmajor.mono' hSmeas
    filter_upwards with omega
    have hS0 : 0 ≤ S omega := ENNReal.toReal_nonneg
    simpa only [Real.norm_eq_abs, abs_of_nonneg hS0] using hpoint omega
  refine ⟨hS, ?_⟩
  calc
    eLpNorm S 4 M.P.toMeasure ≤
        eLpNorm (fun omega => 1 + G omega) 4 M.P.toMeasure := by
      apply eLpNorm_mono_ae hSmeas
      filter_upwards with omega
      have hS0 : 0 ≤ S omega := ENNReal.toReal_nonneg
      have hG0 : 0 ≤ G omega := ENNReal.toReal_nonneg
      have habs : |S omega| ≤ |1 + G omega| := by
        rw [abs_of_nonneg hS0, abs_of_nonneg (add_nonneg zero_le_one hG0)]
        exact hpoint omega
      simpa only [Real.norm_eq_abs] using habs
    _ ≤ eLpNorm (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => (1 : ℝ))
          4 M.P.toMeasure + eLpNorm G 4 M.P.toMeasure := by
      have hOne : AEStronglyMeasurable
          (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => (1 : ℝ))
          M.P.toMeasure := measurable_const.aestronglyMeasurable
      have hadd := eLpNorm_add_le
        (μ := M.P.toMeasure) (p := (4 : ℝ≥0∞))
        (f := fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => (1 : ℝ))
        (g := G) (by norm_num)
      exact hadd
    _ = 1 + eLpNorm G 4 M.P.toMeasure := by
      rw [eLpNorm_const (1 : ℝ) (by norm_num) (NeZero.ne M.P.toMeasure)]
      simp
    _ ≤ D := by
      dsimp only [D]
      gcongr

theorem sourceReplacement_fourthNormBorel_add_le {d : ℕ} (Q : TriadicCube d)
    (u v : HilbertVectorL2 (openCubeSet Q))
    (hu : MemLp (u : Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q))
    (hv : MemLp (v : Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q)) :
    oneStepNormalizedFourthNormBorel Q (u + v) ≤
      oneStepNormalizedFourthNormBorel Q u +
        oneStepNormalizedFourthNormBorel Q v := by
  have hadd : ((u + v : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (u : Vec d → HilbertVec d) + (v : Vec d → HilbertVec d) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    exact Lp.coeFn_add u v
  simp only [oneStepNormalizedFourthNormBorel_eq_cubeLpNorm, cubeLpNorm]
  rw [eLpNorm_norm _ ((hu.add hv).aestronglyMeasurable.congr hadd.symm),
    eLpNorm_norm _ hu.aestronglyMeasurable,
    eLpNorm_norm _ hv.aestronglyMeasurable, eLpNorm_congr_ae hadd]
  have hb := cubeLpNorm_add_le Q 4 (u : Vec d → HilbertVec d)
    (v : Vec d → HilbertVec d) hu hv (by norm_num)
  dsimp only [cubeLpNorm] at hb
  exact hb

theorem sourceReplacement_memLp_four_coe_add {d : ℕ} (Q : TriadicCube d)
    (u v : HilbertVectorL2 (openCubeSet Q))
    (hu : MemLp (u : Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q))
    (hv : MemLp (v : Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q)) :
    MemLp ((u + v : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q) := by
  have hadd : ((u + v : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (u : Vec d → HilbertVec d) + (v : Vec d → HilbertVec d) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    exact Lp.coeFn_add u v
  exact (hu.add hv).ae_eq hadd.symm

private theorem sourceReplacement_fourthNormBorel_neg {d : ℕ} (Q : TriadicCube d)
    (u : HilbertVectorL2 (openCubeSet Q)) :
    oneStepNormalizedFourthNormBorel Q (-u) =
      oneStepNormalizedFourthNormBorel Q u := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.oneStepNormalizedFourthNormBorel_neg (d := d) (Q := Q) (F := u)

private theorem sourceReplacement_fourthNormBorel_sub_le {d : ℕ} (Q : TriadicCube d)
    (u v : HilbertVectorL2 (openCubeSet Q))
    (hu : MemLp (u : Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q))
    (hv : MemLp (v : Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q)) :
    oneStepNormalizedFourthNormBorel Q (u - v) ≤
      oneStepNormalizedFourthNormBorel Q u +
        oneStepNormalizedFourthNormBorel Q v := by
  rw [sub_eq_add_neg]
  have hvneg : MemLp ((-v : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q) := by
    have hneg : ((-v : HilbertVectorL2 (openCubeSet Q)) :
        Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
        fun x => -(v : Vec d → HilbertVec d) x := by
      apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      exact Lp.coeFn_neg v
    exact hv.neg.ae_eq hneg.symm
  have h := sourceReplacement_fourthNormBorel_add_le Q u (-v) hu hvneg
  rwa [sourceReplacement_fourthNormBorel_neg Q v] at h

theorem oneStepNeumannSlope_fourthNorm_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (q : Vec d) (K : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hh : 0 < h) (hq : vecNormSq q = 1) :
    oneStepNormalizedFourthNormBorel (originCube d (K : ℤ))
        (oneStepNeumannSlopeL2 M n h q (originCube d (K : ℤ)) omega hh) ≤
      1 +
        oneStepNormalizedFourthNormBorel (originCube d (K : ℤ))
          (oneStepLinearShellForcingL2 (originCube d (K : ℤ)) q n h omega) +
        oneStepNormalizedFourthNormBorel (originCube d (K : ℤ))
          (oneStepExpRemainderForcingL2 M n h q
            (originCube d (K : ℤ)) omega) +
        oneStepNormalizedFourthNormBorel (originCube d (K : ℤ))
          (oneStepOriginNeumannGradientL2 M n h q (K : ℤ) omega) := by
  let Q := originCube d (K : ℤ)
  let c := oneStepConstantVectorL2 Q q
  let l := oneStepLinearShellForcingL2 Q q n h omega
  let r := oneStepExpRemainderForcingL2 M n h q Q omega
  let f := oneStepShellForcingL2 M n h q Q omega
  let g := H1MeanZeroFunction.gradToHilbertVectorL2
    (oneStepTriadicNeumannSolution M n h q Q omega hh)
  have hc4 : MemLp (c : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    have hcoe : (c : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
        fun _ => HilbertVec.ofVec q := by
      apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      exact coeFn_toHilbertVectorL2OfVecField (memVectorL2_const q)
    exact (memLp_const (HilbertVec.ofVec q)).ae_eq hcoe.symm
  have hl4 : MemLp (l : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    exact memLp_four_oneStepContinuousScalarForcingL2 Q q
      (oneStepShellSumContinuousMap n h omega)
  have hr4 : MemLp (r : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    exact memLp_four_oneStepContinuousScalarForcingL2 Q q
      (oneStepExpRemainderContinuousMap M n h omega)
  have hfEq : f = l + r := by
    exact oneStepShellForcingL2_eq_linear_add_remainder M n h q Q omega hh
  have hf4 : MemLp (f : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    rw [hfEq]
    exact sourceReplacement_memLp_four_coe_add Q l r hl4 hr4
  obtain ⟨_C, _hC, hcz⟩ := exists_oneStepOriginNeumann_gradient_four_cz d
  have hg4 : MemLp (g : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    dsimp only [g, Q]
    rw [← oneStepOriginNeumannGradientL2_eq_triadic
      M n h q (K : ℤ) omega hh]
    have hx := memLp_four_gradToHilbertVectorL2_normalizedCubeMeasure
      (originCube d (K : ℤ))
      (oneStepOriginNeumannSolution M n h q (K : ℤ) omega hh).toH1Function
      (hcz M n h omega q (K : ℤ) hh hq).1
    have hx' : MemLp
        ((oneStepOriginNeumannSolution M n h q (K : ℤ) omega hh)
          |>.gradToHilbertVectorL2 : Vec d → HilbertVec d) 4
        (normalizedCubeMeasure (originCube d (K : ℤ))) := by
      simpa only [H1MeanZeroFunction.gradToHilbertVectorL2] using hx
    rw [oneStepOriginNeumannSolution_gradient_eq
      M n h q (K : ℤ) omega hh] at hx'
    exact hx'
  have hcf := sourceReplacement_fourthNormBorel_add_le Q c f hc4 hf4
  have hslope := sourceReplacement_fourthNormBorel_sub_le Q (c + f) g
    (sourceReplacement_memLp_four_coe_add Q c f hc4 hf4) hg4
  have hforcing := sourceReplacement_fourthNormBorel_add_le Q l r hl4 hr4
  have hc : oneStepNormalizedFourthNormBorel Q c = 1 := by
    rw [oneStepNormalizedFourthNormBorel_eq_cubeLpNorm]
    have hcoe : (c : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
        fun _ => HilbertVec.ofVec q := by
      apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      exact coeFn_toHilbertVectorL2OfVecField (memVectorL2_const q)
    have hnorm : ‖HilbertVec.ofVec q‖ = 1 := by
      have hsquare : ‖HilbertVec.ofVec q‖ ^ 2 = 1 := by
        rw [HilbertVec.norm_sq_ofVec]
        simpa only [vecNormSq] using hq
      nlinarith [norm_nonneg (HilbertVec.ofVec q)]
    have hnormAe : (fun x => ‖(c : Vec d → HilbertVec d) x‖) =ᵐ[
        normalizedCubeMeasure Q] fun _ => ‖HilbertVec.ofVec q‖ := by
      filter_upwards [hcoe] with x hx
      rw [hx]
    unfold cubeLpNorm
    rw [eLpNorm_congr_ae hnormAe]
    have hc := cubeLpNorm_const Q 4 (1 : ℝ) (by norm_num)
    dsimp only [cubeLpNorm] at hc
    simpa only [hnorm, norm_one] using hc
  have hg : oneStepNormalizedFourthNormBorel Q g =
      oneStepNormalizedFourthNormBorel Q
        (oneStepOriginNeumannGradientL2 M n h q (K : ℤ) omega) := by
    dsimp only [g, Q]
    rw [← oneStepOriginNeumannGradientL2_eq_triadic
      M n h q (K : ℤ) omega hh]
  have hf : oneStepNormalizedFourthNormBorel Q f ≤
      oneStepNormalizedFourthNormBorel Q l +
        oneStepNormalizedFourthNormBorel Q r := by
    rw [hfEq]
    exact hforcing
  dsimp only [oneStepNeumannSlopeL2, Q] at hslope
  calc
    _ ≤ oneStepNormalizedFourthNormBorel Q (c + f) +
        oneStepNormalizedFourthNormBorel Q g := by
      exact hslope
    _ ≤ (oneStepNormalizedFourthNormBorel Q c +
          oneStepNormalizedFourthNormBorel Q f) +
        oneStepNormalizedFourthNormBorel Q g := by gcongr
    _ ≤ (1 + (oneStepNormalizedFourthNormBorel Q l +
          oneStepNormalizedFourthNormBorel Q r)) +
        oneStepNormalizedFourthNormBorel Q
          (oneStepOriginNeumannGradientL2 M n h q (K : ℤ) omega) := by
      rw [hc, hg]
      gcongr
    _ = _ := by simp only [Q, l, r]; ring

theorem exists_memLp_four_oneStepNeumannSlopeFourthNorm
    (d : ℕ) [NeZero d] :
    ∃ D : ℝ≥0∞, D < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (q : Vec d) (K : ℕ) (hh : 0 < h) (_hq : vecNormSq q = 1),
        (h : ℝ) ≤ M.delta⁻¹ →
        let S := fun omega => oneStepNormalizedFourthNormBorel
          (originCube d (K : ℤ))
          (oneStepNeumannSlopeL2 M n h q
            (originCube d (K : ℤ)) omega hh)
        MemLp S 4 M.P.toMeasure ∧ eLpNorm S 4 M.P.toMeasure ≤ D := by
  obtain ⟨C, hC, hgrad⟩ :=
    exists_memLp_four_oneStepOriginNeumannFourthNorm d
  let Agrad : ℝ≥0∞ :=
    (C * (ENNReal.ofReal oneStepRatioEightUniformConst) ^ (4 : ℝ)) ^
      (1 / 4 : ℝ)
  let D : ℝ≥0∞ := 1 + oneStepLinearShellFourConst +
    oneStepExpRemainderConst + Agrad
  have hD : D < ∞ := by
    have hlin : oneStepLinearShellFourConst < ∞ := by
      unfold oneStepLinearShellFourConst
      finiteness
    have hrem : oneStepExpRemainderConst < ∞ := by
      unfold oneStepExpRemainderConst
      finiteness
    have hagrad : Agrad < ∞ := by
      dsimp only [Agrad]
      apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      exact ENNReal.mul_ne_top hC.ne
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
    simp only [D, ENNReal.add_lt_top]
    exact ⟨⟨⟨by norm_num, hlin⟩, hrem⟩, hagrad⟩
  refine ⟨D, hD, ?_⟩
  intro M n h q K hh hq hblock
  let Q := originCube d (K : ℤ)
  let L : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    oneStepNormalizedFourthNormBorel Q
      (oneStepLinearShellForcingL2 Q q n h omega)
  let R : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    oneStepNormalizedFourthNormBorel Q
      (oneStepExpRemainderForcingL2 M n h q Q omega)
  let G : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    oneStepNormalizedFourthNormBorel Q
      (oneStepOriginNeumannGradientL2 M n h q (K : ℤ) omega)
  let S : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    oneStepNormalizedFourthNormBorel Q
      (oneStepNeumannSlopeL2 M n h q Q omega hh)
  have hLraw := memLp_four_oneStepLinearShellFourthNorm
    M n h q (K : ℤ) hh hq
  have hRraw := memLp_four_oneStepExpRemainderForcingFourthNorm
    M n h q (K : ℤ) hh hq hblock
  have hGraw := hgrad M n h q (K : ℤ) hh hq
  have hL : MemLp L 4 M.P.toMeasure := by simpa only [L, Q] using hLraw.1
  have hR : MemLp R 4 M.P.toMeasure := by simpa only [R, Q] using hRraw.1
  have hG : MemLp G 4 M.P.toMeasure := by simpa only [G, Q] using hGraw.1
  have hdeltaSqrt : M.delta * Real.sqrt (h : ℝ) ≤ 1 := by
    have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
    have hh0 : 0 ≤ (h : ℝ) := by positivity
    have hdh : M.delta * (h : ℝ) ≤ 1 := by
      have hs : (h : ℝ) ≤ 1 / M.delta := by simpa [one_div] using hblock
      simpa [mul_comm] using (le_div_iff₀ hdelta).mp hs
    have hsqrtSq : (Real.sqrt (h : ℝ)) ^ 2 = (h : ℝ) :=
      Real.sq_sqrt hh0
    have hsq : (M.delta * Real.sqrt (h : ℝ)) ^ 2 ≤ 1 := by
      rw [mul_pow, hsqrtSq]
      nlinarith [M.shellPrefix.delta_le_half]
    nlinarith [mul_nonneg hdelta.le (Real.sqrt_nonneg (h : ℝ))]
  have hdeltaSq : M.delta ^ 2 * (h : ℝ) ≤ 1 := by
    have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
    have hdh : M.delta * (h : ℝ) ≤ 1 := by
      have hs : (h : ℝ) ≤ 1 / M.delta := by simpa [one_div] using hblock
      simpa [mul_comm] using (le_div_iff₀ hdelta).mp hs
    calc
      M.delta ^ 2 * (h : ℝ) = M.delta * (M.delta * (h : ℝ)) := by ring
      _ ≤ M.delta * 1 := mul_le_mul_of_nonneg_left hdh hdelta.le
      _ ≤ 1 := by linarith [M.shellPrefix.delta_le_half]
  have hLnorm : eLpNorm L 4 M.P.toMeasure ≤
      oneStepLinearShellFourConst := by
    calc
      eLpNorm L 4 M.P.toMeasure ≤ oneStepLinearShellFourConst *
          ENNReal.ofReal (M.delta * Real.sqrt (h : ℝ)) := by
        simpa only [L, Q] using hLraw.2
      _ ≤ oneStepLinearShellFourConst * 1 := by
        gcongr
        exact ENNReal.ofReal_le_one.mpr hdeltaSqrt
      _ = _ := mul_one _
  have hRnorm : eLpNorm R 4 M.P.toMeasure ≤
      oneStepExpRemainderConst := by
    calc
      eLpNorm R 4 M.P.toMeasure ≤ oneStepExpRemainderConst *
          ENNReal.ofReal (M.delta ^ 2 * (h : ℝ)) := by
        simpa only [R, Q] using hRraw.2
      _ ≤ oneStepExpRemainderConst * 1 := by
        gcongr
        exact ENNReal.ofReal_le_one.mpr hdeltaSq
      _ = _ := mul_one _
  have hratio : ENNReal.ofReal (oneStepRatioMinusOneEightBound M h) ≤
      ENNReal.ofReal oneStepRatioEightUniformConst :=
    ENNReal.ofReal_le_ofReal (oneStepRatioMinusOneEightBound_le_uniform
      M h hblock)
  have hGnorm : eLpNorm G 4 M.P.toMeasure ≤ Agrad := by
    calc
      eLpNorm G 4 M.P.toMeasure ≤
          (C * (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^
            (4 : ℝ)) ^ (1 / 4 : ℝ) := by
        simpa only [G, Q] using hGraw.2
      _ ≤ Agrad := by dsimp only [Agrad]; gcongr
  have hSmeas : AEStronglyMeasurable S M.P.toMeasure := by
    apply Measurable.aestronglyMeasurable
    exact (measurable_oneStepNormalizedFourthNormBorel Q).comp
      ((measurable_oneStepNeumannSlopeL2_potentialShellIndexSigma_Ioi
        M n h q Q hh).mono
          (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi n)) le_rfl)
  let T : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    1 + L omega + R omega + G omega
  have hT : MemLp T 4 M.P.toMeasure := by
    dsimp only [T]
    exact (((memLp_const (1 : ℝ)).add hL).add hR).add hG
  have hpoint : ∀ omega, S omega ≤ T omega := by
    intro omega
    simpa only [S, T, L, R, G, Q] using
      oneStepNeumannSlope_fourthNorm_le M n h q K omega hh hq
  have hS : MemLp S 4 M.P.toMeasure := by
    apply hT.mono' hSmeas
    filter_upwards with omega
    have hS0 : 0 ≤ S omega := ENNReal.toReal_nonneg
    simpa only [Real.norm_eq_abs, abs_of_nonneg hS0] using hpoint omega
  refine ⟨hS, ?_⟩
  have hST : eLpNorm S 4 M.P.toMeasure ≤ eLpNorm T 4 M.P.toMeasure := by
    apply eLpNorm_mono_ae hSmeas
    filter_upwards with omega
    have hS0 : 0 ≤ S omega := ENNReal.toReal_nonneg
    have hT0 : 0 ≤ T omega := by
      dsimp only [T]
      exact add_nonneg
        (add_nonneg (add_nonneg zero_le_one ENNReal.toReal_nonneg)
          ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
    simpa only [Real.norm_eq_abs, abs_of_nonneg hS0,
      abs_of_nonneg hT0] using hpoint omega
  have hOne : AEStronglyMeasurable
      (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => (1 : ℝ))
      M.P.toMeasure := measurable_const.aestronglyMeasurable
  have hsum1 := eLpNorm_add_le (μ := M.P.toMeasure) (p := (4 : ℝ≥0∞))
    (f := fun _ => (1 : ℝ)) (g := L) (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have hsum2 := eLpNorm_add_le (μ := M.P.toMeasure) (p := (4 : ℝ≥0∞))
    (f := (fun _ => (1 : ℝ)) + L) (g := R) (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have hsum3 := eLpNorm_add_le (μ := M.P.toMeasure) (p := (4 : ℝ≥0∞))
    (f := ((fun _ => (1 : ℝ)) + L) + R) (g := G)
      (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  calc
    eLpNorm S 4 M.P.toMeasure ≤ eLpNorm T 4 M.P.toMeasure := hST
    _ ≤ eLpNorm (fun omega => 1 + L omega + R omega) 4 M.P.toMeasure +
        eLpNorm G 4 M.P.toMeasure := by
      exact hsum3
    _ ≤ (eLpNorm (fun omega => 1 + L omega) 4 M.P.toMeasure +
          eLpNorm R 4 M.P.toMeasure) + eLpNorm G 4 M.P.toMeasure := by
      gcongr
      exact hsum2
    _ ≤ ((eLpNorm (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
          (1 : ℝ)) 4 M.P.toMeasure + eLpNorm L 4 M.P.toMeasure) +
          eLpNorm R 4 M.P.toMeasure) + eLpNorm G 4 M.P.toMeasure := by
      gcongr
      exact hsum1
    _ = 1 + eLpNorm L 4 M.P.toMeasure + eLpNorm R 4 M.P.toMeasure +
        eLpNorm G 4 M.P.toMeasure := by
      rw [eLpNorm_const (1 : ℝ) (by norm_num) (NeZero.ne M.P.toMeasure)]
      simp
    _ ≤ D := by
      dsimp only [D]
      gcongr


theorem integral_pow_four_eq_toReal_eLpNorm_pow_four
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (f : Omega → ℝ) (hf : MemLp f 4 mu) :
    ∫ omega, f omega ^ 4 ∂mu = (eLpNorm f 4 mu).toReal ^ 4 := by
  have hint : Integrable (fun omega => ‖f omega‖ ^ (4 : ℝ)) mu :=
    hf.integrable_norm_rpow (by norm_num) (by norm_num)
  have hpow : (fun omega => f omega ^ 4) =
      fun omega => ‖f omega‖ ^ (4 : ℝ) := by
    funext omega
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    rw [Real.norm_eq_abs]
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ f omega ^ 4)]
  rw [hpow]
  have hlin := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
    (f := f) (μ := mu) (p := (4 : NNReal)) (by norm_num) hf.aestronglyMeasurable
  have htop : eLpNorm f 4 mu ≠ ∞ := hf.eLpNorm_ne_top
  have hreal := congrArg ENNReal.toReal hlin
  rw [← ENNReal.toReal_rpow] at hreal
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (norm_nonneg _) _)
    hint.aestronglyMeasurable]
  convert hreal.symm using 1
  · apply congrArg ENNReal.toReal
    apply lintegral_congr
    intro omega
    rw [← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)]
    all_goals norm_num [Real.rpow_natCast]
  · change (eLpNorm f 4 mu).toReal ^ (4 : ℕ) =
      Real.rpow (eLpNorm f 4 mu).toReal 4
    exact (Real.rpow_natCast _ 4).symm

/-- Samplewise spatial `L⁴` membership of the literal primal slope.  This is
the deterministic cube CZ estimate applied to the already-measurable
Lax--Milgram solution, not a new parameterized solution operator. -/
theorem memLp_four_oneStepDirichletSlopeL2_space
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hh : 0 < h) (hp : vecNormSq p = 1) :
    MemLp ((oneStepDirichletSlopeL2 M n h p
      (originCube d (K : ℤ)) omega hh) : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure (originCube d (K : ℤ))) := by
  let Q := originCube d (K : ℤ)
  let c := oneStepConstantVectorL2 Q p
  let g := H1Function.gradToHilbertVectorL2
    (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
  have hc4 : MemLp (c : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    have hcoe : (c : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
        fun _ => HilbertVec.ofVec p := by
      apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      exact coeFn_toHilbertVectorL2OfVecField (memVectorL2_const p)
    exact (memLp_const (HilbertVec.ofVec p)).ae_eq hcoe.symm
  obtain ⟨_C, _hC, hcz⟩ := exists_oneStepOriginDirichlet_gradient_four_cz d
  have hg4 : MemLp (g : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    dsimp only [g, Q]
    rw [← oneStepOriginDirichletGradientL2_eq_triadic
      M n h p (K : ℤ) omega hh]
    have hx := memLp_four_gradToHilbertVectorL2_normalizedCubeMeasure
      (originCube d (K : ℤ))
      (oneStepOriginDirichletSolution M n h p (K : ℤ) omega hh).toH1Function
      (hcz M n h omega p (K : ℤ) hh hp).1
    rw [oneStepOriginDirichletSolution_gradient_eq
      M n h p (K : ℤ) omega hh] at hx
    exact hx
  have hadd : ((c + g : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (c : Vec d → HilbertVec d) + (g : Vec d → HilbertVec d) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    exact Lp.coeFn_add c g
  simpa only [Q, c, g, oneStepDirichletSlopeL2] using
    (hc4.add hg4).ae_eq hadd.symm

theorem cubeAverage_oneStepDirichletSlope_vecNormSq_sq_eq_fourthNormBorel
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hh : 0 < h) (hp : vecNormSq p = 1) :
    cubeAverage (originCube d (K : ℤ)) (fun x =>
        vecNormSq (oneStepDirichletSlopeField M n h p
          (originCube d (K : ℤ)) omega hh x) ^ 2) =
      Real.rpow (oneStepNormalizedFourthNormBorel (originCube d (K : ℤ))
        (oneStepDirichletSlopeL2 M n h p
          (originCube d (K : ℤ)) omega hh)) 4 := by
  let Q := originCube d (K : ℤ)
  let F := oneStepDirichletSlopeField M n h p Q omega hh
  let u := oneStepDirichletSlopeL2 M n h p Q omega hh
  have hu4 : MemLp (u : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    let c := oneStepConstantVectorL2 Q p
    let g := H1Function.gradToHilbertVectorL2
      (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
    have hc4 : MemLp (c : Vec d → HilbertVec d) 4
        (normalizedCubeMeasure Q) := by
      have hcoe : (c : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
          fun _ => HilbertVec.ofVec p := by
        apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
        exact coeFn_toHilbertVectorL2OfVecField (memVectorL2_const p)
      exact (memLp_const (HilbertVec.ofVec p)).ae_eq hcoe.symm
    obtain ⟨_C, _hC, hcz⟩ := exists_oneStepOriginDirichlet_gradient_four_cz d
    have hg4 : MemLp (g : Vec d → HilbertVec d) 4
        (normalizedCubeMeasure Q) := by
      dsimp only [g, Q]
      rw [← oneStepOriginDirichletGradientL2_eq_triadic
        M n h p (K : ℤ) omega hh]
      have hx := memLp_four_gradToHilbertVectorL2_normalizedCubeMeasure
        (originCube d (K : ℤ))
        (oneStepOriginDirichletSolution M n h p (K : ℤ) omega hh).toH1Function
        (hcz M n h omega p (K : ℤ) hh hp).1
      rw [oneStepOriginDirichletSolution_gradient_eq
        M n h p (K : ℤ) omega hh] at hx
      exact hx
    have hadd : ((c + g : HilbertVectorL2 (openCubeSet Q)) :
        Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
        (c : Vec d → HilbertVec d) + (g : Vec d → HilbertVec d) := by
      apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      exact Lp.coeFn_add c g
    exact (hc4.add hg4).ae_eq hadd.symm
  rw [oneStepNormalizedFourthNormBorel_eq_cubeLpNorm]
  have hnorm := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow Q 4
    (fun x => ‖(u : Vec d → HilbertVec d) x‖)
    (by norm_num) (by norm_num) hu4.norm
  norm_num only [ENNReal.toReal_ofNat] at hnorm
  have hnorm' : Real.rpow
      (cubeLpNorm Q 4 (fun x => ‖(u : Vec d → HilbertVec d) x‖)) 4 =
      cubeAverage Q (fun x => Real.rpow
        ‖(u : Vec d → HilbertVec d) x‖ 4) := by
    change Real.rpow
      (cubeLpNorm Q 4 (fun x => ‖(u : Vec d → HilbertVec d) x‖)) 4 =
      cubeAverage Q (fun x => Real.rpow ‖‖(u : Vec d → HilbertVec d) x‖‖ 4) at hnorm
    simpa only [norm_norm] using hnorm
  change cubeAverage Q (fun x => vecNormSq (F x) ^ 2) =
    Real.rpow (cubeLpNorm Q 4 (fun x => ‖(u : Vec d → HilbertVec d) x‖)) 4
  calc
    cubeAverage Q (fun x => vecNormSq (F x) ^ 2) =
        cubeAverage Q (fun x => Real.rpow
          ‖(u : Vec d → HilbertVec d) x‖ 4) := by
      rw [show u = toHilbertVectorL2OfVecField
          (oneStepDirichletSlopeField_memVectorL2 M n h p Q omega hh) by
        exact oneStepDirichletSlopeL2_eq_toHilbertVectorL2OfVecField
          M n h p Q omega hh]
      rw [cubeAverage_eq_integral_normalizedCubeMeasure,
        cubeAverage_eq_integral_normalizedCubeMeasure]
      apply integral_congr_ae
      have hcoe := ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
        (coeFn_toHilbertVectorL2OfVecField
        (oneStepDirichletSlopeField_memVectorL2 M n h p Q omega hh)
        )
      filter_upwards [hcoe] with x hx
      rw [hx]
      change vecNormSq (F x) ^ 2 =
        Real.rpow ‖HilbertVec.ofVec (F x)‖ 4
      have hs := HilbertVec.norm_sq_ofVec (F x)
      change ‖HilbertVec.ofVec (F x)‖ ^ 2 = vecNormSq (F x) at hs
      calc
        vecNormSq (F x) ^ 2 = ‖HilbertVec.ofVec (F x)‖ ^ (4 : ℕ) := by
          rw [← hs]
          ring
        _ = Real.rpow ‖HilbertVec.ofVec (F x)‖ 4 := by
          symm
          exact Real.rpow_natCast _ 4
    _ = Real.rpow (cubeLpNorm Q 4
        (fun x => ‖(u : Vec d → HilbertVec d) x‖)) 4 := hnorm'.symm


theorem cubeAverage_vecNormSq_sq_eq_fourthNormBorel_of_ae
    {d : ℕ} (Q : TriadicCube d) (F : Vec d → Vec d)
    (u : HilbertVectorL2 (openCubeSet Q))
    (hu4 : MemLp (u : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q))
    (hcoe : (u : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      hilbertifyVecField F) :
    cubeAverage Q (fun x => vecNormSq (F x) ^ 2) =
      Real.rpow (oneStepNormalizedFourthNormBorel Q u) 4 := by
  rw [oneStepNormalizedFourthNormBorel_eq_cubeLpNorm]
  have hnorm := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow Q 4
    (fun x => ‖(u : Vec d → HilbertVec d) x‖)
    (by norm_num) (by norm_num) hu4.norm
  norm_num only [ENNReal.toReal_ofNat] at hnorm
  have hnorm' : Real.rpow
      (cubeLpNorm Q 4 (fun x => ‖(u : Vec d → HilbertVec d) x‖)) 4 =
      cubeAverage Q (fun x => Real.rpow
        ‖(u : Vec d → HilbertVec d) x‖ 4) := by
    change Real.rpow
      (cubeLpNorm Q 4 (fun x => ‖(u : Vec d → HilbertVec d) x‖)) 4 =
      cubeAverage Q (fun x => Real.rpow ‖‖(u : Vec d → HilbertVec d) x‖‖ 4) at hnorm
    simpa only [norm_norm] using hnorm
  calc
    cubeAverage Q (fun x => vecNormSq (F x) ^ 2) =
        cubeAverage Q (fun x => Real.rpow
          ‖(u : Vec d → HilbertVec d) x‖ 4) := by
      rw [cubeAverage_eq_integral_normalizedCubeMeasure,
        cubeAverage_eq_integral_normalizedCubeMeasure]
      apply integral_congr_ae
      filter_upwards [hcoe] with x hx
      rw [hx]
      change vecNormSq (F x) ^ 2 =
        Real.rpow ‖HilbertVec.ofVec (F x)‖ 4
      have hs := HilbertVec.norm_sq_ofVec (F x)
      change ‖HilbertVec.ofVec (F x)‖ ^ 2 = vecNormSq (F x) at hs
      calc
        vecNormSq (F x) ^ 2 = ‖HilbertVec.ofVec (F x)‖ ^ (4 : ℕ) := by
          rw [← hs]
          ring
        _ = Real.rpow ‖HilbertVec.ofVec (F x)‖ 4 := by
          symm
          exact Real.rpow_natCast _ 4
    _ = Real.rpow (cubeLpNorm Q 4
        (fun x => ‖(u : Vec d → HilbertVec d) x‖)) 4 := hnorm'.symm

/-- Samplewise spatial `L⁴` membership of the literal reciprocal slope,
obtained by applying the deterministic Neumann CZ estimate to the measurable
solution and its linear/remainder forcing split. -/
theorem memLp_four_oneStepNeumannSlopeL2_space
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (q : Vec d) (K : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hh : 0 < h) (hq : vecNormSq q = 1) :
    MemLp ((oneStepNeumannSlopeL2 M n h q
      (originCube d (K : ℤ)) omega hh) : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure (originCube d (K : ℤ))) := by
  let Q := originCube d (K : ℤ)
  let u := oneStepNeumannSlopeL2 M n h q Q omega hh
  let c := oneStepConstantVectorL2 Q q
  let l := oneStepLinearShellForcingL2 Q q n h omega
  let r := oneStepExpRemainderForcingL2 M n h q Q omega
  let f := oneStepShellForcingL2 M n h q Q omega
  let g := H1MeanZeroFunction.gradToHilbertVectorL2
    (oneStepTriadicNeumannSolution M n h q Q omega hh)
  have hc4 : MemLp (c : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    have hcoe : (c : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
        fun _ => HilbertVec.ofVec q := by
      apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      exact coeFn_toHilbertVectorL2OfVecField (memVectorL2_const q)
    exact (memLp_const (HilbertVec.ofVec q)).ae_eq hcoe.symm
  have hl4 : MemLp (l : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) :=
    memLp_four_oneStepContinuousScalarForcingL2 Q q
      (oneStepShellSumContinuousMap n h omega)
  have hr4 : MemLp (r : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) :=
    memLp_four_oneStepContinuousScalarForcingL2 Q q
      (oneStepExpRemainderContinuousMap M n h omega)
  have hfEq : f = l + r :=
    oneStepShellForcingL2_eq_linear_add_remainder M n h q Q omega hh
  have hf4 : MemLp (f : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    rw [hfEq]
    have hadd : ((l + r : HilbertVectorL2 (openCubeSet Q)) :
        Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
        (l : Vec d → HilbertVec d) + (r : Vec d → HilbertVec d) := by
      apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      exact Lp.coeFn_add l r
    exact (hl4.add hr4).ae_eq hadd.symm
  obtain ⟨_C, _hC, hcz⟩ := exists_oneStepOriginNeumann_gradient_four_cz d
  have hg4 : MemLp (g : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    dsimp only [g, Q]
    rw [← oneStepOriginNeumannGradientL2_eq_triadic
      M n h q (K : ℤ) omega hh]
    have hx := memLp_four_gradToHilbertVectorL2_normalizedCubeMeasure
      (originCube d (K : ℤ))
      (oneStepOriginNeumannSolution M n h q (K : ℤ) omega hh).toH1Function
      (hcz M n h omega q (K : ℤ) hh hq).1
    have hx' : MemLp
        ((oneStepOriginNeumannSolution M n h q (K : ℤ) omega hh)
          |>.gradToHilbertVectorL2 : Vec d → HilbertVec d) 4
        (normalizedCubeMeasure (originCube d (K : ℤ))) := by
      simpa only [H1MeanZeroFunction.gradToHilbertVectorL2] using hx
    rw [oneStepOriginNeumannSolution_gradient_eq
      M n h q (K : ℤ) omega hh] at hx'
    exact hx'
  have hcf4 := hc4.add hf4
  have hu4 : MemLp (u : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    have hadd : ((c + f : HilbertVectorL2 (openCubeSet Q)) :
        Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
        (c : Vec d → HilbertVec d) + (f : Vec d → HilbertVec d) := by
      apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      exact Lp.coeFn_add c f
    have hsub : ((c + f - g : HilbertVectorL2 (openCubeSet Q)) :
        Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
        ((c + f : HilbertVectorL2 (openCubeSet Q)) : Vec d → HilbertVec d) -
          (g : Vec d → HilbertVec d) := by
      apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      exact Lp.coeFn_sub (c + f) g
    have hraw := (hcf4.ae_eq hadd.symm).sub hg4
    have hraw' := hraw.ae_eq hsub.symm
    simpa only [u, oneStepNeumannSlopeL2, c, f, g] using hraw'
  exact hu4

theorem cubeAverage_oneStepNeumannSlope_vecNormSq_sq_eq_fourthNormBorel
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (q : Vec d) (K : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hh : 0 < h) (hq : vecNormSq q = 1) :
    cubeAverage (originCube d (K : ℤ)) (fun x =>
        vecNormSq (oneStepNeumannSlopeField M n h q
          (originCube d (K : ℤ)) omega hh x) ^ 2) =
      Real.rpow (oneStepNormalizedFourthNormBorel (originCube d (K : ℤ))
        (oneStepNeumannSlopeL2 M n h q
          (originCube d (K : ℤ)) omega hh)) 4 := by
  let Q := originCube d (K : ℤ)
  let F := oneStepNeumannSlopeField M n h q Q omega hh
  let u := oneStepNeumannSlopeL2 M n h q Q omega hh
  let c := oneStepConstantVectorL2 Q q
  let l := oneStepLinearShellForcingL2 Q q n h omega
  let r := oneStepExpRemainderForcingL2 M n h q Q omega
  let f := oneStepShellForcingL2 M n h q Q omega
  let g := H1MeanZeroFunction.gradToHilbertVectorL2
    (oneStepTriadicNeumannSolution M n h q Q omega hh)
  have hc4 : MemLp (c : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    have hcoe : (c : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
        fun _ => HilbertVec.ofVec q := by
      apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      exact coeFn_toHilbertVectorL2OfVecField (memVectorL2_const q)
    exact (memLp_const (HilbertVec.ofVec q)).ae_eq hcoe.symm
  have hl4 : MemLp (l : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) :=
    memLp_four_oneStepContinuousScalarForcingL2 Q q
      (oneStepShellSumContinuousMap n h omega)
  have hr4 : MemLp (r : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) :=
    memLp_four_oneStepContinuousScalarForcingL2 Q q
      (oneStepExpRemainderContinuousMap M n h omega)
  have hfEq : f = l + r :=
    oneStepShellForcingL2_eq_linear_add_remainder M n h q Q omega hh
  have hf4 : MemLp (f : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    rw [hfEq]
    have hadd : ((l + r : HilbertVectorL2 (openCubeSet Q)) :
        Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
        (l : Vec d → HilbertVec d) + (r : Vec d → HilbertVec d) := by
      apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      exact Lp.coeFn_add l r
    exact (hl4.add hr4).ae_eq hadd.symm
  obtain ⟨_C, _hC, hcz⟩ := exists_oneStepOriginNeumann_gradient_four_cz d
  have hg4 : MemLp (g : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    dsimp only [g, Q]
    rw [← oneStepOriginNeumannGradientL2_eq_triadic
      M n h q (K : ℤ) omega hh]
    have hx := memLp_four_gradToHilbertVectorL2_normalizedCubeMeasure
      (originCube d (K : ℤ))
      (oneStepOriginNeumannSolution M n h q (K : ℤ) omega hh).toH1Function
      (hcz M n h omega q (K : ℤ) hh hq).1
    have hx' : MemLp
        ((oneStepOriginNeumannSolution M n h q (K : ℤ) omega hh)
          |>.gradToHilbertVectorL2 : Vec d → HilbertVec d) 4
        (normalizedCubeMeasure (originCube d (K : ℤ))) := by
      simpa only [H1MeanZeroFunction.gradToHilbertVectorL2] using hx
    rw [oneStepOriginNeumannSolution_gradient_eq
      M n h q (K : ℤ) omega hh] at hx'
    exact hx'
  have hcf4 := hc4.add hf4
  have hu4 : MemLp (u : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    have hadd : ((c + f : HilbertVectorL2 (openCubeSet Q)) :
        Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
        (c : Vec d → HilbertVec d) + (f : Vec d → HilbertVec d) := by
      apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      exact Lp.coeFn_add c f
    have hsub : ((c + f - g : HilbertVectorL2 (openCubeSet Q)) :
        Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
        ((c + f : HilbertVectorL2 (openCubeSet Q)) : Vec d → HilbertVec d) -
          (g : Vec d → HilbertVec d) := by
      apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      exact Lp.coeFn_sub (c + f) g
    have hraw := (hcf4.ae_eq hadd.symm).sub hg4
    have hraw' := hraw.ae_eq hsub.symm
    simpa only [u, oneStepNeumannSlopeL2, c, f, g] using hraw'
  have hcoe : (u : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      hilbertifyVecField F := by
    rw [show u = toHilbertVectorL2OfVecField
        (oneStepNeumannSlopeField_memVectorL2 M n h q Q omega hh) by
      exact oneStepNeumannSlopeL2_eq_toHilbertVectorL2OfVecField
        M n h q Q omega hh]
    exact ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      (coeFn_toHilbertVectorL2OfVecField
        (oneStepNeumannSlopeField_memVectorL2 M n h q Q omega hh))
  exact cubeAverage_vecNormSq_sq_eq_fourthNormBorel_of_ae Q F u hu4 hcoe


theorem exists_oneStepDirichletSourceCellEnergy_two_budget
    (d : ℕ) [NeZero d] :
    ∃ a : ℝ, 0 ≤ a ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h K : ℕ)
        (p : Vec d) (hh : 0 < h) (_hp : vecNormSq p = 1)
        (_hblock : (h : ℝ) ≤ M.delta⁻¹),
        (∀ R ∈ oneStepSourceCells d K n M.delta,
          MemLp (fun omega => cubeAverage R (fun x =>
            vecNormSq (oneStepDirichletSlopeField M n h p
              (originCube d (K : ℤ)) omega hh x))) 2 M.P.toMeasure) ∧
        ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega, (cubeAverage R (fun x =>
              vecNormSq (oneStepDirichletSlopeField M n h p
                (originCube d (K : ℤ)) omega hh x))) ^ 2
              ∂M.P.toMeasure ≤ a ^ 2) := by
  obtain ⟨D, hD, hSlope⟩ :=
    exists_memLp_four_oneStepDirichletSlopeFourthNorm d
  let a : ℝ := D.toReal ^ 2 + 1
  refine ⟨a, by dsimp only [a]; positivity, ?_⟩
  intro M n h K p hh hp hblock
  let Q := originCube d (K : ℤ)
  let S : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    oneStepNormalizedFourthNormBorel Q
      (oneStepDirichletSlopeL2 M n h p Q omega hh)
  let P : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    cubeAverage Q (fun x => vecNormSq
      (oneStepDirichletSlopeField M n h p Q omega hh x) ^ 2)
  obtain ⟨hSmem, hSnorm⟩ := hSlope M n h p K hh hp hblock
  have hPS : ∀ omega, P omega = Real.rpow (S omega) 4 := by
    intro omega
    simpa only [P, S, Q] using
      cubeAverage_oneStepDirichletSlope_vecNormSq_sq_eq_fourthNormBorel
        M n h p K omega hh hp
  have hSint : Integrable (fun omega => ‖S omega‖ ^ (4 : ℝ))
      M.P.toMeasure := hSmem.integrable_norm_rpow (by norm_num) (by norm_num)
  have hPint : Integrable P M.P.toMeasure := by
    have heq : P = fun omega => ‖S omega‖ ^ (4 : ℝ) := by
      funext omega
      rw [hPS]
      congr 1
      rw [Real.norm_eq_abs]
      exact (abs_of_nonneg (show 0 ≤ S omega by
        exact ENNReal.toReal_nonneg)).symm
    rw [heq]
    exact hSint
  let s := oneStepSourceCells d K n M.delta
  let A : TriadicCube d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
    fun R omega => cubeAverage R (fun x =>
      vecNormSq (oneStepDirichletSlopeField M n h p Q omega hh x))
  have hsNonempty : s.Nonempty := oneStepSourceCells_nonempty d K n M.delta
  have hsCard : (0 : ℝ) < s.card := by exact_mod_cast hsNonempty.card_pos
  have hpoint : ∀ omega,
      ((s.card : ℝ)⁻¹) * ∑ R ∈ s, (A R omega) ^ 2 ≤ P omega := by
    intro omega
    have hspatial : MemLp (hilbertifyVecField
        (oneStepDirichletSlopeField M n h p Q omega hh)) 4
        (normalizedCubeMeasure Q) := by
      have hu := memLp_four_oneStepDirichletSlopeL2_space
        M n h p K omega hh hp
      have hcoe : ((oneStepDirichletSlopeL2 M n h p Q omega hh) :
          Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
          hilbertifyVecField
            (oneStepDirichletSlopeField M n h p Q omega hh) := by
        rw [oneStepDirichletSlopeL2_eq_toHilbertVectorL2OfVecField]
        exact ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
          (coeFn_toHilbertVectorL2OfVecField
            (oneStepDirichletSlopeField_memVectorL2 M n h p Q omega hh))
      exact hu.ae_eq hcoe
    simpa only [s, A, P, Q, oneStepSourceCells] using
      normalized_sum_descendant_cubeAverage_vecNormSq_sq_le_parent
        Q (oneStepDirichletSlopeField M n h p Q omega hh) hspatial
  have hlocalSqLe : ∀ R ∈ s, ∀ omega,
      (A R omega) ^ 2 ≤ (s.card : ℝ) * P omega := by
    intro R hR omega
    have hterm : (A R omega) ^ 2 ≤ ∑ T ∈ s, (A T omega) ^ 2 := by
      exact Finset.single_le_sum
        (fun T hT => sq_nonneg (A T omega)) hR
    have hsum : ∑ T ∈ s, (A T omega) ^ 2 ≤
        (s.card : ℝ) * P omega :=
      (inv_mul_le_iff₀ hsCard).mp (hpoint omega)
    exact hterm.trans hsum
  have hAmem : ∀ R ∈ s, MemLp (A R) 2 M.P.toMeasure := by
    intro R hR
    have hmeas : Measurable (A R) := by
      simpa only [A, Q, s] using
        measurable_oneStepDirichletSourceCellEnergy M n h p R hR hh
    apply (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
    have hmajor : Integrable (fun omega => (s.card : ℝ) * P omega)
        M.P.toMeasure := hPint.const_mul (s.card : ℝ)
    apply hmajor.mono (hmeas.pow_const 2).aestronglyMeasurable
    filter_upwards with omega
    have hA0 : 0 ≤ A R omega := by
      dsimp only [A]
      exact cubeAverage_nonneg_of_nonneg_on fun x _hx => vecNormSq_nonneg _
    have hP0 : 0 ≤ P omega := by
      dsimp only [P]
      exact cubeAverage_nonneg_of_nonneg_on fun x _hx => sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hP0)]
    exact hlocalSqLe R hR omega
  refine ⟨?_, ?_⟩
  · intro R hR
    simpa only [s, A, Q] using hAmem R hR
  have hAvgInt : Integrable (fun omega =>
      ((s.card : ℝ)⁻¹) * ∑ R ∈ s, (A R omega) ^ 2) M.P.toMeasure := by
    apply Integrable.const_mul
    exact integrable_finsetSum s fun R hR =>
      (memLp_two_iff_integrable_sq (hAmem R hR).aestronglyMeasurable).mp (hAmem R hR)
  have havg := integral_mono hAvgInt hPint
    hpoint
  have hrewrite :
      ∫ omega, ((s.card : ℝ)⁻¹) * ∑ R ∈ s, (A R omega) ^ 2
          ∂M.P.toMeasure =
        ((s.card : ℝ)⁻¹) * ∑ R ∈ s,
          ∫ omega, (A R omega) ^ 2 ∂M.P.toMeasure := by
    rw [integral_const_mul]
    congr 1
    exact integral_finsetSum s fun R hR =>
      (memLp_two_iff_integrable_sq (hAmem R hR).aestronglyMeasurable).mp (hAmem R hR)
  rw [hrewrite] at havg
  have hPNat : P = fun omega => S omega ^ 4 := by
    funext omega
    rw [hPS]
    exact Real.rpow_natCast _ 4
  have hPIntegral : ∫ omega, P omega ∂M.P.toMeasure =
      (eLpNorm S 4 M.P.toMeasure).toReal ^ 4 := by
    rw [hPNat]
    exact integral_pow_four_eq_toReal_eLpNorm_pow_four S hSmem
  have hnormReal : (eLpNorm S 4 M.P.toMeasure).toReal ≤ D.toReal :=
    ENNReal.toReal_mono hD.ne hSnorm
  have hPBound : ∫ omega, P omega ∂M.P.toMeasure ≤ a ^ 2 := by
    rw [hPIntegral]
    dsimp only [a]
    have hnorm0 : 0 ≤ (eLpNorm S 4 M.P.toMeasure).toReal :=
      ENNReal.toReal_nonneg
    have hD0 : 0 ≤ D.toReal := ENNReal.toReal_nonneg
    have hpow4 := pow_le_pow_left₀ hnorm0 hnormReal 4
    have htail : D.toReal ^ 4 ≤ (D.toReal ^ 2 + 1) ^ 2 := by
      nlinarith [sq_nonneg (D.toReal ^ 2)]
    exact hpow4.trans htail
  simpa only [s, A, Q] using havg.trans hPBound

theorem exists_oneStepNeumannSourceCellEnergy_two_budget
    (d : ℕ) [NeZero d] :
    ∃ a : ℝ, 0 ≤ a ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h K : ℕ)
        (q : Vec d) (hh : 0 < h) (_hp : vecNormSq q = 1)
        (_hblock : (h : ℝ) ≤ M.delta⁻¹),
        (∀ R ∈ oneStepSourceCells d K n M.delta,
          MemLp (fun omega => cubeAverage R (fun x =>
            vecNormSq (oneStepNeumannSlopeField M n h q
              (originCube d (K : ℤ)) omega hh x))) 2 M.P.toMeasure) ∧
        ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega, (cubeAverage R (fun x =>
              vecNormSq (oneStepNeumannSlopeField M n h q
                (originCube d (K : ℤ)) omega hh x))) ^ 2
              ∂M.P.toMeasure ≤ a ^ 2) := by
  obtain ⟨D, hD, hSlope⟩ :=
    exists_memLp_four_oneStepNeumannSlopeFourthNorm d
  let a : ℝ := D.toReal ^ 2 + 1
  refine ⟨a, by dsimp only [a]; positivity, ?_⟩
  intro M n h K q hh hq hblock
  let Q := originCube d (K : ℤ)
  let S : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    oneStepNormalizedFourthNormBorel Q
      (oneStepNeumannSlopeL2 M n h q Q omega hh)
  let P : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    cubeAverage Q (fun x => vecNormSq
      (oneStepNeumannSlopeField M n h q Q omega hh x) ^ 2)
  obtain ⟨hSmem, hSnorm⟩ := hSlope M n h q K hh hq hblock
  have hPS : ∀ omega, P omega = Real.rpow (S omega) 4 := by
    intro omega
    simpa only [P, S, Q] using
      cubeAverage_oneStepNeumannSlope_vecNormSq_sq_eq_fourthNormBorel
        M n h q K omega hh hq
  have hSint : Integrable (fun omega => ‖S omega‖ ^ (4 : ℝ))
      M.P.toMeasure := hSmem.integrable_norm_rpow (by norm_num) (by norm_num)
  have hPint : Integrable P M.P.toMeasure := by
    have heq : P = fun omega => ‖S omega‖ ^ (4 : ℝ) := by
      funext omega
      rw [hPS]
      congr 1
      rw [Real.norm_eq_abs]
      exact (abs_of_nonneg (show 0 ≤ S omega by
        exact ENNReal.toReal_nonneg)).symm
    rw [heq]
    exact hSint
  let s := oneStepSourceCells d K n M.delta
  let A : TriadicCube d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
    fun R omega => cubeAverage R (fun x =>
      vecNormSq (oneStepNeumannSlopeField M n h q Q omega hh x))
  have hsNonempty : s.Nonempty := oneStepSourceCells_nonempty d K n M.delta
  have hsCard : (0 : ℝ) < s.card := by exact_mod_cast hsNonempty.card_pos
  have hpoint : ∀ omega,
      ((s.card : ℝ)⁻¹) * ∑ R ∈ s, (A R omega) ^ 2 ≤ P omega := by
    intro omega
    have hspatial : MemLp (hilbertifyVecField
        (oneStepNeumannSlopeField M n h q Q omega hh)) 4
        (normalizedCubeMeasure Q) := by
      have hu := memLp_four_oneStepNeumannSlopeL2_space
        M n h q K omega hh hq
      have hcoe : ((oneStepNeumannSlopeL2 M n h q Q omega hh) :
          Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
          hilbertifyVecField
            (oneStepNeumannSlopeField M n h q Q omega hh) := by
        rw [oneStepNeumannSlopeL2_eq_toHilbertVectorL2OfVecField]
        exact ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
          (coeFn_toHilbertVectorL2OfVecField
            (oneStepNeumannSlopeField_memVectorL2 M n h q Q omega hh))
      exact hu.ae_eq hcoe
    simpa only [s, A, P, Q, oneStepSourceCells] using
      normalized_sum_descendant_cubeAverage_vecNormSq_sq_le_parent
        Q (oneStepNeumannSlopeField M n h q Q omega hh) hspatial
  have hlocalSqLe : ∀ R ∈ s, ∀ omega,
      (A R omega) ^ 2 ≤ (s.card : ℝ) * P omega := by
    intro R hR omega
    have hterm : (A R omega) ^ 2 ≤ ∑ T ∈ s, (A T omega) ^ 2 := by
      exact Finset.single_le_sum
        (fun T hT => sq_nonneg (A T omega)) hR
    have hsum : ∑ T ∈ s, (A T omega) ^ 2 ≤
        (s.card : ℝ) * P omega :=
      (inv_mul_le_iff₀ hsCard).mp (hpoint omega)
    exact hterm.trans hsum
  have hAmem : ∀ R ∈ s, MemLp (A R) 2 M.P.toMeasure := by
    intro R hR
    have hmeas : Measurable (A R) := by
      simpa only [A, Q, s] using
        measurable_oneStepNeumannSourceCellEnergy M n h q R hR hh
    apply (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
    have hmajor : Integrable (fun omega => (s.card : ℝ) * P omega)
        M.P.toMeasure := hPint.const_mul (s.card : ℝ)
    apply hmajor.mono (hmeas.pow_const 2).aestronglyMeasurable
    filter_upwards with omega
    have hA0 : 0 ≤ A R omega := by
      dsimp only [A]
      exact cubeAverage_nonneg_of_nonneg_on fun x _hx => vecNormSq_nonneg _
    have hP0 : 0 ≤ P omega := by
      dsimp only [P]
      exact cubeAverage_nonneg_of_nonneg_on fun x _hx => sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hP0)]
    exact hlocalSqLe R hR omega
  refine ⟨?_, ?_⟩
  · intro R hR
    simpa only [s, A, Q] using hAmem R hR
  have hAvgInt : Integrable (fun omega =>
      ((s.card : ℝ)⁻¹) * ∑ R ∈ s, (A R omega) ^ 2) M.P.toMeasure := by
    apply Integrable.const_mul
    exact integrable_finsetSum s fun R hR =>
      (memLp_two_iff_integrable_sq (hAmem R hR).aestronglyMeasurable).mp (hAmem R hR)
  have havg := integral_mono hAvgInt hPint
    hpoint
  have hrewrite :
      ∫ omega, ((s.card : ℝ)⁻¹) * ∑ R ∈ s, (A R omega) ^ 2
          ∂M.P.toMeasure =
        ((s.card : ℝ)⁻¹) * ∑ R ∈ s,
          ∫ omega, (A R omega) ^ 2 ∂M.P.toMeasure := by
    rw [integral_const_mul]
    congr 1
    exact integral_finsetSum s fun R hR =>
      (memLp_two_iff_integrable_sq (hAmem R hR).aestronglyMeasurable).mp (hAmem R hR)
  rw [hrewrite] at havg
  have hPNat : P = fun omega => S omega ^ 4 := by
    funext omega
    rw [hPS]
    exact Real.rpow_natCast _ 4
  have hPIntegral : ∫ omega, P omega ∂M.P.toMeasure =
      (eLpNorm S 4 M.P.toMeasure).toReal ^ 4 := by
    rw [hPNat]
    exact integral_pow_four_eq_toReal_eLpNorm_pow_four S hSmem
  have hnormReal : (eLpNorm S 4 M.P.toMeasure).toReal ≤ D.toReal :=
    ENNReal.toReal_mono hD.ne hSnorm
  have hPBound : ∫ omega, P omega ∂M.P.toMeasure ≤ a ^ 2 := by
    rw [hPIntegral]
    dsimp only [a]
    have hnorm0 : 0 ≤ (eLpNorm S 4 M.P.toMeasure).toReal :=
      ENNReal.toReal_nonneg
    have hD0 : 0 ≤ D.toReal := ENNReal.toReal_nonneg
    have hpow4 := pow_le_pow_left₀ hnorm0 hnormReal 4
    have htail : D.toReal ^ 4 ≤ (D.toReal ^ 2 + 1) ^ 2 := by
      nlinarith [sq_nonneg (D.toReal ^ 2)]
    exact hpow4.trans htail
  simpa only [s, A, Q] using havg.trans hPBound



theorem exists_normalized_sum_integral_oneStepDirichletSourceCellJensenError_le_delta_seventeen
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h K : ℕ)
        (p : Vec d)
        (_hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
        (_hK : oneStepLocalizationScale n M.delta ≤ K)
        (hh : 0 < h) (_hp : vecNormSq p = 1)
        (_hblock : (h : ℝ) ≤ M.delta⁻¹),
        ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega, oneStepDirichletSourceCellJensenError
              (K := K) M n h p R omega hh ∂M.P.toMeasure) ≤
          C * M.delta ^ 17 := by
  obtain ⟨a, ha0, hbudget⟩ := exists_oneStepDirichletSourceCellEnergy_two_budget d
  let B : ℝ := 2 * (oneStepSourceCellWeightFourthRootConst d + 1) *
    oneStepDerivativeGaugeConst * a
  let C : ℝ := |B| + 1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro M n h K p hsource hK hh hp hblock
  obtain ⟨hA, hAsq⟩ := hbudget M n h K p hh hp hblock
  have hraw := normalized_sum_integral_oneStepDirichletSourceCellJensenError_le
    M n h p hsource hK hh hblock ha0 hA hAsq
  calc
    _ ≤ 2 * (oneStepSourceCellWeightFourthRootConst d + 1) *
        (oneStepDerivativeGaugeConst * M.delta ^ 17) * a := hraw
    _ ≤ C * M.delta ^ 17 := by
      have hdelta : 0 ≤ M.delta ^ 17 :=
        pow_nonneg M.shellPrefix.delta_pos.le 17
      have hB0 : 0 ≤ B := by
        dsimp only [B]
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num)
            (add_nonneg
              (oneStepSourceCellWeightFourthRootConst_pos M).le zero_le_one))
            oneStepDerivativeGaugeConst_pos.le) ha0
      have hBC : B ≤ C := by
        dsimp only [C]
        rw [abs_of_nonneg hB0]
        linarith
      have heq : 2 * (oneStepSourceCellWeightFourthRootConst d + 1) *
          (oneStepDerivativeGaugeConst * M.delta ^ 17) * a =
          B * M.delta ^ 17 := by dsimp only [B]; ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hBC hdelta

theorem exists_normalized_sum_integral_oneStepNeumannSourceCellJensenError_le_delta_seventeen
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h K : ℕ)
        (q : Vec d)
        (_hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
        (_hK : oneStepLocalizationScale n M.delta ≤ K)
        (hh : 0 < h) (_hq : vecNormSq q = 1)
        (_hblock : (h : ℝ) ≤ M.delta⁻¹),
        ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega, oneStepNeumannSourceCellJensenError
              (K := K) M n h q R omega hh ∂M.P.toMeasure) ≤
          C * M.delta ^ 17 := by
  obtain ⟨a, ha0, hbudget⟩ := exists_oneStepNeumannSourceCellEnergy_two_budget d
  let B : ℝ := 2 * (oneStepSourceCellWeightFourthRootConst d + 1) *
    oneStepDerivativeGaugeConst * a
  let C : ℝ := |B| + 1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro M n h K q hsource hK hh hq hblock
  obtain ⟨hA, hAsq⟩ := hbudget M n h K q hh hq hblock
  have hraw := normalized_sum_integral_oneStepNeumannSourceCellJensenError_le
    M n h q hsource hK hh hblock ha0 hA hAsq
  calc
    _ ≤ 2 * (oneStepSourceCellWeightFourthRootConst d + 1) *
        (oneStepDerivativeGaugeConst * M.delta ^ 17) * a := hraw
    _ ≤ C * M.delta ^ 17 := by
      have hdelta : 0 ≤ M.delta ^ 17 :=
        pow_nonneg M.shellPrefix.delta_pos.le 17
      have hB0 : 0 ≤ B := by
        dsimp only [B]
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num)
            (add_nonneg
              (oneStepSourceCellWeightFourthRootConst_pos M).le zero_le_one))
            oneStepDerivativeGaugeConst_pos.le) ha0
      have hBC : B ≤ C := by
        dsimp only [C]
        rw [abs_of_nonneg hB0]
        linarith
      have heq : 2 * (oneStepSourceCellWeightFourthRootConst d + 1) *
          (oneStepDerivativeGaugeConst * M.delta ^ 17) * a =
          B * M.delta ^ 17 := by dsimp only [B]; ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hBC hdelta



end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support




