module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.OGammaSummable
public import SubdiffusiveProcess.CoarseGrainingVocab.ShellSensitivity
public import SubdiffusiveProcess.Assumptions.OGammaBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.SharedStoppingFailures
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.SampleLawBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Action
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GoodSetMeasurable
public import SubdiffusiveProcess.CoarseGrainingVocab.OGammaSplit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSummable
public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
public import SubdiffusiveProcess.CoarseGrainingVocab.Section11.ShellHeadSum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.SharedStoppingSchedule
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedStoppingDerivative
@[expose] public section




set_option autoImplicit false
open Homogenization Homogenization.IndependentSums SubdiffusiveProcess.Frozen.Assumptions MeasureTheory
open Filter Topology ProbabilityTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
open SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC (anchoredC11SampleLaw_preimage)
open SubdiffusiveProcess.CoarseGrainingVocab.OGamma (measureReal_ge_le_of_ogammaLE)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
variable {d : ℕ}

/-- The shell-oscillation envelope's `Γ₂` scale, geometric in the gap between the cube scale
and the layer index.  This is `isBigOWith_gammaTwo_shellOscillationEnvelope` put in
expectation form by `OGammaBridge.ogammaLE_of_isBigO_gammaSigma`. -/
theorem ogammaLE_shellOscillationEnvelope (M : GMCModel d) (j : ℕ) (k : ℤ) :
    SubdiffusiveProcess.OGammaLE M.P.toMeasure 2
      ((4 : ℝ) ^ (2 : ℝ)⁻¹ *
        ((2 * max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ)))) * (3 : ℝ) ^ (k - (j : ℤ)) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)))
      (shellOscillationEnvelope j k) := by
  have hK : 0 < 2 * max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ))) := by
    have := le_max_left (1 : ℝ) (Real.sqrt (shellCoverLogConst * (d : ℝ)))
    linarith
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hA : 0 < (2 * max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ)))) *
      (3 : ℝ) ^ (k - (j : ℤ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by
    refine mul_pos (mul_pos hK (zpow_pos (by norm_num) _)) ?_
    exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) hdelta
  have hbig : IsBigO M.P.toMeasure (gammaSigma 2) (shellOscillationEnvelope j k)
      ((2 * max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ)))) * (3 : ℝ) ^ (k - (j : ℤ)) *
        ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by
    unfold IsBigO
    rw [show (fun omega => |shellOscillationEnvelope j k omega|) =
        shellOscillationEnvelope j k by
      funext omega
      exact abs_of_nonneg (shellOscillationEnvelope_nonneg j k omega)]
    exact isBigOWith_gammaTwo_shellOscillationEnvelope M j k
  exact SubdiffusiveProcess.OGammaBridge.ogammaLE_of_isBigO_gammaSigma (by norm_num : (0:ℝ) < 2) hA
    (measurable_shellOscillationEnvelope j k) hbig

/-! ### The high-frequency layer sum -/

/-- The partial sum of shell-oscillation envelopes over the layers strictly above the cube
scale `n`.  Its `Γ₂` scales are geometric, `3 ^ (-(1+l))`, so the partial sums are all
`O_{Γ₂}` at one scale. -/
def layerOscSum (n L : ℕ) (omega : PotentialSample d) : ℝ :=
  ∑ l ∈ Finset.range (L + 1), shellOscillationEnvelope (n + 1 + l) (n : ℤ) omega

theorem layerOscSum_nonneg (n L : ℕ) (omega : PotentialSample d) :
    0 ≤ layerOscSum n L omega :=
  Finset.sum_nonneg fun _ _ => shellOscillationEnvelope_nonneg _ _ _

theorem layerOscSum_mono (n : ℕ) {L L' : ℕ} (hL : L ≤ L') (omega : PotentialSample d) :
    layerOscSum n L omega ≤ layerOscSum n L' omega := by
  have hsub : Finset.range (L + 1) ⊆ Finset.range (L' + 1) := by
    intro x hx
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (by omega))
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro l _ _
  exact shellOscillationEnvelope_nonneg _ _ _

theorem measurable_layerOscSum (n L : ℕ) : Measurable (layerOscSum (d := d) n L) :=
  Finset.measurable_sum _ fun _ _ => measurable_shellOscillationEnvelope _ _

theorem sum_three_zpow_neg_le (n L : ℕ) :
    ∑ l ∈ Finset.range (L + 1), (3 : ℝ) ^ ((n : ℤ) - ((n + 1 + l : ℕ) : ℤ)) ≤ 1 / 2 := by
  have hterm : ∀ l ∈ Finset.range (L + 1),
      (3 : ℝ) ^ ((n : ℤ) - ((n + 1 + l : ℕ) : ℤ)) = (1 / 3 : ℝ) * (1 / 3 : ℝ) ^ l := by
    intro l _
    have hexp : (n : ℤ) - ((n + 1 + l : ℕ) : ℤ) = -(1 + (l : ℤ)) := by push_cast; ring
    rw [hexp, zpow_neg, zpow_add₀ (by norm_num : (3:ℝ) ≠ 0), zpow_one, zpow_natCast]
    rw [mul_inv, ← inv_pow]
    norm_num
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hgeo : ∑ l ∈ Finset.range (L + 1), (1 / 3 : ℝ) ^ l ≤ 3 / 2 := by
    have hsum : Summable (fun l : ℕ => (1 / 3 : ℝ) ^ l) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hts : ∑' l : ℕ, (1 / 3 : ℝ) ^ l = 3 / 2 := by
      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    rw [← hts]
    exact hsum.sum_le_tsum _ fun l _ => by positivity
  linarith

/-- The constant of the high-frequency layer sum: the per-layer constant times the geometric
total `∑ 3^{-(1+l)} = 1/2`. -/
def oscSumConst (d : ℕ) : ℝ :=
  (4 : ℝ) ^ (2 : ℝ)⁻¹ * (2 * max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ)))) *
    ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) * (1 / 2)

theorem oscSumConst_pos (d : ℕ) : 0 < oscSumConst d := by
  have hK : 0 < 2 * max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ))) := by
    have := le_max_left (1 : ℝ) (Real.sqrt (shellCoverLogConst * (d : ℝ)))
    linarith
  unfold oscSumConst
  have h4 : (0:ℝ) < (4 : ℝ) ^ (2 : ℝ)⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
  have hlog : (0:ℝ) < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ :=
    Real.rpow_pos_of_pos (by positivity) _
  positivity

/-- **Every high-frequency layer sum is `O_{Γ₂}(C δ)`**, uniformly in `L`: the per-layer
scales are geometric in the gap, so the partial scales stay below one constant. -/
theorem ogammaLE_layerOscSum (M : GMCModel d) (n L : ℕ) :
    SubdiffusiveProcess.OGammaLE M.P.toMeasure 2 (oscSumConst d * M.delta) (layerOscSum n L) := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hK : 0 < 2 * max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ))) := by
    have := le_max_left (1 : ℝ) (Real.sqrt (shellCoverLogConst * (d : ℝ)))
    linarith
  have h4 : (0:ℝ) < (4 : ℝ) ^ (2 : ℝ)⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
  have hlog : (0:ℝ) < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ :=
    Real.rpow_pos_of_pos (by positivity) _
  set A : ℕ → ℝ := fun l => (4 : ℝ) ^ (2 : ℝ)⁻¹ *
    ((2 * max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ)))) *
      (3 : ℝ) ^ ((n : ℤ) - ((n + 1 + l : ℕ) : ℤ)) *
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) with hAdef
  have hApos : ∀ l, 0 < A l := by
    intro l
    rw [hAdef]
    have : (0:ℝ) < (3 : ℝ) ^ ((n : ℤ) - ((n + 1 + l : ℕ) : ℤ)) := zpow_pos (by norm_num) _
    positivity
  have hne : (Finset.range (L + 1)).Nonempty := Finset.nonempty_range_add_one
  have hbase := ogammaLE_two_finset_sum (mu := M.P.toMeasure)
    (X := fun l omega => shellOscillationEnvelope (n + 1 + l) (n : ℤ) omega)
    (A := A) hApos
    (fun l => (measurable_shellOscillationEnvelope _ _).aemeasurable)
    (fun l omega => shellOscillationEnvelope_nonneg _ _ _)
    (fun l => ogammaLE_shellOscillationEnvelope M (n + 1 + l) (n : ℤ)) hne
  refine SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.ogammaLE_mono_scale'
    two_pos (Finset.sum_pos (fun l _ => hApos l) hne) ?_ hbase
  have hsum : ∑ l ∈ Finset.range (L + 1), A l =
      (4 : ℝ) ^ (2 : ℝ)⁻¹ * (2 * max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ)))) *
        ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) *
        ∑ l ∈ Finset.range (L + 1), (3 : ℝ) ^ ((n : ℤ) - ((n + 1 + l : ℕ) : ℤ)) := by
    rw [hAdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hsum]
  have hgeo := sum_three_zpow_neg_le n L
  have hpos : (0:ℝ) < (4 : ℝ) ^ (2 : ℝ)⁻¹ *
      (2 * max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ)))) *
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by positivity
  unfold oscSumConst
  nlinarith [hgeo, hpos]

/-! ### From the envelopes to the stopping log-ratio -/

theorem zero_mem_openCubeSet_originCube (K : ℤ) :
    (0 : Vec d) ∈ openCubeSet (originCube d K) := by
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have h : (0:ℝ) < (3:ℝ) ^ K := by positivity
  constructor <;> simp <;> linarith

/-- A single layer's increment across the tested cube is below the layer's envelope on the
translated sample. -/
theorem abs_shell_sub_le_shellOscillationEnvelope (omega : PotentialSample d) (k : ℕ) (K : ℤ)
    (x z : Vec d) (hz : z - x ∈ openCubeSet (originCube d K)) :
    |omega k z - omega k x| ≤
      shellOscillationEnvelope k K (translatePotentialSample x omega) := by
  have hcont : Continuous fun w : Vec d =>
      (translatePotentialSample x omega) k w :=
    ((translatePotentialSample x omega) k).1.1.continuous
  have hx0 : (0 : Vec d) ∈ openCubeSet (originCube d K) := zero_mem_openCubeSet_originCube K
  have hval1 : (translatePotentialSample x omega) k (z - x) = omega k z := by
    show PotentialField.translate x (omega k) (z - x) = omega k z
    rw [PotentialField.translate_apply, sub_add_cancel]
  have hval2 : (translatePotentialSample x omega) k (0 : Vec d) = omega k x := by
    show PotentialField.translate x (omega k) 0 = omega k x
    rw [PotentialField.translate_apply, zero_add]
  have hosc := cubeOscillation_le_shellOscillationEnvelope (d := d) k K
    (translatePotentialSample x omega)
  have hA : omega k z - omega k x ≤
      cubeOscillation K ((translatePotentialSample x omega) k) := by
    rw [← hval1, ← hval2]
    exact sub_le_cubeOscillation_of_continuous K hcont hz hx0
  have hB : omega k x - omega k z ≤
      cubeOscillation K ((translatePotentialSample x omega) k) := by
    rw [← hval1, ← hval2]
    exact sub_le_cubeOscillation_of_continuous K hcont hx0 hz
  rw [abs_sub_le_iff]
  exact ⟨hA.trans hosc, hB.trans hosc⟩

/-- `log a_anchored - log a_L` reads off the layers above the cutoff: its increment between
two points is the limit of the partial sums of the layer increments. -/
theorem tendsto_stoppingLogRatio_sub (M : GMCModel d) (s : AnchoredC11Sample d) (K : ℕ)
    (x z : Vec d) :
    Filter.Tendsto
      (fun L : ℕ => ∑ l ∈ Finset.range (L + 1), (s.val (K + 1 + l) z - s.val (K + 1 + l) x))
      Filter.atTop
      (nhds (stoppingLogRatio M s K z - stoppingLogRatio M s K x)) := by
  classical
  have hspec := anchoredLog_spec s
  have hKcompact : IsCompact ({x, z} : Set (Vec d)) := (Set.toFinite _).isCompact
  have hxK : x ∈ ({x, z} : Set (Vec d)) := Set.mem_insert _ _
  have hzK : z ∈ ({x, z} : Set (Vec d)) := Set.mem_insert_of_mem _ rfl
  have htz := (hspec.value_tendsto _ hKcompact).tendsto_at hzK
  have htx := (hspec.value_tendsto _ hKcompact).tendsto_at hxK
  have hdiff : Filter.Tendsto
      (fun L : ℕ => anchoredPartialSum s.val L z - anchoredPartialSum s.val L x)
      Filter.atTop (nhds (anchoredLog s z - anchoredLog s x)) := htz.sub htx
  have hshift : Filter.Tendsto (fun L : ℕ => K + 1 + L) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun L => Nat.le_add_left L (K + 1)) Filter.tendsto_id
  have hconst : Filter.Tendsto
      (fun L : ℕ => (anchoredPartialSum s.val (K + 1 + L) z -
          anchoredPartialSum s.val (K + 1 + L) x) -
        ∑ k ∈ Finset.range (K + 1), (s.val k z - s.val k x))
      Filter.atTop
      (nhds ((anchoredLog s z - anchoredLog s x) -
        ∑ k ∈ Finset.range (K + 1), (s.val k z - s.val k x))) :=
    (hdiff.comp hshift).sub_const _
  have hrewrite : ∀ L : ℕ,
      (anchoredPartialSum s.val (K + 1 + L) z - anchoredPartialSum s.val (K + 1 + L) x) -
          ∑ k ∈ Finset.range (K + 1), (s.val k z - s.val k x) =
        ∑ l ∈ Finset.range (L + 1), (s.val (K + 1 + l) z - s.val (K + 1 + l) x) := by
    intro L
    have hsum : anchoredPartialSum s.val (K + 1 + L) z -
        anchoredPartialSum s.val (K + 1 + L) x =
          ∑ k ∈ Finset.range (K + 1 + (L + 1)), (s.val k z - s.val k x) := by
      unfold anchoredPartialSum
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsum, Finset.sum_range_add]
    ring
  have hlimit : (anchoredLog s z - anchoredLog s x) -
      ∑ k ∈ Finset.range (K + 1), (s.val k z - s.val k x) =
        stoppingLogRatio M s K z - stoppingLogRatio M s K x := by
    have hz : Real.log (aAnchored M s z) = anchoredLog s z := by
      rw [aAnchored, Real.log_exp]
    have hx' : Real.log (aAnchored M s x) = anchoredLog s x := by
      rw [aAnchored, Real.log_exp]
    have hcz : Real.log (aCutoff M K s.val z) =
        ∑ k ∈ Finset.range (K + 1), (s.val k z - tauSq M.P) := by
      rw [aCutoff, Real.log_exp]
    have hcx : Real.log (aCutoff M K s.val x) =
        ∑ k ∈ Finset.range (K + 1), (s.val k x - tauSq M.P) := by
      rw [aCutoff, Real.log_exp]
    have hS : ∑ k ∈ Finset.range (K + 1), (s.val k z - s.val k x) =
        (∑ k ∈ Finset.range (K + 1), (s.val k z - tauSq M.P)) -
          ∑ k ∈ Finset.range (K + 1), (s.val k x - tauSq M.P) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    unfold stoppingLogRatio
    rw [hz, hx', hcz, hcx, hS]
    ring
  rw [← hlimit]
  exact hconst.congr hrewrite

/-- The layer-sum envelope transports to the translated sample, `M.P` being translation
invariant. -/
theorem ogammaLE_layerOscSum_translate (M : GMCModel d) (x : Vec d) (n L : ℕ) :
    SubdiffusiveProcess.OGammaLE M.P.toMeasure 2 (oscSumConst d * M.delta)
      (fun omega : PotentialSample d => layerOscSum n L (translatePotentialSample x omega)) :=
  SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_comp_measurePreserving
    (Section6Covariance.measurePreserving_translatePotentialSample M x)
    (measurable_layerOscSum n L).aemeasurable (ogammaLE_layerOscSum M n L)

/-- **The high-frequency comparison, pathwise.**  If every partial layer-sum envelope on the
translated sample is below `c`, the stopping log-ratio increment across the tested cube is
below `c` as well. -/
theorem abs_stoppingLogRatio_sub_le_of_layerOscSum (M : GMCModel d) (s : AnchoredC11Sample d)
    (K : ℕ) (x z : Vec d) (hz : z - x ∈ openCubeSet (originCube d (K : ℤ))) {c : ℝ}
    (hb : ∀ L : ℕ, layerOscSum K L (translatePotentialSample x s.val) ≤ c) :
    |stoppingLogRatio M s K z - stoppingLogRatio M s K x| ≤ c := by
  have htend := (tendsto_stoppingLogRatio_sub M s K x z).abs
  refine le_of_tendsto htend (Filter.Eventually.of_forall ?_)
  intro L
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum ?_) (hb L)
  intro l _
  exact abs_shell_sub_le_shellOscillationEnvelope s.val (K + 1 + l) (K : ℤ) x z hz

/-- **The high-frequency half of the ambient comparison.**  On the tested cube of scale `K`
the probability that the stopping log-ratio moves by more than `c` is a `Γ₂` tail with the
scale `oscSumConst d * delta`, uniform in `K` and in the base point. -/
theorem measureReal_stoppingLogRatio_cube_gt (M : GMCModel d) (x : Vec d) (K : ℕ) {c : ℝ}
    (hc : 0 ≤ c) :
    (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
        (measure_anchoredC11GoodSet_eq_one M)).toMeasure.real
        {s : AnchoredC11Sample d | ∃ z : Vec d, z - x ∈ openCubeSet (originCube d (K : ℤ)) ∧
          c < |stoppingLogRatio M s K z - stoppingLogRatio M s K x|} ≤
      2 * Real.exp (-(((oscSumConst d * M.delta)⁻¹ * c) ^ (2:ℝ))) := by
  classical
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hA : (0:ℝ) < oscSumConst d * M.delta := mul_pos (oscSumConst_pos d) hdelta
  set B : ℝ := 2 * Real.exp (-(((oscSumConst d * M.delta)⁻¹ * c) ^ (2:ℝ))) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  set E : ℕ → Set (PotentialSample d) :=
    fun L => {omega | c < layerOscSum K L (translatePotentialSample x omega)} with hEdef
  have hEmono : Monotone E := by
    intro L L' hL omega homega
    exact lt_of_lt_of_le homega (layerOscSum_mono K hL _)
  have hEmeas : ∀ L, MeasurableSet (E L) := fun L =>
    measurableSet_lt measurable_const
      ((measurable_layerOscSum K L).comp
        (Section6Covariance.measurable_translatePotentialSample x))
  have hEbound : ∀ L, M.P.toMeasure (E L) ≤ ENNReal.ofReal B := by
    intro L
    have hmark := measureReal_ge_le_of_ogammaLE (ogammaLE_layerOscSum_translate M x K L) hA
      (by norm_num) hc
    have hsub : E L ⊆ {omega | c ≤ layerOscSum K L (translatePotentialSample x omega)} := by
      intro omega homega
      have h' : c < layerOscSum K L (translatePotentialSample x omega) := homega
      exact le_of_lt h'
    have hle : M.P.toMeasure.real (E L) ≤ B :=
      le_trans (measureReal_mono hsub (measure_ne_top _ _)) hmark
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hB0).mpr hle
  have hunion : M.P.toMeasure (⋃ L, E L) ≤ ENNReal.ofReal B := by
    rw [hEmono.measure_iUnion]
    exact iSup_le hEbound
  have hinc : {s : AnchoredC11Sample d | ∃ z : Vec d,
        z - x ∈ openCubeSet (originCube d (K : ℤ)) ∧
        c < |stoppingLogRatio M s K z - stoppingLogRatio M s K x|} ⊆
      Subtype.val ⁻¹' (⋃ L, E L) := by
    intro s hs
    obtain ⟨z, hz, hlt⟩ := hs
    by_contra hcon
    simp only [Set.mem_preimage, Set.mem_iUnion, not_exists, hEdef, Set.mem_setOf_eq,
      not_lt] at hcon
    exact absurd (abs_stoppingLogRatio_sub_le_of_layerOscSum M s K x z hz hcon) (not_le.mpr hlt)
  refine le_trans (measureReal_mono hinc (measure_ne_top _ _)) ?_
  have heq : (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
      (measure_anchoredC11GoodSet_eq_one M)).toMeasure (Subtype.val ⁻¹' (⋃ L, E L)) =
      M.P.toMeasure (⋃ L, E L) :=
    anchoredC11SampleLaw_preimage M _ _ _
  unfold Measure.real
  rw [heq]
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hB0).mp hunion

/-- Two cutoff levels differ by the finitely many layers between them. -/
theorem stoppingLogRatio_sub_stoppingLogRatio (M : GMCModel d) (s : AnchoredC11Sample d)
    {n K : ℕ} (hnK : n ≤ K) (w : Vec d) :
    stoppingLogRatio M s n w - stoppingLogRatio M s K w =
      ∑ k ∈ Finset.Ico (n + 1) (K + 1), (s.val k w - tauSq M.P) := by
  have hcn : Real.log (aCutoff M n s.val w) =
      ∑ k ∈ Finset.range (n + 1), (s.val k w - tauSq M.P) := by
    rw [aCutoff, Real.log_exp]
  have hcK : Real.log (aCutoff M K s.val w) =
      ∑ k ∈ Finset.range (K + 1), (s.val k w - tauSq M.P) := by
    rw [aCutoff, Real.log_exp]
  have hIco : ∑ k ∈ Finset.Ico (n + 1) (K + 1), (s.val k w - tauSq M.P) =
      (∑ k ∈ Finset.range (K + 1), (s.val k w - tauSq M.P)) -
        ∑ k ∈ Finset.range (n + 1), (s.val k w - tauSq M.P) :=
    Finset.sum_Ico_eq_sub _ (by omega)
  unfold stoppingLogRatio
  rw [hcn, hcK, hIco]
  ring

/-- **The ambient split.**  Below the ball's own scale `K` the comparison is a finite sum of
layer increments; above it, it is the high-frequency tail already bounded by
`measureReal_stoppingLogRatio_cube_gt`. -/
theorem abs_stoppingLogRatio_sub_le_split (M : GMCModel d) (s : AnchoredC11Sample d)
    {n K : ℕ} (hnK : n ≤ K) (x z : Vec d) :
    |stoppingLogRatio M s n z - stoppingLogRatio M s n x| ≤
      |∑ k ∈ Finset.Ico (n + 1) (K + 1), (s.val k z - s.val k x)| +
        |stoppingLogRatio M s K z - stoppingLogRatio M s K x| := by
  have hz := stoppingLogRatio_sub_stoppingLogRatio M s hnK z
  have hx := stoppingLogRatio_sub_stoppingLogRatio M s hnK x
  have hsum : (∑ k ∈ Finset.Ico (n + 1) (K + 1), (s.val k z - tauSq M.P)) -
      (∑ k ∈ Finset.Ico (n + 1) (K + 1), (s.val k x - tauSq M.P)) =
      ∑ k ∈ Finset.Ico (n + 1) (K + 1), (s.val k z - s.val k x) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hsplit : stoppingLogRatio M s n z - stoppingLogRatio M s n x =
      (∑ k ∈ Finset.Ico (n + 1) (K + 1), (s.val k z - s.val k x)) +
        (stoppingLogRatio M s K z - stoppingLogRatio M s K x) := by
    rw [← hsum, ← hz, ← hx]
    ring
  rw [hsplit]
  exact abs_add_le _ _

/-- A Euclidean ball of radius at most the cube's half-side sits inside the tested cube. -/
theorem sub_mem_openCubeSet_of_mem_euclideanBall {K : ℤ} {x z : Vec d} {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2 * (3 : ℝ) ^ K) (hz : z ∈ euclideanBall x r) :
    z - x ∈ openCubeSet (originCube d K) := by
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hsq : ((z - x) i) ^ 2 ≤ vecNormSq (z - x) := sq_apply_le_vecNormSq _ i
  have hball : vecNormSq (z - x) < r ^ 2 := hz
  have hlt : ((z - x) i) ^ 2 < r ^ 2 := lt_of_le_of_lt hsq hball
  have hcoord : (z - x) i = z i - x i := rfl
  constructor
  · nlinarith [hlt, hr, hr0]
  · nlinarith [hlt, hr, hr0]

/-- **The high-frequency half on the tested ball.**  Combining the cube estimate with the
containment of the ball in the cube of the same scale. -/
theorem measureReal_stoppingLogRatio_ball_gt (M : GMCModel d) (x : Vec d) (K : ℕ) {r c : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2 * (3 : ℝ) ^ (K : ℤ)) (hc : 0 ≤ c) :
    (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
        (measure_anchoredC11GoodSet_eq_one M)).toMeasure.real
        {s : AnchoredC11Sample d | ∃ z ∈ euclideanBall x r,
          c < |stoppingLogRatio M s K z - stoppingLogRatio M s K x|} ≤
      2 * Real.exp (-(((oscSumConst d * M.delta)⁻¹ * c) ^ (2:ℝ))) := by
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
    (measureReal_stoppingLogRatio_cube_gt M x K hc)
  rintro s ⟨z, hz, hlt⟩
  exact ⟨z, sub_mem_openCubeSet_of_mem_euclideanBall hr0 hr hz, hlt⟩

/-! ### The low-frequency half: independent layers, and the mesh -/

/-- The `Γ₂` scale of one layer increment between two fixed points. -/
def shellIncrementConst (M : GMCModel d) : ℝ :=
  (1 + Real.log 2) ^ (2:ℝ)⁻¹ * (M.delta + M.delta)

theorem shellIncrementConst_pos (M : GMCModel d) : 0 < shellIncrementConst M := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hlog : 0 < 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
  exact mul_pos (Real.rpow_pos_of_pos hlog _) (by linarith)

/-- **A single layer increment is sub-Gaussian at the scale of the layer itself**, with no
loss in the distance between the two points: `(g2)` bounds each fixed evaluation. -/
theorem isBigO_shellIncrement (M : GMCModel d) (k : ℕ) (x y : Vec d) :
    IsBigO M.P.toMeasure (gammaSigma 2)
      (fun omega : PotentialSample d => omega k y - omega k x) (shellIncrementConst M) := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hy := ogammaLE_abs_potentialCoordinate_apply M k y
  have hx := ogammaLE_abs_potentialCoordinate_apply M k x
  have hmy : AEMeasurable (fun omega : PotentialSample d => |omega k y|) M.P.toMeasure :=
    (((PotentialField.measurable_eval y).comp
      (measurable_potentialCoordinate (d := d) k)).abs).aemeasurable
  have hmx : AEMeasurable (fun omega : PotentialSample d => |omega k x|) M.P.toMeasure :=
    (((PotentialField.measurable_eval x).comp
      (measurable_potentialCoordinate (d := d) k)).abs).aemeasurable
  have hsum := ogammaLE_two_add hdelta hdelta hmy hmx
    (fun _ => abs_nonneg _) (fun _ => abs_nonneg _) hy hx
  have hbig := SubdiffusiveProcess.OGammaBridge.isBigO_gammaSigma_of_ogammaLE
    (μ := M.P.toMeasure) (σ := 2) (A := M.delta + M.delta)
    (X := fun omega : PotentialSample d => |omega k y| + |omega k x|)
    (by norm_num) (by linarith) (fun _ => by positivity) hsum
  unfold IsBigO at hbig ⊢
  refine IsBigOWith.of_le hbig ?_
  intro omega
  have habs : |omega k y - omega k x| ≤ |omega k y| + |omega k x| := abs_sub _ _
  calc |omega k y - omega k x| ≤ |omega k y| + |omega k x| := habs
    _ = |(|omega k y| + |omega k x|)| := (abs_of_nonneg (by positivity)).symm

/-- **The low-frequency sum at a mesh point.**  Independence of the layers and the centring of
each layer turn the `ℓ¹` count `card` into the `ℓ²` count `√card`: this is the source's
"independence of the layers gives a sub-Gaussian parameter `C δ √V_{a,j}`". -/
theorem exists_ogammaLE_shellIncrementSum_pair (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : GMCModel d) (x y : Vec d) (s : Finset ℕ), s.Nonempty →
      SubdiffusiveProcess.OGammaLE M.P.toMeasure 2 (C * Real.sqrt (s.card : ℝ) * shellIncrementConst M)
        (fun omega : PotentialSample d => ∑ k ∈ s, (omega k y - omega k x)) := by
  obtain ⟨C, hC, hengine⟩ := Section11.exists_ogammaLE_shellFamilySum d
  refine ⟨C, hC, ?_⟩
  intro M x y s hs
  refine hengine M (fun k omega => omega k y - omega k x) s (shellIncrementConst M) hs
    (shellIncrementConst_pos M) ?_ ?_ ?_ ?_
  · intro k
    exact ⟨fun g => g y - g x,
      (PotentialField.measurable_eval y).sub (PotentialField.measurable_eval x), fun _ => rfl⟩
  · intro k
    exact ((PotentialField.measurable_eval y).comp (measurable_potentialCoordinate k)).sub
      ((PotentialField.measurable_eval x).comp (measurable_potentialCoordinate k))
  · intro k _
    rw [integral_sub (Section11.integrable_shell_apply M k y)
        (Section11.integrable_shell_apply M k x),
      Section11.integral_shell_apply_eq_zero M k y,
      Section11.integral_shell_apply_eq_zero M k x, sub_zero]
  · intro k _
    exact isBigO_shellIncrement M k x y

/-! ### The scale-`3^n` mesh of the tested ball -/

/-- Coordinate control from the Euclidean ball. -/
theorem abs_sub_lt_of_mem_euclideanBall {x z : Vec d} {r : ℝ} (hr : 0 ≤ r)
    (hz : z ∈ euclideanBall x r) (i : Fin d) : |z i - x i| < r := by
  have hsq : ((z - x) i) ^ 2 ≤ vecNormSq (z - x) := sq_apply_le_vecNormSq _ i
  have hball : vecNormSq (z - x) < r ^ 2 := hz
  have hcoord : (z - x) i = z i - x i := rfl
  rw [hcoord] at hsq
  have hlt : (z i - x i) ^ 2 < r ^ 2 := lt_of_le_of_lt hsq hball
  rcases abs_cases (z i - x i) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> nlinarith [hlt, hr]

/-- The mesh offsets: a cube of integer shifts of side `2N + 1`. -/
def ambientMeshShifts (d N : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) (N : ℤ)

theorem card_ambientMeshShifts (d N : ℕ) :
    (ambientMeshShifts d N).card = (2 * N + 1) ^ d := by
  classical
  rw [ambientMeshShifts, Fintype.card_piFinset]
  have hone : ∀ _i : Fin d, (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
    intro _
    rw [Int.card_Icc]
    omega
  rw [Finset.prod_congr rfl (fun i _ => hone i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The mesh point attached to an offset. -/
def ambientMeshPoint (n : ℕ) (x : Vec d) (p : Fin d → ℤ) : Vec d :=
  fun i => x i + ((3:ℝ) ^ n / 2) * (p i : ℝ)

/-- **The mesh covers the ball**: every point of `B_r(x)` lies in the scale-`3^n` cube around
some mesh point, provided the mesh has `⌈2r/3^n⌉` steps in each direction. -/
theorem exists_ambientMeshPoint (n : ℕ) (x : Vec d) {r : ℝ} (hr : 0 ≤ r) {z : Vec d}
    (hz : z ∈ euclideanBall x r) (N : ℕ) (hN : 2 * r / (3:ℝ) ^ n ≤ (N : ℝ)) :
    ∃ p ∈ ambientMeshShifts d N,
      z - ambientMeshPoint n x p ∈ openCubeSet (originCube d (n : ℤ)) := by
  classical
  have h3 : (0:ℝ) < (3:ℝ) ^ n := by positivity
  set p : Fin d → ℤ := fun i => round (2 * (z i - x i) / (3:ℝ) ^ n) with hp
  have hround : ∀ i, |2 * (z i - x i) / (3:ℝ) ^ n - (p i : ℝ)| ≤ 1 / 2 := by
    intro i
    exact abs_sub_round _
  have hmem : p ∈ ambientMeshShifts d N := by
    rw [ambientMeshShifts, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hlt := abs_sub_lt_of_mem_euclideanBall hr hz i
    have hquot : |2 * (z i - x i) / (3:ℝ) ^ n| ≤ 2 * r / (3:ℝ) ^ n := by
      rw [abs_div, abs_of_pos h3, abs_mul, abs_two]
      gcongr
    have hb : |(p i : ℝ)| ≤ (N : ℝ) + 1 / 2 := by
      have := abs_sub_abs_le_abs_sub (2 * (z i - x i) / (3:ℝ) ^ n) ((p i : ℝ))
      have h2 := hround i
      have h3' : |2 * (z i - x i) / (3:ℝ) ^ n| ≤ (N : ℝ) := le_trans hquot hN
      rcases abs_cases ((p i : ℝ)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
        [skip; skip] <;> cases abs_cases (2 * (z i - x i) / (3:ℝ) ^ n) with
        | inl h => rw [h.1] at h3'; rw [abs_sub_comm] at h2;
                   rcases abs_le.mp h2 with ⟨hl, hu⟩; linarith
        | inr h => rw [h.1] at h3'; rw [abs_sub_comm] at h2;
                   rcases abs_le.mp h2 with ⟨hl, hu⟩; linarith
    have hbZ : |p i| ≤ (N : ℤ) := by
      have hcast : ((|p i| : ℤ) : ℝ) ≤ ((N : ℤ) : ℝ) + 1 / 2 := by
        push_cast
        exact hb
      by_contra hcon
      push_neg at hcon
      have : ((N : ℤ) : ℝ) + 1 ≤ ((|p i| : ℤ) : ℝ) := by exact_mod_cast hcon
      linarith
    rcases abs_le.mp hbZ with ⟨hl, hu⟩
    exact ⟨hl, hu⟩
  refine ⟨p, hmem, ?_⟩
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hcoord : (z - ambientMeshPoint n x p) i = (z i - x i) - ((3:ℝ) ^ n / 2) * (p i : ℝ) := by
    show z i - (x i + ((3:ℝ) ^ n / 2) * (p i : ℝ)) = _
    ring
  have hkey : |(z i - x i) - ((3:ℝ) ^ n / 2) * (p i : ℝ)| ≤ (3:ℝ) ^ n / 4 := by
    have h2 := hround i
    have hfac : (z i - x i) - ((3:ℝ) ^ n / 2) * (p i : ℝ) =
        ((3:ℝ) ^ n / 2) * (2 * (z i - x i) / (3:ℝ) ^ n - (p i : ℝ)) := by
      field_simp
    rw [hfac, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (3:ℝ) ^ n / 2)]
    nlinarith [h2, h3]
  have hzpow : (3:ℝ) ^ ((n : ℤ)) = (3:ℝ) ^ n := by
    rw [zpow_natCast]
  rw [hcoord, hzpow]
  rcases abs_le.mp hkey with ⟨hl, hu⟩
  constructor <;> nlinarith [h3]

/-! ### The mesh union bound, and the two halves joined -/

/-- Inside one mesh cube the finite low-frequency sum is below the layer-oscillation sum. -/
theorem abs_sum_Ico_sub_le_layerOscSum (omega : PotentialSample d) (n K : ℕ) (hnK : n < K)
    (y z : Vec d) (hz : z - y ∈ openCubeSet (originCube d (n : ℤ))) :
    |∑ k ∈ Finset.Ico (n + 1) (K + 1), (omega k z - omega k y)| ≤
      layerOscSum n (K - n - 1) (translatePotentialSample y omega) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hrange : ∑ k ∈ Finset.Ico (n + 1) (K + 1), |omega k z - omega k y| =
      ∑ l ∈ Finset.range (K - n), |omega (n + 1 + l) z - omega (n + 1 + l) y| := by
    have hnn : K + 1 - (n + 1) = K - n := by omega
    rw [Finset.sum_Ico_eq_sum_range, hnn]
  have hL : K - n = (K - n - 1) + 1 := by omega
  rw [hrange, hL]
  refine Finset.sum_le_sum ?_
  intro l _
  exact abs_shell_sub_le_shellOscillationEnvelope omega (n + 1 + l) (n : ℤ) y z hz

/-- **The low-frequency half of the ambient comparison.**  A union bound over the scale-`3^n`
mesh of the tested ball: inside each mesh cube the geometric layer-oscillation sum takes over,
and at each mesh point the independent layers give the `√card` scale. -/
theorem exists_measureReal_ambientLowFrequency (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : GMCModel d) (x : Vec d) (n K N : ℕ) (r c : ℝ),
      0 ≤ r → 2 * r / (3:ℝ) ^ n ≤ (N : ℝ) → 0 ≤ c → n < K →
      M.P.toMeasure.real
          {omega : PotentialSample d | ∃ z ∈ euclideanBall x r,
            c < |∑ k ∈ Finset.Ico (n + 1) (K + 1), (omega k z - omega k x)|} ≤
        (((2 * N + 1) ^ d : ℕ) : ℝ) *
          (2 * Real.exp (-(((oscSumConst d * M.delta)⁻¹ * (c / 2)) ^ (2:ℝ))) +
            4 * Real.exp (-(((C * Real.sqrt (((K - n : ℕ)) : ℝ) * shellIncrementConst M)⁻¹ *
              (c / 2)) ^ (2:ℝ)))) := by
  classical
  obtain ⟨C, hC, hpair⟩ := exists_ogammaLE_shellIncrementSum_pair d
  refine ⟨C, hC, ?_⟩
  intro M x n K N r c hr hN hc hnK
  set s : Finset ℕ := Finset.Ico (n + 1) (K + 1) with hsdef
  have hs : s.Nonempty := ⟨n + 1, by rw [hsdef, Finset.mem_Ico]; omega⟩
  have hscard : s.card = K - n := by rw [hsdef, Nat.card_Ico]; omega
  have hKn : 0 < K - n := by omega
  have hKnR : (0:ℝ) < ((K - n : ℕ) : ℝ) := by exact_mod_cast hKn
  set A1 : ℝ := oscSumConst d * M.delta with hA1
  have hA1pos : 0 < A1 := mul_pos (oscSumConst_pos d) M.shellPrefix.delta_pos
  set A2 : ℝ := C * Real.sqrt (((K - n : ℕ)) : ℝ) * shellIncrementConst M with hA2
  have hA2pos : 0 < A2 := by
    rw [hA2]
    exact mul_pos (mul_pos hC (Real.sqrt_pos.mpr hKnR)) (shellIncrementConst_pos M)
  have hc2 : (0:ℝ) ≤ c / 2 := by linarith
  set y : (Fin d → ℤ) → Vec d := fun p => ambientMeshPoint n x p with hy
  set E : (Fin d → ℤ) → Set (PotentialSample d) := fun p =>
    {omega | c / 2 ≤ layerOscSum n (K - n - 1) (translatePotentialSample (y p) omega)} ∪
      ({omega | c / 2 ≤ ∑ k ∈ s, (omega k (y p) - omega k x)} ∪
        {omega | c / 2 ≤ ∑ k ∈ s, (omega k x - omega k (y p))}) with hE
  have hsub : {omega : PotentialSample d | ∃ z ∈ euclideanBall x r,
      c < |∑ k ∈ s, (omega k z - omega k x)|} ⊆ ⋃ p ∈ ambientMeshShifts d N, E p := by
    rintro omega ⟨z, hz, hlt⟩
    obtain ⟨p, hp, hcube⟩ := exists_ambientMeshPoint n x hr hz N hN
    refine Set.mem_biUnion hp ?_
    have hsplit : ∑ k ∈ s, (omega k z - omega k x) =
        (∑ k ∈ s, (omega k z - omega k (y p))) + ∑ k ∈ s, (omega k (y p) - omega k x) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have htri : |∑ k ∈ s, (omega k z - omega k x)| ≤
        |∑ k ∈ s, (omega k z - omega k (y p))| + |∑ k ∈ s, (omega k (y p) - omega k x)| := by
      rw [hsplit]
      exact abs_add_le _ _
    by_cases hfirst : c / 2 ≤ |∑ k ∈ s, (omega k z - omega k (y p))|
    · refine Or.inl ?_
      show c / 2 ≤ layerOscSum n (K - n - 1) (translatePotentialSample (y p) omega)
      exact le_trans hfirst
        (abs_sum_Ico_sub_le_layerOscSum omega n K hnK (y p) z hcube)
    · refine Or.inr ?_
      push_neg at hfirst
      have hsecond : c / 2 < |∑ k ∈ s, (omega k (y p) - omega k x)| := by linarith
      rcases le_or_gt (c / 2) (∑ k ∈ s, (omega k (y p) - omega k x)) with hpos | hneg
      · exact Or.inl hpos
      · refine Or.inr ?_
        show c / 2 ≤ ∑ k ∈ s, (omega k x - omega k (y p))
        have hneg' : ∑ k ∈ s, (omega k x - omega k (y p)) =
            -∑ k ∈ s, (omega k (y p) - omega k x) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [hneg']
        rcases abs_cases (∑ k ∈ s, (omega k (y p) - omega k x)) with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he] at hsecond; linarith
        · rw [he] at hsecond; linarith
  have hEbound : ∀ p, M.P.toMeasure.real (E p) ≤
      2 * Real.exp (-((A1⁻¹ * (c / 2)) ^ (2:ℝ))) +
        4 * Real.exp (-((A2⁻¹ * (c / 2)) ^ (2:ℝ))) := by
    intro p
    have h1 : M.P.toMeasure.real
        {omega : PotentialSample d | c / 2 ≤
          layerOscSum n (K - n - 1) (translatePotentialSample (y p) omega)} ≤
        2 * Real.exp (-((A1⁻¹ * (c / 2)) ^ (2:ℝ))) :=
      measureReal_ge_le_of_ogammaLE (ogammaLE_layerOscSum_translate M (y p) n (K - n - 1))
        hA1pos (by norm_num) hc2
    have hpair1 := hpair M x (y p) s hs
    have hpair2 := hpair M (y p) x s hs
    rw [hscard] at hpair1 hpair2
    have h2 : M.P.toMeasure.real
        {omega : PotentialSample d | c / 2 ≤ ∑ k ∈ s, (omega k (y p) - omega k x)} ≤
        2 * Real.exp (-((A2⁻¹ * (c / 2)) ^ (2:ℝ))) :=
      measureReal_ge_le_of_ogammaLE hpair1 hA2pos (by norm_num) hc2
    have h3 : M.P.toMeasure.real
        {omega : PotentialSample d | c / 2 ≤ ∑ k ∈ s, (omega k x - omega k (y p))} ≤
        2 * Real.exp (-((A2⁻¹ * (c / 2)) ^ (2:ℝ))) :=
      measureReal_ge_le_of_ogammaLE hpair2 hA2pos (by norm_num) hc2
    have hu2 := measureReal_union_le (μ := M.P.toMeasure)
      {omega : PotentialSample d | c / 2 ≤ ∑ k ∈ s, (omega k (y p) - omega k x)}
      {omega : PotentialSample d | c / 2 ≤ ∑ k ∈ s, (omega k x - omega k (y p))}
    have hu1 := measureReal_union_le (μ := M.P.toMeasure)
      {omega : PotentialSample d | c / 2 ≤
        layerOscSum n (K - n - 1) (translatePotentialSample (y p) omega)}
      ({omega : PotentialSample d | c / 2 ≤ ∑ k ∈ s, (omega k (y p) - omega k x)} ∪
        {omega : PotentialSample d | c / 2 ≤ ∑ k ∈ s, (omega k x - omega k (y p))})
    rw [hE]
    linarith
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_biUnion_finset_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun p _ => hEbound p) ?_
  rw [Finset.sum_const, card_ambientMeshShifts, nsmul_eq_mul]

/-- **The ambient comparison at one tested scale.**  The two halves, joined at the ball's own
scale `K`: below `K` the mesh union bound, above `K` the geometric envelope. -/
theorem exists_measureReal_ambient_perScale (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : GMCModel d) (x : Vec d) (n K N : ℕ) (r c : ℝ),
      0 ≤ r → 2 * r / (3:ℝ) ^ n ≤ (N : ℝ) → r ≤ 1 / 2 * (3:ℝ) ^ (K : ℤ) → 0 ≤ c → n < K →
      (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
          (measure_anchoredC11GoodSet_eq_one M)).toMeasure.real
          {s : AnchoredC11Sample d | ∃ z ∈ euclideanBall x r,
            c < |stoppingLogRatio M s n z - stoppingLogRatio M s n x|} ≤
        (((2 * N + 1) ^ d : ℕ) : ℝ) *
            (2 * Real.exp (-(((oscSumConst d * M.delta)⁻¹ * (c / 4)) ^ (2:ℝ))) +
              4 * Real.exp (-(((C * Real.sqrt (((K - n : ℕ)) : ℝ) * shellIncrementConst M)⁻¹ *
                (c / 4)) ^ (2:ℝ)))) +
          2 * Real.exp (-(((oscSumConst d * M.delta)⁻¹ * (c / 2)) ^ (2:ℝ))) := by
  classical
  obtain ⟨C, hC, hlow⟩ := exists_measureReal_ambientLowFrequency d
  refine ⟨C, hC, ?_⟩
  intro M x n K N r c hr hN hball hc hnK
  have hsub : {s : AnchoredC11Sample d | ∃ z ∈ euclideanBall x r,
      c < |stoppingLogRatio M s n z - stoppingLogRatio M s n x|} ⊆
      (Subtype.val ⁻¹' {omega : PotentialSample d | ∃ z ∈ euclideanBall x r,
        c / 2 < |∑ k ∈ Finset.Ico (n + 1) (K + 1), (omega k z - omega k x)|}) ∪
      {s : AnchoredC11Sample d | ∃ z ∈ euclideanBall x r,
        c / 2 < |stoppingLogRatio M s K z - stoppingLogRatio M s K x|} := by
    rintro s ⟨z, hz, hlt⟩
    have hsplit := abs_stoppingLogRatio_sub_le_split M s (le_of_lt hnK) x z
    by_cases hfirst : c / 2 < |∑ k ∈ Finset.Ico (n + 1) (K + 1), (s.val k z - s.val k x)|
    · exact Or.inl ⟨z, hz, hfirst⟩
    · push_neg at hfirst
      exact Or.inr ⟨z, hz, by linarith⟩
  have heq : (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
      (measure_anchoredC11GoodSet_eq_one M)).toMeasure
      (Subtype.val ⁻¹' {omega : PotentialSample d | ∃ z ∈ euclideanBall x r,
        c / 2 < |∑ k ∈ Finset.Ico (n + 1) (K + 1), (omega k z - omega k x)|}) =
      M.P.toMeasure {omega : PotentialSample d | ∃ z ∈ euclideanBall x r,
        c / 2 < |∑ k ∈ Finset.Ico (n + 1) (K + 1), (omega k z - omega k x)|} :=
    anchoredC11SampleLaw_preimage M _ _ _
  have hSLbound : (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
      (measure_anchoredC11GoodSet_eq_one M)).toMeasure.real
      (Subtype.val ⁻¹' {omega : PotentialSample d | ∃ z ∈ euclideanBall x r,
        c / 2 < |∑ k ∈ Finset.Ico (n + 1) (K + 1), (omega k z - omega k x)|}) ≤
      (((2 * N + 1) ^ d : ℕ) : ℝ) *
        (2 * Real.exp (-(((oscSumConst d * M.delta)⁻¹ * (c / 4)) ^ (2:ℝ))) +
          4 * Real.exp (-(((C * Real.sqrt (((K - n : ℕ)) : ℝ) * shellIncrementConst M)⁻¹ *
            (c / 4)) ^ (2:ℝ)))) := by
    have hhalf : (c / 2) / 2 = c / 4 := by ring
    have := hlow M x n K N r (c / 2) hr hN (by linarith) hnK
    rw [hhalf] at this
    unfold Measure.real
    rw [heq]
    exact this
  have hSHbound : (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
      (measure_anchoredC11GoodSet_eq_one M)).toMeasure.real
      {s : AnchoredC11Sample d | ∃ z ∈ euclideanBall x r,
        c / 2 < |stoppingLogRatio M s K z - stoppingLogRatio M s K x|} ≤
      2 * Real.exp (-(((oscSumConst d * M.delta)⁻¹ * (c / 2)) ^ (2:ℝ))) :=
    measureReal_stoppingLogRatio_ball_gt M x K hr hball (by linarith)
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_union_le _ _) ?_
  linarith

/-! ### Measurability in the sample -/

theorem measurable_anchoredPartialSum_apply (L : ℕ) (z : Vec d) :
    Measurable (fun s : AnchoredC11Sample d => anchoredPartialSum s.val L z) := by
  unfold anchoredPartialSum
  refine Finset.measurable_sum _ ?_
  intro k _
  exact (((PotentialField.measurable_eval z).comp
      ((measurable_potentialCoordinate k).comp measurable_subtype_coe)).sub
    ((PotentialField.measurable_eval 0).comp
      ((measurable_potentialCoordinate k).comp measurable_subtype_coe)))

/-- **The selected anchored potential is measurable in the sample**, even though it is defined
by `Classical.choose`: it is the pointwise limit of the measurable partial sums. -/
theorem measurable_anchoredLog_apply (z : Vec d) :
    Measurable (fun s : AnchoredC11Sample d => anchoredLog s z) := by
  have hlim : ∀ s : AnchoredC11Sample d,
      Filter.Tendsto (fun L : ℕ => anchoredPartialSum s.val L z) Filter.atTop
        (nhds (anchoredLog s z)) := by
    intro s
    have hspec := anchoredLog_spec s
    have hcompact : IsCompact ({z} : Set (Vec d)) := isCompact_singleton
    exact (hspec.value_tendsto _ hcompact).tendsto_at (Set.mem_singleton z)
  refine measurable_of_tendsto_metrizable
    (fun L => measurable_anchoredPartialSum_apply L z) ?_
  exact tendsto_pi_nhds.mpr hlim

theorem measurable_aAnchored_apply (M : GMCModel d) (z : Vec d) :
    Measurable (fun s : AnchoredC11Sample d => aAnchored M s z) :=
  Real.measurable_exp.comp (measurable_anchoredLog_apply z)

/-- **The stopping log-ratio is measurable in the sample**, which discharges the hypothesis of
`WeightedStoppingLevel.measurableSet_stoppingAmbientFailure`. -/
theorem measurable_stoppingLogRatio (M : GMCModel d) (n : ℕ) (z : Vec d) :
    Measurable (fun s : AnchoredC11Sample d => stoppingLogRatio M s n z) := by
  have heq : (fun s : AnchoredC11Sample d => stoppingLogRatio M s n z) =
      fun s : AnchoredC11Sample d => anchoredLog s z -
        ∑ k ∈ Finset.range (n + 1), (s.val k z - tauSq M.P) := by
    funext s
    unfold stoppingLogRatio
    rw [aAnchored, Real.log_exp, aCutoff, Real.log_exp]
  rw [heq]
  refine (measurable_anchoredLog_apply z).sub ?_
  refine Finset.measurable_sum _ ?_
  intro k _
  exact ((PotentialField.measurable_eval z).comp
    ((measurable_potentialCoordinate k).comp measurable_subtype_coe)).sub measurable_const

/-! ### The schedule instantiation -/

/-- Twice the scale-free part of the tested radius, `2C(m+2)^{a+1}e^{(a+1)h+j}`. -/
def ambientRadiusFactor (C : ℝ) (m h a j : ℕ) : ℝ :=
  2 * C * (((m : ℝ) + 2) ^ (a + 1) * Real.exp (((a + 1 : ℕ) : ℝ) * h + j))

theorem ambientRadiusFactor_pos {C : ℝ} (hC : 0 < C) (m h a j : ℕ) :
    0 < ambientRadiusFactor C m h a j := by
  unfold ambientRadiusFactor
  have h1 : (0:ℝ) < ((m : ℝ) + 2) ^ (a + 1) := by positivity
  have h2 : (0:ℝ) < Real.exp (((a + 1 : ℕ) : ℝ) * h + j) := Real.exp_pos _
  positivity

/-- The mesh count of the tested ball: `⌈2C(m+2)^{a+1}e^{(a+1)h+j}⌉`, independent of `n`. -/
def ambientMeshCount (C : ℝ) (m h a j : ℕ) : ℕ := ⌈ambientRadiusFactor C m h a j⌉₊

/-- The source's crossover `k_0`, the least power of three above the radius factor.  Its
value is comparable to `V_{a,j}`, and it is independent of `n`. -/
def ambientCrossover (C : ℝ) (m h a j : ℕ) : ℕ :=
  ⌈Real.log (ambientRadiusFactor C m h a j) / Real.log 3⌉₊ + 1

theorem one_le_ambientCrossover (C : ℝ) (m h a j : ℕ) : 1 ≤ ambientCrossover C m h a j := by
  unfold ambientCrossover; omega

theorem ambientRadiusFactor_le_three_pow {C : ℝ} (hC : 0 < C) (m h a j : ℕ) :
    ambientRadiusFactor C m h a j ≤ (3 : ℝ) ^ ambientCrossover C m h a j := by
  set F : ℝ := ambientRadiusFactor C m h a j with hF
  have hFpos : 0 < F := ambientRadiusFactor_pos hC m h a j
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hpow : (3 : ℝ) ^ ambientCrossover C m h a j =
      Real.exp ((ambientCrossover C m h a j : ℝ) * Real.log 3) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num : (0:ℝ) < 3),
      Real.rpow_natCast]
  rw [hpow, ← Real.exp_log hFpos]
  refine Real.exp_le_exp.mpr ?_
  have hceil : Real.log F / Real.log 3 ≤ (⌈Real.log F / Real.log 3⌉₊ : ℝ) ∨
      Real.log F / Real.log 3 ≤ 0 := by
    rcases le_or_gt (Real.log F / Real.log 3) 0 with hle | hgt
    · exact Or.inr hle
    · exact Or.inl (Nat.le_ceil _)
  have hbound : Real.log F / Real.log 3 ≤ (ambientCrossover C m h a j : ℝ) := by
    unfold ambientCrossover
    push_cast
    rcases hceil with hc | hc
    · linarith [Nat.cast_nonneg (α := ℝ) ⌈Real.log F / Real.log 3⌉₊]
    · have : (0:ℝ) ≤ (⌈Real.log F / Real.log 3⌉₊ : ℝ) := Nat.cast_nonneg _
      linarith
  calc Real.log F = (Real.log F / Real.log 3) * Real.log 3 := by field_simp
    _ ≤ (ambientCrossover C m h a j : ℝ) * Real.log 3 :=
        mul_le_mul_of_nonneg_right hbound hlog3.le

theorem radius_le_half_three_pow {C : ℝ} (hC : 0 < C) (m h a j n : ℕ) :
    C * stoppingTestRadius m h a j n ≤
      1 / 2 * (3 : ℝ) ^ ((n + ambientCrossover C m h a j : ℕ) : ℤ) := by
  have hkey := ambientRadiusFactor_le_three_pow hC m h a j
  have h3n : (0:ℝ) < (3:ℝ) ^ n := by positivity
  have hz : (3 : ℝ) ^ ((n + ambientCrossover C m h a j : ℕ) : ℤ) =
      (3:ℝ) ^ n * (3:ℝ) ^ ambientCrossover C m h a j := by
    rw [zpow_natCast, pow_add]
  rw [hz]
  unfold stoppingTestRadius ambientRadiusFactor at *
  nlinarith [hkey, h3n]

theorem mesh_count_bound {C : ℝ} (hC : 0 < C) (m h a j n : ℕ) :
    2 * (C * stoppingTestRadius m h a j n) / (3:ℝ) ^ n ≤
      (ambientMeshCount C m h a j : ℝ) := by
  have h3n : (0:ℝ) < (3:ℝ) ^ n := by positivity
  have heq : 2 * (C * stoppingTestRadius m h a j n) / (3:ℝ) ^ n =
      ambientRadiusFactor C m h a j := by
    unfold stoppingTestRadius ambientRadiusFactor
    field_simp
  rw [heq]
  exact Nat.le_ceil _

/-- **The ambient group of Step 2, at the schedule.**  The crossover `k_0` and the mesh count
are read off the schedule: both are independent of the tested scale `n`, so `K - n = k_0` and
the mesh cardinality are the same at every tested scale, and the union over
`n ≤ stoppingTestScale` costs only the factor `stoppingTestScale + 1`. -/
theorem exists_measureReal_stoppingAmbientFailure_bound (d : ℕ) :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ (M : GMCModel d) (B C : ℝ) (m h : ℕ) (x : Vec d) (a j : ℕ),
      0 < C → 0 ≤ B * (stoppingTestHeight h a j : ℝ) →
      (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
          (measure_anchoredC11GoodSet_eq_one M)).toMeasure.real
          (stoppingAmbientFailure M B C m h x a j) ≤
        ((stoppingTestScale m h a j + 1 : ℕ) : ℝ) *
          ((((2 * ambientMeshCount C m h a j + 1) ^ d : ℕ) : ℝ) *
              (2 * Real.exp (-(((oscSumConst d * M.delta)⁻¹ *
                  (B * (stoppingTestHeight h a j : ℝ) / 4)) ^ (2:ℝ))) +
                4 * Real.exp (-(((Cs * Real.sqrt ((ambientCrossover C m h a j : ℕ) : ℝ) *
                  shellIncrementConst M)⁻¹ *
                  (B * (stoppingTestHeight h a j : ℝ) / 4)) ^ (2:ℝ)))) +
            2 * Real.exp (-(((oscSumConst d * M.delta)⁻¹ *
              (B * (stoppingTestHeight h a j : ℝ) / 2)) ^ (2:ℝ)))) := by
  classical
  obtain ⟨Cs, hCs, hper⟩ := exists_measureReal_ambient_perScale d
  refine ⟨Cs, hCs, ?_⟩
  intro M B C m h x a j hC hBH
  set k0 : ℕ := ambientCrossover C m h a j with hk0
  set N : ℕ := ambientMeshCount C m h a j with hN
  set c : ℝ := B * (stoppingTestHeight h a j : ℝ) with hc
  set E : ℕ → Set (AnchoredC11Sample d) := fun n =>
    {s : AnchoredC11Sample d | ∃ z ∈ euclideanBall x (C * stoppingTestRadius m h a j n),
      c < |stoppingLogRatio M s n z - stoppingLogRatio M s n x|} with hE
  have hsub : stoppingAmbientFailure M B C m h x a j ⊆
      ⋃ n ∈ Finset.range (stoppingTestScale m h a j + 1), E n := by
    rintro s ⟨n, hn, z, hz, hlt⟩
    exact Set.mem_biUnion (Finset.mem_range.mpr (by omega)) ⟨z, hz, hlt⟩
  have hEbound : ∀ n : ℕ, (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
      (measure_anchoredC11GoodSet_eq_one M)).toMeasure.real (E n) ≤
      (((2 * N + 1) ^ d : ℕ) : ℝ) *
          (2 * Real.exp (-(((oscSumConst d * M.delta)⁻¹ * (c / 4)) ^ (2:ℝ))) +
            4 * Real.exp (-(((Cs * Real.sqrt ((k0 : ℕ) : ℝ) * shellIncrementConst M)⁻¹ *
              (c / 4)) ^ (2:ℝ)))) +
        2 * Real.exp (-(((oscSumConst d * M.delta)⁻¹ * (c / 2)) ^ (2:ℝ))) := by
    intro n
    have hr0 : 0 ≤ C * stoppingTestRadius m h a j n :=
      le_of_lt (mul_pos hC (stoppingTestRadius_pos m h a j n))
    have hmesh := mesh_count_bound hC m h a j n
    have hballle := radius_le_half_three_pow hC m h a j n
    have hlt : n < n + k0 := by
      have := one_le_ambientCrossover C m h a j
      omega
    have hsubn : (n + k0) - n = k0 := by omega
    have := hper M x n (n + k0) N (C * stoppingTestRadius m h a j n) c hr0 hmesh hballle hBH hlt
    rw [hsubn] at this
    exact this
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_biUnion_finset_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun n _ => hEbound n) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### The entropy absorption, and the group in the display's slot -/

/-- The scale-free exponent of the tested radius, `(a+1)log(m+2) + (a+1)h + j`. -/
def ambientRadiusExponent (m h a j : ℕ) : ℝ :=
  ((a + 1 : ℕ) : ℝ) * Real.log ((m : ℝ) + 2) + (((a + 1 : ℕ) : ℝ) * (h : ℝ) + (j : ℝ))

theorem ambientRadiusExponent_nonneg (m h a j : ℕ) : 0 ≤ ambientRadiusExponent m h a j := by
  unfold ambientRadiusExponent
  have hlog : (0:ℝ) ≤ Real.log ((m : ℝ) + 2) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) m; linarith)
  have ha : (0:ℝ) ≤ ((a + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hh : (0:ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hj : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  positivity

/-- The entropy has the radius exponent inside it, with `(a+1) ≥ 1` to spare. -/
theorem ambientRadiusExponent_add_one_le_entropy (m h a j : ℕ) :
    ambientRadiusExponent m h a j + 1 ≤ stoppingTestEntropy m h a j := by
  unfold ambientRadiusExponent stoppingTestEntropy
  have ha : (1:ℝ) ≤ ((a + 1 : ℕ) : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) a
    push_cast
    linarith
  nlinarith [ha]

theorem ambientRadiusExponent_le_entropy (m h a j : ℕ) :
    ambientRadiusExponent m h a j ≤ stoppingTestEntropy m h a j := by
  have := ambientRadiusExponent_add_one_le_entropy m h a j
  linarith

theorem ambientRadiusFactor_eq {C : ℝ} (m h a j : ℕ) :
    ambientRadiusFactor C m h a j = 2 * C * Real.exp (ambientRadiusExponent m h a j) := by
  unfold ambientRadiusFactor ambientRadiusExponent
  have hm : (0:ℝ) < (m : ℝ) + 2 := by positivity
  have hpow : ((m : ℝ) + 2) ^ (a + 1) =
      Real.exp (((a + 1 : ℕ) : ℝ) * Real.log ((m : ℝ) + 2)) := by
    rw [Real.exp_nat_mul, Real.exp_log hm]
  rw [hpow, ← Real.exp_add]

/-- The number of tested scales is below `2 exp` of the radius exponent. -/
theorem stoppingTestScale_succ_le (m h a j : ℕ) :
    ((stoppingTestScale m h a j : ℕ) : ℝ) + 1 ≤
      2 * Real.exp (ambientRadiusExponent m h a j) := by
  have hlog : (0:ℝ) ≤ Real.log ((m : ℝ) + 2) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) m; linarith)
  have ha : (1:ℝ) ≤ ((a + 1 : ℕ) : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) a
    push_cast
    linarith
  have hh : (0:ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hj : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  set W : ℝ := ambientRadiusExponent m h a j with hW
  have hW0 : 0 ≤ W := ambientRadiusExponent_nonneg m h a j
  -- the head `m + 2` is `exp (log (m+2))` and `log (m+2) ≤ W`
  have hmW : Real.log ((m : ℝ) + 2) ≤ W := by
    rw [hW]
    unfold ambientRadiusExponent
    nlinarith [ha, hlog, hh, hj]
  have hm2 : ((m : ℝ) + 2) ≤ Real.exp W := by
    have hm : (0:ℝ) < (m : ℝ) + 2 := by positivity
    calc ((m : ℝ) + 2) = Real.exp (Real.log ((m : ℝ) + 2)) := (Real.exp_log hm).symm
      _ ≤ Real.exp W := Real.exp_le_exp.mpr hmW
  -- the tail `(a+1)h + j` is below `W`, hence below `exp W`
  have htailW : ((a + 1 : ℕ) : ℝ) * (h : ℝ) + (j : ℝ) ≤ W := by
    rw [hW]
    unfold ambientRadiusExponent
    nlinarith [ha, hlog]
  have hWexp : W ≤ Real.exp W := (Real.add_one_le_exp W).trans' (by linarith)
  have hscale : ((stoppingTestScale m h a j : ℕ) : ℝ) + 1 ≤
      ((m : ℝ) + 2) + (((a + 1 : ℕ) : ℝ) * (h : ℝ) + (j : ℝ)) := by
    unfold stoppingTestScale
    push_cast
    have : ((a : ℝ) + 1) * (h : ℝ) = ((a + 1 : ℕ) : ℝ) * (h : ℝ) := by push_cast; ring
    rw [this]
    linarith
  linarith [hscale, hm2, htailW, hWexp]

/-- The mesh side is below a constant times `exp` of the radius exponent. -/
theorem two_mul_ambientMeshCount_succ_le {C : ℝ} (hC : 0 < C) (m h a j : ℕ) :
    2 * ((ambientMeshCount C m h a j : ℕ) : ℝ) + 1 ≤
      (4 * C + 3) * Real.exp (ambientRadiusExponent m h a j) := by
  set W : ℝ := ambientRadiusExponent m h a j with hW
  have hW0 : 0 ≤ W := ambientRadiusExponent_nonneg m h a j
  have hexp1 : (1:ℝ) ≤ Real.exp W := Real.one_le_exp hW0
  have hFpos : 0 < ambientRadiusFactor C m h a j := ambientRadiusFactor_pos hC m h a j
  have hceil : ((ambientMeshCount C m h a j : ℕ) : ℝ) <
      ambientRadiusFactor C m h a j + 1 := by
    unfold ambientMeshCount
    exact Nat.ceil_lt_add_one hFpos.le
  have hFeq : ambientRadiusFactor C m h a j = 2 * C * Real.exp W := by
    rw [hW]; exact ambientRadiusFactor_eq m h a j
  rw [hFeq] at hceil
  nlinarith [hceil, hexp1, hC]

/-- **The ambient entropy absorption.**  The number of tested scales times the mesh
cardinality is `exp (C_count V_{a,j})` for one constant depending only on `d` and `C`. -/
theorem exists_ambientCount_bound (d : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ Ccount : ℝ, 0 < Ccount ∧ ∀ m h a j : ℕ,
      (((stoppingTestScale m h a j : ℕ) : ℝ) + 1) *
          ((((2 * ambientMeshCount C m h a j + 1) ^ d : ℕ)) : ℝ) ≤
        Real.exp (Ccount * stoppingTestEntropy m h a j) := by
  have hbase : (1:ℝ) ≤ 4 * C + 3 := by linarith
  have hlogbase : (0:ℝ) ≤ Real.log (4 * C + 3) := Real.log_nonneg hbase
  refine ⟨Real.log 2 + (d : ℝ) * Real.log (4 * C + 3) + ((d : ℝ) + 1), by positivity, ?_⟩
  intro m h a j
  set W : ℝ := ambientRadiusExponent m h a j with hW
  have hW0 : 0 ≤ W := ambientRadiusExponent_nonneg m h a j
  have hWV : W ≤ stoppingTestEntropy m h a j := ambientRadiusExponent_le_entropy m h a j
  have hV1 : 1 ≤ stoppingTestEntropy m h a j := one_le_stoppingTestEntropy m h a j
  have hexp1 : (1:ℝ) ≤ Real.exp W := Real.one_le_exp hW0
  have hscale := stoppingTestScale_succ_le m h a j
  have hmesh := two_mul_ambientMeshCount_succ_le hC m h a j
  have hcast : ((((2 * ambientMeshCount C m h a j + 1) ^ d : ℕ)) : ℝ) =
      (2 * ((ambientMeshCount C m h a j : ℕ) : ℝ) + 1) ^ d := by push_cast; ring
  have hmeshpow : (2 * ((ambientMeshCount C m h a j : ℕ) : ℝ) + 1) ^ d ≤
      ((4 * C + 3) * Real.exp W) ^ d := by
    refine pow_le_pow_left₀ (by positivity) ?_ d
    rw [← hW] at hmesh
    exact hmesh
  have hprod : (((stoppingTestScale m h a j : ℕ) : ℝ) + 1) *
      ((((2 * ambientMeshCount C m h a j + 1) ^ d : ℕ)) : ℝ) ≤
      (2 * Real.exp W) * ((4 * C + 3) * Real.exp W) ^ d := by
    rw [hcast]
    refine mul_le_mul ?_ hmeshpow (by positivity) (by positivity)
    rw [← hW] at hscale
    exact hscale
  refine le_trans hprod ?_
  have hsplit : ((4 * C + 3) * Real.exp W) ^ d =
      Real.exp ((d : ℝ) * Real.log (4 * C + 3)) * Real.exp ((d : ℝ) * W) := by
    rw [mul_pow, Real.exp_nat_mul, Real.exp_log (by linarith : (0:ℝ) < 4 * C + 3),
      Real.exp_nat_mul]
  have hd : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hlog2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [hsplit]
  have hrw : 2 * Real.exp W *
      (Real.exp ((d : ℝ) * Real.log (4 * C + 3)) * Real.exp ((d : ℝ) * W)) =
      2 * Real.exp (W + ((d : ℝ) * Real.log (4 * C + 3) + (d : ℝ) * W)) := by
    rw [Real.exp_add, Real.exp_add]
    ring
  rw [hrw]
  have h2le : (2:ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
  calc 2 * Real.exp (W + ((d : ℝ) * Real.log (4 * C + 3) + (d : ℝ) * W))
      = Real.exp (Real.log 2) *
          Real.exp (W + ((d : ℝ) * Real.log (4 * C + 3) + (d : ℝ) * W)) := by rw [← h2le]
    _ = Real.exp (Real.log 2 + (W + ((d : ℝ) * Real.log (4 * C + 3) + (d : ℝ) * W))) :=
        (Real.exp_add _ _).symm
    _ ≤ Real.exp ((Real.log 2 + (d : ℝ) * Real.log (4 * C + 3) + ((d : ℝ) + 1)) *
          stoppingTestEntropy m h a j) := by
        refine Real.exp_le_exp.mpr ?_
        have e1 : (0:ℝ) ≤ Real.log 2 * (stoppingTestEntropy m h a j - 1) :=
          mul_nonneg hlog2 (by linarith)
        have e2 : (0:ℝ) ≤ ((d : ℝ) * Real.log (4 * C + 3)) *
            (stoppingTestEntropy m h a j - 1) :=
          mul_nonneg (mul_nonneg hd hlogbase) (by linarith)
        have e3 : (0:ℝ) ≤ ((d : ℝ) + 1) * (stoppingTestEntropy m h a j - W) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith [e1, e2, e3]

/-- **The crossover is comparable to the entropy**, which is the source's "its value is
comparable to `V_{a,j}`". -/
theorem exists_ambientCrossover_le_entropy {C : ℝ} (hC : 0 < C) :
    ∃ c : ℝ, 0 < c ∧ ∀ m h a j : ℕ,
      ((ambientCrossover C m h a j : ℕ) : ℝ) ≤ c * stoppingTestEntropy m h a j := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨|Real.log (2 * C)| / Real.log 3 + 1 / Real.log 3 + 2, by positivity, ?_⟩
  intro m h a j
  set W : ℝ := ambientRadiusExponent m h a j with hW
  have hW0 : 0 ≤ W := ambientRadiusExponent_nonneg m h a j
  have hWV : W ≤ stoppingTestEntropy m h a j := ambientRadiusExponent_le_entropy m h a j
  have hV1 : 1 ≤ stoppingTestEntropy m h a j := one_le_stoppingTestEntropy m h a j
  have hFeq : ambientRadiusFactor C m h a j = 2 * C * Real.exp W := by
    rw [hW]; exact ambientRadiusFactor_eq m h a j
  have hlogF : Real.log (ambientRadiusFactor C m h a j) = Real.log (2 * C) + W := by
    rw [hFeq, Real.log_mul (by positivity) (Real.exp_ne_zero W), Real.log_exp]
  set x : ℝ := Real.log (ambientRadiusFactor C m h a j) / Real.log 3 with hx
  have hxle : x ≤ (|Real.log (2 * C)| + W) / Real.log 3 := by
    rw [hx, hlogF]
    have habs := le_abs_self (Real.log (2 * C))
    gcongr
  have hceil : ((⌈x⌉₊ : ℕ) : ℝ) ≤ (|Real.log (2 * C)| + W) / Real.log 3 + 1 := by
    rcases le_or_gt x 0 with hle | hgt
    · have hz : ⌈x⌉₊ = 0 := Nat.ceil_eq_zero.mpr hle
      rw [hz]
      have hnn : (0:ℝ) ≤ (|Real.log (2 * C)| + W) / Real.log 3 := by positivity
      push_cast
      linarith
    · have := Nat.ceil_lt_add_one (le_of_lt hgt)
      linarith [this, hxle]
  have hk : ((ambientCrossover C m h a j : ℕ) : ℝ) ≤
      (|Real.log (2 * C)| + W) / Real.log 3 + 2 := by
    unfold ambientCrossover
    push_cast
    have : ((⌈Real.log (ambientRadiusFactor C m h a j) / Real.log 3⌉₊ : ℕ) : ℝ) = ((⌈x⌉₊ : ℕ) : ℝ) := by
      rw [hx]
    rw [this]
    linarith [hceil]
  refine le_trans hk ?_
  have hdiv : (|Real.log (2 * C)| + W) / Real.log 3 =
      |Real.log (2 * C)| / Real.log 3 + W / Real.log 3 := by ring
  rw [hdiv]
  have hA : |Real.log (2 * C)| / Real.log 3 ≤
      (|Real.log (2 * C)| / Real.log 3) * stoppingTestEntropy m h a j := by
    have hnn : (0:ℝ) ≤ |Real.log (2 * C)| / Real.log 3 := by positivity
    nlinarith [hV1, hnn]
  have hB : W / Real.log 3 ≤ (1 / Real.log 3) * stoppingTestEntropy m h a j := by
    rw [one_div, inv_mul_eq_div]
    gcongr
  have hC2 : (2:ℝ) ≤ 2 * stoppingTestEntropy m h a j := by linarith
  linarith [hA, hB, hC2]

/-- **The ambient group in the level display's slot.**  After the entropy absorption the
ambient failure has the geometric reserve `e^{-(a+1)-j}` in front of a Gaussian exponent whose
scale is `δ √V_{a,j}` -- the source's
`C exp(-c a²h²/(δ²(h+ℓ_m)) - V_{a,j})`, in the form
`measureReal_stoppingLevelFailure_display` consumes.

The second hypothesis is the Gaussian exponent at the `δ√V` scale rather than at `δ√k_0`:
`exists_ambientCrossover_le_entropy` lets it be stated that way, which is what makes it
comparable with `H²/(δ²(h+ℓ_m))`. -/
theorem exists_measureReal_stoppingAmbientFailure_display (d : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ Cs Ccount ccross : ℝ, 0 < Cs ∧ 0 < Ccount ∧ 0 < ccross ∧
      ∀ (M : GMCModel d) (B G : ℝ) (m h : ℕ) (x : Vec d) (a j : ℕ),
        0 ≤ B * (stoppingTestHeight h a j : ℝ) →
        G ≤ ((oscSumConst d * M.delta)⁻¹ *
              (B * (stoppingTestHeight h a j : ℝ) / 4)) ^ (2:ℝ) →
        G ≤ ((Cs * Real.sqrt (ccross * stoppingTestEntropy m h a j) *
              shellIncrementConst M)⁻¹ *
              (B * (stoppingTestHeight h a j : ℝ) / 4)) ^ (2:ℝ) →
        Ccount * stoppingTestEntropy m h a j + ((a : ℝ) + 1) + (j : ℝ) ≤ G / 2 →
        (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
            (measure_anchoredC11GoodSet_eq_one M)).toMeasure.real
            (stoppingAmbientFailure M B C m h x a j) ≤
          8 * Real.exp (-(G / 2)) * Real.exp (-((a : ℝ) + 1) - (j : ℝ)) := by
  classical
  obtain ⟨Cs, hCs, hbound⟩ := exists_measureReal_stoppingAmbientFailure_bound d
  obtain ⟨Ccount, hCcount, hcount⟩ := exists_ambientCount_bound d hC
  obtain ⟨ccross, hccross, hcross⟩ := exists_ambientCrossover_le_entropy hC
  refine ⟨Cs, Ccount, ccross, hCs, hCcount, hccross, ?_⟩
  intro M B G m h x a j hBH hG1 hG2 hres
  set t : ℝ := B * (stoppingTestHeight h a j : ℝ) with ht
  set A1 : ℝ := oscSumConst d * M.delta with hA1
  have hA1pos : 0 < A1 := mul_pos (oscSumConst_pos d) M.shellPrefix.delta_pos
  set A2 : ℝ := Cs * Real.sqrt ((ambientCrossover C m h a j : ℕ) : ℝ) *
    shellIncrementConst M with hA2
  set A2' : ℝ := Cs * Real.sqrt (ccross * stoppingTestEntropy m h a j) *
    shellIncrementConst M with hA2'
  have hsIC : 0 < shellIncrementConst M := shellIncrementConst_pos M
  have hk1 : (1:ℝ) ≤ ((ambientCrossover C m h a j : ℕ) : ℝ) := by
    have := one_le_ambientCrossover C m h a j
    exact_mod_cast this
  have hA2pos : 0 < A2 := by
    rw [hA2]
    exact mul_pos (mul_pos hCs (Real.sqrt_pos.mpr (by linarith))) hsIC
  have hA2le : A2 ≤ A2' := by
    rw [hA2, hA2']
    have hsq : Real.sqrt ((ambientCrossover C m h a j : ℕ) : ℝ) ≤
        Real.sqrt (ccross * stoppingTestEntropy m h a j) :=
      Real.sqrt_le_sqrt (hcross m h a j)
    have hCsnn : (0:ℝ) ≤ Cs := hCs.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hCsnn) hsIC.le
  -- the three exponents all dominate `G`
  have ht4 : 0 ≤ t / 4 := by linarith
  have hGE2 : G ≤ (A2⁻¹ * (t / 4)) ^ (2:ℝ) := by
    refine le_trans hG2 ?_
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    have hinv : A2'⁻¹ ≤ A2⁻¹ := by
      exact one_div_le_one_div_of_le hA2pos hA2le |>.trans_eq (by rw [one_div]) |>.trans_eq' (by rw [one_div])
    exact mul_le_mul_of_nonneg_right hinv ht4
  have hGE1' : G ≤ (A1⁻¹ * (t / 2)) ^ (2:ℝ) := by
    refine le_trans hG1 ?_
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    have : t / 4 ≤ t / 2 := by linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hexp1 : Real.exp (-((A1⁻¹ * (t / 4)) ^ (2:ℝ))) ≤ Real.exp (-G) :=
    Real.exp_le_exp.mpr (by linarith [hG1])
  have hexp1' : Real.exp (-((A1⁻¹ * (t / 2)) ^ (2:ℝ))) ≤ Real.exp (-G) :=
    Real.exp_le_exp.mpr (by linarith [hGE1'])
  have hexp2 : Real.exp (-((A2⁻¹ * (t / 4)) ^ (2:ℝ))) ≤ Real.exp (-G) :=
    Real.exp_le_exp.mpr (by linarith [hGE2])
  -- the per-scale bound, with every exponential replaced by `e^{-G}`
  have hmain := hbound M B C m h x a j hC hBH
  have hNpow1 : (1:ℝ) ≤ ((((2 * ambientMeshCount C m h a j + 1) ^ d : ℕ)) : ℝ) := by
    have : 1 ≤ (2 * ambientMeshCount C m h a j + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast this
  have hscale1 : (1:ℝ) ≤ ((stoppingTestScale m h a j + 1 : ℕ) : ℝ) := by
    have : 1 ≤ stoppingTestScale m h a j + 1 := by omega
    exact_mod_cast this
  have hstep : ((stoppingTestScale m h a j + 1 : ℕ) : ℝ) *
      (((((2 * ambientMeshCount C m h a j + 1) ^ d : ℕ)) : ℝ) *
          (2 * Real.exp (-((A1⁻¹ * (t / 4)) ^ (2:ℝ))) +
            4 * Real.exp (-((A2⁻¹ * (t / 4)) ^ (2:ℝ)))) +
        2 * Real.exp (-((A1⁻¹ * (t / 2)) ^ (2:ℝ)))) ≤
      (((stoppingTestScale m h a j : ℕ) : ℝ) + 1) *
        ((((2 * ambientMeshCount C m h a j + 1) ^ d : ℕ)) : ℝ) * (8 * Real.exp (-G)) := by
    have hcast : ((stoppingTestScale m h a j + 1 : ℕ) : ℝ) =
        ((stoppingTestScale m h a j : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hinner : ((((2 * ambientMeshCount C m h a j + 1) ^ d : ℕ)) : ℝ) *
        (2 * Real.exp (-((A1⁻¹ * (t / 4)) ^ (2:ℝ))) +
          4 * Real.exp (-((A2⁻¹ * (t / 4)) ^ (2:ℝ)))) +
        2 * Real.exp (-((A1⁻¹ * (t / 2)) ^ (2:ℝ))) ≤
        ((((2 * ambientMeshCount C m h a j + 1) ^ d : ℕ)) : ℝ) * (8 * Real.exp (-G)) := by
      have hsum : 2 * Real.exp (-((A1⁻¹ * (t / 4)) ^ (2:ℝ))) +
          4 * Real.exp (-((A2⁻¹ * (t / 4)) ^ (2:ℝ))) ≤ 6 * Real.exp (-G) := by
        linarith only [hexp1, hexp2]
      have hfirst := mul_le_mul_of_nonneg_left hsum (le_trans zero_le_one hNpow1)
      have hlast := mul_le_mul_of_nonneg_left hexp1' (by norm_num : (0:ℝ) ≤ 2)
      have hreserve := mul_le_mul_of_nonneg_right hNpow1
        (by positivity : (0:ℝ) ≤ 2 * Real.exp (-G))
      nlinarith only [hfirst, hlast, hreserve]
    have hpos : (0:ℝ) ≤ ((stoppingTestScale m h a j : ℕ) : ℝ) + 1 := by positivity
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hinner hpos
  refine le_trans (le_trans hmain hstep) ?_
  -- the entropy absorption and the reserve
  have hcnt := hcount m h a j
  have hexpG : (0:ℝ) < Real.exp (-G) := Real.exp_pos _
  have habs : (((stoppingTestScale m h a j : ℕ) : ℝ) + 1) *
      ((((2 * ambientMeshCount C m h a j + 1) ^ d : ℕ)) : ℝ) * (8 * Real.exp (-G)) ≤
      Real.exp (Ccount * stoppingTestEntropy m h a j) * (8 * Real.exp (-G)) := by
    exact mul_le_mul_of_nonneg_right hcnt (by positivity)
  refine le_trans habs ?_
  have hfin : Real.exp (Ccount * stoppingTestEntropy m h a j) * (8 * Real.exp (-G)) =
      8 * Real.exp (Ccount * stoppingTestEntropy m h a j - G) := by
    rw [Real.exp_sub, Real.exp_neg]
    ring
  rw [hfin]
  have hcomb : 8 * Real.exp (-(G / 2)) * Real.exp (-((a : ℝ) + 1) - (j : ℝ)) =
      8 * Real.exp (-(G / 2) + (-((a : ℝ) + 1) - (j : ℝ))) := by
    rw [Real.exp_add]
    ring
  rw [hcomb]
  have hle : Ccount * stoppingTestEntropy m h a j - G ≤
      -(G / 2) + (-((a : ℝ) + 1) - (j : ℝ)) := by linarith [hres]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (by norm_num)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
