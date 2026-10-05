module

public import SubdiffusiveProcess.Section6.CutoffUniformMoments
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.ProbeMomentNonpos
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.QuenchedProbeStep
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.LogHomogenizedBound

@[expose] public section

/-! Probe moments with constants chosen before the shell law. -/
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab hiding TriadicCube Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
open scoped BigOperators

noncomputable section
namespace SubdiffusiveProcess.Section6
variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem absCoordSum_smul (c : ℝ) (v : Vec d) :
    absCoordSum (c • v) = |c| * absCoordSum v := by
  simp only [absCoordSum, Pi.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]

omit [NeZero d] in
private theorem probe_envelope_coefficient_eq {alpha : ℝ} (halpha : 0 < alpha)
    (v : Vec d) :
    (1 / 2 : ℝ) * absCoordSum ((Real.sqrt alpha)⁻¹ • v) *
        absCoordSum ((Real.sqrt alpha)⁻¹ • v) +
      (1 / 2 : ℝ) * absCoordSum (Real.sqrt alpha • v) *
        absCoordSum (Real.sqrt alpha • v) =
      (1 / 2 : ℝ) * (alpha⁻¹ + alpha) * absCoordSum v ^ 2 := by
  rw [absCoordSum_smul, absCoordSum_smul,
    abs_of_nonneg (Real.sqrt_nonneg alpha),
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg alpha))]
  have hs := Real.mul_self_sqrt halpha.le
  have hi : (Real.sqrt alpha)⁻¹ * (Real.sqrt alpha)⁻¹ = alpha⁻¹ := by
    rw [← mul_inv, hs]
  calc
    _ = (1 / 2 : ℝ) *
      ((Real.sqrt alpha)⁻¹ * (Real.sqrt alpha)⁻¹ +
        Real.sqrt alpha * Real.sqrt alpha) * absCoordSum v ^ 2 := by ring
    _ = _ := by rw [hi, hs]

omit [NeZero d] in
private theorem probe_cross_eq {alpha : ℝ} (halpha : 0 < alpha) (v : Vec d) :
    vecDot ((Real.sqrt alpha)⁻¹ • v) (Real.sqrt alpha • v) = vecDot v v := by
  rw [Homogenization.vecDot_smul_left, Homogenization.vecDot_smul_right,
    ← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr halpha).ne', one_mul]

omit [NeZero d] in
/-- The inverse homogenized coefficient has a common bound at fixed cutoff
    and fixed disorder strength. -/
theorem ahom_inv_le_exp_uniform (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    (ahom M L)⁻¹ ≤ Real.exp ((L + 1 : ℝ) * ((Real.log 2 / 2) * M.delta ^ 2)) := by
  have hlower := _root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L
  have hinv := inv_le_inv₀ (ahom_pos M L) (Real.exp_pos _) |>.mpr hlower
  have htau := mul_le_mul_of_nonneg_left (tauSq_le_delta_sq M)
    (show 0 ≤ (L + 1 : ℝ) by positivity)
  calc
    (ahom M L)⁻¹ ≤ (Real.exp (-((L + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)))⁻¹ := by simpa only [neg_mul] using hinv
    _ = Real.exp ((L + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
      rw [Real.exp_neg, inv_inv]
    _ ≤ _ := Real.exp_le_exp.mpr htau

omit [NeZero d] in
/-- Uniform moment root of each envelope exponential. -/
theorem lpMoment_exp_envelope_le (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (L : ℕ) (k : ℤ) {xi : ℝ} (hxi : 1 ≤ xi) :
    lpMoment M.P.toMeasure xi (fun omega =>
      Real.exp (aCutoffCubeLogEnvelope M L k omega)) ≤
      cutoffEnvelopeExpMomentBound d L k M.delta xi ^ xi⁻¹ := by
  have hxi0 : 0 < xi := lt_of_lt_of_le zero_lt_one hxi
  unfold lpMoment
  simp only [abs_of_pos (Real.exp_pos _), ← Real.exp_mul]
  have heq : (fun omega => Real.exp (aCutoffCubeLogEnvelope M L k omega * xi)) =
      fun omega => Real.exp (xi * aCutoffCubeLogEnvelope M L k omega) := by
    funext omega
    rw [mul_comm]
  rw [heq]
  exact Real.rpow_le_rpow (integral_nonneg fun _ => (Real.exp_pos _).le)
    (integral_exp_mul_cutoffEnvelope_le M L k hxi0) (by positivity)

/-- Uniform probe moments on every cube, including the negative scales. -/
theorem exists_law_uniform_probe_moment (L : ℕ) (delta : ℝ) (v : Vec d)
    {xi : ℝ} (hxi : 1 ≤ xi) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta = delta →
      ∀ R : TriadicCube d,
        lpMoment M.P.toMeasure xi
          (fun omega => cutoffProbeForm M L (ahom M L) R omega v) ≤ B := by
  let K := (1 / 2 : ℝ) *
    (Real.exp ((L + 1 : ℝ) * ((Real.log 2 / 2) * delta ^ 2)) + 1) * absCoordSum v ^ 2
  let B := K * (cutoffEnvelopeExpMomentBound d L 0 delta xi ^ xi⁻¹ +
    cutoffEnvelopeExpMomentBound d L 1 delta xi ^ xi⁻¹) + |vecDot v v|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg (mul_nonneg hK (add_nonneg
      (Real.rpow_nonneg (cutoffEnvelopeExpMomentBound_pos _ _ _ _ _).le _)
      (Real.rpow_nonneg (cutoffEnvelopeExpMomentBound_pos _ _ _ _ _).le _)))
      (abs_nonneg _)
  refine ⟨B, hB, ?_⟩
  intro M hdelta
  have halpha := ahom_pos M L
  have hcoeff : (1 / 2 : ℝ) * ((ahom M L)⁻¹ + ahom M L) * absCoordSum v ^ 2 ≤ K := by
    have hi := ahom_inv_le_exp_uniform M L
    rw [hdelta] at hi
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add hi (ahom_le_one M L)) (by norm_num))
      (sq_nonneg _)
  let Z := fun omega => K * (Real.exp (aCutoffCubeLogEnvelope M L 0 omega) +
    Real.exp (aCutoffCubeLogEnvelope M L 1 omega)) + |vecDot v v|
  have hZ0 : ∀ omega, 0 ≤ Z omega := fun omega => add_nonneg
    (mul_nonneg hK (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)) (abs_nonneg _)
  have h0 := memLp_exp_aCutoffCubeLogEnvelope M L 0 hxi
  have h1 := memLp_exp_aCutoffCubeLogEnvelope M L 1 hxi
  have hZm : MemLp Z (ENNReal.ofReal xi) M.P.toMeasure :=
    ((h0.add h1).const_mul K).add (memLp_const _)
  have hxi0 : 0 < xi := lt_of_lt_of_le zero_lt_one hxi
  have hZbound : lpMoment M.P.toMeasure xi Z ≤ B := by
    have ht := lpMoment_add_le hxi ((h0.add h1).const_mul K)
      (memLp_const |vecDot v v|)
    rw [lpMoment_const_mul hxi0, abs_of_nonneg hK, lpMoment_const hxi0,
      abs_abs] at ht
    have ht2 := lpMoment_add_le hxi h0 h1
    have h00 := lpMoment_exp_envelope_le M L 0 hxi
    have h11 := lpMoment_exp_envelope_le M L 1 hxi
    rw [hdelta] at h00 h11
    exact ht.trans (add_le_add
      (mul_le_mul_of_nonneg_left (ht2.trans (add_le_add h00 h11)) hK) (le_refl _))
  have hnonpos : ∀ k : ℤ, k ≤ 0 → lpMoment M.P.toMeasure xi
      (fun omega => cutoffProbeForm M L (ahom M L) (originCube d k) omega v) ≤ B := by
    intro k hk
    have hdepth := aCutoffCubeOriginCoverDepth_originCube_le_one (d := d) hk
    have hcover : aCutoffCubeOriginCoverScale (originCube d k) = 0 ∨
        aCutoffCubeOriginCoverScale (originCube d k) = 1 := by
      unfold aCutoffCubeOriginCoverScale
      have hcases : aCutoffCubeOriginCoverDepth (originCube d k) = 0 ∨
          aCutoffCubeOriginCoverDepth (originCube d k) = 1 := by omega
      rcases hcases with h | h <;> simp only [h, Nat.cast_zero, Nat.cast_one] <;> tauto
    apply le_trans (lpMoment_mono hxi0
      (integrable_abs_rpow_of_memLp hxi0 (memLp_cutoffResponseOnCube M L _ _ _ hxi))
      (integrable_abs_rpow_of_memLp hxi0 hZm) ?_) hZbound
    intro omega
    change |cutoffProbeForm M L (ahom M L) (originCube d k) omega v| ≤ |Z omega|
    rw [abs_of_nonneg (cutoffProbeForm_nonneg M L _ _ _ _), abs_of_nonneg (hZ0 omega)]
    have hb := abs_cutoffResponseOnCube_le_exp_envelope M L
      ((Real.sqrt (ahom M L))⁻¹ • v) (Real.sqrt (ahom M L) • v)
      (originCube d k) omega
    rw [probe_envelope_coefficient_eq halpha v, probe_cross_eq halpha v] at hb
    have hstep := (le_abs_self (cutoffProbeForm M L (ahom M L)
      (originCube d k) omega v)).trans hb
    have hcoefstep := mul_le_mul_of_nonneg_right hcoeff
      (Real.exp_pos (aCutoffCubeLogEnvelope M L (aCutoffCubeOriginCoverScale (originCube d k)) omega)).le
    have hfinal := hstep.trans (add_le_add hcoefstep (le_refl _))
    rcases hcover with h | h
    · rw [h] at hfinal
      exact hfinal.trans (add_le_add (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (Real.exp_pos _).le) hK) (le_refl _))
    · rw [h] at hfinal
      exact hfinal.trans (add_le_add (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (Real.exp_pos _).le) hK) (le_refl _))
  intro R
  rw [lpMoment_cutoffProbeForm_eq M L (ahom M L) R v xi,
    integral_cutoffProbeForm_rpow_eq_originCube]
  rcases le_or_gt (0 : ℤ) R.scale with hk | hk
  · have hnat : R.scale = ((R.scale.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hk).symm
    rw [hnat]
    have hunit := hnonpos 0 le_rfl
    rw [lpMoment_cutoffProbeForm_eq] at hunit
    exact (Real.rpow_le_rpow
      (integral_nonneg fun omega => Real.rpow_nonneg
        (cutoffProbeForm_nonneg M L _ _ _ _) _)
      (integral_cutoffProbeForm_rpow_originCube_le M L halpha R.scale.toNat v hxi)
      (by positivity)).trans hunit
  · have hsmall := hnonpos R.scale hk.le
    rwa [lpMoment_cutoffProbeForm_eq] at hsmall

/-- A uniform moment root for the complete finite probe family. -/
theorem exists_law_uniform_finite_probe_moment (L : ℕ) (delta : ℝ)
    {xi : ℝ} (hxi : 1 ≤ xi) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta = delta →
      ∀ R : TriadicCube d,
        lpMoment M.P.toMeasure xi
          (fun omega => finiteProbeSum M L (ahom M L) R omega) ≤ B := by
  classical
  have hxi0 : 0 < xi := lt_of_lt_of_le zero_lt_one hxi
  have hall := fun u : Vec d => exists_law_uniform_probe_moment (d := d) L delta u hxi
  choose Bu hBu0 hBu using hall
  refine ⟨∑ i : Fin d, ∑ j : Fin d, (1 / 2 : ℝ) *
      (Bu ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
        Bu (Pi.single i (1 : ℝ) : Vec d) + Bu (Pi.single j (1 : ℝ) : Vec d)), ?_, ?_⟩
  · refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    have h1 := hBu0 ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d))
    have h2 := hBu0 (Pi.single i (1 : ℝ) : Vec d)
    have h3 := hBu0 (Pi.single j (1 : ℝ) : Vec d)
    linarith
  · intro M hdelta R
    have hcpfmem : ∀ u : Vec d, MemLp
        (fun omega => cutoffProbeForm M L (ahom M L) R omega u)
        (ENNReal.ofReal xi) M.P.toMeasure :=
      fun u => memLp_cutoffResponseOnCube M L _ _ _ hxi
    have hbound : ∀ u : Vec d,
        lpMoment M.P.toMeasure xi
          (fun omega => cutoffProbeForm M L (ahom M L) R omega u) ≤ Bu u :=
      fun u => hBu u M hdelta R
    have hijmem : ∀ i j : Fin d, MemLp (fun omega => (1 / 2 : ℝ) *
        (cutoffProbeForm M L (ahom M L) R omega
            ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
          cutoffProbeForm M L (ahom M L) R omega (Pi.single i (1 : ℝ) : Vec d) +
          cutoffProbeForm M L (ahom M L) R omega (Pi.single j (1 : ℝ) : Vec d)))
        (ENNReal.ofReal xi) M.P.toMeasure :=
      fun i j => (((hcpfmem _).add (hcpfmem _)).add (hcpfmem _)).const_mul _
    have himem : ∀ i : Fin d, MemLp (fun omega => ∑ j : Fin d, (1 / 2 : ℝ) *
        (cutoffProbeForm M L (ahom M L) R omega
            ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
          cutoffProbeForm M L (ahom M L) R omega (Pi.single i (1 : ℝ) : Vec d) +
          cutoffProbeForm M L (ahom M L) R omega (Pi.single j (1 : ℝ) : Vec d)))
        (ENNReal.ofReal xi) M.P.toMeasure :=
      fun i => memLp_finsetSum _ fun j _ => hijmem i j
    have houter := lpMoment_finsetSum_le (mu := M.P.toMeasure)
      (Finset.univ : Finset (Fin d))
      (F := fun i omega => ∑ j : Fin d, (1 / 2 : ℝ) *
        (cutoffProbeForm M L (ahom M L) R omega
            ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
          cutoffProbeForm M L (ahom M L) R omega (Pi.single i (1 : ℝ) : Vec d) +
          cutoffProbeForm M L (ahom M L) R omega (Pi.single j (1 : ℝ) : Vec d)))
      hxi (fun i _ => himem i)
    refine le_trans houter ?_
    refine Finset.sum_le_sum fun i _ => ?_
    have hinner := lpMoment_finsetSum_le (mu := M.P.toMeasure)
      (Finset.univ : Finset (Fin d))
      (F := fun j omega => (1 / 2 : ℝ) *
        (cutoffProbeForm M L (ahom M L) R omega
            ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
          cutoffProbeForm M L (ahom M L) R omega (Pi.single i (1 : ℝ) : Vec d) +
          cutoffProbeForm M L (ahom M L) R omega (Pi.single j (1 : ℝ) : Vec d)))
      hxi (fun j _ => hijmem i j)
    refine le_trans hinner ?_
    refine Finset.sum_le_sum fun j _ => ?_
    have hhalf : lpMoment M.P.toMeasure xi (fun omega => (1 / 2 : ℝ) *
        (cutoffProbeForm M L (ahom M L) R omega
            ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
          cutoffProbeForm M L (ahom M L) R omega (Pi.single i (1 : ℝ) : Vec d) +
          cutoffProbeForm M L (ahom M L) R omega (Pi.single j (1 : ℝ) : Vec d))) =
        (1 / 2 : ℝ) * lpMoment M.P.toMeasure xi (fun omega =>
          cutoffProbeForm M L (ahom M L) R omega
              ((Pi.single i (1 : ℝ) : Vec d) +
                (Pi.single j (1 : ℝ) : Vec d)) +
            cutoffProbeForm M L (ahom M L) R omega (Pi.single i (1 : ℝ) : Vec d) +
            cutoffProbeForm M L (ahom M L) R omega
              (Pi.single j (1 : ℝ) : Vec d)) := by
      rw [lpMoment_const_mul hxi0]
      norm_num
    rw [hhalf]
    have hadd12 : MemLp (fun omega =>
        cutoffProbeForm M L (ahom M L) R omega
            ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
          cutoffProbeForm M L (ahom M L) R omega (Pi.single i (1 : ℝ) : Vec d))
        (ENNReal.ofReal xi) M.P.toMeasure := (hcpfmem _).add (hcpfmem _)
    have htri1 := lpMoment_add_le (mu := M.P.toMeasure) hxi hadd12
      (hcpfmem (Pi.single j (1 : ℝ) : Vec d))
    have htri2 := lpMoment_add_le (mu := M.P.toMeasure) hxi
      (hcpfmem ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)))
      (hcpfmem (Pi.single i (1 : ℝ) : Vec d))
    have hb1 := hbound ((Pi.single i (1 : ℝ) : Vec d) +
      (Pi.single j (1 : ℝ) : Vec d))
    have hb2 := hbound (Pi.single i (1 : ℝ) : Vec d)
    have hb3 := hbound (Pi.single j (1 : ℝ) : Vec d)
    linarith


/-- A common bound on the unit-probe constant used in the quenched step. -/
theorem exists_law_uniform_probe_unit_constant (L : ℕ) (delta : ℝ)
    {xi : ℝ} (hxi : 1 ≤ xi) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta = delta →
      probeSumUnitConst M L (ahom M L) xi ≤ B := by
  classical
  have hall := fun u : Vec d => exists_law_uniform_probe_moment (d := d) L delta u hxi
  have hall1 := fun u : Vec d => exists_law_uniform_probe_moment (d := d) L delta u (xi := 1) le_rfl
  choose Bx hBx0 hBx using hall
  choose B1 hB10 hB1 using hall1
  let B := fun u : Vec d => Bx u + B1 u
  have hB0 : ∀ u, 0 ≤ B u := fun u => add_nonneg (hBx0 u) (hB10 u)
  refine ⟨∑ i : Fin d, ∑ j : Fin d, (1 / 2 : ℝ) *
      (B ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
        B (Pi.single i (1 : ℝ) : Vec d) + B (Pi.single j (1 : ℝ) : Vec d)), ?_, ?_⟩
  · refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    exact mul_nonneg (by norm_num) (add_nonneg (add_nonneg (hB0 _) (hB0 _)) (hB0 _))
  · intro M hdelta
    have hunit : ∀ u, probeUnitConst M L (ahom M L) xi u ≤ B u := by
      intro u
      have h1 := hB1 u M hdelta (originCube d 0)
      unfold lpMoment at h1
      simp only [Real.rpow_one, inv_one,
        abs_of_nonneg (cutoffProbeForm_nonneg M L (ahom M L) _ _ _)] at h1
      exact add_le_add (hBx u M hdelta (originCube d 0)) h1
    unfold probeSumUnitConst
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add (hunit _) (hunit _))
      (hunit _)) (by norm_num)

end SubdiffusiveProcess.Section6
