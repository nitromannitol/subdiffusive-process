module

public import SubdiffusiveProcess.Static.HarmonicCellEnvelopeBank
public import SubdiffusiveProcess.Static.HarmonicCellDerivativeBank

@[expose] public section

/-! # Literal coefficient and logarithmic-modulus readouts on signed physical cells -/

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The physical logarithmic derivative is dominated everywhere on the
larger open cube by its finite measurable bank. -/
theorem norm_logCutoff_derivative_le_bank {d : ℕ} (M : GMCModel d) (j k : ℕ)
    (omega : PotentialSample d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d ((k + 1 : ℕ) : ℤ))) :
    ‖fderiv ℝ (fun y => Real.log (aCutoff M j omega y)) x‖ ≤
      harmonicMicroscopicDerivativeBank M j k omega := by
  obtain ⟨p, hp, hpx⟩ := exists_physicalShellCoverCenter_mem 0 ((k + 1 : ℕ) : ℤ) hx
  simp only [Nat.cast_zero, sub_zero] at hp hpx
  have hmem : x ∈ translatedCube d 0 (physicalShellCoverCenter 0 p) :=
    ⟨x - physicalShellCoverCenter 0 p, hpx, by abel⟩
  rw [(hasFDerivAt_log_aCutoff M j omega x).fderiv]
  have hlocal := norm_fixedCutoffLogFDeriv_le_envelope j (physicalShellCoverCenter 0 p) omega hmem
  have henv : fixedCutoffLogDerivativeEnvelope j (physicalShellCoverCenter 0 p) omega ≤
      harmonicMicroscopicDerivativeEnvelope j (physicalShellCoverCenter 0 p) omega := by
    unfold harmonicMicroscopicDerivativeEnvelope
    rw [fixedCutoffOscillationEnvelope_eq_two_mul_logDerivativeEnvelope]
    have hn : 0 ≤ fixedCutoffLogDerivativeEnvelope j (physicalShellCoverCenter 0 p) omega := by
      unfold fixedCutoffLogDerivativeEnvelope
      exact Finset.sum_nonneg fun k _ => translatedSmallShellEnvelope_nonneg k _ _ _
    linarith
  exact (hlocal.trans henv).trans (Finset.le_sup'
    (fun p => harmonicMicroscopicDerivativeEnvelope j (physicalShellCoverCenter 0 p) omega) hp)

/-- Convexity turns the actual derivative readout into a logarithmic modulus. -/
theorem logCutoff_sub_le_derivative_bank {d : ℕ} (M : GMCModel d) (j k : ℕ)
    (omega : PotentialSample d) {x y : Vec d}
    (hx : x ∈ openCubeSet (originCube d ((k + 1 : ℕ) : ℤ)))
    (hy : y ∈ openCubeSet (originCube d ((k + 1 : ℕ) : ℤ))) :
    |Real.log (aCutoff M j omega x) - Real.log (aCutoff M j omega y)| ≤
      harmonicMicroscopicDerivativeBank M j k omega * ‖x - y‖ := by
  have h := (convex_openCubeSet (originCube d ((k + 1 : ℕ) : ℤ))).norm_image_sub_le_of_norm_fderiv_le
    (f := fun x => Real.log (aCutoff M j omega x))
    (fun x _ => (hasFDerivAt_log_aCutoff M j omega x).differentiableAt)
    (fun x hx => norm_logCutoff_derivative_le_bank M j k omega hx) hx hy
  simpa only [Real.norm_eq_abs, abs_sub_comm, norm_sub_rev] using h

/-- A signed physical cell fits strictly into the bank's larger open cube,
including its closed boundary. Negative scales use bank scale zero. -/
theorem scaled_unit_closedBall_subset_bankCube {d : ℕ} (k : ℤ) {x : Vec d}
    (hx : x ∈ Metric.closedBall (0 : Vec d) (1 / 2)) :
    (3 : ℝ) ^ k • x ∈ openCubeSet (originCube d ((k.toNat + 1 : ℕ) : ℤ)) := by
  have hk : k < ((k.toNat + 1 : ℕ) : ℤ) := by omega
  have hscale := zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 3) hk
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hcoord : |x i| ≤ 1 / 2 := by
    have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    exact hi.trans hx
  have hb : |((3 : ℝ) ^ k • x) i| < (3 : ℝ) ^ ((k.toNat + 1 : ℕ) : ℤ) / 2 := by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul,
      abs_of_pos (show 0 < (3 : ℝ) ^ k by positivity)]
    exact (mul_le_mul_of_nonneg_left hcoord (by positivity)).trans_lt (by linarith)
  rw [abs_lt] at hb
  constructor <;> linarith [hb.1, hb.2]

/-- Both ellipticity bounds and a usable logarithmic modulus of the literal
normalized chart coefficient hold simultaneously at every closed-cell point. -/
theorem harmonicMicroscopicBank_unit_coefficient_bounds {d : ℕ} (M : GMCModel d)
    (j : ℕ) (k : ℤ) (omega : PotentialSample d) :
    let R := harmonicMicroscopicCoefficientBank M j k.toNat omega
    let D := harmonicMicroscopicDerivativeBank M j k.toNat omega
    let a := fun x : Vec d => (ahom M j)⁻¹ * aCutoff M j omega ((3 : ℝ) ^ k • x)
    (∀ x ∈ Metric.closedBall (0 : Vec d) (1 / 2), R⁻¹ ≤ a x ∧ a x ≤ R) ∧
      ∀ x ∈ Metric.closedBall (0 : Vec d) (1 / 2),
        ∀ y ∈ Metric.closedBall (0 : Vec d) (1 / 2),
          |Real.log (a x) - Real.log (a y)| ≤ ((3 : ℝ) ^ k.toNat * D) * ‖x - y‖ := by
  dsimp only
  constructor
  · intro x hx
    have h := harmonicMicroscopicCoefficientBank_comparison M j k.toNat omega
      (scaled_unit_closedBall_subset_bankCube k hx)
    have ha : 0 < (ahom M j)⁻¹ * aCutoff M j omega ((3 : ℝ) ^ k • x) :=
      mul_pos (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M j)) (aCutoff_pos _ _ _ _)
    have hR := zero_lt_one.trans_le (one_le_harmonicMicroscopicCoefficientBank M j k.toNat omega)
    refine ⟨?_, h.1⟩
    have hm := (inv_le_comm₀ ha hR).mp h.2
    exact hm
  · intro x hx y hy
    have hlog := logCutoff_sub_le_derivative_bank M j k.toNat omega
      (scaled_unit_closedBall_subset_bankCube k hx) (scaled_unit_closedBall_subset_bankCube k hy)
    have hn : (ahom M j)⁻¹ ≠ 0 := inv_ne_zero (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M j).ne'
    rw [Real.log_mul hn (aCutoff_pos M j omega _).ne',
      Real.log_mul hn (aCutoff_pos M j omega _).ne', add_sub_add_left_eq_sub]
    refine hlog.trans ?_
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (3 : ℝ) ^ k)]
    have hk : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ k.toNat := by
      have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
        (show k ≤ (k.toNat : ℤ) by omega)
      simpa only [zpow_natCast] using h
    have hD := zero_le_one.trans (one_le_harmonicMicroscopicDerivativeBank M j k.toNat omega)
    nlinarith only [mul_le_mul_of_nonneg_right hk (mul_nonneg hD (norm_nonneg (x - y)))]

end SubdiffusiveProcess.Static
