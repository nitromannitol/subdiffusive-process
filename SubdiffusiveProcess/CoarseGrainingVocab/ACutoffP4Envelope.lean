import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffRestrictionLaw
import SubdiffusiveProcess.CoarseGrainingVocab.ShellSensitivity
import Homogenization.Probability.IndependentSums.GammaSigmaExpRegime.OneVariable

/-!
# A local lognormal envelope for the finite GMC cutoff

This is the stochastic input for the Chapter 5 `(P4)` package.  On a fixed
origin cube, each physical shell is transported to its own scale and covered
by finitely many unit cubes.  The maximum over the finitely many shell gauges
has a `Gamma_2` tail, and hence every exponential moment required below is
finite.

PROVENANCE: this is the scalar-lognormal analogue of
`Algsuperdiff/Section3/Cutoff/P4UpperMoments.lean`.  The finite-cover gauges
come from `ShellSensitivity.lean`, where they were proved directly from `(g2)`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Filter MeasureTheory Homogenization Homogenization.Book
  Homogenization.IndependentSums
open scoped BigOperators

noncomputable section


private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The maximum of the own-scale `(g2)` gauges needed to observe all shells of
the level-`L` cutoff on `cu_k`. -/
def aCutoffCubeShellGauge {d : ℕ} (L : ℕ) (k : ℤ) (omega : Sample d) : ℝ :=
  (Finset.univ : Finset (Fin (L + 1))).sup' Finset.univ_nonempty fun j =>
    largeCubeShellG2 (j : ℕ) (k - (j : ℤ)) omega

theorem aCutoffCubeShellGauge_nonneg {d : ℕ} (L : ℕ) (k : ℤ)
    (omega : Sample d) :
    0 ≤ aCutoffCubeShellGauge L k omega := by
  let j : Fin (L + 1) := ⟨0, by omega⟩
  exact (largeCubeShellG2_nonneg (j : ℕ) (k - (j : ℤ)) omega).trans
    (Finset.le_sup' (fun i : Fin (L + 1) =>
      largeCubeShellG2 (i : ℕ) (k - (i : ℤ)) omega) (Finset.mem_univ j))

theorem measurable_aCutoffCubeShellGauge {d : ℕ} (L : ℕ) (k : ℤ) :
    Measurable (aCutoffCubeShellGauge (d := d) L k) := by
  let Y : Sample d → ℝ :=
    (Finset.univ : Finset (Fin (L + 1))).sup' Finset.univ_nonempty fun j =>
      largeCubeShellG2 (j : ℕ) (k - (j : ℤ))
  have hY : Measurable Y := Finset.measurable_sup' Finset.univ_nonempty
    (fun j _ => measurable_largeCubeShellG2 (j : ℕ) (k - (j : ℤ)))
  have heq : Y = aCutoffCubeShellGauge L k := by
    funext omega
    exact Finset.sup'_apply Finset.univ_nonempty
      (fun j : Fin (L + 1) =>
        largeCubeShellG2 (j : ℕ) (k - (j : ℤ))) omega
  rwa [← heq]

/-- A deterministic positive `Gamma_2` scale for the shell maximum. -/
def aCutoffCubeShellGaugeScale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (k : ℤ) : ℝ :=
  if L = 0 then
    ((3 * Real.log ((shellCoverShifts d k).card : ℝ)) ^ (2 : ℝ)⁻¹) *
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)
  else
    ((3 * Real.log ((L + 1 : ℕ) : ℝ)) ^ (2 : ℝ)⁻¹) *
      (Finset.univ : Finset (Fin (L + 1))).sup' Finset.univ_nonempty
        (fun j =>
          ((3 * Real.log
            ((shellCoverShifts d (k - (j : ℤ))).card : ℝ)) ^ (2 : ℝ)⁻¹) *
            ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta))

theorem aCutoffCubeShellGaugeScale_pos {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (k : ℤ) :
    0 < aCutoffCubeShellGaugeScale M L k := by
  by_cases hL : L = 0
  · subst L
    rw [aCutoffCubeShellGaugeScale, if_pos rfl]
    have hcard := shellCoverShifts_card_ge_two M k
    have hlog : 0 < Real.log ((shellCoverShifts d k).card : ℝ) :=
      Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hcard))
    exact mul_pos
      (Real.rpow_pos_of_pos (mul_pos (by norm_num) hlog) _)
      (mul_pos (Real.rpow_pos_of_pos
        (by nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]) _)
        M.shellPrefix.delta_pos)
  · rw [aCutoffCubeShellGaugeScale, if_neg hL]
    have hcard : 2 ≤ L + 1 := by omega
    have hlog : 0 < Real.log ((L + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hcard))
    let j : Fin (L + 1) := ⟨0, by omega⟩
    have hcover := shellCoverShifts_card_ge_two M (k - (j : ℤ))
    have hcoverlog : 0 < Real.log
        ((shellCoverShifts d (k - (j : ℤ))).card : ℝ) :=
      Real.log_pos (by exact_mod_cast
        (lt_of_lt_of_le (by omega : 1 < 2) hcover))
    have hterm : 0 <
        ((3 * Real.log
          ((shellCoverShifts d (k - (j : ℤ))).card : ℝ)) ^ (2 : ℝ)⁻¹) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      exact mul_pos
        (Real.rpow_pos_of_pos (mul_pos (by norm_num) hcoverlog) _)
        (mul_pos (Real.rpow_pos_of_pos (by nlinarith [hlog2]) _)
          M.shellPrefix.delta_pos)
    have hsup : 0 <
        (Finset.univ : Finset (Fin (L + 1))).sup' Finset.univ_nonempty
          (fun i =>
            ((3 * Real.log
              ((shellCoverShifts d (k - (i : ℤ))).card : ℝ)) ^ (2 : ℝ)⁻¹) *
              ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) :=
      hterm.trans_le (Finset.le_sup'
        (fun i : Fin (L + 1) =>
          ((3 * Real.log
            ((shellCoverShifts d (k - (i : ℤ))).card : ℝ)) ^ (2 : ℝ)⁻¹) *
            ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta))
        (Finset.mem_univ j))
    exact mul_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) hlog) _) hsup

theorem isBigOWith_gammaTwo_aCutoffCubeShellGauge {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (k : ℤ) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (aCutoffCubeShellGauge L k) (aCutoffCubeShellGaugeScale M L k) := by
  by_cases hL : L = 0
  · subst L
    have heq : aCutoffCubeShellGauge (d := d) 0 k =
        largeCubeShellG2 0 k := by
      funext omega
      apply le_antisymm
      · apply Finset.sup'_le
        intro j _
        have hj : j = (0 : Fin 1) := by
          apply Fin.ext
          omega
        subst j
        simp
      · change largeCubeShellG2 0 k omega ≤
          (Finset.univ : Finset (Fin 1)).sup' Finset.univ_nonempty
            (fun j => largeCubeShellG2 (j : ℕ) (k - (j : ℤ)) omega)
        have h := Finset.le_sup'
          (fun j : Fin 1 => largeCubeShellG2 (j : ℕ) (k - (j : ℤ)) omega)
          (Finset.mem_univ (0 : Fin 1))
        simpa only [Fin.val_zero, Nat.cast_zero, Int.ofNat_zero, sub_zero] using h
    rw [heq, aCutoffCubeShellGaugeScale, if_pos rfl]
    exact isBigOWith_gammaTwo_largeCubeShellG2 M 0 k
  · have hcard : 2 ≤ (Finset.univ : Finset (Fin (L + 1))).card := by
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    simpa [aCutoffCubeShellGauge, aCutoffCubeShellGaugeScale, hL] using
      (isBigOWith_gammaSigma_finset_sup'_of_scales
        (μ := M.P.toMeasure) (s := (Finset.univ : Finset (Fin (L + 1))))
        (hs := Finset.univ_nonempty) (σ := (2 : ℝ)) (by norm_num) hcard
        (fun j _ => isBigOWith_gammaTwo_largeCubeShellG2 M
          (j : ℕ) (k - (j : ℤ))))

/-- Symmetric logarithmic envelope for `a_L` and its reciprocal on `cu_k`. -/
def aCutoffCubeLogEnvelope {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (k : ℤ)
    (omega : Sample d) : ℝ :=
  (L + 1 : ℝ) *
    (aCutoffCubeShellGauge L k omega + SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)

theorem aCutoffCubeLogEnvelope_nonneg {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (k : ℤ)
    (omega : Sample d) :
    0 ≤ aCutoffCubeLogEnvelope M L k omega := by
  exact mul_nonneg (by positivity)
    (add_nonneg (aCutoffCubeShellGauge_nonneg L k omega) M.G4.tauSq_pos.le)

theorem measurable_aCutoffCubeLogEnvelope {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (k : ℤ) :
    Measurable (aCutoffCubeLogEnvelope M L k) :=
  measurable_const.mul
    ((measurable_aCutoffCubeShellGauge L k).add_const _)

private theorem abs_potential_apply_le_shellGauge {d : ℕ}
    (L : ℕ) (k : ℤ) (omega : Sample d) (j : Fin (L + 1))
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d k)) :
    |omega j x| ≤ aCutoffCubeShellGauge L k omega := by
  let x' : Vec d := (((3 : ℝ) ^ (j : ℕ))⁻¹) • x
  have hx' : x' ∈ openCubeSet (originCube d (k - (j : ℤ))) := by
    rw [mem_openCubeSet_originCube_iff] at hx ⊢
    intro i
    have hpow : (3 : ℝ) ^ (k - (j : ℤ)) =
        ((3 : ℝ) ^ (j : ℕ))⁻¹ * (3 : ℝ) ^ k := by
      rw [← zpow_natCast, ← zpow_neg,
        ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1
      ring
    have hjpos : (0 : ℝ) < (3 : ℝ) ^ (j : ℕ) := by positivity
    have hinv : (0 : ℝ) < ((3 : ℝ) ^ (j : ℕ))⁻¹ := inv_pos.mpr hjpos
    have hxi := hx i
    simp only [x', Pi.smul_apply, smul_eq_mul]
    rw [hpow]
    constructor
    · simpa [mul_assoc, mul_left_comm, mul_comm] using
        (mul_lt_mul_of_pos_left hxi.1 hinv)
    · simpa [mul_assoc, mul_left_comm, mul_comm] using
        (mul_lt_mul_of_pos_left hxi.2 hinv)
  have hpoint := abs_unscalePotential_apply_le_largeCubeShellG2
    (d := d) (j : ℕ) (k - (j : ℤ)) omega hx'
  have hval : unscalePotential (j : ℕ) (omega j) x' = omega j x := by
    simp only [x', unscalePotential,
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale_apply, smul_smul]
    rw [mul_inv_cancel₀ (by positivity : (3 : ℝ) ^ (j : ℕ) ≠ 0), one_smul]
  rw [hval] at hpoint
  exact hpoint.trans (Finset.le_sup'
    (fun i : Fin (L + 1) =>
      largeCubeShellG2 (i : ℕ) (k - (i : ℤ)) omega)
    (Finset.mem_univ j))

/-- Pointwise two-sided logarithmic control on the observation cube. -/
theorem abs_log_aCutoff_le_aCutoffCubeLogEnvelope {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (k : ℤ)
    (omega : Sample d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d k)) :
    |Real.log (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)| ≤
      aCutoffCubeLogEnvelope M L k omega := by
  rw [SubdiffusiveProcess.Frozen.Assumptions.aCutoff,
    Real.log_exp]
  calc
    |∑ j ∈ Finset.range (L + 1),
        (omega j x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)| ≤
        ∑ j ∈ Finset.range (L + 1),
          |omega j x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (L + 1),
        (aCutoffCubeShellGauge L k omega +
          SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [Finset.mem_range] at hj
      have hjfin : j < L + 1 := hj
      calc
        |omega j x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P| ≤
            |omega j x| + |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P| := abs_sub _ _
        _ = |omega j x| + SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
          rw [abs_of_pos M.G4.tauSq_pos]
        _ ≤ aCutoffCubeShellGauge L k omega +
            SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P :=
          add_le_add
            (abs_potential_apply_le_shellGauge L k omega ⟨j, hjfin⟩ hx) le_rfl
    _ = aCutoffCubeLogEnvelope M L k omega := by
      simp [aCutoffCubeLogEnvelope]
      ring

theorem exp_neg_aCutoffCubeLogEnvelope_le_aCutoff {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (k : ℤ)
    (omega : Sample d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d k)) :
    Real.exp (-aCutoffCubeLogEnvelope M L k omega) ≤
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x := by
  rw [← Real.exp_log (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x)]
  exact Real.exp_le_exp.mpr
    ((neg_le_of_abs_le (abs_log_aCutoff_le_aCutoffCubeLogEnvelope M L k omega hx)))

theorem aCutoff_le_exp_aCutoffCubeLogEnvelope {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (k : ℤ)
    (omega : Sample d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d k)) :
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x ≤
      Real.exp (aCutoffCubeLogEnvelope M L k omega) := by
  rw [← Real.exp_log (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x)]
  exact Real.exp_le_exp.mpr
    (le_of_abs_le (abs_log_aCutoff_le_aCutoffCubeLogEnvelope M L k omega hx))



theorem integrable_exp_mul_aCutoffCubeLogEnvelope {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (k : ℤ)
    {q : ℝ} (hq : 0 < q) :
    Integrable (fun omega : Sample d =>
      Real.exp (q * aCutoffCubeLogEnvelope M L k omega)) M.P.toMeasure := by
  let H : Sample d → ℝ := aCutoffCubeShellGauge L k
  let A : ℝ := aCutoffCubeShellGaugeScale M L k
  let c : ℝ := q * (L + 1 : ℝ)
  have hA : 0 < A := aCutoffCubeShellGaugeScale_pos M L k
  have hc : 0 < c := mul_pos hq (by positivity)
  have hHm : AEMeasurable H M.P.toMeasure :=
    (measurable_aCutoffCubeShellGauge L k).aemeasurable
  have hHbig : IsBigO M.P.toMeasure (gammaSigma 2) H A := by
    simpa [IsBigO, H, abs_of_nonneg (aCutoffCubeShellGauge_nonneg L k _)] using
      (isBigOWith_gammaTwo_aCutoffCubeShellGauge M L k)
  have hexp : Integrable (fun omega => Real.exp (c * H omega)) M.P.toMeasure :=
    integrable_exp_mul_of_isBigO_gammaSigma_of_one_lt
      (μ := M.P.toMeasure) hHm (by norm_num : (1 : ℝ) < 2) hA hc.le hHbig
  have hconst := hexp.const_mul
    (Real.exp (c * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))
  refine hconst.congr ?_
  filter_upwards with omega
  simp only [H, c, aCutoffCubeLogEnvelope, ← Real.exp_add]
  congr 1
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab
