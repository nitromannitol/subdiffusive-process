module

public import SubdiffusiveProcess.CoarseGrainingVocab.PrefixSuffixMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.AnchoredGrowth
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.ShellColumns
public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodFieldOne
public import Mathlib.Data.Int.NatAbs

@[expose] public section

/-!
# The first shell-field score for density of good scales

This file builds the one-shell carrier in the proof of
`l.bad.scales.for.nabla.gj`.  Its measurable representative is the finite-cover
maximum `largeCubeShellG2`; hence the entire `i`th score column reads only the
`i`th shell.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Density

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
  Homogenization.IndependentSums
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
open scoped BigOperators ENNReal

noncomputable section

private abbrev Sample (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- Rescaling a point of the scale-`k` cube by the inverse own scale of shell
`i` places it in the reverse-scaled observation cube. -/
theorem inv_shell_scale_mem_reverseCube {d i k : ℕ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (k : ℤ))) :
    (((3 : ℝ) ^ i)⁻¹) • x ∈
      openCubeSet (originCube d ((k : ℤ) - (i : ℤ))) := by
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro a
  have hpow : (3 : ℝ) ^ ((k : ℤ) - (i : ℤ)) =
      (((3 : ℝ) ^ i)⁻¹) * (3 : ℝ) ^ (k : ℤ) := by
    rw [← zpow_natCast, ← zpow_neg,
      ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    omega
  have hinv : 0 < (((3 : ℝ) ^ i)⁻¹) := by positivity
  have hxa := hx a
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hpow]
  exact ⟨by simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_lt_mul_of_pos_left hxa.1 hinv,
    by simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_lt_mul_of_pos_left hxa.2 hinv⟩

/-- The literal value-plus-scaled-gradient atom from `GoodFieldOne` is bounded
by a single measurable finite-cover shell gauge. -/
theorem fieldOne_atom_le_largeCubeShellG2 {d i k : ℕ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (k : ℤ))) :
    |omega i x| + (3 : ℝ) ^ i * euclideanNorm (shellGradient (omega i) x) ≤
      ((d : ℝ) + 1) * largeCubeShellG2 i ((k : ℤ) - (i : ℤ)) omega := by
  let x' : Vec d := (((3 : ℝ) ^ i)⁻¹) • x
  have hx' : x' ∈ openCubeSet (originCube d ((k : ℤ) - (i : ℤ))) :=
    inv_shell_scale_mem_reverseCube hx
  have hvalue' := abs_unscalePotential_apply_le_largeCubeShellG2
    i ((k : ℤ) - (i : ℤ)) omega hx'
  have hvalue : |omega i x| ≤
      largeCubeShellG2 i ((k : ℤ) - (i : ℤ)) omega := by
    have heval : unscalePotential i (omega i) x' = omega i x := by
      simp only [x', unscalePotential,
        _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply, smul_smul]
      rw [mul_inv_cancel₀ (by positivity : (3 : ℝ) ^ i ≠ 0), one_smul]
    simpa only [heval] using hvalue'
  obtain ⟨p, hp, hpMem⟩ := exists_shellCoverShift_mem hx'
  have hbox := norm_deriv_unscalePotential_le_translatedShellG2 i omega p hpMem
  have hbox' : ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv
        (unscalePotential i (omega i)) x'‖ ≤
      largeCubeShellG2 i ((k : ℤ) - (i : ℤ)) omega :=
    hbox.trans (Finset.le_sup'
      (fun q ↦ translatedShellG2 i (shellCoverCenter q) omega) hp)
  have hderiv : ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega i) x‖ ≤
      (((3 : ℝ) ^ i)⁻¹) *
        largeCubeShellG2 i ((k : ℤ) - (i : ℤ)) omega := by
    have hinv : 0 < (((3 : ℝ) ^ i)⁻¹) := by positivity
    rw [deriv_eq_smul_deriv_unscalePotential i (omega i) x, norm_smul,
      Real.norm_eq_abs, abs_of_pos hinv]
    simpa only [x'] using mul_le_mul_of_nonneg_left hbox' (by positivity)
  have hgradient : (3 : ℝ) ^ i * euclideanNorm (shellGradient (omega i) x) ≤
      (d : ℝ) * largeCubeShellG2 i ((k : ℤ) - (i : ℤ)) omega := by
    calc
      (3 : ℝ) ^ i * euclideanNorm (shellGradient (omega i) x) ≤
          (3 : ℝ) ^ i * ((d : ℝ) *
            ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega i) x‖) :=
        mul_le_mul_of_nonneg_left (euclideanNorm_shellGradient_le _ _) (by positivity)
      _ ≤ (3 : ℝ) ^ i * ((d : ℝ) *
          ((((3 : ℝ) ^ i)⁻¹) *
            largeCubeShellG2 i ((k : ℤ) - (i : ℤ)) omega)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hderiv (Nat.cast_nonneg d)) (by positivity)
      _ = (d : ℝ) * largeCubeShellG2 i ((k : ℤ) - (i : ℤ)) omega := by
        field_simp
  linarith

/-- Supremizing the literal atom over the observation cube preserves the same
one-shell majorant. -/
theorem fieldOne_supNormOn_le_largeCubeShellG2 {d i k : ℕ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    supNormOn (cube d k) (fun x ↦
        |omega i x| + (3 : ℝ) ^ i * euclideanNorm (shellGradient (omega i) x)) ≤
      ((d : ℝ) + 1) * largeCubeShellG2 i ((k : ℤ) - (i : ℤ)) omega := by
  unfold supNormOn
  apply csSup_le
  · refine ⟨|(|omega i 0| + (3 : ℝ) ^ i *
        euclideanNorm (shellGradient (omega i) 0))|, 0, ?_, rfl⟩
    · rw [cube, mem_openCubeSet_originCube_iff]
      intro a
      have hpow : 0 < (3 : ℝ) ^ (k : ℤ) := zpow_pos (by norm_num) _
      constructor <;> simp only [Pi.zero_apply] <;> nlinarith
  · rintro _ ⟨x, hx, rfl⟩
    rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg (by positivity)
      (euclideanNorm_nonneg _)))]
    exact fieldOne_atom_le_largeCubeShellG2 omega hx

/-! ## A genuinely one-shell measurable score column -/

/-- The singleton shell-index sigma-field is definitionally the same carrier
as the column sigma-field used by the Appendix-B adapter. -/
theorem shellSigma_eq_potentialShellIndexSigma_singleton (d i : ℕ) :
    shellSigma d i = potentialShellIndexSigma (d := d) ({i} : Set ℕ) := by
  apply le_antisymm
  · exact le_iSup_of_le i (le_iSup_of_le (Set.mem_singleton i) le_rfl)
  · refine iSup_le fun k ↦ iSup_le fun hk ↦ ?_
    rw [Set.mem_singleton_iff] at hk
    subst k
    exact le_rfl

/-- The measurable majorant for the field-one atom on the scale-`k` cube. -/
noncomputable def fieldOneCubeMajorant {d : ℕ} (i k : ℕ) : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
  fun omega ↦ ((d : ℝ) + 1) *
    largeCubeShellG2 i ((k : ℤ) - (i : ℤ)) omega

theorem fieldOneCubeMajorant_nonneg {d : ℕ} (i k : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ fieldOneCubeMajorant i k omega :=
  mul_nonneg (by positivity) (largeCubeShellG2_nonneg i _ omega)

theorem measurable_fieldOneCubeMajorant_shellSigma {d : ℕ} (i k : ℕ) :
    Measurable[shellSigma d i] (fieldOneCubeMajorant (d := d) i k) := by
  rw [shellSigma_eq_potentialShellIndexSigma_singleton]
  exact measurable_const.mul
    (measurable_largeCubeShellG2_potentialShellIndexSigma
      (d := d) (Set.mem_singleton i) ((k : ℤ) - (i : ℤ)))

/-- Exact Gamma-two scale of the one-cube majorant, before the elementary
log-cardinality estimate is summed in `q`. -/
def fieldOneCubeMajorantScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i k : ℕ) : ℝ :=
  ((d : ℝ) + 1) *
    (((3 * Real.log
      ((shellCoverShifts d ((k : ℤ) - (i : ℤ))).card : ℝ)) ^ (2 : ℝ)⁻¹) *
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta))

theorem isBigOWith_gammaTwo_fieldOneCubeMajorant {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i k : ℕ) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (fieldOneCubeMajorant (d := d) i k)
      (fieldOneCubeMajorantScale M i k) := by
  simpa only [fieldOneCubeMajorant, fieldOneCubeMajorantScale] using!
    (isBigOWith_gammaTwo_largeCubeShellG2 M i
      ((k : ℤ) - (i : ℤ))).const_mul (by positivity : 0 ≤ (d : ℝ) + 1)

theorem fieldOneCubeMajorantScale_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i k : ℕ) :
    0 < fieldOneCubeMajorantScale M i k := by
  unfold fieldOneCubeMajorantScale
  have hcard : 1 < ((shellCoverShifts d ((k : ℤ) - (i : ℤ))).card : ℝ) := by
    exact_mod_cast shellCoverShifts_card_ge_two M ((k : ℤ) - (i : ℤ))
  have hlog : 0 < Real.log
      ((shellCoverShifts d ((k : ℤ) - (i : ℤ))).card : ℝ) :=
    Real.log_pos hcard
  have hlogTwo : 0 < 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  exact mul_pos (by positivity)
    (mul_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) hlog) _)
      (mul_pos (Real.rpow_pos_of_pos hlogTwo _) M.shellPrefix.delta_pos))

/-- The nonnegative extended-real version of the manuscript's `X_{m,i}`.
Writing the inner series in `ℝ≥0∞` makes measurability unconditional; its
`toReal` readout below is used only after the tail estimate proves finiteness. -/
def fieldOneIndexDistance (m i : ℕ) : ℕ :=
  ((m : ℤ) - (i : ℤ)).natAbs

theorem fieldOne_reverseScale_bounds (m i q : ℕ) :
    0 < ((m + 1 + (fieldOneIndexDistance m i + q) : ℕ) : ℤ) - (i : ℤ) ∧
    ((m + 1 + (fieldOneIndexDistance m i + q) : ℕ) : ℤ) - (i : ℤ) ≤
      (2 * fieldOneIndexDistance m i + q + 1 : ℕ) := by
  by_cases hmi : m ≤ i
  · have hdist : fieldOneIndexDistance m i = i - m := by
      unfold fieldOneIndexDistance
      exact Int.natAbs_natCast_sub_natCast_of_le hmi
    rw [hdist]
    omega
  · have him : i ≤ m := Nat.le_of_not_ge hmi
    have hnonneg : 0 ≤ (m : ℤ) - (i : ℤ) := by omega
    have hdistZ : ((fieldOneIndexDistance m i : ℕ) : ℤ) =
        (m : ℤ) - (i : ℤ) := by
      unfold fieldOneIndexDistance
      exact Int.natAbs_of_nonneg hnonneg
    constructor <;> push_cast <;> omega

/-- Dimension/model factor left after the cover maximum is reduced to its
square-root scale cost. -/
def fieldOneGammaDimScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) : ℝ :=
  ((d : ℝ) + 1) * Real.sqrt (shellCoverLogConst * (d : ℝ)) *
    ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)

theorem fieldOneCubeMajorantScale_le_sqrt {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m i q : ℕ) :
    fieldOneCubeMajorantScale M i
        (m + 1 + (fieldOneIndexDistance m i + q)) ≤
      fieldOneGammaDimScale M *
        Real.sqrt ((2 * fieldOneIndexDistance m i + q : ℕ) + 1) := by
  let r : ℤ :=
    ((m + 1 + (fieldOneIndexDistance m i + q) : ℕ) : ℤ) - (i : ℤ)
  have hr := fieldOne_reverseScale_bounds m i q
  have hcover := shellCover_gaussianFactor_le_sqrt M (r := r) hr.1
  have hrleR : (r : ℝ) ≤
      ((2 * fieldOneIndexDistance m i + q + 1 : ℕ) : ℝ) := by
    dsimp only [r]
    exact_mod_cast hr.2
  have hsqrt : Real.sqrt (r : ℝ) ≤
      Real.sqrt ((2 * fieldOneIndexDistance m i + q : ℕ) + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.sqrt_le_sqrt hrleR
  have hbase : 0 ≤ (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta :=
    mul_nonneg (Real.rpow_nonneg (by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith) _) M.shellPrefix.delta_pos.le
  have hCd : 0 ≤ Real.sqrt (shellCoverLogConst * (d : ℝ)) := Real.sqrt_nonneg _
  unfold fieldOneCubeMajorantScale fieldOneGammaDimScale
  change ((d : ℝ) + 1) *
      (((3 * Real.log ((shellCoverShifts d r).card : ℝ)) ^ (2 : ℝ)⁻¹) *
        ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) ≤ _
  calc
    ((d : ℝ) + 1) *
        (((3 * Real.log ((shellCoverShifts d r).card : ℝ)) ^ (2 : ℝ)⁻¹) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) ≤
        ((d : ℝ) + 1) *
          ((Real.sqrt (shellCoverLogConst * (d : ℝ)) * Real.sqrt (r : ℝ)) *
            ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcover hbase) (by positivity)
    _ ≤ ((d : ℝ) + 1) *
          ((Real.sqrt (shellCoverLogConst * (d : ℝ)) *
              Real.sqrt ((2 * fieldOneIndexDistance m i + q : ℕ) + 1)) *
            ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt hCd) hbase) (by positivity)
    _ = (((d : ℝ) + 1) * Real.sqrt (shellCoverLogConst * (d : ℝ)) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) *
        Real.sqrt ((2 * fieldOneIndexDistance m i + q : ℕ) + 1) := by ring

/-- The `q`th summand of `X_{m,i}`, after reindexing the manuscript's inner
sum by `j = |m-i|+q`. -/
noncomputable def fieldOneScoreTerm {d : ℕ}
    (s K : ℝ) (m i q : ℕ) : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
  fun omega ↦
    K * (3 : ℝ) ^ (-(s * (fieldOneIndexDistance m i : ℝ)) / 2) *
      (3 : ℝ) ^ (-(s * (q : ℝ))) *
      fieldOneCubeMajorant i (m + 1 + (fieldOneIndexDistance m i + q)) omega

def fieldOneScoreTermScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (s K : ℝ) (m i q : ℕ) : ℝ :=
  K * (3 : ℝ) ^ (-(s * (fieldOneIndexDistance m i : ℝ)) / 2) *
    (3 : ℝ) ^ (-(s * (q : ℝ))) *
    fieldOneCubeMajorantScale M i
      (m + 1 + (fieldOneIndexDistance m i + q))

theorem fieldOneScoreTerm_nonneg {d : ℕ} {s K : ℝ}
    (hK : 0 ≤ K) (m i q : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ fieldOneScoreTerm (d := d) s K m i q omega := by
  unfold fieldOneScoreTerm
  exact mul_nonneg
    (mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (by norm_num) _))
    (fieldOneCubeMajorant_nonneg i _ omega)

theorem measurable_fieldOneScoreTerm_shellSigma {d : ℕ}
    (s K : ℝ) (m i q : ℕ) :
    Measurable[shellSigma d i] (fieldOneScoreTerm (d := d) s K m i q) := by
  unfold fieldOneScoreTerm
  exact measurable_const.mul (measurable_fieldOneCubeMajorant_shellSigma i _)

theorem isBigOWith_gammaTwo_fieldOneScoreTerm {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s K : ℝ} (hK : 0 ≤ K)
    (m i q : ℕ) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (fieldOneScoreTerm (d := d) s K m i q)
      (fieldOneScoreTermScale M s K m i q) := by
  have hc : 0 ≤ K *
      (3 : ℝ) ^ (-(s * (fieldOneIndexDistance m i : ℝ)) / 2) *
      (3 : ℝ) ^ (-(s * (q : ℝ))) := by positivity
  unfold fieldOneScoreTerm fieldOneScoreTermScale
  simpa only [mul_assoc] using
    (isBigOWith_gammaTwo_fieldOneCubeMajorant M i
      (m + 1 + (fieldOneIndexDistance m i + q))).const_mul hc

def fieldOneGeometricBase (s : ℝ) : ℝ := (3 : ℝ) ^ (-s)

theorem fieldOneGeometricBase_nonneg (s : ℝ) :
    0 ≤ fieldOneGeometricBase s :=
  Real.rpow_nonneg (by norm_num) _

theorem fieldOneGeometricBase_lt_one {s : ℝ} (hs : 0 < s) :
    fieldOneGeometricBase s < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem fieldOne_qWeight_eq_pow (s : ℝ) (q : ℕ) :
    (3 : ℝ) ^ (-(s * (q : ℝ))) = fieldOneGeometricBase s ^ q := by
  unfold fieldOneGeometricBase
  calc
    (3 : ℝ) ^ (-(s * (q : ℝ))) = (3 : ℝ) ^ ((-s) * (q : ℝ)) := by
      congr 1
      ring
    _ = ((3 : ℝ) ^ (-s)) ^ (q : ℝ) :=
      Real.rpow_mul (by norm_num) _ _
    _ = ((3 : ℝ) ^ (-s)) ^ q := Real.rpow_natCast _ _

theorem summable_fieldOne_geometric_sqrt (s : ℝ) (hs : 0 < s) (n : ℕ) :
    Summable fun q : ℕ ↦
      (3 : ℝ) ^ (-(s * (q : ℝ))) *
        Real.sqrt ((n + q : ℕ) + 1) := by
  have hbase := summable_geom_mul_sqrt
    (fieldOneGeometricBase_nonneg s) (fieldOneGeometricBase_lt_one hs)
  have hdom : Summable fun q : ℕ ↦
      Real.sqrt ((n : ℝ) + 1) *
        (fieldOneGeometricBase s ^ q * Real.sqrt ((q : ℝ) + 1)) :=
    hbase.mul_left _
  refine Summable.of_nonneg_of_le (fun q ↦ by positivity) (fun q ↦ ?_) hdom
  rw [fieldOne_qWeight_eq_pow]
  have hsqrt := sqrt_natAdd_le_mul n q
  have hmul := mul_le_mul_of_nonneg_left hsqrt
    (pow_nonneg (fieldOneGeometricBase_nonneg s) q)
  simpa only [Nat.cast_add, Nat.cast_one] using hmul.trans_eq (by ring)

theorem fieldOneScoreTermScale_le_sqrt {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s K : ℝ} (hK : 0 ≤ K)
    (m i q : ℕ) :
    fieldOneScoreTermScale M s K m i q ≤
      (K * (3 : ℝ) ^ (-(s * (fieldOneIndexDistance m i : ℝ)) / 2) *
        fieldOneGammaDimScale M) *
      ((3 : ℝ) ^ (-(s * (q : ℝ))) *
        Real.sqrt ((2 * fieldOneIndexDistance m i + q : ℕ) + 1)) := by
  unfold fieldOneScoreTermScale
  have hcoeff : 0 ≤ K *
      (3 : ℝ) ^ (-(s * (fieldOneIndexDistance m i : ℝ)) / 2) *
      (3 : ℝ) ^ (-(s * (q : ℝ))) := by positivity
  have h := mul_le_mul_of_nonneg_left
    (fieldOneCubeMajorantScale_le_sqrt M m i q) hcoeff
  calc
    K * (3 : ℝ) ^ (-(s * (fieldOneIndexDistance m i : ℝ)) / 2) *
        (3 : ℝ) ^ (-(s * (q : ℝ))) *
        fieldOneCubeMajorantScale M i
          (m + 1 + (fieldOneIndexDistance m i + q)) ≤
      K * (3 : ℝ) ^ (-(s * (fieldOneIndexDistance m i : ℝ)) / 2) *
        (3 : ℝ) ^ (-(s * (q : ℝ))) *
        (fieldOneGammaDimScale M *
          Real.sqrt ((2 * fieldOneIndexDistance m i + q : ℕ) + 1)) := h
    _ = _ := by ring

theorem summable_fieldOneScoreTermScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s K : ℝ}
    (hs : 0 < s) (hK : 0 < K) (m i : ℕ) :
    Summable fun q : ℕ ↦ fieldOneScoreTermScale M s K m i q := by
  have hupper := (summable_fieldOne_geometric_sqrt s hs
    (2 * fieldOneIndexDistance m i)).mul_left
      (K * (3 : ℝ) ^ (-(s * (fieldOneIndexDistance m i : ℝ)) / 2) *
        fieldOneGammaDimScale M)
  refine Summable.of_nonneg_of_le (fun q ↦ ?_) (fun q ↦ ?_) hupper
  · unfold fieldOneScoreTermScale
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg (by norm_num) _))
      (fieldOneCubeMajorantScale_pos M i _).le
  · exact fieldOneScoreTermScale_le_sqrt M hK.le m i q

noncomputable def fieldOneScoreENN {d : ℕ} (s K : ℝ) (m i : ℕ) :
    _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ :=
  fun omega ↦ ∑' q : ℕ,
    ENNReal.ofReal (fieldOneScoreTerm s K m i q omega)

/-- Real-valued score column passed to `concentration_for_scales`. -/
noncomputable def fieldOneScore {d : ℕ} (s K : ℝ) (m i : ℕ) :
    _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
  fun omega ↦ (fieldOneScoreENN (d := d) s K m i omega).toReal

theorem measurable_fieldOneScore_shellSigma {d : ℕ}
    (s K : ℝ) (m i : ℕ) :
    Measurable[shellSigma d i] (fieldOneScore (d := d) s K m i) := by
  let : MeasurableSpace (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
    shellSigma d i
  unfold fieldOneScore fieldOneScoreENN
  apply ENNReal.measurable_toReal.comp
  exact Measurable.tsum fun q ↦
    ENNReal.continuous_ofReal.measurable.comp
      (measurable_fieldOneScoreTerm_shellSigma s K m i q)

theorem isBigOWith_gammaTwo_fieldOneScore_tsum {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s K : ℝ}
    (hs : 0 < s) (hK : 0 < K) (m i : ℕ) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ ∑' q : ℕ, fieldOneScoreTerm s K m i q omega)
      (gammaTriangleConst 2 * ∑' q : ℕ, fieldOneScoreTermScale M s K m i q) := by
  apply isBigOWith_gammaSigma_tsum_nonneg (by norm_num : (0 : ℝ) < 2)
  · exact fun q omega ↦ fieldOneScoreTerm_nonneg hK.le m i q omega
  · exact fun q ↦ (measurable_fieldOneScoreTerm_shellSigma s K m i q).mono
      (shellSigma_le i) le_rfl
  · intro q
    unfold fieldOneScoreTermScale
    exact mul_pos
      (mul_pos (mul_pos hK (Real.rpow_pos_of_pos (by norm_num) _))
        (Real.rpow_pos_of_pos (by norm_num) _))
      (fieldOneCubeMajorantScale_pos M i _)
  · exact summable_fieldOneScoreTermScale M hs hK m i
  · exact fun q ↦ isBigOWith_gammaTwo_fieldOneScoreTerm M hK.le m i q

theorem ae_summable_fieldOneScoreTerm {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s K : ℝ}
    (hs : 0 < s) (hK : 0 < K) (m i : ℕ) :
    ∀ᵐ omega ∂M.P.toMeasure,
      Summable fun q : ℕ ↦ fieldOneScoreTerm s K m i q omega := by
  apply ae_summable_of_isBigOWith_gammaSigma
    (X := fun q ↦ fieldOneScoreTerm (d := d) s K m i q)
    (a := fun q ↦ fieldOneScoreTermScale M s K m i q)
    (by norm_num : (0 : ℝ) < 2)
  · exact fun q omega ↦ fieldOneScoreTerm_nonneg hK.le m i q omega
  · exact fun q ↦ ((measurable_fieldOneScoreTerm_shellSigma s K m i q).mono
      (shellSigma_le i) le_rfl).aemeasurable
  · intro q
    unfold fieldOneScoreTermScale
    exact mul_pos
      (mul_pos (mul_pos hK (Real.rpow_pos_of_pos (by norm_num) _))
        (Real.rpow_pos_of_pos (by norm_num) _))
      (fieldOneCubeMajorantScale_pos M i _)
  · exact summable_fieldOneScoreTermScale M hs hK m i
  · exact fun q ↦ isBigOWith_gammaTwo_fieldOneScoreTerm M hK.le m i q

theorem ae_fieldOneScore_eq_tsum {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s K : ℝ}
    (hs : 0 < s) (hK : 0 < K) (m i : ℕ) :
    fieldOneScore (d := d) s K m i =ᵐ[M.P.toMeasure]
      fun omega ↦ ∑' q : ℕ, fieldOneScoreTerm s K m i q omega := by
  filter_upwards [ae_summable_fieldOneScoreTerm M hs hK m i] with omega hsum
  unfold fieldOneScore fieldOneScoreENN
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun q ↦ fieldOneScoreTerm_nonneg hK.le m i q omega) hsum,
    ENNReal.toReal_ofReal
      (tsum_nonneg fun q ↦ fieldOneScoreTerm_nonneg hK.le m i q omega)]

theorem isBigOWith_gammaTwo_fieldOneScore {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s K : ℝ}
    (hs : 0 < s) (hK : 0 < K) (m i : ℕ) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (fieldOneScore (d := d) s K m i)
      (gammaTriangleConst 2 * ∑' q : ℕ, fieldOneScoreTermScale M s K m i q) := by
  have heq := ae_fieldOneScore_eq_tsum M hs hK m i
  have hraw := isBigOWith_gammaTwo_fieldOneScore_tsum M hs hK m i
  intro t ht
  calc
    M.P.toMeasure.real
        (upperTailEvent (fieldOneScore s K m i)
          ((gammaTriangleConst 2 * ∑' q : ℕ,
            fieldOneScoreTermScale M s K m i q) * t)) =
      M.P.toMeasure.real
        (upperTailEvent (fun omega ↦ ∑' q : ℕ, fieldOneScoreTerm s K m i q omega)
          ((gammaTriangleConst 2 * ∑' q : ℕ,
            fieldOneScoreTermScale M s K m i q) * t)) := by
      apply congrArg ENNReal.toReal
      apply measure_congr
      filter_upwards [heq] with omega homega
      change
        ((gammaTriangleConst 2 * ∑' q : ℕ,
            fieldOneScoreTermScale M s K m i q) * t < fieldOneScore s K m i omega) =
          ((gammaTriangleConst 2 * ∑' q : ℕ,
            fieldOneScoreTermScale M s K m i q) * t <
            ∑' q : ℕ, fieldOneScoreTerm s K m i q omega)
      exact congrArg (fun x : ℝ ↦
        (gammaTriangleConst 2 * ∑' q : ℕ,
          fieldOneScoreTermScale M s K m i q) * t < x) homega
    _ ≤ (gammaSigma 2 t)⁻¹ := hraw ht

/-- The manuscript's extension by zero to integer rows and columns. -/
noncomputable def fieldOneScoreArray {d : ℕ} (s K : ℝ) :
    ℤ → ℤ → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
  fun m i omega ↦
    if 0 ≤ m ∧ 0 ≤ i then fieldOneScore s K m.toNat i.toNat omega else 0

theorem fieldOneScore_nonneg {d : ℕ} (s K : ℝ) (m i : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ fieldOneScore (d := d) s K m i omega :=
  ENNReal.toReal_nonneg

theorem measurable_fieldOneScoreArray {d : ℕ} (s K : ℝ) (m i : ℤ) :
    Measurable (fieldOneScoreArray (d := d) s K m i) := by
  unfold fieldOneScoreArray
  split_ifs
  · exact (measurable_fieldOneScore_shellSigma s K m.toNat i.toNat).mono
      (shellSigma_le i.toNat) le_rfl
  · exact measurable_const

theorem fieldOneScoreArray_nonneg {d : ℕ} (s K : ℝ)
    (m i : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ fieldOneScoreArray (d := d) s K m i omega := by
  unfold fieldOneScoreArray
  split_ifs
  · exact fieldOneScore_nonneg s K m.toNat i.toNat omega
  · exact le_rfl

theorem columnsIndep_fieldOneScoreArray {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s K : ℝ) {r : ℕ} (hr : 1 ≤ r) :
    SubdiffusiveProcess.Concentration.ColumnsIndep M.P.toMeasure
      (fieldOneScoreArray (d := d) s K) r := by
  apply columnsIndep_of_nonnegative_shellColumn_of_constant M _ hr
  · intro m i hi
    unfold fieldOneScoreArray
    by_cases hm : 0 ≤ m
    · simpa only [hm, hi, and_self, ite_true, Int.toNat_of_nonneg hi] using
        measurable_fieldOneScore_shellSigma (d := d) s K m.toNat i.toNat
    · simpa only [hm, false_and, ite_false] using
        (measurable_const : Measurable[shellSigma d i.toNat]
          (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ (0 : ℝ)))
  · intro m i hi
    refine ⟨0, fun omega ↦ ?_⟩
    simp [fieldOneScoreArray, show ¬0 ≤ i by omega]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
