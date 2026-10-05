module

public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.CutoffSpeedMeasure
public import SubdiffusiveProcess.Main.CutoffSpeedDensity
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.WeightedChaosCutoff
public import SubdiffusiveProcess.Main.ChaosCutoff
public import SubdiffusiveProcess.Main.ConditionalFineFiltration
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Main.SemigroupSymmetric
public import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
public import SubdiffusiveProcess.Main.HasStrongMarkovRestart
public import SubdiffusiveProcess.Main.HasFiniteMeanExits
public import SubdiffusiveProcess.Main.PathLevyProkhorovDist
public import SubdiffusiveProcess.Main.PhysicalRescaledPath
public import SubdiffusiveProcess.Main.PhysicalTimeFactor
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.ResponseMoments.DirichletForm
public import SubdiffusiveProcess.VariationalResponses.KilledInverse
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Probability.CubeMassMartingale
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Inputs.MarkovProcesses
public import MarkovProcess.Trajectory.StoppingLtTop
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.Frozen.Vocab.Ahom
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

noncomputable section
namespace SubdiffusiveProcess.Paper



lemma aux_in_timescale_rpow_interp {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    x * ((3 : ℝ) ^ t) ^ Real.logb 3 (y / x) = x ^ (1 - t) * y ^ t := by
  rw [Real.rpow_def_of_pos (Real.rpow_pos_of_pos (by norm_num) _),
    Real.log_rpow (by norm_num), Real.rpow_def_of_pos hx,
    Real.rpow_def_of_pos hy, Real.logb, Real.log_div hy.ne' hx.ne']
  nth_rewrite 1 [show x = Real.exp (Real.log x) by rw [Real.exp_log hx]]
  rw [← Real.exp_add]
  rw [← Real.exp_add]
  congr 1
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 3))]
  ring_nf

lemma aux_in_timescale_index_lower {r : ℝ} (hr : 1 ≤ r) :
    (3 : ℝ) ^ (⌊Real.logb 3 r⌋₊ : ℕ) ≤ r := by
  have hlog : 0 ≤ Real.logb 3 r := Real.logb_nonneg (by norm_num) hr
  have hfloor : ((⌊Real.logb 3 r⌋₊ : ℕ) : ℝ) ≤ Real.logb 3 r :=
    Nat.floor_le hlog
  have hpow : (3 : ℝ) ^ ((⌊Real.logb 3 r⌋₊ : ℕ) : ℝ) ≤
      (3 : ℝ) ^ Real.logb 3 r :=
    Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 3) |>.mpr hfloor
  rw [Real.rpow_natCast,
    Real.rpow_logb (by norm_num) (by norm_num) (by linarith)] at hpow
  exact hpow

lemma aux_in_timescale_index_upper {r : ℝ} (hr : 1 ≤ r) :
    r < (3 : ℝ) ^ (⌊Real.logb 3 r⌋₊ + 1 : ℕ) := by
  have hlog : 0 ≤ Real.logb 3 r := Real.logb_nonneg (by norm_num) hr
  have hfloor : Real.logb 3 r < (⌊Real.logb 3 r⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hpow : (3 : ℝ) ^ Real.logb 3 r <
      (3 : ℝ) ^ ((⌊Real.logb 3 r⌋₊ : ℝ) + 1) :=
    Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 3) |>.mpr hfloor
  rw [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)] at hpow
  have hcast : (3 : ℝ) ^ ((⌊Real.logb 3 r⌋₊ : ℝ) + 1) =
      (3 : ℝ) ^ (⌊Real.logb 3 r⌋₊ + 1 : ℕ) := by
    rw [show ((⌊Real.logb 3 r⌋₊ : ℝ) + 1) =
        ((⌊Real.logb 3 r⌋₊ + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  rwa [hcast] at hpow

lemma aux_in_timescale_triadic_index (m : ℕ) :
    ⌊Real.logb 3 ((3 : ℝ) ^ m)⌋₊ = m := by
  have hcast : ((3 : ℝ) ^ m) = (3 : ℝ) ^ (m : ℝ) :=
    (Real.rpow_natCast 3 m).symm
  rw [hcast, Real.logb_rpow (b := 3) (by norm_num) (by norm_num),
    Nat.floor_natCast]

lemma aux_in_timescale_triadic_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (m : ℕ) :
    0 < (3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m := by
  exact div_pos (by positivity) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M m)

lemma aux_in_timescale_triadic_mono {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (m : ℕ) :
    (3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m ≤
      (3 : ℝ) ^ (2 * (m + 1)) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (m + 1) := by
  have horder := (SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds.2 M (m + 1) m
    (by omega)).1
  have hnum : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * m) := by positivity
  have hdiv := div_le_div_of_nonneg_left hnum
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (m + 1)) horder
  calc
    (3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m ≤
        (3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (m + 1) := hdiv
    _ ≤ (3 : ℝ) ^ (2 * (m + 1)) /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M (m + 1) := by
      apply div_le_div_of_nonneg_right _ (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (m + 1)).le
      have hpow : (3 : ℝ) ^ (2 * m) ≤ (3 : ℝ) ^ (2 * (m + 1)) := by
        apply pow_le_pow_right₀ (by norm_num)
        omega
      exact hpow

lemma aux_in_timescale_triadic_ratio {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {m n : ℕ} (hmn : m ≤ n) :
    (3 : ℝ) ^ (2 * n) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M n ≤
      ((3 : ℝ) ^ (2 * (n - m)) *
        Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((n - m : ℕ) : ℝ))) *
        ((3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m) := by
  rcases hmn.eq_or_lt with rfl | hmn
  · simp
  have horder := (SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds.2 M n m hmn).2
  have hdiv : 1 / SubdiffusiveProcess.CoarseGrainingVocab.ahom M n ≤
      Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((n - m : ℕ) : ℝ)) /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M m := by
    apply (div_le_div_iff₀ (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M n)
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M m)).2
    simpa [one_mul] using horder
  have hpow : (3 : ℝ) ^ (2 * n) =
      (3 : ℝ) ^ (2 * (n - m)) * (3 : ℝ) ^ (2 * m) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    (3 : ℝ) ^ (2 * n) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M n =
        (3 : ℝ) ^ (2 * n) * (1 / SubdiffusiveProcess.CoarseGrainingVocab.ahom M n) := by
          simp [div_eq_mul_inv]
    _ ≤ (3 : ℝ) ^ (2 * n) *
        (Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((n - m : ℕ) : ℝ)) /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M m) := by
      exact mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = ((3 : ℝ) ^ (2 * (n - m)) *
        Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((n - m : ℕ) : ℝ))) *
        ((3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m) := by
      rw [hpow]
      field_simp

lemma aux_in_timescale_factor (tau : ℝ) (n : ℕ) :
    (3 : ℝ) ^ (2 * n) * Real.exp (2 * tau * (n : ℝ)) =
      ((3 : ℝ) ^ n) ^ (2 + 2 * tau / Real.log 3) := by
  have hthree : (3 : ℝ) ^ (2 * n) =
      Real.exp ((2 * (n : ℝ)) * Real.log 3) := by
    rw [← Real.rpow_natCast (3 : ℝ) (2 * n),
      Real.rpow_def_of_pos (by norm_num)]
    congr 1
    push_cast
    ring
  rw [hthree, Real.rpow_def_of_pos (by positivity), Real.log_pow,
    ← Real.exp_add]
  congr 1
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 3))]

theorem in_timescale {d : ℕ} (_hd : 2 ≤ d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ∃ (Tscale : ℝ → ℝ) (C beta : ℝ), 0 < C ∧ 0 < beta ∧
      (∀ m : ℕ, Tscale ((3 : ℝ) ^ m) = ((3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m)) ∧
      (∀ (m : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1 →
        Tscale ((3 : ℝ) ^ ((m : ℝ) + t))
          = ((3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m) ^ (1 - t)
            * ((3 : ℝ) ^ (2 * (m + 1)) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (m + 1)) ^ t) ∧
      (∀ r : ℝ, 1 ≤ r → 0 < Tscale r) ∧
      beta ≤ 2 + 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P / Real.log 3 ∧
      (∀ r S : ℝ, 1 ≤ r → r ≤ S → Tscale S ≤ C * (S / r) ^ beta * Tscale r) := by
  let q : ℕ → ℝ := fun m =>
    (3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m
  let e : ℕ → ℝ := fun m => Real.logb 3 (q (m + 1) / q m)
  let idx : ℝ → ℕ := fun r => ⌊Real.logb 3 r⌋₊
  let Tscale : ℝ → ℝ := fun r =>
    if 1 ≤ r then q (idx r) * (r / (3 : ℝ) ^ idx r) ^ e (idx r) else 1
  let C : ℝ := (9 : ℝ) ^ (2 + 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P / Real.log 3)
  let beta : ℝ := 2 + 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P / Real.log 3
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have htau : 0 < _root_.SubdiffusiveProcess.Model.tauSq M.P := M.G4.tauSq_pos
  have hbeta : 0 < beta := by
    dsimp [beta]
    have hquot : 0 < 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P / Real.log 3 :=
      div_pos (mul_pos (by norm_num) htau) hlog3
    linarith
  have hqpos (m : ℕ) : 0 < q m := by
    simpa [q] using aux_in_timescale_triadic_pos M m
  have hqmono (m : ℕ) : q m ≤ q (m + 1) := by
    simpa [q] using aux_in_timescale_triadic_mono M m
  refine ⟨Tscale, C, beta, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [C]
    positivity
  · exact hbeta
  · intro m
    dsimp [Tscale, idx]
    rw [ite_eq_left (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)),
      aux_in_timescale_triadic_index m]
    simp [q]
  · intro m t ht0 ht1
    have hnonneg : 0 ≤ (m : ℝ) + t := by positivity
    have hbase1 : (1 : ℝ) ≤ (3 : ℝ) ^ ((m : ℝ) + t) :=
      Real.one_le_rpow (by norm_num) hnonneg
    by_cases ht : t = 1
    · subst t
      have harg : (3 : ℝ) ^ ((m : ℝ) + 1) = (3 : ℝ) ^ (m + 1) := by
        rw [show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast]
      rw [harg]
      dsimp [Tscale, idx]
      rw [ite_eq_left (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)),
        aux_in_timescale_triadic_index]
      simp [q]
    · have htlt : t < 1 := lt_of_le_of_ne ht1 ht
      have hidx : idx ((3 : ℝ) ^ ((m : ℝ) + t)) = m := by
        dsimp [idx]
        rw [Real.logb_rpow (b := 3) (by norm_num) (by norm_num)]
        apply (Nat.floor_eq_iff (by positivity : 0 ≤ (m : ℝ) + t)).2
        constructor <;> linarith
      have hratio :
          (3 : ℝ) ^ ((m : ℝ) + t) / (3 : ℝ) ^ m = (3 : ℝ) ^ t := by
        rw [← Real.rpow_natCast (3 : ℝ) m, ← Real.rpow_sub (by norm_num)]
        congr 1
        ring
      dsimp [Tscale]
      rw [ite_eq_left hbase1, hidx, hratio]
      change q m * ((3 : ℝ) ^ t) ^ e m = q m ^ (1 - t) * q (m + 1) ^ t
      exact aux_in_timescale_rpow_interp (hqpos m) (hqpos (m + 1)) t
  · intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hbase : 0 < r / (3 : ℝ) ^ idx r := by positivity
    dsimp [Tscale]
    rw [ite_eq_left hr]
    exact mul_pos (hqpos (idx r)) (Real.rpow_pos_of_pos hbase _)
  · dsimp [beta]
    rfl
  · intro r S hr hRS
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hS : 1 ≤ S := hr.trans hRS
    let k : ℕ := idx r
    let l : ℕ := idx S
    have hkl : k ≤ l := by
      dsimp [k, l, idx]
      apply Nat.floor_mono
      exact (Real.logb_le_logb (b := 3) (by norm_num) hrpos
        (hrpos.trans_le hRS)).mpr hRS
    have hk1 : k ≤ l + 1 := hkl.trans (Nat.le_succ l)
    have hbaseR1 : 1 ≤ r / (3 : ℝ) ^ k := by
      apply (le_div_iff₀ (by positivity)).2
      simpa [k, idx] using aux_in_timescale_index_lower hr
    have hbaseR3 : r < 3 * (3 : ℝ) ^ k := by
      simpa [k, idx, pow_succ, mul_comm] using aux_in_timescale_index_upper hr
    have hbaseS3 : S / (3 : ℝ) ^ l < 3 := by
      apply (div_lt_iff₀ (by positivity)).2
      simpa [l, idx, pow_succ, mul_comm] using aux_in_timescale_index_upper hS
    have hbaseS1 : (3 : ℝ) ^ l ≤ S := by
      simpa [l, idx] using aux_in_timescale_index_lower hS
    have he_nonneg (j : ℕ) : 0 ≤ e j := by
      dsimp [e]
      apply Real.logb_nonneg (by norm_num)
      apply (le_div_iff₀ (hqpos j)).2
      simpa using hqmono j
    have hpoweq (j : ℕ) : (3 : ℝ) ^ e j = q (j + 1) / q j := by
      dsimp [e]
      simpa using Real.rpow_logb (by norm_num) (by norm_num)
        (div_pos (hqpos (j + 1)) (hqpos j))
    have hupperT : Tscale S ≤ q (l + 1) := by
      change (if 1 ≤ S then q (idx S) *
        (S / (3 : ℝ) ^ idx S) ^ e (idx S) else 1) ≤ q (l + 1)
      rw [ite_eq_left hS]
      change q l * (S / (3 : ℝ) ^ l) ^ e l ≤ q (l + 1)
      have hpowle : (S / (3 : ℝ) ^ l) ^ e l ≤ (3 : ℝ) ^ e l :=
        Real.rpow_le_rpow (by positivity) hbaseS3.le (he_nonneg l)
      calc
        q l * (S / (3 : ℝ) ^ l) ^ e l ≤ q l * (3 : ℝ) ^ e l :=
          mul_le_mul_of_nonneg_left hpowle (hqpos l).le
        _ = q (l + 1) := by
          rw [hpoweq l]
          field_simp [ne_of_gt (hqpos l)]
    have hlowerT : q k ≤ Tscale r := by
      change q k ≤ (if 1 ≤ r then q (idx r) *
        (r / (3 : ℝ) ^ idx r) ^ e (idx r) else 1)
      rw [ite_eq_left hr]
      change q k ≤ q k * (r / (3 : ℝ) ^ k) ^ e k
      have hpowge : 1 ≤ (r / (3 : ℝ) ^ k) ^ e k :=
        Real.one_le_rpow hbaseR1 (he_nonneg k)
      simpa [one_mul] using mul_le_mul_of_nonneg_left hpowge (hqpos k).le
    have hTrpos : 0 < Tscale r := by
      change 0 < (if 1 ≤ r then q (idx r) *
        (r / (3 : ℝ) ^ idx r) ^ e (idx r) else 1)
      rw [ite_eq_left hr]
      exact mul_pos (hqpos (idx r))
        (Real.rpow_pos_of_pos (by positivity) _)
    let n : ℕ := l + 1 - k
    have hpowgap : (3 : ℝ) ^ n * (3 : ℝ) ^ k = (3 : ℝ) ^ (l + 1) := by
      rw [← pow_add]
      congr 1
      dsimp [n]
      omega
    have hnum : (3 : ℝ) ^ (l + 1) ≤ 3 * S := by
      calc
        (3 : ℝ) ^ (l + 1) = 3 * (3 : ℝ) ^ l := by
          rw [pow_succ]
          ring
        _ ≤ 3 * S := mul_le_mul_of_nonneg_left hbaseS1 (by norm_num)
    have hmul : (3 : ℝ) ^ n * r < 9 * S := by
      have hmul' := mul_lt_mul_of_pos_left hbaseR3
        (show 0 < (3 : ℝ) ^ n by positivity)
      have hrewrite : (3 : ℝ) ^ n * (3 * (3 : ℝ) ^ k) =
          3 * (3 : ℝ) ^ (l + 1) := by
        calc
          (3 : ℝ) ^ n * (3 * (3 : ℝ) ^ k) =
              3 * ((3 : ℝ) ^ n * (3 : ℝ) ^ k) := by ring
          _ = 3 * (3 : ℝ) ^ (l + 1) := by rw [hpowgap]
      calc
        (3 : ℝ) ^ n * r < (3 : ℝ) ^ n * (3 * (3 : ℝ) ^ k) := hmul'
        _ = 3 * (3 : ℝ) ^ (l + 1) := hrewrite
        _ ≤ 9 * S := by nlinarith [hnum]
    have hgap : (3 : ℝ) ^ n ≤ 9 * (S / r) := by
      rw [show 9 * (S / r) = (9 * S) / r by ring]
      exact (le_div_iff₀ hrpos).2 hmul.le
    have hfactor :
        (3 : ℝ) ^ (2 * n) *
            Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (n : ℝ)) ≤
          C * (S / r) ^ beta := by
      have hpow := Real.rpow_le_rpow (by positivity) hgap hbeta.le
      calc
        (3 : ℝ) ^ (2 * n) *
              Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (n : ℝ)) =
            ((3 : ℝ) ^ n) ^ beta := by
              simpa [beta] using aux_in_timescale_factor
                (_root_.SubdiffusiveProcess.Model.tauSq M.P) n
        _ ≤ (9 * (S / r)) ^ beta := hpow
        _ = (9 : ℝ) ^ beta * (S / r) ^ beta := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
        _ = C * (S / r) ^ beta := rfl
    have hratio := aux_in_timescale_triadic_ratio M hk1
    have hratio' : q (l + 1) ≤
        ((3 : ℝ) ^ (2 * n) *
          Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (n : ℝ))) * q k := by
      simpa [q, n] using hratio
    calc
      Tscale S ≤ q (l + 1) := hupperT
      _ ≤ ((3 : ℝ) ^ (2 * n) *
          Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (n : ℝ))) * q k := hratio'
      _ ≤ ((3 : ℝ) ^ (2 * n) *
          Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (n : ℝ))) * Tscale r := by
        exact mul_le_mul_of_nonneg_left hlowerT (by positivity)
      _ ≤ (C * (S / r) ^ beta) * Tscale r :=
        mul_le_mul_of_nonneg_right hfactor hTrpos.le

end SubdiffusiveProcess.Paper
