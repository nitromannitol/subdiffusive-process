module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section45Support
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepScales
public import SubdiffusiveProcess.Providers.Section5.OneStepConcretePrimalClosure
public import SubdiffusiveProcess.Section3.SpecialTwoDExactFormula
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Assembly of the sharp diffusivity asymptotic

This module states the one-step upper and lower conclusions and combines them
into the logarithmic block estimate. Concrete primal budgets supply the upper
bound, and the dual-cell construction supplies the lower bound. The final
provider `SubdiffusiveProcess.Providers.Section5.sharp_asymptotic` calls
`Section5DualCompetitor.sharp_asymptotic_final`; keeping the scalar block
arithmetic here avoids an import cycle with that dual construction.
-/

namespace SubdiffusiveProcess.Providers.Section5

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- The centered logarithmic diffusivity appearing in
`e.main.asymptotic`. -/
def sharpCenteredLog {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) : ℝ :=
  Real.log (ahom M m) +
    2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d

/-- The sharp asymptotic in dimension two follows directly from the planar
self-duality formula. The higher-dimensional construction uses the one-step
primal and dual estimates. -/
theorem sharp_asymptotic_two_dimensional :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel 2,
        M.delta ≤ delta0 → ∀ m : ℕ,
          |Real.log (ahom M m) +
              2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / 2| ≤
            C * M.delta ^ 2 * |Real.log M.delta| *
              (1 + (m : ℝ) * M.delta) := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro M _hdelta m
  rw [_root_.SubdiffusiveProcess.Section3.special_two_d_exact_formula M m,
    Real.log_exp]
  have hzero :
      -(m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
          2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / 2 = 0 := by
    ring
  rw [hzero, abs_zero]
  apply mul_nonneg
  · exact mul_nonneg (mul_nonneg zero_le_one (sq_nonneg _)) (abs_nonneg _)
  · have hm : (0 : ℝ) ≤ m := by positivity
    have hdelta := M.shellPrefix.delta_pos
    positivity



def SharpOneStepUpperConclusion (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ),
      (h : ℝ) ≤ M.delta⁻¹ →
      16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n →
      ahom M (n + h) ≤ ahom M n *
        (1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / d +
          C * M.delta ^ 4 * (h : ℝ) ^ 2 +
          C * M.delta ^ 2 * |Real.log M.delta|)

/-- The exact `e.one.step.lower` output, in the same lower-endpoint
parametrization as `SharpOneStepUpperConclusion`. -/
def SharpOneStepLowerConclusion (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ),
      (h : ℝ) ≤ M.delta⁻¹ →
      16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n →
      (ahom M (n + h))⁻¹ ≤ (ahom M n)⁻¹ *
        (1 + 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / d +
          C * M.delta ^ 4 * (h : ℝ) ^ 2 +
          C * M.delta ^ 2 * |Real.log M.delta|)

/-- The exact post-one-step payload.

The two one-step estimates first give the logarithmic increment on every full
block of length `H` and on the final remainder block.  The base estimate is
available at every scale below `J`.  The two numerical inequalities on `H`
are the only properties of `H = floor (delta^-1)` used by the Euclidean block
telescope.  Thus this carrier contains the analytic recurrence but none of
the telescope performed below. -/
def SharpBlockIncrementConclusion (d : ℕ) : Prop :=
  ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
    ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      M.delta ≤ delta0 →
        ∃ J H : ℕ, 0 < H ∧
          M.delta * (H : ℝ) ≤ 1 ∧
          (1 : ℝ) / 2 ≤ M.delta * (H : ℝ) ∧
          (∀ m : ℕ, m ≤ J →
            |sharpCenteredLog M m| ≤
              C * M.delta ^ 2 * |Real.log M.delta|) ∧
          (∀ q : ℕ,
            |sharpCenteredLog M (J + (q + 1) * H) -
                sharpCenteredLog M (J + q * H)| ≤
              C * M.delta ^ 4 * (H : ℝ) ^ 2 +
                C * M.delta ^ 2 * |Real.log M.delta|) ∧
          ∀ (q r : ℕ), 0 < r → r < H →
            |sharpCenteredLog M (J + q * H + r) -
                sharpCenteredLog M (J + q * H)| ≤
              C * M.delta ^ 4 * (r : ℝ) ^ 2 +
                C * M.delta ^ 2 * |Real.log M.delta|

/-- Assemble the exact post-one-step block payload from the two printed
one-step lemmas.  All scale choices, constant unification, base-scale
arithmetic, and logarithmic conversion are discharged here. -/
theorem sharp_block_increments_of_one_step_bounds {d : ℕ}
    (hUpper : SharpOneStepUpperConclusion d)
    (hLower : SharpOneStepLowerConclusion d) :
    SharpBlockIncrementConclusion d := by
  rcases hUpper with ⟨Cupper, hCupper, hUpper⟩
  rcases hLower with ⟨Clower, hClower, hLower⟩
  let C : ℝ := max 132 (max Cupper Clower)
  have hC132 : (132 : ℝ) ≤ C := le_max_left _ _
  have hCupperLe : Cupper ≤ C :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hClowerLe : Clower ≤ C :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) hC132
  refine ⟨1 / 2, C, by norm_num, hC, ?_⟩
  intro M _hM
  let J : ℕ := Section5Support.sharpStartScale M.delta
  let H : ℕ := Section5Support.sharpBlockLength M.delta
  have hH : 0 < H := Section5Support.sharpBlockLength_pos
    M.shellPrefix.delta_pos M.shellPrefix.delta_le_half
  have hHupper : M.delta * (H : ℝ) ≤ 1 :=
    Section5Support.delta_mul_sharpBlockLength_le_one M.shellPrefix.delta_pos
  have hHlower : (1 : ℝ) / 2 ≤ M.delta * (H : ℝ) :=
    Section5Support.half_le_delta_mul_sharpBlockLength
      M.shellPrefix.delta_pos M.shellPrefix.delta_le_half
  have hHinv : (H : ℝ) ≤ M.delta⁻¹ := by
    exact Nat.floor_le (inv_nonneg.mpr M.shellPrefix.delta_pos.le)
  have hsourceJ : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ J :=
    Section5Support.sourceStartScale_le_sharpStartScale
      M.shellPrefix.delta_pos M.shellPrefix.delta_le_half
  refine ⟨J, H, hH, hHupper, hHlower, ?_, ?_, ?_⟩
  · intro m hm
    have hbase := Section5Support.sharp_base_scale_bound M m hm
    exact hbase.trans (by
      have hnonneg : 0 ≤ M.delta ^ 2 * |Real.log M.delta| := by positivity
      nlinarith)
  · intro q
    let n : ℕ := J + q * H
    let error : ℝ := C * M.delta ^ 4 * (H : ℝ) ^ 2 +
      C * M.delta ^ 2 * |Real.log M.delta|
    have hnsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n := by
      dsimp [n]
      omega
    have hupperRaw := hUpper M n H hHinv hnsource
    have hlowerRaw := hLower M n H hHinv hnsource
    have hprev : 0 < ahom M n :=
      (Real.exp_pos _).trans_le
        (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M n)
    have hprevInv : 0 < (ahom M n)⁻¹ := inv_pos.mpr hprev
    have herrorUpper :
        Cupper * M.delta ^ 4 * (H : ℝ) ^ 2 +
            Cupper * M.delta ^ 2 * |Real.log M.delta| ≤ error := by
      dsimp [error]
      have hfour : 0 ≤ M.delta ^ 4 * (H : ℝ) ^ 2 := by positivity
      have htwo : 0 ≤ M.delta ^ 2 * |Real.log M.delta| := by positivity
      nlinarith
    have herrorLower :
        Clower * M.delta ^ 4 * (H : ℝ) ^ 2 +
            Clower * M.delta ^ 2 * |Real.log M.delta| ≤ error := by
      dsimp [error]
      have hfour : 0 ≤ M.delta ^ 4 * (H : ℝ) ^ 2 := by positivity
      have htwo : 0 ≤ M.delta ^ 2 * |Real.log M.delta| := by positivity
      nlinarith
    have hupperCommon :
        ahom M (n + H) ≤ ahom M n *
          (1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (H : ℝ) / d + error) := by
      calc
        ahom M (n + H) ≤ ahom M n *
            (1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (H : ℝ) / d +
              Cupper * M.delta ^ 4 * (H : ℝ) ^ 2 +
              Cupper * M.delta ^ 2 * |Real.log M.delta|) := hupperRaw
        _ ≤ ahom M n *
            (1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (H : ℝ) / d + error) := by
          apply mul_le_mul_of_nonneg_left _ hprev.le
          linarith
    have hlowerCommon :
        (ahom M (n + H))⁻¹ ≤ (ahom M n)⁻¹ *
          (1 + 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (H : ℝ) / d + error) := by
      calc
        (ahom M (n + H))⁻¹ ≤ (ahom M n)⁻¹ *
            (1 + 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (H : ℝ) / d +
              Clower * M.delta ^ 4 * (H : ℝ) ^ 2 +
              Clower * M.delta ^ 2 * |Real.log M.delta|) := hlowerRaw
        _ ≤ (ahom M n)⁻¹ *
            (1 + 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (H : ℝ) / d + error) := by
          apply mul_le_mul_of_nonneg_left _ hprevInv.le
          linarith
    have hlog := Section5Support.abs_centered_log_increment_le_of_one_step_bounds
      M n H error hupperCommon hlowerCommon
    have hnext : J + (q + 1) * H = n + H := by
      simp [n, Nat.add_mul, Nat.add_assoc]
    have hcurrent : J + q * H = n := by rfl
    rw [hnext, hcurrent]
    simpa only [sharpCenteredLog, error, Nat.cast_add] using hlog
  · intro q r hrpos hrH
    let n : ℕ := J + q * H
    let error : ℝ := C * M.delta ^ 4 * (r : ℝ) ^ 2 +
      C * M.delta ^ 2 * |Real.log M.delta|
    have hrinv : (r : ℝ) ≤ M.delta⁻¹ := by
      have hrHreal : (r : ℝ) ≤ H := by exact_mod_cast hrH.le
      exact hrHreal.trans hHinv
    have hnsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n := by
      dsimp [n]
      omega
    have hupperRaw := hUpper M n r hrinv hnsource
    have hlowerRaw := hLower M n r hrinv hnsource
    have hprev : 0 < ahom M n :=
      (Real.exp_pos _).trans_le
        (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M n)
    have hprevInv : 0 < (ahom M n)⁻¹ := inv_pos.mpr hprev
    have herrorUpper :
        Cupper * M.delta ^ 4 * (r : ℝ) ^ 2 +
            Cupper * M.delta ^ 2 * |Real.log M.delta| ≤ error := by
      dsimp [error]
      have hfour : 0 ≤ M.delta ^ 4 * (r : ℝ) ^ 2 := by positivity
      have htwo : 0 ≤ M.delta ^ 2 * |Real.log M.delta| := by positivity
      nlinarith
    have herrorLower :
        Clower * M.delta ^ 4 * (r : ℝ) ^ 2 +
            Clower * M.delta ^ 2 * |Real.log M.delta| ≤ error := by
      dsimp [error]
      have hfour : 0 ≤ M.delta ^ 4 * (r : ℝ) ^ 2 := by positivity
      have htwo : 0 ≤ M.delta ^ 2 * |Real.log M.delta| := by positivity
      nlinarith
    have hupperCommon :
        ahom M (n + r) ≤ ahom M n *
          (1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (r : ℝ) / d + error) := by
      calc
        ahom M (n + r) ≤ ahom M n *
            (1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (r : ℝ) / d +
              Cupper * M.delta ^ 4 * (r : ℝ) ^ 2 +
              Cupper * M.delta ^ 2 * |Real.log M.delta|) := hupperRaw
        _ ≤ ahom M n *
            (1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (r : ℝ) / d + error) := by
          apply mul_le_mul_of_nonneg_left _ hprev.le
          linarith
    have hlowerCommon :
        (ahom M (n + r))⁻¹ ≤ (ahom M n)⁻¹ *
          (1 + 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (r : ℝ) / d + error) := by
      calc
        (ahom M (n + r))⁻¹ ≤ (ahom M n)⁻¹ *
            (1 + 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (r : ℝ) / d +
              Clower * M.delta ^ 4 * (r : ℝ) ^ 2 +
              Clower * M.delta ^ 2 * |Real.log M.delta|) := hlowerRaw
        _ ≤ (ahom M n)⁻¹ *
            (1 + 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (r : ℝ) / d + error) := by
          apply mul_le_mul_of_nonneg_left _ hprevInv.le
          linarith
    have hlog := Section5Support.abs_centered_log_increment_le_of_one_step_bounds
      M n r error hupperCommon hlowerCommon
    have hnext : J + q * H + r = n + r := by rfl
    have hcurrent : J + q * H = n := by rfl
    rw [hnext, hcurrent]
    simpa only [sharpCenteredLog, error, Nat.cast_add] using hlog

/-- The block-telescoping conclusion before absorbing the quadratic disorder term into the logarithmic error. -/
def SharpBlockTelescopeConclusion (d : ℕ) : Prop :=
  ∃ delta0 K : ℝ, 0 < delta0 ∧ 0 < K ∧
    ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      M.delta ≤ delta0 → ∀ m : ℕ,
        |Real.log (ahom M m) +
            2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d| ≤
          K * M.delta ^ 2 * |Real.log M.delta| +
            (1 + (m : ℝ) * M.delta) *
              (K * M.delta ^ 2 +
                K * M.delta ^ 2 * |Real.log M.delta|)

private theorem abs_block_telescope {F : ℕ → ℝ} {J H : ℕ} {base error : ℝ}
    (hbase : |F J| ≤ base)
    (hstep : ∀ q : ℕ, |F (J + (q + 1) * H) - F (J + q * H)| ≤ error) :
    ∀ q : ℕ, |F (J + q * H)| ≤ base + (q : ℝ) * error := by
  intro q
  induction q with
  | zero => simpa using hbase
  | succ q ih =>
      have htriangle :
          |F (J + (q + 1) * H) - F (J + q * H) + F (J + q * H)| ≤
            |F (J + (q + 1) * H) - F (J + q * H)| +
              |F (J + q * H)| := abs_add_le _ _
      calc
        |F (J + (q + 1) * H)| =
            |F (J + (q + 1) * H) - F (J + q * H) +
              F (J + q * H)| := by congr 1; ring
        _ ≤ |F (J + (q + 1) * H) - F (J + q * H)| +
              |F (J + q * H)| := htriangle
        _ ≤ error + (base + (q : ℝ) * error) :=
          add_le_add (hstep q) ih
        _ = base + ((q + 1 : ℕ) : ℝ) * error := by
          push_cast
          ring

private theorem abs_block_telescope_with_remainder
    {F : ℕ → ℝ} {J H m : ℕ} {base error : ℝ}
    (hH : 0 < H) (hJm : J < m)
    (hbase : |F J| ≤ base)
    (hfull : ∀ q : ℕ,
      |F (J + (q + 1) * H) - F (J + q * H)| ≤ error)
    (hremainder : ∀ (q r : ℕ), 0 < r → r < H →
      |F (J + q * H + r) - F (J + q * H)| ≤ error) :
    |F m| ≤ base + (((m - J) / H + 1 : ℕ) : ℝ) * error := by
  let N : ℕ := m - J
  let q : ℕ := N / H
  let r : ℕ := N % H
  have hrlt : r < H := by
    dsimp [r]
    exact Nat.mod_lt _ hH
  have hdecomp : N = q * H + r := by
    simpa [q, r, Nat.mul_comm] using (Nat.div_add_mod N H).symm
  have hmdecomp : m = J + q * H + r := by
    dsimp [N] at hdecomp
    omega
  have hfull' : |F (J + q * H)| ≤ base + (q : ℝ) * error :=
    abs_block_telescope hbase hfull q
  have hresult : |F m| ≤ base + ((q + 1 : ℕ) : ℝ) * error := by
    by_cases hr0 : r = 0
    · subst r
      calc
        |F m| = |F (J + q * H)| := by
          simpa [hr0] using congrArg (fun n => |F n|) hmdecomp
        _ ≤ base + (q : ℝ) * error := hfull'
        _ ≤ base + ((q + 1 : ℕ) : ℝ) * error := by
          have herror : 0 ≤ error := le_trans (abs_nonneg _) (hfull 0)
          push_cast
          nlinarith
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
      calc
        |F m| = |(F (J + q * H + r) - F (J + q * H)) +
            F (J + q * H)| := by rw [hmdecomp]; congr 1; ring
        _ ≤ |F (J + q * H + r) - F (J + q * H)| +
            |F (J + q * H)| := abs_add_le _ _
        _ ≤ error + (base + (q : ℝ) * error) :=
          add_le_add (hremainder q r hrpos hrlt) hfull'
        _ = base + ((q + 1 : ℕ) : ℝ) * error := by push_cast; ring
  simpa [q, N] using hresult

/-- Perform the source's quotient/remainder telescope
 from the logarithmic block increments. -/
theorem sharp_block_telescope_of_block_increments {d : ℕ}
    (hIncrements : SharpBlockIncrementConclusion d) :
    SharpBlockTelescopeConclusion d := by
  rcases hIncrements with
    ⟨delta0, C, hdelta0, hC, hIncrements⟩
  refine ⟨delta0, 2 * C, hdelta0, by positivity, ?_⟩
  intro M hM m
  rcases hIncrements M hM with
    ⟨J, H, hH, hHupper, hHlower, hbase, hfull, hremainder⟩
  by_cases hmJ : m ≤ J
  · have hm := hbase m hmJ
    have hbaseNonneg :
        0 ≤ C * M.delta ^ 2 * |Real.log M.delta| := by positivity
    have hnonneg :
        0 ≤ (1 + (m : ℝ) * M.delta) *
          ((2 * C) * M.delta ^ 2 +
            (2 * C) * M.delta ^ 2 * |Real.log M.delta|) := by
      apply mul_nonneg
      · exact add_nonneg zero_le_one
          (mul_nonneg (Nat.cast_nonneg m) M.shellPrefix.delta_pos.le)
      · exact add_nonneg (by positivity) (by positivity)
    exact hm.trans (by nlinarith [hnonneg, hbaseNonneg])
  · have hJm : J < m := Nat.lt_of_not_ge hmJ
    let N : ℕ := m - J
    let q : ℕ := N / H
    let A : ℝ := C * M.delta ^ 2
    let B : ℝ := C * M.delta ^ 2 * |Real.log M.delta|
    let E : ℝ := C * M.delta ^ 4 * (H : ℝ) ^ 2 + B
    have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
    have hE : 0 ≤ E := by dsimp [E, B]; positivity
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have htotal :
        |sharpCenteredLog M m| ≤ B + ((q + 1 : ℕ) : ℝ) * E := by
      apply abs_block_telescope_with_remainder (F := sharpCenteredLog M)
        hH hJm
      · simpa [B] using hbase J le_rfl
      · intro i
        simpa [E, B] using hfull i
      · intro i s hspos hsH
        have hrem := hremainder i s hspos hsH
        have hscast : (s : ℝ) ≤ H := by exact_mod_cast hsH.le
        have hsnonneg : (0 : ℝ) ≤ s := by positivity
        have hHnonneg : (0 : ℝ) ≤ H := by positivity
        have hssq : (s : ℝ) ^ 2 ≤ (H : ℝ) ^ 2 := by nlinarith
        have hcoef : 0 ≤ C * M.delta ^ 4 := by positivity
        dsimp [E, B]
        exact hrem.trans (add_le_add
          (mul_le_mul_of_nonneg_left hssq hcoef) le_rfl)
    have hEbound : E ≤ A + B := by
      have hdeltaHnonneg : 0 ≤ M.delta * (H : ℝ) := by positivity
      have hdeltaHsq : (M.delta * (H : ℝ)) ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (1 - M.delta * (H : ℝ))]
      have hrewrite :
          C * M.delta ^ 4 * (H : ℝ) ^ 2 =
            A * (M.delta * (H : ℝ)) ^ 2 := by
        dsimp [A]
        ring
      change C * M.delta ^ 4 * (H : ℝ) ^ 2 + B ≤ A + B
      rw [hrewrite]
      simpa [add_comm] using add_le_add_right
        (mul_le_of_le_one_right hA hdeltaHsq) B
    have hqH : q * H ≤ m := by
      have hqHN : q * H ≤ N := by
        dsimp [q]
        simpa [Nat.mul_comm] using Nat.mul_div_le N H
      dsimp [N] at hqHN
      omega
    have hqHreal : (q : ℝ) * (H : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hqH
    have hqbound : (q : ℝ) + 1 ≤ 2 * (1 + (m : ℝ) * M.delta) := by
      have hqhalf : (q : ℝ) / 2 ≤ (m : ℝ) * M.delta := by
        have hmul := mul_le_mul_of_nonneg_left hHlower (Nat.cast_nonneg q)
        have hscale := mul_le_mul_of_nonneg_right hqHreal hdelta.le
        nlinarith
      nlinarith
    have hcount :
        ((q + 1 : ℕ) : ℝ) * E ≤
          2 * (1 + (m : ℝ) * M.delta) * (A + B) := by
      push_cast
      exact (mul_le_mul hqbound hEbound hE
        (by positivity : 0 ≤ 2 * (1 + (m : ℝ) * M.delta))).trans_eq
          (by ring)
    change |sharpCenteredLog M m| ≤ _
    calc
      |sharpCenteredLog M m| ≤ B + ((q + 1 : ℕ) : ℝ) * E := htotal
      _ ≤ B + 2 * (1 + (m : ℝ) * M.delta) * (A + B) :=
        by simpa [add_comm] using add_le_add_left hcount B
      _ ≤ 2 * B + 2 * (1 + (m : ℝ) * M.delta) * (A + B) := by
        linarith
      _ = (2 * C) * M.delta ^ 2 * |Real.log M.delta| +
          (1 + (m : ℝ) * M.delta) *
            ((2 * C) * M.delta ^ 2 +
              (2 * C) * M.delta ^ 2 * |Real.log M.delta|) := by
        dsimp [A, B]
        ring

private theorem half_le_abs_log_delta {delta : ℝ}
    (hdelta : 0 < delta) (hhalf : delta ≤ (1 : ℝ) / 2) :
    (1 : ℝ) / 2 ≤ |Real.log delta| := by
  have hdeltaOne : delta ≤ 1 := hhalf.trans (by norm_num)
  have hlogNonpos : Real.log delta ≤ 0 := Real.log_nonpos hdelta.le hdeltaOne
  rw [abs_of_nonpos hlogNonpos]
  have hmono : Real.log delta ≤ Real.log ((1 : ℝ) / 2) :=
    Real.log_le_log hdelta hhalf
  have hhalfLog : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    simp
  rw [hhalfLog] at hmono
  have hlogTwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  linarith

/-- Absorb the penultimate block-telescope estimate into the exact frozen
sharp-asymptotic conclusion. -/
theorem sharp_asymptotic_of_block_telescope {d : ℕ}
    (hBlocks : SharpBlockTelescopeConclusion d) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        M.delta ≤ delta0 → ∀ m : ℕ,
          |Real.log (ahom M m) +
              2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d| ≤
            C * M.delta ^ 2 * |Real.log M.delta| *
              (1 + (m : ℝ) * M.delta) := by
  rcases hBlocks with ⟨delta0, K, hdelta0, hK, hBlocks⟩
  refine ⟨delta0, 4 * K, hdelta0, by positivity, ?_⟩
  intro M hM m
  have hlog : (1 : ℝ) / 2 ≤ |Real.log M.delta| :=
    half_le_abs_log_delta M.shellPrefix.delta_pos M.shellPrefix.delta_le_half
  let A : ℝ := K * M.delta ^ 2
  let B : ℝ := K * M.delta ^ 2 * |Real.log M.delta|
  let T : ℝ := 1 + (m : ℝ) * M.delta
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hT : 1 ≤ T := by
    dsimp [T]
    exact le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg m) M.shellPrefix.delta_pos.le)
  have hAB : A ≤ 2 * B := by
    dsimp [A, B]
    have hscale : 0 ≤ K * M.delta ^ 2 := by positivity
    nlinarith [mul_nonneg hscale (sub_nonneg.mpr hlog)]
  have hsum : B + T * (A + B) ≤ 4 * B * T := by
    have hmul : T * (A + B) ≤ T * (2 * B + B) :=
      mul_le_mul_of_nonneg_left (add_le_add hAB le_rfl) (zero_le_one.trans hT)
    have hBT : B ≤ B * T := by
      calc
        B = B * 1 := by ring
        _ ≤ B * T := mul_le_mul_of_nonneg_left hT hB
    calc
      B + T * (A + B) ≤ B + T * (2 * B + B) := add_le_add le_rfl hmul
      _ = B + 3 * B * T := by ring
      _ ≤ B * T + 3 * B * T := add_le_add hBT le_rfl
      _ = 4 * B * T := by ring
  calc
    |Real.log (ahom M m) +
        2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d| ≤
        B + T * (A + B) := by
          simpa [A, B, T] using hBlocks M hM m
    _ ≤ 4 * B * T := hsum
    _ = (4 * K) * M.delta ^ 2 * |Real.log M.delta| *
        (1 + (m : ℝ) * M.delta) := by dsimp [B, T]; ring

/-- The source-facing sharp asymptotic follows from the explicit one-step upper and lower estimates. -/
theorem sharp_asymptotic_of_one_step_bounds {d : ℕ}
    (hUpper : SharpOneStepUpperConclusion d)
    (hLower : SharpOneStepLowerConclusion d) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        M.delta ≤ delta0 → ∀ m : ℕ,
          |Real.log (ahom M m) +
              2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d| ≤
            C * M.delta ^ 2 * |Real.log M.delta| *
              (1 + (m : ℝ) * M.delta) :=
  sharp_asymptotic_of_block_telescope
    (sharp_block_telescope_of_block_increments
      (sharp_block_increments_of_one_step_bounds hUpper hLower))

/-- Promotion boundary after separating off the exact planar branch.  The two
analytic one-step nodes are needed only in dimensions at least three; the
dimension-zero and dimension-one cases contain no standing GMC model. -/
theorem sharp_asymptotic_of_high_dimensional_one_step_bounds {d : ℕ}
    (hUpper : 3 ≤ d → SharpOneStepUpperConclusion d)
    (hLower : 3 ≤ d → SharpOneStepLowerConclusion d) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        M.delta ≤ delta0 → ∀ m : ℕ,
          |Real.log (ahom M m) +
              2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d| ≤
            C * M.delta ^ 2 * |Real.log M.delta| *
              (1 + (m : ℝ) * M.delta) := by
  by_cases hd2 : d = 2
  · subst d
    exact sharp_asymptotic_two_dimensional
  by_cases hd3 : 3 ≤ d
  · exact sharp_asymptotic_of_one_step_bounds (hUpper hd3) (hLower hd3)
  · refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro M _hdelta _m
    have hdim := M.shellPrefix.dimension
    omega

/-- Final assembly seam after the concrete primal one-step closure: only the
high-dimensional reciprocal one-step theorem is carried as the hypothesis `hLower`. -/
theorem sharp_asymptotic_of_high_dimensional_lower_bound {d : ℕ}
    (hLower : 3 ≤ d → SharpOneStepLowerConclusion d) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        M.delta ≤ delta0 → ∀ m : ℕ,
          |Real.log (ahom M m) +
              2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d| ≤
            C * M.delta ^ 2 * |Real.log M.delta| *
              (1 + (m : ℝ) * M.delta) := by
  apply sharp_asymptotic_of_high_dimensional_one_step_bounds
  · intro hd
    let : NeZero d := ⟨by omega⟩
    exact sharpOneStepUpperConclusion_of_concrete hd
  · exact hLower

end

end SubdiffusiveProcess.Providers.Section5
